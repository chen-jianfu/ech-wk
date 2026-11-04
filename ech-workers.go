package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/binary"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/gorilla/websocket"
)

// ======================== 全局参数 ========================

// Config 配置文件结构（与 ech-workers.go 的 config.json 兼容）
type Config struct {
	Listen    string   `json:"listen"`
	Server    string   `json:"server"`
	ServerIP  []string `json:"serverIP"`
	Token     string   `json:"token"`
	DNS       string   `json:"dns"`
	ECHDomain    string   `json:"echDomain"`
	Routing      string   `json:"routing"`
	EnableECH    string   `json:"enableECH"`
	PrivateIP    []string `json:"privateIP"`
	PrivateDomain []string `json:"privateDomain"`
}

var (
	listenAddr  string
	serverAddr  string
	serverIP    string
	token       string
	dnsServer   string
	echDomain   string
	routingMode string // 分流模式: "global", "bypass_cn", "none"
	enableECH   string   // ECH开关: "y"=开启, "n"=关闭，默认 "y"
	configPath  string

	privateIPFlag     string
	privateDomainFlag string

	echListMu  sync.RWMutex
	echList    []byte
	echVersion uint64 // ECH 配置版本号，用于判断 DoH 客户端是否需要重建

	// 中国IP列表（IPv4）
	chinaIPRangesMu sync.RWMutex
	chinaIPRanges   []ipRange

	// 中国IP列表（IPv6）
	chinaIPV6RangesMu sync.RWMutex
	chinaIPV6Ranges   []ipRangeV6

	// 中国域名列表
	chinaDomainsMu sync.RWMutex
	chinaDomains   map[string]bool

	// 白名单 IP CIDR 列表
	privateIPRangesMu sync.RWMutex
	privateIPRanges   []ipRange

	// 白名单域名列表
	privateDomainsMu sync.RWMutex
	privateDomains   map[string]bool
)

// ======================== 性能优化全局缓存 ========================

var (
	// 系统根证书缓存（避免每次 TLS 握手重复加载）
	systemCertPoolOnce sync.Once
	systemCertPool     *x509.CertPool
	systemCertPoolErr  error

	// TLS 会话缓存（会话复用，降低握手开销）
	tlsSessionCache = tls.NewLRUClientSessionCache(64)

	// DoH 客户端缓存（按 ECH 配置版本重建，连接复用）
	dohClientValue atomic.Value // *dohClientBox
)

// 分流 DNS 缓存
const (
	dnsCacheTTL       = 5 * time.Minute
	dnsCacheNegTTL    = 30 * time.Second
	dnsCacheNegMaxTTL = 5 * time.Minute
	dnsCacheMaxLen    = 4096
)

var (
	dnsCacheMu sync.RWMutex
	dnsCache   = make(map[string]dnsCacheEntry)

	dnsInflightMu sync.Mutex
	dnsInflight   = make(map[string]*dnsLookupCall)

	// 可注入，便于测试
	lookupIPFunc = func(ctx context.Context, host string) ([]net.IP, error) {
		return net.DefaultResolver.LookupIP(ctx, "ip", host)
	}
	dnsLookupTimeout = 2 * time.Second
)

// ipRange 表示一个IPv4 IP范围
type ipRange struct {
	start uint32
	end   uint32
}

// ipRangeV6 表示一个IPv6 IP范围
type ipRangeV6 struct {
	start [16]byte
	end   [16]byte
}

// dnsCacheEntry 分流判断用的 DNS 解析缓存条目
type dnsCacheEntry struct {
	ips      []net.IP // 解析结果，nil 表示负缓存（解析失败）
	expireAt time.Time
	failures int
}

// dnsLookupCall 合并同一域名的并发解析请求
type dnsLookupCall struct {
	done chan struct{}
	ips  []net.IP
}

// lookupIPWithCache 带缓存的域名解析，避免每个请求都同步查询 DNS
func lookupIPWithCache(host string) []net.IP {
	now := time.Now()

	dnsCacheMu.RLock()
	prev, ok := dnsCache[host]
	dnsCacheMu.RUnlock()
	if ok && now.Before(prev.expireAt) {
		return prev.ips
	}

	// 合并同一域名的并发解析，避免缓存失效瞬间重复查询 DNS
	dnsInflightMu.Lock()
	if call, ok := dnsInflight[host]; ok {
		dnsInflightMu.Unlock()
		<-call.done
		return call.ips
	}
	call := &dnsLookupCall{done: make(chan struct{})}
	dnsInflight[host] = call
	dnsInflightMu.Unlock()

	var entry dnsCacheEntry
	func() {
		// 确保等待方一定会被唤醒，即使解析过程发生 panic
		defer func() {
			call.ips = entry.ips
			dnsInflightMu.Lock()
			delete(dnsInflight, host)
			dnsInflightMu.Unlock()
			close(call.done)
		}()

		entry = resolveDNSCacheEntry(host, prev)

		dnsCacheMu.Lock()
		storeDNSCacheEntryLocked(host, entry)
		dnsCacheMu.Unlock()
	}()

	return entry.ips
}

// resolveDNSCacheEntry 执行一次带超时的域名解析，并生成缓存条目
func resolveDNSCacheEntry(host string, prev dnsCacheEntry) dnsCacheEntry {
	ctx, cancel := context.WithTimeout(context.Background(), dnsLookupTimeout)
	defer cancel()

	start := time.Now()
	ips, err := lookupIPFunc(ctx, host)
	elapsed := time.Since(start)
	if elapsed > 500*time.Millisecond {
		log.Printf("[DNS] 解析 %s 耗时 %v (err=%v)", host, elapsed, err)
	}

	// 有部分结果时也接受，避免 DNS 超时导致可用的 IP 被丢弃
	if len(ips) > 0 {
		return dnsCacheEntry{
			ips:      ips,
			expireAt: time.Now().Add(dnsCacheTTL),
		}
	}

	failures := 1
	if prev.ips == nil && prev.failures > 0 {
		failures = prev.failures + 1
	}
	return dnsCacheEntry{
		expireAt: time.Now().Add(dnsNegativeTTL(failures)),
		failures: failures,
	}
}

// dnsNegativeTTL 解析失败后的退避时间：30s 起，逐次翻倍，上限 5 分钟
func dnsNegativeTTL(failures int) time.Duration {
	ttl := dnsCacheNegTTL
	for i := 1; i < failures; i++ {
		if ttl >= dnsCacheNegMaxTTL {
			return dnsCacheNegMaxTTL
		}
		ttl *= 2
	}
	if ttl > dnsCacheNegMaxTTL {
		return dnsCacheNegMaxTTL
	}
	return ttl
}

// storeDNSCacheEntryLocked 写入缓存并在容量达到上限时清理过期条目，调用方需持有 dnsCacheMu
func storeDNSCacheEntryLocked(host string, entry dnsCacheEntry) {
	now := time.Now()
	if len(dnsCache) >= dnsCacheMaxLen {
		for k, v := range dnsCache {
			if now.After(v.expireAt) {
				delete(dnsCache, k)
			}
		}
		if len(dnsCache) >= dnsCacheMaxLen {
			dnsCache = make(map[string]dnsCacheEntry)
		}
	}
	dnsCache[host] = entry
}

func init() {
	flag.StringVar(&listenAddr, "l", "127.0.0.1:30000", "代理监听地址 (支持 SOCKS5 和 HTTP)")
	flag.StringVar(&serverAddr, "f", "", "服务端地址 (格式: x.x.workers.dev:443)")
	flag.StringVar(&serverIP, "ip", "", "指定服务端 IP（绕过 DNS 解析）")
	flag.StringVar(&token, "token", "", "身份验证令牌")
	flag.StringVar(&dnsServer, "dns", "dns.alidns.com/dns-query", "ECH 查询 DoH 服务器")
	flag.StringVar(&echDomain, "ech", "cloudflare-ech.com", "ECH 查询域名")
	flag.StringVar(&enableECH, "enable_ech", "y", "ECH开关: y=开启, n=关闭，默认开启")
	flag.StringVar(&routingMode, "routing", "global", "分流模式: global(全局代理), bypass_cn(中国域名直连/非中国域名代理), none(不改变代理)")
	flag.StringVar(&configPath, "config", "config.json", "配置文件路径")
	flag.StringVar(&privateIPFlag, "private_ip", "", "局域网直连 IP 白名单 (CIDR, 逗号分隔)")
	flag.StringVar(&privateDomainFlag, "private_domain", "", "局域网直连域名白名单 (逗号分隔)")
}

func loadConfig(path string) (*Config, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, fmt.Errorf("读取配置文件失败: %w", err)
	}

	var cfg Config
	if err := json.Unmarshal(data, &cfg); err != nil {
		return nil, fmt.Errorf("解析配置文件失败: %w", err)
	}

	return &cfg, nil
}

// parseListFlag 解析逗号分隔的列表参数
func parseListFlag(value string) []string {
	var items []string
	for _, item := range strings.Split(value, ",") {
		item = strings.TrimSpace(item)
		if item != "" {
			items = append(items, item)
		}
	}
	return items
}

// resolvePrivateLists 合并配置文件与命令行参数，命令行参数优先
func resolvePrivateLists(cfg *Config, ipFlagSet, domainFlagSet bool, ipFlag, domainFlag string) ([]string, []string) {
	var ips, domains []string
	if cfg != nil {
		ips = cfg.PrivateIP
		domains = cfg.PrivateDomain
	}
	if ipFlagSet {
		ips = parseListFlag(ipFlag)
	}
	if domainFlagSet {
		domains = parseListFlag(domainFlag)
	}
	return ips, domains
}

func main() {
	flag.Parse()

	// 记录命令行显式设置的参数，保证其优先级高于配置文件
	visited := make(map[string]bool)
	flag.Visit(func(f *flag.Flag) {
		visited[f.Name] = true
	})

	cfg, err := loadConfig(configPath)
	if err != nil {
		log.Printf("[配置] 加载配置文件失败: %v", err)
	}

	if cfg != nil {
		log.Printf("[配置] 已加载配置文件: %s", configPath)
		if !visited["l"] && cfg.Listen != "" {
			listenAddr = cfg.Listen
		}
		if !visited["f"] && cfg.Server != "" {
			serverAddr = cfg.Server
		}
		if !visited["ip"] && len(cfg.ServerIP) > 0 {
			serverIP = cfg.ServerIP[0]
			if len(cfg.ServerIP) > 1 {
				log.Printf("[配置] serverIP 仅支持单个地址，已使用第一个: %s", serverIP)
			}
		}
		if !visited["token"] && cfg.Token != "" {
			token = cfg.Token
		}
		if !visited["dns"] && cfg.DNS != "" {
			dnsServer = cfg.DNS
		}
		if !visited["ech"] && cfg.ECHDomain != "" {
			echDomain = cfg.ECHDomain
		}
		if !visited["enable_ech"] && cfg.EnableECH != "" {
			enableECH = cfg.EnableECH
		}
		if !visited["routing"] && cfg.Routing != "" {
			routingMode = cfg.Routing
		}
	}

	// 加载局域网直连白名单（命令行参数优先于配置文件）
	privateIPs, privateDomains := resolvePrivateLists(cfg, visited["private_ip"], visited["private_domain"], privateIPFlag, privateDomainFlag)
	if len(privateIPs) > 0 {
		loadPrivateIPList(privateIPs)
	}
	if len(privateDomains) > 0 {
		loadPrivateDomainList(privateDomains)
	}

	if serverAddr == "" {
		log.Fatal("必须指定服务端地址 -f 或在配置文件中指定\n\n示例:\n  ./client -l 127.0.0.1:1080 -f your-worker.workers.dev:443 -token your-token\n\n配置文件示例 (config.json):\n{\n  \"listen\": \"127.0.0.1:30000\",\n  \"server\": \"your-worker.workers.dev:443\",\n  \"serverIP\": [\"1.2.3.4\"],\n  \"token\": \"your-token\",\n  \"dns\": \"dns.alidns.com/dns-query\",\n  \"echDomain\": \"cloudflare-ech.com\",\n  \"routing\": \"global\"\n}")
	}

	log.Printf("[启动] 正在获取 ECH 配置...")
	if err := prepareECH(); err != nil {
		log.Fatalf("[启动] 获取 ECH 配置失败: %v", err)
	}

	// 加载中国IP列表（如果需要）
	if routingMode == "bypass_cn" {
		log.Printf("[启动] 分流模式: 中国域名直连/非中国域名代理，正在加载中国IP列表和域名列表...")
		ipv4Count := 0
		ipv6Count := 0
	domainCount := 0

		if err := loadChinaIPList(); err != nil {
			log.Printf("[警告] 加载中国IPv4列表失败: %v", err)
		} else {
			chinaIPRangesMu.RLock()
			ipv4Count = len(chinaIPRanges)
			chinaIPRangesMu.RUnlock()
		}

		if err := loadChinaIPV6List(); err != nil {
			log.Printf("[警告] 加载中国IPv6列表失败: %v", err)
		} else {
			chinaIPV6RangesMu.RLock()
			ipv6Count = len(chinaIPV6Ranges)
			chinaIPV6RangesMu.RUnlock()
		}

		if err := loadChinaDomainList(); err != nil {
		log.Printf("[警告] 加载中国域名列表失败: %v", err)
	} else {
		chinaDomainsMu.RLock()
		domainCount = len(chinaDomains)
		chinaDomainsMu.RUnlock()
	}

	if ipv4Count > 0 || ipv6Count > 0 || domainCount > 0 {
		log.Printf("[启动] 已加载 %d 个中国IPv4段, %d 个中国IPv6段, %d 个中国域名", ipv4Count, ipv6Count, domainCount)
	} else {
		log.Printf("[警告] 未加载到任何中国IP或域名列表，将使用默认规则")
	}

} else if routingMode == "global" {
		log.Printf("[启动] 分流模式: 全局代理")
	} else if routingMode == "none" {
		log.Printf("[启动] 分流模式: 不改变代理（直连模式）")
	} else {
		log.Printf("[警告] 未知的分流模式: %s，使用默认模式 global", routingMode)
		routingMode = "global"
	}

	runProxyServer(listenAddr)
}

// ======================== 工具函数 ========================

// ipToUint32 将IP地址转换为uint32
func ipToUint32(ip net.IP) uint32 {
	ip = ip.To4()
	if ip == nil {
		return 0
	}
	return uint32(ip[0])<<24 | uint32(ip[1])<<16 | uint32(ip[2])<<8 | uint32(ip[3])
}

// isChinaIP 检查IP是否在中国IP列表中（支持IPv4和IPv6）
func isChinaIP(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}

	// 检查IPv4
	if ip.To4() != nil {
		ipUint32 := ipToUint32(ip)
		if ipUint32 == 0 {
			return false
		}

		chinaIPRangesMu.RLock()
		defer chinaIPRangesMu.RUnlock()

		// 二分查找
		left, right := 0, len(chinaIPRanges)
		for left < right {
			mid := (left + right) / 2
			r := chinaIPRanges[mid]
			if ipUint32 < r.start {
				right = mid
			} else if ipUint32 > r.end {
				left = mid + 1
			} else {
				return true
			}
		}
		return false
	}

	// 检查IPv6
	ipBytes := ip.To16()
	if ipBytes == nil {
		return false
	}

	var ipArray [16]byte
	copy(ipArray[:], ipBytes)

	chinaIPV6RangesMu.RLock()
	defer chinaIPV6RangesMu.RUnlock()

	// 二分查找IPv6
	left, right := 0, len(chinaIPV6Ranges)
	for left < right {
		mid := (left + right) / 2
		r := chinaIPV6Ranges[mid]

		// 比较起始IP
		cmpStart := compareIPv6(ipArray, r.start)
		if cmpStart < 0 {
			right = mid
			continue
		}

		// 比较结束IP
		cmpEnd := compareIPv6(ipArray, r.end)
		if cmpEnd > 0 {
			left = mid + 1
			continue
		}

		// 在范围内
		return true
	}
	return false
}

// compareIPv6 比较两个IPv6地址，返回 -1, 0, 或 1
func compareIPv6(a, b [16]byte) int {
	for i := 0; i < 16; i++ {
		if a[i] < b[i] {
			return -1
		} else if a[i] > b[i] {
			return 1
		}
	}
	return 0
}

// downloadIPList 下载IP列表文件
func downloadIPList(url, filePath string) error {
	log.Printf("[下载] 正在下载 IP 列表: %s", url)

	client := &http.Client{
		Timeout: 30 * time.Second,
	}

	resp, err := client.Get(url)
	if err != nil {
		return fmt.Errorf("下载失败: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("下载失败: HTTP %d", resp.StatusCode)
	}

	// 读取内容
	content, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("读取下载内容失败: %w", err)
	}

	// 保存到文件
	if err := os.WriteFile(filePath, content, 0644); err != nil {
		return fmt.Errorf("保存文件失败: %w", err)
	}

	log.Printf("[下载] 已保存到: %s", filePath)
	return nil
}

// loadChinaIPList 从程序目录加载中国IP列表
func loadChinaIPList() error {
	// 获取可执行文件所在目录
	exePath, err := os.Executable()
	if err != nil {
		return fmt.Errorf("获取可执行文件路径失败: %w", err)
	}
	exeDir := filepath.Dir(exePath)
	ipListFile := filepath.Join(exeDir, "chn_ip.txt")

	// 如果文件不存在，尝试当前目录
	if _, err := os.Stat(ipListFile); os.IsNotExist(err) {
		ipListFile = "chn_ip.txt"
	}

	// 检查文件是否存在或为空
	needDownload := false
	if info, err := os.Stat(ipListFile); os.IsNotExist(err) {
		needDownload = true
		log.Printf("[加载] IPv4 列表文件不存在，将自动下载")
	} else if info.Size() == 0 {
		needDownload = true
		log.Printf("[加载] IPv4 列表文件为空，将自动下载")
	}

	// 如果需要下载，先下载文件
	if needDownload {
		url := "https://raw.githubusercontent.com/mayaxcn/china-ip-list/refs/heads/master/chn_ip.txt"
		if err := downloadIPList(url, ipListFile); err != nil {
			return fmt.Errorf("自动下载 IPv4 列表失败: %w", err)
		}
	}

	file, err := os.Open(ipListFile)
	if err != nil {
		return fmt.Errorf("打开IP列表文件失败: %w", err)
	}
	defer file.Close()

	var ranges []ipRange
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		parts := strings.Fields(line)
		if len(parts) < 2 {
			continue
		}

		startIP := net.ParseIP(parts[0])
		endIP := net.ParseIP(parts[1])
		if startIP == nil || endIP == nil {
			continue
		}

		start := ipToUint32(startIP)
		end := ipToUint32(endIP)
		if start > 0 && end > 0 && start <= end {
			ranges = append(ranges, ipRange{start: start, end: end})
		}
	}

	if err := scanner.Err(); err != nil {
		return fmt.Errorf("读取IP列表文件失败: %w", err)
	}

	if len(ranges) == 0 {
		return errors.New("IP列表为空")
	}

	// 按起始IP排序
	sort.Slice(ranges, func(i, j int) bool {
		return ranges[i].start < ranges[j].start
	})

	chinaIPRangesMu.Lock()
	chinaIPRanges = ranges
	chinaIPRangesMu.Unlock()

	return nil
}

// loadChinaIPV6List 从程序目录加载中国IPv6 IP列表
func loadChinaIPV6List() error {
	// 获取可执行文件所在目录
	exePath, err := os.Executable()
	if err != nil {
		return fmt.Errorf("获取可执行文件路径失败: %w", err)
	}
	exeDir := filepath.Dir(exePath)
	ipListFile := filepath.Join(exeDir, "chn_ip_v6.txt")

	// 如果文件不存在，尝试当前目录
	if _, err := os.Stat(ipListFile); os.IsNotExist(err) {
		ipListFile = "chn_ip_v6.txt"
	}

	// 检查文件是否存在或为空
	needDownload := false
	if info, err := os.Stat(ipListFile); os.IsNotExist(err) {
		needDownload = true
		log.Printf("[加载] IPv6 列表文件不存在，将自动下载")
	} else if info.Size() == 0 {
		needDownload = true
		log.Printf("[加载] IPv6 列表文件为空，将自动下载")
	}

	// 如果需要下载，先下载文件
	if needDownload {
		url := "https://raw.githubusercontent.com/mayaxcn/china-ip-list/refs/heads/master/chn_ip_v6.txt"
		if err := downloadIPList(url, ipListFile); err != nil {
			log.Printf("[警告] 自动下载 IPv6 列表失败: %v，将跳过 IPv6 支持", err)
			return nil // IPv6 列表下载失败不算致命错误
		}
	}

	file, err := os.Open(ipListFile)
	if err != nil {
		// 文件打开失败，不算致命错误
		log.Printf("[警告] 打开 IPv6 IP列表文件失败: %v，将跳过 IPv6 支持", err)
		return nil
	}
	defer file.Close()

	var ranges []ipRangeV6
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		parts := strings.Fields(line)
		if len(parts) < 2 {
			continue
		}

		startIP := net.ParseIP(parts[0])
		endIP := net.ParseIP(parts[1])
		if startIP == nil || endIP == nil {
			continue
		}

		// 转换为16字节数组
		startBytes := startIP.To16()
		endBytes := endIP.To16()
		if startBytes == nil || endBytes == nil {
			continue
		}

		var start, end [16]byte
		copy(start[:], startBytes)
		copy(end[:], endBytes)

		// 检查范围是否有效
		if compareIPv6(start, end) <= 0 {
			ranges = append(ranges, ipRangeV6{start: start, end: end})
		}
	}

	if err := scanner.Err(); err != nil {
		return fmt.Errorf("读取IPv6 IP列表文件失败: %w", err)
	}

	if len(ranges) == 0 {
		// IPv6列表为空不算错误，可能文件不存在或为空
		return nil
	}

	// 按起始IP排序
	sort.Slice(ranges, func(i, j int) bool {
		return compareIPv6(ranges[i].start, ranges[j].start) < 0
	})

	chinaIPV6RangesMu.Lock()
	chinaIPV6Ranges = ranges
	chinaIPV6RangesMu.Unlock()

	return nil
}

// loadChinaDomainList 从程序目录加载中国域名列表（dnsmasq 格式: server=/domain.com/114.114.114.114）
func loadChinaDomainList() error {
	// 获取可执行文件所在目录
	exePath, err := os.Executable()
	if err != nil {
		return fmt.Errorf("获取可执行文件路径失败: %w", err)
	}
	exeDir := filepath.Dir(exePath)
	domainListFile := filepath.Join(exeDir, "chn_domain.txt")

	// 如果文件不存在，尝试当前目录
	if _, err := os.Stat(domainListFile); os.IsNotExist(err) {
		domainListFile = "chn_domain.txt"
	}

	// 检查文件是否存在或为空
	needDownload := false
	if info, err := os.Stat(domainListFile); os.IsNotExist(err) {
		needDownload = true
		log.Printf("[加载] 域名列表文件不存在，将自动下载")
	} else if info.Size() == 0 {
		needDownload = true
		log.Printf("[加载] 域名列表文件为空，将自动下载")
	}

	// 如果需要下载，先下载文件
	if needDownload {
		url := "https://raw.githubusercontent.com/mayaxcn/china-ip-list/refs/heads/master/chn_domain.txt"
		if err := downloadIPList(url, domainListFile); err != nil {
			return fmt.Errorf("自动下载域名列表失败: %w", err)
		}
	}

	file, err := os.Open(domainListFile)
	if err != nil {
		return fmt.Errorf("打开域名列表文件失败: %w", err)
	}
	defer file.Close()

	domains := make(map[string]bool, 128*1024)
	scanner := bufio.NewScanner(file)
	// 增加缓冲区大小以支持长行
	scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		// 解析 dnsmasq 格式: server=/domain.com/114.114.114.114
		domain := parseChinaDomain(line)
		if domain != "" {
			domains[domain] = true
		}
	}

	if err := scanner.Err(); err != nil {
		return fmt.Errorf("读取域名列表文件失败: %w", err)
	}

	if len(domains) == 0 {
		return errors.New("域名列表为空")
	}

	chinaDomainsMu.Lock()
	chinaDomains = domains
	chinaDomainsMu.Unlock()

	log.Printf("[加载] 已加载 %d 个中国域名", len(domains))
	return nil
}

// parseChinaDomain 从 dnsmasq 格式行中提取域名
// 格式: server=/domain.com/114.114.114.114
func parseChinaDomain(line string) string {
	if !strings.HasPrefix(line, "server=/") {
		return ""
	}
	rest := strings.TrimPrefix(line, "server=/")
	slashIdx := strings.Index(rest, "/")
	if slashIdx == -1 {
		return ""
	}
	return strings.ToLower(strings.TrimSpace(rest[:slashIdx]))
}

// isChinaDomain 检查域名是否是中国域名（支持精确匹配和父域匹配）
func isChinaDomain(host string) bool {
	if host == "" {
		return false
	}
	host = strings.ToLower(host)

	chinaDomainsMu.RLock()
	defer chinaDomainsMu.RUnlock()

	// 依次检查完整域名和每一级父域，子串切片不产生内存分配
	for {
		if chinaDomains[host] {
			return true
		}
		dot := strings.IndexByte(host, '.')
		if dot == -1 {
			return false
		}
		host = host[dot+1:]
	}
}

// loadPrivateIPList 加载白名单 IP CIDR 列表
func loadPrivateIPList(cidrs []string) {
	var ranges []ipRange
	for _, cidr := range cidrs {
		cidr = strings.TrimSpace(cidr)
		if cidr == "" {
			continue
		}
		// 单个 IPv4 默认按 /32 处理，方便直接填写
		if !strings.Contains(cidr, "/") {
			if ip := net.ParseIP(cidr); ip != nil && ip.To4() != nil {
				cidr += "/32"
			}
		}
		// 解析 CIDR 格式如 192.168.0.0/16
		ip, ipNet, err := net.ParseCIDR(cidr)
		if err != nil {
			log.Printf("[警告] 无效的白名单 IP CIDR: %s, 错误: %v", cidr, err)
			continue
		}
		// 只处理 IPv4
		if ip4 := ip.To4(); ip4 != nil {
			start := ipToUint32(ip4)
			// 计算掩码范围
			ones, bits := ipNet.Mask.Size()
			if bits == 32 {
				mask := uint32(0xFFFFFFFF) << (32 - ones)
				end := start | (^mask & 0xFFFFFFFF)
				if start <= end {
					ranges = append(ranges, ipRange{start: start, end: end})
				}
			}
		}
	}
	if len(ranges) > 0 {
		sort.Slice(ranges, func(i, j int) bool {
			return ranges[i].start < ranges[j].start
		})
		privateIPRangesMu.Lock()
		privateIPRanges = ranges
		privateIPRangesMu.Unlock()
		log.Printf("[加载] 已加载 %d 个白名单 IP 段", len(ranges))
	}
}

// loadPrivateDomainList 加载白名单域名列表
func loadPrivateDomainList(domains []string) {
	dom := make(map[string]bool)
	for _, d := range domains {
		d = strings.TrimSpace(strings.ToLower(d))
		if d != "" {
			dom[d] = true
		}
	}
	if len(dom) > 0 {
		privateDomainsMu.Lock()
		privateDomains = dom
		privateDomainsMu.Unlock()
		log.Printf("[加载] 已加载 %d 个白名单域名", len(dom))
	}
}

// isPrivateIP 检查 IP 是否在白名单 CIDR 中
func isPrivateIP(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}
	ip4 := ip.To4()
	if ip4 == nil {
		return false
	}
	ipUint32 := ipToUint32(ip4)
	if ipUint32 == 0 {
		return false
	}
	privateIPRangesMu.RLock()
	defer privateIPRangesMu.RUnlock()
	left, right := 0, len(privateIPRanges)
	for left < right {
		mid := (left + right) / 2
		r := privateIPRanges[mid]
		if ipUint32 < r.start {
			right = mid
		} else if ipUint32 > r.end {
			left = mid + 1
		} else {
			return true
		}
	}
	return false
}

// isPrivateDomain 检查域名是否在白名单中（支持后缀匹配）
func isPrivateDomain(host string) bool {
	if host == "" {
		return false
	}
	host = strings.ToLower(host)
	privateDomainsMu.RLock()
	defer privateDomainsMu.RUnlock()
	// 精确匹配
	if privateDomains[host] {
		return true
	}
	// 后缀匹配：例如 "local" 匹配 "router.local"
	for suffix := range privateDomains {
		if strings.HasSuffix(host, "."+suffix) || host == suffix {
			return true
		}
	}
	return false
}

// shouldBypassProxy 根据分流模式判断是否应该绕过代理（直连）
// 返回直连决定以及分流解析得到的 IP（仅域名命中中国 IP 时非空）
func shouldBypassProxy(targetHost string) (bool, []net.IP) {
	if routingMode == "none" {
		// "不改变代理"模式：所有流量都直连
		return true, nil
	}
	if routingMode == "global" {
		// "全局代理"模式：白名单中的 IP 和域名直连，其余走代理
		if ip := net.ParseIP(targetHost); ip != nil {
			if isPrivateIP(targetHost) {
				return true, nil
			}
		} else {
			if isPrivateDomain(targetHost) {
				return true, nil
			}
		}
		return false, nil
	}
	if routingMode == "bypass_cn" {
		// "中国域名直连/非中国域名代理"模式
		// 优先检查白名单：白名单中的 IP 和域名始终直连
		if ip := net.ParseIP(targetHost); ip != nil {
			if isPrivateIP(targetHost) {
				return true, nil
			}
		} else {
			if isPrivateDomain(targetHost) {
				return true, nil
			}
		}
		// 检查中国域名
		if isChinaDomain(targetHost) {
			return true, nil
		}
		// 先尝试解析为IP
		if ip := net.ParseIP(targetHost); ip != nil {
			return isChinaIP(targetHost), nil
		}
		// 如果是域名，通过缓存解析IP（避免每个请求重复同步查询DNS）
		ips := lookupIPWithCache(targetHost)
		if len(ips) == 0 {
			// 解析失败，默认走代理
			return false, nil
		}
		var chinaIPs, otherIPs []net.IP
		for _, ip := range ips {
			if isChinaIP(ip.String()) {
				chinaIPs = append(chinaIPs, ip)
			} else {
				otherIPs = append(otherIPs, ip)
			}
		}
		if len(chinaIPs) == 0 {
			// 都不是中国IP，走代理
			return false, nil
		}
		// 中国 IP 优先，直连时尽量连到实际命中的地址
		ordered := make([]net.IP, 0, len(ips))
		ordered = append(ordered, chinaIPs...)
		ordered = append(ordered, otherIPs...)
		return true, ordered
	}
	// 未知模式，默认走代理
	return false, nil
}

func isNormalCloseError(err error) bool {
	if err == nil {
		return false
	}
	if err == io.EOF {
		return true
	}
	errStr := err.Error()
	return strings.Contains(errStr, "use of closed network connection") ||
		strings.Contains(errStr, "broken pipe") ||
		strings.Contains(errStr, "connection reset by peer") ||
		strings.Contains(errStr, "normal closure")
}

// ======================== ECH 支持 ========================

const typeHTTPS = 65

// isECHEnabled 判断 ECH 是否启用（"y"=开启, "n"=关闭，默认开启）
func isECHEnabled() bool {
	return strings.ToLower(enableECH) != "n"
}

func prepareECH() error {
	if !isECHEnabled() {
		log.Printf("[ECH] ECH 已关闭，跳过获取 ECH 配置")
		return nil
	}

	echBase64, err := queryHTTPSRecord(echDomain, dnsServer)
	if err != nil {
		return fmt.Errorf("DNS 查询失败: %w", err)
	}
	if echBase64 == "" {
		return errors.New("未找到 ECH 参数")
	}
	raw, err := base64.StdEncoding.DecodeString(echBase64)
	if err != nil {
		return fmt.Errorf("ECH 解码失败: %w", err)
	}
	echListMu.Lock()
	echList = raw
	echVersion++
	echListMu.Unlock()
	log.Printf("[ECH] 配置已加载，长度: %d 字节", len(raw))
	return nil
}

// getECHVersion 获取当前 ECH 配置版本号
func getECHVersion() uint64 {
	echListMu.RLock()
	defer echListMu.RUnlock()
	return echVersion
}

func refreshECH() error {
	log.Printf("[ECH] 刷新配置...")
	return prepareECH()
}

func getECHList() ([]byte, error) {
	echListMu.RLock()
	defer echListMu.RUnlock()
	if len(echList) == 0 {
		return nil, errors.New("ECH 配置未加载")
	}
	return echList, nil
}

// getSystemCertPool 获取缓存的系统根证书池
func getSystemCertPool() (*x509.CertPool, error) {
	systemCertPoolOnce.Do(func() {
		systemCertPool, systemCertPoolErr = x509.SystemCertPool()
	})
	return systemCertPool, systemCertPoolErr
}

func buildTLSConfigWithECH(serverName string, echList []byte) (*tls.Config, error) {
	roots, err := getSystemCertPool()
	if err != nil {
		return nil, fmt.Errorf("加载系统根证书失败: %w", err)
	}

	config := &tls.Config{
		MinVersion:         tls.VersionTLS13,
		ServerName:         serverName,
		RootCAs:            roots,
		ClientSessionCache: tlsSessionCache,
	}

	if len(echList) > 0 {
		// 使用反射设置 ECH 字段（ECH 是核心功能，必须设置成功）
		if err := setECHConfig(config, echList); err != nil {
			return nil, fmt.Errorf("设置 ECH 配置失败（需要 Go 1.23+ 或支持 ECH 的版本）: %w", err)
		}
	} else if isECHEnabled() {
		return nil, errors.New("ECH 配置为空，这是必需功能")
	}

	return config, nil
}

// setECHConfig 使用反射设置 ECH 配置（ECH 是核心功能，必须成功）
func setECHConfig(config *tls.Config, echList []byte) error {
	configValue := reflect.ValueOf(config).Elem()

	// 设置 EncryptedClientHelloConfigList（必需）
	field1 := configValue.FieldByName("EncryptedClientHelloConfigList")
	if !field1.IsValid() || !field1.CanSet() {
		return fmt.Errorf("EncryptedClientHelloConfigList 字段不可用，需要 Go 1.23+ 版本")
	}
	field1.Set(reflect.ValueOf(echList))

	// 设置 EncryptedClientHelloRejectionVerify（必需）
	field2 := configValue.FieldByName("EncryptedClientHelloRejectionVerify")
	if !field2.IsValid() || !field2.CanSet() {
		return fmt.Errorf("EncryptedClientHelloRejectionVerify 字段不可用，需要 Go 1.23+ 版本")
	}
	rejectionFunc := func(cs tls.ConnectionState) error {
		return errors.New("服务器拒绝 ECH")
	}
	field2.Set(reflect.ValueOf(rejectionFunc))

	return nil
}

// queryHTTPSRecord 通过 UDP DNS 或 DoH 查询 HTTPS 记录
func queryHTTPSRecord(domain, dnsServer string) (string, error) {
	if strings.HasPrefix(dnsServer, "udp://") {
		return queryUDP(domain, dnsServer)
	}

	dohURL := dnsServer
	if !strings.HasPrefix(dohURL, "https://") && !strings.HasPrefix(dohURL, "http://") {
		dohURL = "https://" + dohURL
	}
	return queryDoH(domain, dohURL)
}

// queryUDP 通过 UDP DNS 查询 HTTPS 记录
func queryUDP(domain, dnsServer string) (string, error) {
	addr := strings.TrimPrefix(dnsServer, "udp://")

	if _, _, err := net.SplitHostPort(addr); err != nil {
		addr = net.JoinHostPort(addr, "53")
	}

	dnsQuery := buildDNSQuery(domain, typeHTTPS)

	conn, err := net.DialTimeout("udp", addr, 5*time.Second)
	if err != nil {
		return "", fmt.Errorf("连接 UDP DNS 服务器失败: %w", err)
	}
	defer conn.Close()

	conn.SetDeadline(time.Now().Add(5 * time.Second))

	if _, err := conn.Write(dnsQuery); err != nil {
		return "", fmt.Errorf("发送 UDP DNS 查询失败: %w", err)
	}

	buf := make([]byte, 4096)
	n, err := conn.Read(buf)
	if err != nil {
		return "", fmt.Errorf("接收 UDP DNS 响应失败: %w", err)
	}

	return parseDNSResponse(buf[:n])
}

// queryDoH 执行 DoH 查询（用于获取 ECH 配置）
func queryDoH(domain, dohURL string) (string, error) {
	u, err := url.Parse(dohURL)
	if err != nil {
		return "", fmt.Errorf("无效的 DoH URL: %v", err)
	}

	dnsQuery := buildDNSQuery(domain, typeHTTPS)
	dnsBase64 := base64.RawURLEncoding.EncodeToString(dnsQuery)

	q := u.Query()
	q.Set("dns", dnsBase64)
	u.RawQuery = q.Encode()

	req, err := http.NewRequest("GET", u.String(), nil)
	if err != nil {
		return "", fmt.Errorf("创建请求失败: %v", err)
	}
	req.Header.Set("Accept", "application/dns-message")
	req.Header.Set("Content-Type", "application/dns-message")

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return "", fmt.Errorf("DoH 请求失败: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("DoH 服务器返回错误: %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("读取 DoH 响应失败: %v", err)
	}

	return parseDNSResponse(body)
}

func buildDNSQuery(domain string, qtype uint16) []byte {
	query := make([]byte, 0, 512)
	query = append(query, 0x00, 0x01, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
	for _, label := range strings.Split(domain, ".") {
		query = append(query, byte(len(label)))
		query = append(query, []byte(label)...)
	}
	query = append(query, 0x00, byte(qtype>>8), byte(qtype), 0x00, 0x01)
	return query
}

func parseDNSResponse(response []byte) (string, error) {
	if len(response) < 12 {
		return "", errors.New("响应过短")
	}
	ancount := binary.BigEndian.Uint16(response[6:8])
	if ancount == 0 {
		return "", errors.New("无应答记录")
	}

	offset := 12
	for offset < len(response) && response[offset] != 0 {
		offset += int(response[offset]) + 1
	}
	offset += 5

	for i := 0; i < int(ancount); i++ {
		if offset >= len(response) {
			break
		}
		if response[offset]&0xC0 == 0xC0 {
			offset += 2
		} else {
			for offset < len(response) && response[offset] != 0 {
				offset += int(response[offset]) + 1
			}
			offset++
		}
		if offset+10 > len(response) {
			break
		}
		rrType := binary.BigEndian.Uint16(response[offset : offset+2])
		offset += 8
		dataLen := binary.BigEndian.Uint16(response[offset : offset+2])
		offset += 2
		if offset+int(dataLen) > len(response) {
			break
		}
		data := response[offset : offset+int(dataLen)]
		offset += int(dataLen)

		if rrType == typeHTTPS {
			if ech := parseHTTPSRecord(data); ech != "" {
				return ech, nil
			}
		}
	}
	return "", nil
}

func parseHTTPSRecord(data []byte) string {
	if len(data) < 2 {
		return ""
	}
	offset := 2
	if offset < len(data) && data[offset] == 0 {
		offset++
	} else {
		for offset < len(data) && data[offset] != 0 {
			offset += int(data[offset]) + 1
		}
		offset++
	}
	for offset+4 <= len(data) {
		key := binary.BigEndian.Uint16(data[offset : offset+2])
		length := binary.BigEndian.Uint16(data[offset+2 : offset+4])
		offset += 4
		if offset+int(length) > len(data) {
			break
		}
		value := data[offset : offset+int(length)]
		offset += int(length)
		if key == 5 {
			return base64.StdEncoding.EncodeToString(value)
		}
	}
	return ""
}

// ======================== DoH 代理支持 ========================

// dohClientBox 按 ECH 配置版本缓存的 DoH 客户端
type dohClientBox struct {
	version uint64
	client  *http.Client
}

// getDoHClient 获取带连接池的 DoH 客户端（ECH 配置变更时自动重建）
func getDoHClient() (*http.Client, error) {
	var version uint64
	var echBytes []byte
	if isECHEnabled() {
		version = getECHVersion()
		if b, _ := dohClientValue.Load().(*dohClientBox); b != nil && b.version == version {
			return b.client, nil
		}

		var err error
		echBytes, err = getECHList()
		if err != nil {
			return nil, fmt.Errorf("获取 ECH 配置失败: %w", err)
		}
	}

	tlsCfg, err := buildTLSConfigWithECH("cloudflare-dns.com", echBytes)
	if err != nil {
		return nil, fmt.Errorf("构建 TLS 配置失败: %w", err)
	}

	transport := &http.Transport{
		TLSClientConfig:     tlsCfg,
		MaxIdleConns:        8,
		MaxIdleConnsPerHost: 8,
		IdleConnTimeout:     90 * time.Second,
	}

	// 如果指定了 IP，使用自定义 Dialer
	if serverIP != "" {
		transport.DialContext = func(ctx context.Context, network, addr string) (net.Conn, error) {
			_, port, err := net.SplitHostPort(addr)
			if err != nil {
				return nil, err
			}
			dialer := &net.Dialer{
				Timeout: 10 * time.Second,
			}
			return dialer.DialContext(ctx, network, net.JoinHostPort(serverIP, port))
		}
	}

	client := &http.Client{
		Transport: transport,
		Timeout:   10 * time.Second,
	}

	dohClientValue.Store(&dohClientBox{version: version, client: client})
	return client, nil
}

// queryDoHForProxy 通过 ECH 转发 DNS 查询到 Cloudflare DoH（复用连接池）
func queryDoHForProxy(dnsQuery []byte) ([]byte, error) {
	_, port, _, err := parseServerAddr(serverAddr)
	if err != nil {
		return nil, err
	}

	client, err := getDoHClient()
	if err != nil {
		return nil, err
	}

	// 构建 DoH URL
	dohURL := fmt.Sprintf("https://cloudflare-dns.com:%s/dns-query", port)

	// 发送 DoH 请求
	req, err := http.NewRequest("POST", dohURL, bytes.NewReader(dnsQuery))
	if err != nil {
		return nil, err
	}

	req.Header.Set("Content-Type", "application/dns-message")
	req.Header.Set("Accept", "application/dns-message")

	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("DoH 请求失败: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("DoH 响应错误: %d", resp.StatusCode)
	}

	return io.ReadAll(resp.Body)
}

// ======================== WebSocket 客户端 ========================

func parseServerAddr(addr string) (host, port, path string, err error) {
	path = "/"
	slashIdx := strings.Index(addr, "/")
	if slashIdx != -1 {
		path = addr[slashIdx:]
		addr = addr[:slashIdx]
	}

	host, port, err = net.SplitHostPort(addr)
	if err != nil {
		return "", "", "", fmt.Errorf("无效的服务器地址格式: %v", err)
	}

	return host, port, path, nil
}

func dialWebSocketWithECH(maxRetries int) (*websocket.Conn, error) {
	host, port, path, err := parseServerAddr(serverAddr)
	if err != nil {
		return nil, err
	}

	wsURL := fmt.Sprintf("wss://%s:%s%s", host, port, path)

	// 获取 ECH 配置（仅在启用 ECH 时需要）
	var echBytes []byte
	if isECHEnabled() {
		echBytes, err = getECHList()
		if err != nil {
			if maxRetries > 1 {
				refreshECH()
				echBytes, err = getECHList()
				if err != nil {
					return nil, err
				}
			} else {
				return nil, err
			}
		}
	}

	for attempt := 1; attempt <= maxRetries; attempt++ {
		tlsCfg, tlsErr := buildTLSConfigWithECH(host, echBytes)
		if tlsErr != nil {
			return nil, tlsErr
		}

		dialer := websocket.Dialer{
			TLSClientConfig: tlsCfg,
			Subprotocols: func() []string {
				if token == "" {
					return nil
				}
				return []string{token}
			}(),
			HandshakeTimeout: 10 * time.Second,
		}

		if serverIP != "" {
			dialer.NetDial = func(network, address string) (net.Conn, error) {
				_, port, err := net.SplitHostPort(address)
				if err != nil {
					return nil, err
				}
				return net.DialTimeout(network, net.JoinHostPort(serverIP, port), 10*time.Second)
			}
		}

		wsConn, _, dialErr := dialer.Dial(wsURL, nil)
		if dialErr != nil {
			if strings.Contains(dialErr.Error(), "ECH") && attempt < maxRetries {
				log.Printf("[ECH] 连接失败，尝试刷新配置 (%d/%d)", attempt, maxRetries)
				refreshECH()
				time.Sleep(time.Second)
				continue
			}
			return nil, dialErr
		}

		return wsConn, nil
	}

	return nil, errors.New("连接失败，已达最大重试次数")
}

// ======================== WebSocket 隧道 ========================

const freshConnectTO = 20 * time.Second // 新建连接 CONNECT 等待上限

// sendConnect 发送 CONNECT 请求并等待服务器确认
// 返回值 broken 为 true 表示连接本身失效（可回退新建），false 表示服务端明确拒绝（重试无意义）
func sendConnect(ws *websocket.Conn, target, firstFrame string, timeout time.Duration) (broken bool, err error) {
	connectMsg := fmt.Sprintf("CONNECT:%s|%s", target, firstFrame)
	if writeErr := ws.WriteMessage(websocket.TextMessage, []byte(connectMsg)); writeErr != nil {
		return true, writeErr
	}

	// 等待响应（限时，避免失效连接长时间挂起）
	if setErr := ws.SetReadDeadline(time.Now().Add(timeout)); setErr != nil {
		return true, setErr
	}
	defer ws.SetReadDeadline(time.Time{})

	_, msg, readErr := ws.ReadMessage()
	if readErr != nil {
		return true, readErr
	}

	response := string(msg)
	if strings.HasPrefix(response, "ERROR:") {
		return false, errors.New(response)
	}
	if response != "CONNECTED" {
		return false, fmt.Errorf("意外响应: %s", response)
	}
	return false, nil
}

// connectTunnel 建立代理隧道（含 ECH 刷新重试）
func connectTunnel(target, firstFrame string) (*websocket.Conn, error) {
	ws, err := dialWebSocketWithECH(2)
	if err != nil {
		return nil, err
	}
	if _, err := sendConnect(ws, target, firstFrame, freshConnectTO); err != nil {
		ws.Close()
		return nil, err
	}
	return ws, nil
}

// ======================== 统一代理服务器 ========================

func runProxyServer(addr string) {
	listener, err := net.Listen("tcp", addr)
	if err != nil {
		log.Fatalf("[代理] 监听失败: %v", err)
	}
	defer listener.Close()

	log.Printf("[代理] 服务器启动: %s (支持 SOCKS5 和 HTTP)", addr)
	log.Printf("[代理] 后端服务器: %s", serverAddr)
	if serverIP != "" {
		log.Printf("[代理] 使用固定 IP: %s", serverIP)
	}

	for {
		conn, err := listener.Accept()
		if err != nil {
			log.Printf("[代理] 接受连接失败: %v", err)
			continue
		}

		go handleConnection(conn)
	}
}

func handleConnection(conn net.Conn) {
	defer conn.Close()

	clientAddr := conn.RemoteAddr().String()
	conn.SetDeadline(time.Now().Add(30 * time.Second))

	// 读取第一个字节判断协议
	buf := make([]byte, 1)
	n, err := conn.Read(buf)
	if err != nil || n == 0 {
		return
	}

	firstByte := buf[0]

	// 使用 switch 判断协议类型
	switch firstByte {
	case 0x05:
		// SOCKS5 协议
		handleSOCKS5(conn, clientAddr, firstByte)
	case 'C', 'G', 'P', 'H', 'D', 'O', 'T':
		// HTTP 协议 (CONNECT, GET, POST, HEAD, DELETE, OPTIONS, TRACE, PUT, PATCH)
		handleHTTP(conn, clientAddr, firstByte)
	default:
		log.Printf("[代理] %s 未知协议: 0x%02x", clientAddr, firstByte)
	}
}

// ======================== SOCKS5 处理 ========================

func handleSOCKS5(conn net.Conn, clientAddr string, firstByte byte) {
	// 验证版本
	if firstByte != 0x05 {
		log.Printf("[SOCKS5] %s 版本错误: 0x%02x", clientAddr, firstByte)
		return
	}

	// 读取认证方法数量
	buf := make([]byte, 1)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return
	}

	nmethods := buf[0]
	methods := make([]byte, nmethods)
	if _, err := io.ReadFull(conn, methods); err != nil {
		return
	}

	// 响应无需认证
	if _, err := conn.Write([]byte{0x05, 0x00}); err != nil {
		return
	}

	// 读取请求
	buf = make([]byte, 4)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return
	}

	if buf[0] != 5 {
		return
	}

	command := buf[1]
	atyp := buf[3]

	var host string
	switch atyp {
	case 0x01: // IPv4
		buf = make([]byte, 4)
		if _, err := io.ReadFull(conn, buf); err != nil {
			return
		}
		host = net.IP(buf).String()

	case 0x03: // 域名
		buf = make([]byte, 1)
		if _, err := io.ReadFull(conn, buf); err != nil {
			return
		}
		domainBuf := make([]byte, buf[0])
		if _, err := io.ReadFull(conn, domainBuf); err != nil {
			return
		}
		host = string(domainBuf)

	case 0x04: // IPv6
		buf = make([]byte, 16)
		if _, err := io.ReadFull(conn, buf); err != nil {
			return
		}
		host = net.IP(buf).String()

	default:
		conn.Write([]byte{0x05, 0x08, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return
	}

	// 读取端口
	buf = make([]byte, 2)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return
	}
	port := int(buf[0])<<8 | int(buf[1])

	switch command {
	case 0x01: // CONNECT
		var target string
		if atyp == 0x04 {
			target = fmt.Sprintf("[%s]:%d", host, port)
		} else {
			target = fmt.Sprintf("%s:%d", host, port)
		}

		log.Printf("[SOCKS5] %s -> %s", clientAddr, target)

		if err := handleTunnel(conn, target, clientAddr, modeSOCKS5, "", nil); err != nil {
			if !isNormalCloseError(err) {
				log.Printf("[SOCKS5] %s 代理失败: %v", clientAddr, err)
			}
		}

	case 0x03: // UDP ASSOCIATE
		handleUDPAssociate(conn, clientAddr)

	default:
		conn.Write([]byte{0x05, 0x07, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return
	}
}

func handleUDPAssociate(tcpConn net.Conn, clientAddr string) {
	// 创建 UDP 监听器
	udpAddr, err := net.ResolveUDPAddr("udp", "127.0.0.1:0")
	if err != nil {
		log.Printf("[UDP] %s 解析地址失败: %v", clientAddr, err)
		tcpConn.Write([]byte{0x05, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return
	}

	udpConn, err := net.ListenUDP("udp", udpAddr)
	if err != nil {
		log.Printf("[UDP] %s 监听失败: %v", clientAddr, err)
		tcpConn.Write([]byte{0x05, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return
	}

	// 获取实际监听的端口
	localAddr := udpConn.LocalAddr().(*net.UDPAddr)
	port := localAddr.Port

	log.Printf("[UDP] %s UDP ASSOCIATE 监听端口: %d", clientAddr, port)

	// 发送成功响应
	response := []byte{0x05, 0x00, 0x00, 0x01}
	response = append(response, 127, 0, 0, 1) // 127.0.0.1
	response = append(response, byte(port>>8), byte(port&0xff))

	if _, err := tcpConn.Write(response); err != nil {
		udpConn.Close()
		return
	}

	// 启动 UDP 处理
	stopChan := make(chan struct{})
	go handleUDPRelay(udpConn, clientAddr, stopChan)

	// 保持 TCP 连接，直到客户端关闭
	buf := make([]byte, 1)
	tcpConn.Read(buf)

	close(stopChan)
	udpConn.Close()
	log.Printf("[UDP] %s UDP ASSOCIATE 连接关闭", clientAddr)
}

func handleUDPRelay(udpConn *net.UDPConn, clientAddr string, stopChan chan struct{}) {
	buf := make([]byte, 65535)
	for {
		select {
		case <-stopChan:
			return
		default:
		}

		udpConn.SetReadDeadline(time.Now().Add(1 * time.Second))
		n, addr, err := udpConn.ReadFromUDP(buf)
		if err != nil {
			if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
				continue
			}
			return
		}

		// 解析 SOCKS5 UDP 请求头
		if n < 10 {
			continue
		}

		// SOCKS5 UDP 请求格式:
		// +----+------+------+----------+----------+----------+
		// |RSV | FRAG | ATYP | DST.ADDR | DST.PORT |   DATA   |
		// +----+------+------+----------+----------+----------+
		// | 2  |  1   |  1   | Variable |    2     | Variable |
		// +----+------+------+----------+----------+----------+

		data := buf[:n]

		if data[2] != 0x00 { // FRAG 必须为 0
			continue
		}

		atyp := data[3]
		var headerLen int
		var dstHost string
		var dstPort int

		switch atyp {
		case 0x01: // IPv4
			if n < 10 {
				continue
			}
			dstHost = net.IP(data[4:8]).String()
			dstPort = int(data[8])<<8 | int(data[9])
			headerLen = 10

		case 0x03: // 域名
			if n < 5 {
				continue
			}
			domainLen := int(data[4])
			if n < 7+domainLen {
				continue
			}
			dstHost = string(data[5 : 5+domainLen])
			dstPort = int(data[5+domainLen])<<8 | int(data[6+domainLen])
			headerLen = 7 + domainLen

		case 0x04: // IPv6
			if n < 22 {
				continue
			}
			dstHost = net.IP(data[4:20]).String()
			dstPort = int(data[20])<<8 | int(data[21])
			headerLen = 22

		default:
			continue
		}

		udpData := data[headerLen:]
		target := fmt.Sprintf("%s:%d", dstHost, dstPort)

		// 检查是否是 DNS 查询（端口 53）
		if dstPort == 53 {
			log.Printf("[UDP-DNS] %s -> %s (DoH 查询)", clientAddr, target)
			go handleDNSQuery(udpConn, addr, udpData, data[:headerLen])
		} else {
			log.Printf("[UDP] %s -> %s (暂不支持非 DNS UDP)", clientAddr, target)
			// 这里可以扩展支持其他 UDP 流量
		}
	}
}

func handleDNSQuery(udpConn *net.UDPConn, clientAddr *net.UDPAddr, dnsQuery []byte, socks5Header []byte) {
	// 通过 DoH 查询（使用重命名后的函数）
	dnsResponse, err := queryDoHForProxy(dnsQuery)
	if err != nil {
		log.Printf("[UDP-DNS] DoH 查询失败: %v", err)
		return
	}

	// 构建 SOCKS5 UDP 响应
	response := make([]byte, 0, len(socks5Header)+len(dnsResponse))
	response = append(response, socks5Header...)
	response = append(response, dnsResponse...)

	// 发送响应
	_, err = udpConn.WriteToUDP(response, clientAddr)
	if err != nil {
		log.Printf("[UDP-DNS] 发送响应失败: %v", err)
		return
	}

	log.Printf("[UDP-DNS] DoH 查询成功，响应 %d 字节", len(dnsResponse))
}

// ======================== HTTP 处理 ========================

// maxInlineBody 内联到首帧的最大请求体大小，超出部分走流式转发
const maxInlineBody = 64 * 1024

func handleHTTP(conn net.Conn, clientAddr string, firstByte byte) {
	// 将第一个字节放回缓冲区（加大读缓冲，减少系统调用）
	reader := bufio.NewReaderSize(io.MultiReader(
		strings.NewReader(string(firstByte)),
		conn,
	), 65536)

	// 读取 HTTP 请求行
	requestLine, err := reader.ReadString('\n')
	if err != nil {
		return
	}

	parts := strings.Fields(requestLine)
	if len(parts) < 3 {
		return
	}

	method := parts[0]
	requestURL := parts[1]
	httpVersion := parts[2]

	// 读取所有 headers
	headers := make(map[string]string)
	var headerLines []string
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		headerLines = append(headerLines, line)
		if idx := strings.Index(line, ":"); idx > 0 {
			key := strings.TrimSpace(line[:idx])
			value := strings.TrimSpace(line[idx+1:])
			headers[strings.ToLower(key)] = value
		}
	}

	switch method {
	case "CONNECT":
		// HTTPS 隧道代理 - 需要发送 200 响应
		log.Printf("[HTTP-CONNECT] %s -> %s", clientAddr, requestURL)
		if err := handleTunnel(conn, requestURL, clientAddr, modeHTTPConnect, "", reader); err != nil {
			if !isNormalCloseError(err) {
				log.Printf("[HTTP-CONNECT] %s 代理失败: %v", clientAddr, err)
			}
		}

	case "GET", "POST", "PUT", "DELETE", "HEAD", "OPTIONS", "PATCH", "TRACE":
		// HTTP 代理 - 直接转发，不发送 200 响应
		log.Printf("[HTTP-%s] %s -> %s", method, clientAddr, requestURL)

		var target string
		var path string

		if strings.HasPrefix(requestURL, "http://") {
			// 解析完整 URL
			urlWithoutScheme := strings.TrimPrefix(requestURL, "http://")
			idx := strings.Index(urlWithoutScheme, "/")
			if idx > 0 {
				target = urlWithoutScheme[:idx]
				path = urlWithoutScheme[idx:]
			} else {
				target = urlWithoutScheme
				path = "/"
			}
		} else {
			// 相对路径，从 Host header 获取
			target = headers["host"]
			path = requestURL
		}

		if target == "" {
			conn.Write([]byte("HTTP/1.1 400 Bad Request\r\n\r\n"))
			return
		}

		// 添加默认端口
		if !strings.Contains(target, ":") {
			target += ":80"
		}

		// 重构 HTTP 请求（去掉完整 URL，使用相对路径）
		var requestBuilder strings.Builder
		requestBuilder.WriteString(fmt.Sprintf("%s %s %s\r\n", method, path, httpVersion))

		// 写入 headers（过滤掉 Proxy-Connection）
		for _, line := range headerLines {
			key := strings.Split(line, ":")[0]
			keyLower := strings.ToLower(strings.TrimSpace(key))
			if keyLower != "proxy-connection" && keyLower != "proxy-authorization" {
				requestBuilder.WriteString(line)
				requestBuilder.WriteString("\r\n")
			}
		}
		requestBuilder.WriteString("\r\n")

		// 小请求体内联到首帧（省一个RTT）；大请求体留在流中，隧道建立后流式转发
		if contentLength := headers["content-length"]; contentLength != "" {
			var length int
			if _, err := fmt.Sscanf(contentLength, "%d", &length); err == nil && length > 0 && length <= maxInlineBody {
				body := make([]byte, length)
				if _, err := io.ReadFull(reader, body); err == nil {
					requestBuilder.Write(body)
				}
			}
		}

		firstFrame := requestBuilder.String()

		// 使用 modeHTTPProxy 模式（不发送 200 响应），reader 中剩余数据（大请求体等）通过隧道继续转发
		if err := handleTunnel(conn, target, clientAddr, modeHTTPProxy, firstFrame, reader); err != nil {
			if !isNormalCloseError(err) {
				log.Printf("[HTTP-%s] %s 代理失败: %v", method, clientAddr, err)
			}
		}

	default:
		log.Printf("[HTTP] %s 不支持的方法: %s", clientAddr, method)
		conn.Write([]byte("HTTP/1.1 405 Method Not Allowed\r\n\r\n"))
	}
}

// ======================== 通用隧道处理 ========================

// 代理模式常量
const (
	modeSOCKS5      = 1 // SOCKS5 代理
	modeHTTPConnect = 2 // HTTP CONNECT 隧道
	modeHTTPProxy   = 3 // HTTP 普通代理（GET/POST等）
)

func handleTunnel(conn net.Conn, target, clientAddr string, mode int, firstFrame string, src io.Reader) error {
	// 解析目标地址
	targetHost, _, err := net.SplitHostPort(target)
	if err != nil {
		targetHost = target
	}

	// 客户端数据读取源（HTTP 模式下可能已有缓冲数据，不能直接从 conn 读）
	readSrc := io.Reader(conn)
	if src != nil {
		readSrc = src
	}

	// 协议协商已完成，清除握手阶段的超时限制
	conn.SetDeadline(time.Time{})

	// 检查是否应该绕过代理（直连）
	bypass, resolvedIPs := shouldBypassProxy(targetHost)
	if bypass {
		log.Printf("[分流] %s -> %s (直连，绕过代理)", clientAddr, target)
		return handleDirectConnection(conn, target, clientAddr, mode, firstFrame, readSrc, resolvedIPs)
	}

	// 走代理（每次新建 WebSocket 隧道）
	log.Printf("[分流] %s -> %s (通过代理)", clientAddr, target)

	// 如果没有预设的 firstFrame，尝试读取第一帧数据（仅 SOCKS5）
	if firstFrame == "" && mode == modeSOCKS5 {
		_ = conn.SetReadDeadline(time.Now().Add(100 * time.Millisecond))
		buffer := make([]byte, 32768)
		n, _ := conn.Read(buffer)
		_ = conn.SetReadDeadline(time.Time{})
		if n > 0 {
			firstFrame = string(buffer[:n])
		}
	}

	wsConn, err := connectTunnel(target, firstFrame)
	if err != nil {
		sendErrorResponse(conn, mode)
		return err
	}
	defer wsConn.Close()

	var mu sync.Mutex

	// 保活
	stopPing := make(chan bool)
	go func() {
		ticker := time.NewTicker(10 * time.Second)
		defer ticker.Stop()
		for {
			select {
			case <-ticker.C:
				mu.Lock()
				wsConn.WriteMessage(websocket.PingMessage, nil)
				mu.Unlock()
			case <-stopPing:
				return
			}
		}
	}()
	defer close(stopPing)

	// 发送成功响应（根据模式不同而不同）
	if err := sendSuccessResponse(conn, mode); err != nil {
		return err
	}

	log.Printf("[代理] %s 已连接: %s", clientAddr, target)

	// 双向转发
	done := make(chan bool, 2)

	// Client -> Server
	go func() {
		buf := make([]byte, 65536)
		for {
			n, err := readSrc.Read(buf)
			if err != nil {
				mu.Lock()
				wsConn.WriteMessage(websocket.TextMessage, []byte("CLOSE"))
				mu.Unlock()
				done <- true
				return
			}

			mu.Lock()
			err = wsConn.WriteMessage(websocket.BinaryMessage, buf[:n])
			mu.Unlock()
			if err != nil {
				done <- true
				return
			}
		}
	}()

	// Server -> Client
	go func() {
		for {
			mt, msg, err := wsConn.ReadMessage()
			if err != nil {
				done <- true
				return
			}

			if mt == websocket.TextMessage {
				if string(msg) == "CLOSE" {
					done <- true
					return
				}
			}

			if _, err := conn.Write(msg); err != nil {
				done <- true
				return
			}
		}
	}()

	<-done
	log.Printf("[代理] %s 已断开: %s", clientAddr, target)
	return nil
}

// ======================== 直连处理 ========================

const (
	directDialTimeout  = 10 * time.Second
	directPerIPTimeout = 2 * time.Second
	directCachedBudget = 5 * time.Second
)

var dialTCP = func(ctx context.Context, addr string) (net.Conn, error) {
	var dialer net.Dialer
	return dialer.DialContext(ctx, "tcp", addr)
}

// dialDirect 直连目标；有缓存 IP 时优先使用，全部失败后回退到域名拨号
func dialDirect(host, port string, cachedIPs []net.IP) (net.Conn, error) {
	hostPort := net.JoinHostPort(host, port)

	if len(cachedIPs) == 0 || net.ParseIP(host) != nil {
		ctx, cancel := context.WithTimeout(context.Background(), directDialTimeout)
		defer cancel()
		return dialTCP(ctx, hostPort)
	}

	ordered := orderIPv4First(cachedIPs)
	cachedCtx, cachedCancel := context.WithTimeout(context.Background(), directCachedBudget)
	defer cachedCancel()

	var lastErr error
	for _, ip := range ordered {
		if cachedCtx.Err() != nil {
			lastErr = cachedCtx.Err()
			break
		}
		attemptCtx, attemptCancel := context.WithTimeout(cachedCtx, directPerIPTimeout)
		conn, err := dialTCP(attemptCtx, net.JoinHostPort(ip.String(), port))
		attemptCancel()
		if err == nil {
			return conn, nil
		}
		lastErr = err
	}

	// 缓存 IP 不可用（可能已过期），回退到域名拨号重新解析
	fallbackCtx, fallbackCancel := context.WithTimeout(context.Background(), directDialTimeout)
	defer fallbackCancel()
	conn, err := dialTCP(fallbackCtx, hostPort)
	if err == nil {
		return conn, nil
	}
	if lastErr != nil {
		return nil, fmt.Errorf("缓存 IP 连接失败: %v; 域名拨号失败: %w", lastErr, err)
	}
	return nil, err
}

// orderIPv4First 优先尝试 IPv4，避免 IPv6 不可用时等待超时
func orderIPv4First(ips []net.IP) []net.IP {
	ordered := make([]net.IP, 0, len(ips))
	for _, ip := range ips {
		if ip.To4() != nil {
			ordered = append(ordered, ip)
		}
	}
	for _, ip := range ips {
		if ip.To4() == nil {
			ordered = append(ordered, ip)
		}
	}
	return ordered
}

// handleDirectConnection 处理直连（绕过代理）
func handleDirectConnection(conn net.Conn, target, clientAddr string, mode int, firstFrame string, readSrc io.Reader, resolvedIPs []net.IP) error {
	// 解析目标地址
	host, port, err := net.SplitHostPort(target)
	if err != nil {
		// 如果没有端口，根据模式添加默认端口
		host = target
		if mode == modeHTTPConnect || mode == modeHTTPProxy {
			port = "443"
		} else {
			port = "80"
		}
		target = net.JoinHostPort(host, port)
	}

	// 直接连接到目标
	targetConn, err := dialDirect(host, port, resolvedIPs)
	if err != nil {
		sendErrorResponse(conn, mode)
		return fmt.Errorf("直连失败: %w", err)
	}
	defer targetConn.Close()

	// 发送成功响应
	if err := sendSuccessResponse(conn, mode); err != nil {
		return err
	}

	// 如果有预设的第一帧数据，先发送
	if firstFrame != "" {
		if _, err := targetConn.Write([]byte(firstFrame)); err != nil {
			return err
		}
	}

	if readSrc == nil {
		readSrc = conn
	}

	// 双向转发
	done := make(chan bool, 2)

	// Client -> Target
	go func() {
		io.CopyBuffer(targetConn, readSrc, make([]byte, 65536))
		done <- true
	}()

	// Target -> Client
	go func() {
		io.CopyBuffer(conn, targetConn, make([]byte, 65536))
		done <- true
	}()

	<-done
	log.Printf("[分流] %s 直连已断开: %s", clientAddr, target)
	return nil
}

// ======================== 响应辅助函数 ========================

func sendErrorResponse(conn net.Conn, mode int) {
	switch mode {
	case modeSOCKS5:
		conn.Write([]byte{0x05, 0x04, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
	case modeHTTPConnect, modeHTTPProxy:
		conn.Write([]byte("HTTP/1.1 502 Bad Gateway\r\n\r\n"))
	}
}

func sendSuccessResponse(conn net.Conn, mode int) error {
	switch mode {
	case modeSOCKS5:
		// SOCKS5 成功响应
		_, err := conn.Write([]byte{0x05, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return err
	case modeHTTPConnect:
		// HTTP CONNECT 需要发送 200 响应
		_, err := conn.Write([]byte("HTTP/1.1 200 Connection Established\r\n\r\n"))
		return err
	case modeHTTPProxy:
		// HTTP GET/POST 等不需要发送响应，直接转发目标服务器的响应
		return nil
	}
	return nil
}
