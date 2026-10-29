package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/binary"
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

var (
	listenAddr  string
	serverAddr  string
	serverIP    string
	token       string
	dnsServer   string
	echDomain   string
	routingMode string // 分流模式: "global", "bypass_cn", "none"

	enableECHFlag string // -enable_ech 原始参数
	enableECH     bool   // 是否启用 ECH（默认 true）

	echListMu  sync.RWMutex
	echList    []byte
	echVersion uint64 // ECH 配置版本号，用于判断 DoH 客户端是否需要重建

	// 中国IP列表（IPv4）
	chinaIPRangesMu sync.RWMutex
	chinaIPRanges   []ipRange

	// 中国IP列表（IPv6）
	chinaIPV6RangesMu sync.RWMutex
	chinaIPV6Ranges   []ipRangeV6

	// 中国域名列表（域名分流）
	chinaDomainsMu sync.RWMutex
	chinaDomains   map[string]struct{}
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

func init() {
	flag.StringVar(&listenAddr, "l", "127.0.0.1:30000", "代理监听地址 (支持 SOCKS5 和 HTTP)")
	flag.StringVar(&serverAddr, "f", "", "服务端地址 (格式: x.x.workers.dev:443)")
	flag.StringVar(&serverIP, "ip", "", "指定服务端 IP（绕过 DNS 解析）")
	flag.StringVar(&token, "token", "", "身份验证令牌")
	flag.StringVar(&dnsServer, "dns", "dns.alidns.com/dns-query", "ECH 查询 DoH 服务器")
	flag.StringVar(&echDomain, "ech", "cloudflare-ech.com", "ECH 查询域名")
	flag.StringVar(&routingMode, "routing", "global", "分流模式: global(全局代理), bypass_cn(中国域名直连，其余走代理), none(不改变代理)")
	flag.StringVar(&enableECHFlag, "enable_ech", "y", "是否启用 ECH: y=开启(默认), n=关闭")
}

// parseEnableECH 解析 -enable_ech 参数（y=开启, n=关闭，默认开启）
func parseEnableECH(v string) bool {
	switch strings.ToLower(strings.TrimSpace(v)) {
	case "n", "no", "false", "0", "off":
		return false
	case "y", "yes", "true", "1", "on", "":
		return true
	default:
		log.Printf("[警告] 未知的 enable_ech 值: %q，默认开启 ECH", v)
		return true
	}
}

func main() {
	flag.Parse()

	enableECH = parseEnableECH(enableECHFlag)

	if serverAddr == "" {
		log.Fatal("必须指定服务端地址 -f\n\n示例:\n  ./client -l 127.0.0.1:1080 -f your-worker.workers.dev:443 -token your-token")
	}

	if enableECH {
		log.Printf("[启动] 正在获取 ECH 配置...")
		if err := prepareECH(); err != nil {
			log.Fatalf("[启动] 获取 ECH 配置失败: %v", err)
		}
	} else {
		log.Printf("[启动] ECH 已禁用，使用普通 TLS 连接")
	}

	// 加载中国域名/IP列表（如果需要）
	if routingMode == "bypass_cn" {
		log.Printf("[启动] 分流模式: 中国域名直连，其余走代理，正在加载中国域名列表...")

		if err := loadChinaDomainList(); err != nil {
			log.Printf("[警告] 加载中国域名列表失败: %v", err)
			log.Printf("[警告] 未加载中国域名列表，除本地域名与 .cn 外均走代理")
		} else {
			chinaDomainsMu.RLock()
			domainCount := len(chinaDomains)
			chinaDomainsMu.RUnlock()
			log.Printf("[启动] 已加载 %d 个中国域名（.cn 域名默认直连）", domainCount)
		}

		ipv4Count := 0
		ipv6Count := 0

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

		if ipv4Count > 0 || ipv6Count > 0 {
			log.Printf("[启动] 已加载 %d 个中国IPv4段, %d 个中国IPv6段（用于 IP 直连目标判断）", ipv4Count, ipv6Count)
		} else {
			log.Printf("[警告] 未加载到任何中国IP列表，IP 直连目标将走代理")
		}
	} else if routingMode == "global" {
		log.Printf("[启动] 分流模式: 全局代理")
	} else if routingMode == "none" {
		log.Printf("[启动] 分流模式: 不改变代理（直连模式）")
	} else {
		log.Printf("[警告] 未知的分流模式: %s，使用默认模式 global", routingMode)
		routingMode = "global"
	}

	// 启动 WebSocket 连接池（预热连接，省去每次新建隧道的握手延迟）
	if routingMode != "none" {
		connPool.start()
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

// downloadListFile 下载IP列表文件
func downloadListFile(url, filePath string) error {
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
		if err := downloadListFile(url, ipListFile); err != nil {
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
		if err := downloadListFile(url, ipListFile); err != nil {
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

// loadChinaDomainList 从程序目录加载中国域名列表
func loadChinaDomainList() error {
	// 获取可执行文件所在目录
	exePath, err := os.Executable()
	if err != nil {
		return fmt.Errorf("获取可执行文件路径失败: %w", err)
	}
	exeDir := filepath.Dir(exePath)
	listFile := filepath.Join(exeDir, "chn_domain.txt")

	// 如果文件不存在，尝试当前目录
	if _, err := os.Stat(listFile); os.IsNotExist(err) {
		listFile = "chn_domain.txt"
	}

	// 检查文件是否存在或为空
	needDownload := false
	if info, err := os.Stat(listFile); os.IsNotExist(err) {
		needDownload = true
		log.Printf("[加载] 域名列表文件不存在，将自动下载")
	} else if info.Size() == 0 {
		needDownload = true
		log.Printf("[加载] 域名列表文件为空，将自动下载")
	}

	// 如果需要下载，先下载文件（优先后用可用的 CDN 镜像）
	if needDownload {
		urls := []string{
			"https://fastly.jsdelivr.net/gh/felixonmars/dnsmasq-china-list@master/accelerated-domains.china.conf",
			"https://raw.githubusercontent.com/felixonmars/dnsmasq-china-list/master/accelerated-domains.china.conf",
		}
		var lastErr error
		downloaded := false
		for _, url := range urls {
			if err := downloadListFile(url, listFile); err != nil {
				lastErr = err
				continue
			}
			downloaded = true
			break
		}
		if !downloaded {
			return fmt.Errorf("自动下载域名列表失败: %w", lastErr)
		}
	}

	file, err := os.Open(listFile)
	if err != nil {
		return fmt.Errorf("打开域名列表文件失败: %w", err)
	}
	defer file.Close()

	domains := make(map[string]struct{}, 131072)
	scanner := bufio.NewScanner(file)
	scanner.Buffer(make([]byte, 64*1024), 64*1024)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		var domain string
		if strings.HasPrefix(line, "server=/") {
			// dnsmasq 格式: server=/example.com/114.114.114.114
			rest := strings.TrimPrefix(line, "server=/")
			if i := strings.IndexByte(rest, '/'); i > 0 {
				domain = rest[:i]
			}
		} else if !strings.HasPrefix(line, "server=") && !strings.ContainsAny(line, " \t") {
			// 兼容每行一个域名的格式
			domain = line
		}

		domain = strings.ToLower(strings.TrimSuffix(strings.TrimSpace(domain), "."))
		if domain == "" || !strings.Contains(domain, ".") {
			continue
		}
		domains[domain] = struct{}{}
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

	return nil
}

// isChinaDomain 检查域名是否属于中国域名（含 .cn、本地域名及其子域名）
func isChinaDomain(host string) bool {
	host = strings.ToLower(strings.TrimSpace(host))
	host = strings.TrimSuffix(host, ".")
	if host == "" {
		return false
	}

	// 本机/局域网域名始终直连
	if host == "localhost" || strings.HasSuffix(host, ".localhost") ||
		strings.HasSuffix(host, ".local") || strings.HasSuffix(host, ".lan") {
		return true
	}

	// .cn 与 .中国 域名一律直连
	if strings.HasSuffix(host, ".cn") || strings.HasSuffix(host, ".xn--fiqs8s") {
		return true
	}

	chinaDomainsMu.RLock()
	defer chinaDomainsMu.RUnlock()
	if len(chinaDomains) == 0 {
		return false
	}

	// 逐级匹配父域名（覆盖子域名），不匹配裸顶级域
	for {
		if _, ok := chinaDomains[host]; ok {
			return true
		}
		i := strings.IndexByte(host, '.')
		if i < 0 {
			return false
		}
		host = host[i+1:]
		if !strings.Contains(host, ".") {
			return false
		}
	}
}

// isLocalIP 判断是否为本机/内网/链路本地地址
func isLocalIP(ip net.IP) bool {
	return ip.IsLoopback() || ip.IsPrivate() || ip.IsLinkLocalUnicast() ||
		ip.IsLinkLocalMulticast() || ip.IsUnspecified()
}

// shouldBypassProxy 根据分流模式判断是否应该绕过代理（直连）
func shouldBypassProxy(targetHost string) bool {
	if routingMode == "none" {
		// "不改变代理"模式：所有流量都直连
		return true
	}
	if routingMode == "global" {
		// "全局代理"模式：所有流量都走代理
		return false
	}
	if routingMode == "bypass_cn" {
		// 中国域名直连，其余域名走代理
		if ip := net.ParseIP(targetHost); ip != nil {
			// IP 目标：本机/内网直连，其余回退到中国 IP 列表判断
			if isLocalIP(ip) {
				return true
			}
			return isChinaIP(targetHost)
		}
		return isChinaDomain(targetHost)
	}
	// 未知模式，默认走代理
	return false
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

func prepareECH() error {
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

	if !enableECH {
		return config, nil
	}

	if len(echList) == 0 {
		return nil, errors.New("ECH 配置为空，这是必需功能")
	}

	// 使用反射设置 ECH 字段（ECH 是核心功能，必须设置成功）
	if err := setECHConfig(config, echList); err != nil {
		return nil, fmt.Errorf("设置 ECH 配置失败（需要 Go 1.23+ 或支持 ECH 的版本）: %w", err)
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

// queryHTTPSRecord 通过 DoH 查询 HTTPS 记录
func queryHTTPSRecord(domain, dnsServer string) (string, error) {
	dohURL := dnsServer
	if !strings.HasPrefix(dohURL, "https://") && !strings.HasPrefix(dohURL, "http://") {
		dohURL = "https://" + dohURL
	}
	return queryDoH(domain, dohURL)
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
	version := getECHVersion()
	if b, _ := dohClientValue.Load().(*dohClientBox); b != nil && b.version == version {
		return b.client, nil
	}

	var echBytes []byte
	if enableECH {
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

	for attempt := 1; attempt <= maxRetries; attempt++ {
		var echBytes []byte
		if enableECH {
			var echErr error
			echBytes, echErr = getECHList()
			if echErr != nil {
				if attempt < maxRetries {
					refreshECH()
					continue
				}
				return nil, echErr
			}
		}

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
			if enableECH && strings.Contains(dialErr.Error(), "ECH") && attempt < maxRetries {
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

// ======================== WebSocket 连接池 ========================

const (
	poolTargetSize = 3                // 预热连接数量
	poolTTL        = 2 * time.Minute  // 连接最长空闲时间，到期回收重建
	poolPingEvery  = 15 * time.Second // 保活 ping 间隔
	poolFillDelay  = 2 * time.Second  // 维护循环间隔
	poolConnectTO  = 8 * time.Second  // 池连接 CONNECT 等待上限
	freshConnectTO = 20 * time.Second // 新建连接 CONNECT 等待上限
)

type poolEntry struct {
	conn *websocket.Conn
	born time.Time
}

type wsConnPool struct {
	mu      sync.Mutex
	conns   []*poolEntry
	fillSig chan struct{}
}

var connPool = &wsConnPool{fillSig: make(chan struct{}, 1)}

// start 启动连接池后台维护（预热、保活、回收）
func (p *wsConnPool) start() {
	log.Printf("[连接池] 启动预热（目标: %d 条连接）", poolTargetSize)
	p.trySignalFill()
	go p.maintainLoop()
}

func (p *wsConnPool) trySignalFill() {
	select {
	case p.fillSig <- struct{}{}:
	default:
	}
}

// tryGet 取出一条预热连接（无可用连接时返回 nil）
func (p *wsConnPool) tryGet() *websocket.Conn {
	p.mu.Lock()
	defer p.mu.Unlock()

	if len(p.conns) == 0 {
		return nil
	}
	e := p.conns[len(p.conns)-1]
	p.conns = p.conns[:len(p.conns)-1]

	if len(p.conns) == 0 {
		p.trySignalFill()
	}
	return e.conn
}

// maintainLoop 后台维护：回收过期/失效连接、保活、补充预热连接
func (p *wsConnPool) maintainLoop() {
	lastPing := time.Now().Add(-poolPingEvery)
	for {
		select {
		case <-p.fillSig:
		case <-time.After(poolFillDelay):
		}

		now := time.Now()
		var toClose []*poolEntry

		p.mu.Lock()
		// 回收超过 TTL 的连接
		alive := p.conns[:0]
		for _, e := range p.conns {
			if now.Sub(e.born) >= poolTTL {
				toClose = append(toClose, e)
				continue
			}
			alive = append(alive, e)
		}
		p.conns = alive

		// 保活 ping（在锁内完成，避免与取出的连接产生并发写）
		if now.Sub(lastPing) >= poolPingEvery {
			lastPing = now
			for i := len(p.conns) - 1; i >= 0; i-- {
				if err := p.conns[i].conn.WriteMessage(websocket.PingMessage, nil); err != nil {
					toClose = append(toClose, p.conns[i])
					p.conns = append(p.conns[:i], p.conns[i+1:]...)
				}
			}
		}
		need := poolTargetSize - len(p.conns)
		p.mu.Unlock()

		for _, e := range toClose {
			e.conn.Close()
		}

		// 补充预热连接（拨号在锁外进行，不阻塞取用）
		for i := 0; i < need; i++ {
			ws, err := dialWebSocketWithECH(2)
			if err != nil {
				break
			}
			p.mu.Lock()
			if len(p.conns) < poolTargetSize {
				p.conns = append(p.conns, &poolEntry{conn: ws, born: time.Now()})
				p.mu.Unlock()
			} else {
				p.mu.Unlock()
				ws.Close()
				break
			}
		}
	}
}

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

// connectTunnel 建立代理隧道：优先使用连接池中的预热连接，失败时回退新建
func connectTunnel(target, firstFrame string) (*websocket.Conn, error) {
	// 最多尝试 2 条预热连接，防止失效连接拖慢请求
	for i := 0; i < 2; i++ {
		pooled := connPool.tryGet()
		if pooled == nil {
			break
		}
		broken, err := sendConnect(pooled, target, firstFrame, poolConnectTO)
		if err == nil {
			return pooled, nil
		}
		pooled.Close()
		if !broken {
			// 服务端明确拒绝（目标不可达等），不再重试
			return nil, err
		}
	}

	// 新建连接（含 ECH 刷新重试）
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
	if shouldBypassProxy(targetHost) {
		log.Printf("[分流] %s -> %s (直连，绕过代理)", clientAddr, target)
		return handleDirectConnection(conn, target, clientAddr, mode, firstFrame, readSrc)
	}

	// 走代理（优先复用连接池中的预热连接，省去 TLS/WS 握手时间）
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

// handleDirectConnection 处理直连（绕过代理）
func handleDirectConnection(conn net.Conn, target, clientAddr string, mode int, firstFrame string, readSrc io.Reader) error {
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
	targetConn, err := net.DialTimeout("tcp", target, 10*time.Second)
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
