// --- START OF FILE ech-workers.go ---

package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/md5"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
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
	"time"

	"github.com/gorilla/websocket"
)

// ======================== 全局参数 ========================

type Config struct {
	Listen         string   `json:"listen"`
	Server         string   `json:"server"`
	ServerIP       string   `json:"serverIP"`
	Token          string   `json:"token"`
	DNS            string   `json:"dns"`
	ECHDomain      string   `json:"echDomain"`
	Routing        string   `json:"routing"`
	UpdateInterval string   `json:"updateInterval"`
	PrivateIP      []string `json:"privateIP"`
	PrivateDomain  []string `json:"privateDomain"`
}

var (
	listenAddr     string
	serverAddr     string
	serverIP       string
	token          string
	dnsServer      string
	echDomain      string
	routingMode    string
	updateInterval time.Duration

	echListMu sync.RWMutex
	echList   []byte

	chinaDomainsMu sync.RWMutex
	chinaDomains   map[string]struct{}
	domainFileHash string

	chinaIPsMu      sync.RWMutex
	chinaIPv4Ranges []ipRangeV4
	chinaIPv6Ranges []ipRangeV6
	ipFileHash      string

	privateIPsMu      sync.RWMutex
	privateIPv4Ranges []ipRangeV4
	privateIPv6Ranges []ipRangeV6

	privateDomainsMu sync.RWMutex
	privateDomains   map[string]struct{}
)

type ipRangeV4 struct {
	start uint32
	end   uint32
}

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
	flag.StringVar(&routingMode, "routing", "global", "分流模式: global(全局代理), bypass_cn(跳过中国大陆域名和IP), none(不改变代理)")
	flag.DurationVar(&updateInterval, "update", 24*time.Hour, "自动更新路由规则的时间间隔 (设为 0 禁用)")
	flag.StringVar(&configPath, "config", "config.json", "配置文件路径")
}

var configPath string

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

func main() {
	flag.Parse()

	cfg, err := loadConfig(configPath)
	if err != nil {
		log.Printf("[配置] 加载配置文件失败: %v", err)
	}

	if cfg != nil {
		log.Printf("[配置] 已加载配置文件: %s", configPath)
		if listenAddr == "127.0.0.1:30000" && cfg.Listen != "" {
			listenAddr = cfg.Listen
		}
		if serverAddr == "" && cfg.Server != "" {
			serverAddr = cfg.Server
		}
		if serverIP == "" && cfg.ServerIP != "" {
			serverIP = cfg.ServerIP
		}
		if token == "" && cfg.Token != "" {
			token = cfg.Token
		}
		if dnsServer == "dns.alidns.com/dns-query" && cfg.DNS != "" {
			dnsServer = cfg.DNS
		}
		if echDomain == "cloudflare-ech.com" && cfg.ECHDomain != "" {
			echDomain = cfg.ECHDomain
		}
		if routingMode == "global" && cfg.Routing != "" {
			routingMode = cfg.Routing
		}
		if updateInterval == 24*time.Hour && cfg.UpdateInterval != "" {
			if dur, err := time.ParseDuration(cfg.UpdateInterval); err == nil {
				updateInterval = dur
			}
		}
	}

	loadPrivateRules(cfg)

	if serverAddr == "" {
		log.Fatal("必须指定服务端地址 -f 或在配置文件中指定\n\n示例:\n  ./client -l 127.0.0.1:1080 -f your-worker.workers.dev:443 -token your-token\n\n配置文件示例 (config.json):\n{\n  \"listen\": \"127.0.0.1:30000\",\n  \"server\": \"your-worker.workers.dev:443\",\n  \"serverIP\": \"\",\n  \"token\": \"your-token\",\n  \"dns\": \"dns.alidns.com/dns-query\",\n  \"echDomain\": \"cloudflare-ech.com\",\n  \"routing\": \"global\",\n  \"updateInterval\": \"24h\"\n}")
	}

	log.Printf("[启动] 正在获取 ECH 配置...")
	if err := prepareECH(); err != nil {
		log.Fatalf("[启动] 获取 ECH 配置失败: %v", err)
	}

	// 加载分流规则（中国域名列表 + 中国 IP 列表）
	if routingMode == "bypass_cn" {
		log.Printf("[启动] 分流模式: 跳过中国大陆，正在加载路由列表...")

		// 初始化加载规则 (false 表示优先从本地读取)
		updateDomainList(false)
		updateIPList(false)

		// 启动后台自动更新守护协程
		startAutoUpdater()

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

// ======================== 数据更新与工具函数 ========================

// calculateMD5 计算数据的 MD5 哈希
func calculateMD5(data []byte) string {
	hash := md5.Sum(data)
	return hex.EncodeToString(hash[:])
}

// downloadData 纯内存下载数据
func downloadData(url string) ([]byte, error) {
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Get(url)
	if err != nil {
		return nil, fmt.Errorf("下载失败: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("HTTP 状态码异常: %d", resp.StatusCode)
	}

	return io.ReadAll(resp.Body)
}

// updateDomainList 热更新域名列表
func updateDomainList(forceDownload bool) {
	exePath, _ := os.Executable()
	filePath := filepath.Join(filepath.Dir(exePath), "chn_domain.txt")

	var data []byte
	var err error

	info, statErr := os.Stat(filePath)
	isLocalMissing := os.IsNotExist(statErr) || info.Size() == 0

	if forceDownload || isLocalMissing {
		if isLocalMissing && !forceDownload {
			log.Printf("[加载-域名] 本地列表缺失，准备从远端下载...")
		} else if forceDownload {
			log.Printf("[更新-域名] 开始检查远端规则更新...")
		}
		
		url := "https://raw.githubusercontent.com/felixonmars/dnsmasq-china-list/master/accelerated-domains.china.conf"
		data, err = downloadData(url)
		if err != nil {
			log.Printf("[警告-域名] 获取远端规则失败: %v", err)
			return
		}
	} else {
		data, err = os.ReadFile(filePath)
		if err != nil {
			log.Printf("[警告-域名] 读取本地文件失败: %v", err)
			return
		}
	}

	// 1. 内容 Hash 校验
	newHash := calculateMD5(data)
	chinaDomainsMu.RLock()
	currentHash := domainFileHash
	chinaDomainsMu.RUnlock()

	if forceDownload && newHash == currentHash {
		log.Printf("[更新-域名] 远端规则内容无变化 (MD5匹配)，无需更新")
		return
	}

	// 2. 解析数据到全新 Map
	newDomains := make(map[string]struct{})
	scanner := bufio.NewScanner(bytes.NewReader(data))
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if strings.HasPrefix(line, "server=/") {
			parts := strings.Split(line, "/")
			if len(parts) >= 3 {
				newDomains[strings.ToLower(parts[1])] = struct{}{}
			}
		} else {
			newDomains[strings.ToLower(line)] = struct{}{}
		}
	}

	// 3. 容错校验
	if len(newDomains) == 0 {
		log.Printf("[警告-域名] 解析到的规则数为 0，可能数据损坏，拒绝替换现有规则")
		return
	}

	// 4. 写盘保存 (如果是新下载的数据)
	if forceDownload || isLocalMissing {
		if err := os.WriteFile(filePath, data, 0644); err != nil {
			log.Printf("[警告-域名] 保存到本地缓存文件失败: %v", err)
		} else if isLocalMissing {
			log.Printf("[加载-域名] 已成功下载并保存至: %s", filePath)
		}
	}

	// 5. 无锁热替换 (瞬间完成)
	chinaDomainsMu.Lock()
	chinaDomains = newDomains
	domainFileHash = newHash
	chinaDomainsMu.Unlock()

	if forceDownload {
		log.Printf("[更新-域名] 规则热更新成功！最新规则数: %d 条", len(newDomains))
	} else {
		log.Printf("[启动-域名] 规则加载完毕: %d 条", len(newDomains))
	}
}

// updateIPList 热更新 IP 列表
func updateIPList(forceDownload bool) {
	exePath, _ := os.Executable()
	filePath := filepath.Join(filepath.Dir(exePath), "chn_ip.txt")

	var data []byte
	var err error

	info, statErr := os.Stat(filePath)
	isLocalMissing := os.IsNotExist(statErr) || info.Size() == 0

	if forceDownload || isLocalMissing {
		if isLocalMissing && !forceDownload {
			log.Printf("[加载-IP] 本地列表缺失，准备从远端下载...")
		} else if forceDownload {
			log.Printf("[更新-IP] 开始检查远端规则更新...")
		}

		url := "https://raw.githubusercontent.com/PaPerseller/chn-iplist/refs/heads/master/chnroute.txt"
		data, err = downloadData(url)
		if err != nil {
			log.Printf("[警告-IP] 获取远端规则失败: %v", err)
			return
		}
	} else {
		data, err = os.ReadFile(filePath)
		if err != nil {
			log.Printf("[警告-IP] 读取本地文件失败: %v", err)
			return
		}
	}

	// 1. 内容 Hash 校验
	newHash := calculateMD5(data)
	chinaIPsMu.RLock()
	currentHash := ipFileHash
	chinaIPsMu.RUnlock()

	if forceDownload && newHash == currentHash {
		log.Printf("[更新-IP] 远端规则内容无变化 (MD5匹配)，无需更新")
		return
	}

	// 2. 解析数据到全新 Slice
	var v4Ranges []ipRangeV4
	var v6Ranges []ipRangeV6

	scanner := bufio.NewScanner(bytes.NewReader(data))
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		ip, ipnet, err := net.ParseCIDR(line)
		if err != nil {
			continue
		}

		if ip4 := ip.To4(); ip4 != nil {
			start := binary.BigEndian.Uint32(ip4)
			mask := binary.BigEndian.Uint32(ipnet.Mask)
			end := start | (^mask)
			v4Ranges = append(v4Ranges, ipRangeV4{start: start, end: end})
		} else {
			var start, end [16]byte
			mask := ipnet.Mask
			ip16 := ip.To16()
			for i := 0; i < 16; i++ {
				start[i] = ip16[i] & mask[i]
				end[i] = start[i] | ^mask[i]
			}
			v6Ranges = append(v6Ranges, ipRangeV6{start: start, end: end})
		}
	}

	// 3. 容错校验
	if len(v4Ranges)+len(v6Ranges) == 0 {
		log.Printf("[警告-IP] 解析到的规则数为 0，可能数据损坏，拒绝替换现有规则")
		return
	}

	// 排序以便二分查找
	sort.Slice(v4Ranges, func(i, j int) bool { return v4Ranges[i].start < v4Ranges[j].start })
	sort.Slice(v6Ranges, func(i, j int) bool { return bytes.Compare(v6Ranges[i].start[:], v6Ranges[j].start[:]) < 0 })

	// 4. 写盘保存
	if forceDownload || isLocalMissing {
		if err := os.WriteFile(filePath, data, 0644); err != nil {
			log.Printf("[警告-IP] 保存到本地缓存文件失败: %v", err)
		} else if isLocalMissing {
			log.Printf("[加载-IP] 已成功下载并保存至: %s", filePath)
		}
	}

	// 5. 无锁热替换 (瞬间完成)
	chinaIPsMu.Lock()
	chinaIPv4Ranges = v4Ranges
	chinaIPv6Ranges = v6Ranges
	ipFileHash = newHash
	chinaIPsMu.Unlock()

	if forceDownload {
		log.Printf("[更新-IP] 规则热更新成功！最新 IPv4: %d 段, IPv6: %d 段", len(v4Ranges), len(v6Ranges))
	} else {
		log.Printf("[启动-IP] 规则加载完毕: IPv4: %d 段, IPv6: %d 段", len(v4Ranges), len(v6Ranges))
	}
}

// startAutoUpdater 启动后台自动更新守护进程
func startAutoUpdater() {
	if updateInterval <= 0 {
		log.Printf("[守护进程] 自动更新功能已禁用 (-update 0)")
		return
	}

	log.Printf("[守护进程] 自动热更新已启动，更新频率: %v", updateInterval)
	ticker := time.NewTicker(updateInterval)

	go func() {
		for range ticker.C {
			log.Printf("==============================================")
			log.Printf("[自动更新] 触发定时任务，正在检查远端路由库...")
			updateDomainList(true) // true 强制从远端拉取并校验
			updateIPList(true)
			log.Printf("==============================================")
		}
	}()
}

func loadPrivateRules(cfg *Config) {
	privateIPsMu.Lock()
	defer privateIPsMu.Unlock()

	privateDomainsMu.Lock()
	defer privateDomainsMu.Unlock()

	if cfg == nil || (len(cfg.PrivateIP) == 0 && len(cfg.PrivateDomain) == 0) {
		return
	}

	var v4Ranges []ipRangeV4
	var v6Ranges []ipRangeV6

	for _, cidr := range cfg.PrivateIP {
		ip, ipnet, err := net.ParseCIDR(cidr)
		if err != nil {
			continue
		}

		if ip4 := ip.To4(); ip4 != nil {
			start := binary.BigEndian.Uint32(ip4)
			mask := binary.BigEndian.Uint32(ipnet.Mask)
			end := start | (^mask)
			v4Ranges = append(v4Ranges, ipRangeV4{start: start, end: end})
		} else {
			var start, end [16]byte
			mask := ipnet.Mask
			ip16 := ip.To16()
			for i := 0; i < 16; i++ {
				start[i] = ip16[i] & mask[i]
				end[i] = start[i] | ^mask[i]
			}
			v6Ranges = append(v6Ranges, ipRangeV6{start: start, end: end})
		}
	}

	sort.Slice(v4Ranges, func(i, j int) bool { return v4Ranges[i].start < v4Ranges[j].start })
	sort.Slice(v6Ranges, func(i, j int) bool { return bytes.Compare(v6Ranges[i].start[:], v6Ranges[j].start[:]) < 0 })

	privateIPv4Ranges = v4Ranges
	privateIPv6Ranges = v6Ranges

	domains := make(map[string]struct{})
	for _, d := range cfg.PrivateDomain {
		domains[strings.ToLower(d)] = struct{}{}
	}
	privateDomains = domains

	log.Printf("[私有规则] 已加载: IPv4/IPv6段 %d, 域名 %d", len(v4Ranges)+len(v6Ranges), len(domains))
}

func isPrivateIP(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}

	privateIPsMu.RLock()
	defer privateIPsMu.RUnlock()

	if ip4 := ip.To4(); ip4 != nil {
		val := binary.BigEndian.Uint32(ip4)
		idx := sort.Search(len(privateIPv4Ranges), func(i int) bool {
			return privateIPv4Ranges[i].end >= val
		})
		if idx < len(privateIPv4Ranges) && privateIPv4Ranges[idx].start <= val {
			return true
		}
		return false
	}

	ip16 := ip.To16()
	idx := sort.Search(len(privateIPv6Ranges), func(i int) bool {
		return bytes.Compare(privateIPv6Ranges[i].end[:], ip16) >= 0
	})
	if idx < len(privateIPv6Ranges) && bytes.Compare(privateIPv6Ranges[idx].start[:], ip16) <= 0 {
		return true
	}
	return false
}

func isPrivateDomain(domain string) bool {
	domain = strings.ToLower(domain)
	privateDomainsMu.RLock()
	defer privateDomainsMu.RUnlock()

	if _, exists := privateDomains[domain]; exists {
		return true
	}

	parts := strings.Split(domain, ".")
	for i := 0; i < len(parts); i++ {
		subDomain := strings.Join(parts[i:], ".")
		if _, exists := privateDomains[subDomain]; exists {
			return true
		}
	}
	return false
}

func isChinaDomain(domain string) bool {
	domain = strings.ToLower(domain)
	chinaDomainsMu.RLock()
	defer chinaDomainsMu.RUnlock()

	parts := strings.Split(domain, ".")
	for i := 0; i < len(parts); i++ {
		subDomain := strings.Join(parts[i:], ".")
		if _, exists := chinaDomains[subDomain]; exists {
			return true
		}
	}
	return false
}

func isChinaIP(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}

	chinaIPsMu.RLock()
	defer chinaIPsMu.RUnlock()

	if ip4 := ip.To4(); ip4 != nil {
		// IPv4 二分查找
		val := binary.BigEndian.Uint32(ip4)
		idx := sort.Search(len(chinaIPv4Ranges), func(i int) bool {
			return chinaIPv4Ranges[i].end >= val
		})
		if idx < len(chinaIPv4Ranges) && chinaIPv4Ranges[idx].start <= val {
			return true
		}
		return false
	}

	// IPv6 二分查找
	ip16 := ip.To16()
	idx := sort.Search(len(chinaIPv6Ranges), func(i int) bool {
		return bytes.Compare(chinaIPv6Ranges[i].end[:], ip16) >= 0
	})
	if idx < len(chinaIPv6Ranges) && bytes.Compare(chinaIPv6Ranges[idx].start[:], ip16) <= 0 {
		return true
	}
	return false
}

func shouldBypassProxy(targetHost string) bool {
	if ip := net.ParseIP(targetHost); ip != nil {
		if isPrivateIP(targetHost) {
			return true
		}
	} else {
		if isPrivateDomain(targetHost) {
			return true
		}
	}

	if routingMode == "none" {
		return true 
	}
	if routingMode == "global" {
		return false
	}

	if routingMode == "bypass_cn" {
		// 1. 【IP兜底机制】：如果目标直接就是一个 IP 地址
		if ip := net.ParseIP(targetHost); ip != nil {
			isCN := isChinaIP(targetHost)
			return isCN
		}

		// 2. 如果是域名，判断是否是中国域名
		if isChinaDomain(targetHost) {
			// 如果你也想看域名的匹配日志，可以把下面这行注释打开
			//log.Printf("[路由-域名匹配] %s -> 命中中国域名，放行直连", targetHost)
			return true 
		}

		// 非中国域名，一律走代理（不进行本地 DNS 解析防污染）
		return false
	}

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
	echListMu.Unlock()
	log.Printf("[ECH] 配置已加载，长度: %d 字节", len(raw))
	return nil
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

func buildTLSConfigWithECH(serverName string, echList []byte) (*tls.Config, error) {
	roots, err := x509.SystemCertPool()
	if err != nil {
		return nil, fmt.Errorf("加载系统根证书失败: %w", err)
	}

	if echList == nil || len(echList) == 0 {
		return nil, errors.New("ECH 配置为空，这是必需功能")
	}

	config := &tls.Config{
		MinVersion: tls.VersionTLS13,
		ServerName: serverName,
		RootCAs:    roots,
	}

	if err := setECHConfig(config, echList); err != nil {
		return nil, fmt.Errorf("设置 ECH 配置失败（需要 Go 1.23+ 或支持 ECH 的版本）: %w", err)
	}

	return config, nil
}

func setECHConfig(config *tls.Config, echList []byte) error {
	configValue := reflect.ValueOf(config).Elem()

	field1 := configValue.FieldByName("EncryptedClientHelloConfigList")
	if !field1.IsValid() || !field1.CanSet() {
		return fmt.Errorf("EncryptedClientHelloConfigList 字段不可用，需要 Go 1.23+ 版本")
	}
	field1.Set(reflect.ValueOf(echList))

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

	_, err = conn.Write(dnsQuery)
	if err != nil {
		return "", fmt.Errorf("发送 UDP DNS 查询失败: %w", err)
	}

	buf := make([]byte, 4096)
	n, err := conn.Read(buf)
	if err != nil {
		return "", fmt.Errorf("接收 UDP DNS 响应失败: %w", err)
	}

	return parseDNSResponse(buf[:n])
}

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

func queryDoHForProxy(dnsQuery []byte) ([]byte, error) {
	_, port, _, err := parseServerAddr(serverAddr)
	if err != nil {
		return nil, err
	}

	dohURL := fmt.Sprintf("https://cloudflare-dns.com:%s/dns-query", port)

	echBytes, err := getECHList()
	if err != nil {
		return nil, fmt.Errorf("获取 ECH 配置失败: %w", err)
	}

	tlsCfg, err := buildTLSConfigWithECH("cloudflare-dns.com", echBytes)
	if err != nil {
		return nil, fmt.Errorf("构建 TLS 配置失败: %w", err)
	}

	transport := &http.Transport{
		TLSClientConfig: tlsCfg,
	}

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
		echBytes, echErr := getECHList()
		if echErr != nil {
			if attempt < maxRetries {
				refreshECH()
				continue
			}
			return nil, echErr
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

	buf := make([]byte, 1)
	n, err := conn.Read(buf)
	if err != nil || n == 0 {
		return
	}

	firstByte := buf[0]

	switch firstByte {
	case 0x05:
		handleSOCKS5(conn, clientAddr, firstByte)
	case 'C', 'G', 'P', 'H', 'D', 'O', 'T':
		handleHTTP(conn, clientAddr, firstByte)
	default:
		log.Printf("[代理] %s 未知协议: 0x%02x", clientAddr, firstByte)
	}
}

// ======================== SOCKS5 处理 ========================

func handleSOCKS5(conn net.Conn, clientAddr string, firstByte byte) {
	if firstByte != 0x05 {
		log.Printf("[SOCKS5] %s 版本错误: 0x%02x", clientAddr, firstByte)
		return
	}

	buf := make([]byte, 1)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return
	}

	nmethods := buf[0]
	methods := make([]byte, nmethods)
	if _, err := io.ReadFull(conn, methods); err != nil {
		return
	}

	if _, err := conn.Write([]byte{0x05, 0x00}); err != nil {
		return
	}

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

		if err := handleTunnel(conn, target, clientAddr, modeSOCKS5, ""); err != nil {
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

	localAddr := udpConn.LocalAddr().(*net.UDPAddr)
	port := localAddr.Port

	log.Printf("[UDP] %s UDP ASSOCIATE 监听端口: %d", clientAddr, port)

	response := []byte{0x05, 0x00, 0x00, 0x01}
	response = append(response, 127, 0, 0, 1)
	response = append(response, byte(port>>8), byte(port&0xff))

	if _, err := tcpConn.Write(response); err != nil {
		udpConn.Close()
		return
	}

	stopChan := make(chan struct{})
	go handleUDPRelay(udpConn, clientAddr, stopChan)

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

		if n < 10 {
			continue
		}

		data := buf[:n]
		if data[2] != 0x00 {
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

		if dstPort == 53 {
			log.Printf("[UDP-DNS] %s -> %s (DoH 查询)", clientAddr, target)
			go handleDNSQuery(udpConn, addr, udpData, data[:headerLen])
		} else {
			log.Printf("[UDP] %s -> %s (暂不支持非 DNS UDP)", clientAddr, target)
		}
	}
}

func handleDNSQuery(udpConn *net.UDPConn, clientAddr *net.UDPAddr, dnsQuery []byte, socks5Header []byte) {
	dnsResponse, err := queryDoHForProxy(dnsQuery)
	if err != nil {
		log.Printf("[UDP-DNS] DoH 查询失败: %v", err)
		return
	}

	response := make([]byte, 0, len(socks5Header)+len(dnsResponse))
	response = append(response, socks5Header...)
	response = append(response, dnsResponse...)

	_, err = udpConn.WriteToUDP(response, clientAddr)
	if err != nil {
		log.Printf("[UDP-DNS] 发送响应失败: %v", err)
		return
	}

	log.Printf("[UDP-DNS] DoH 查询成功，响应 %d 字节", len(dnsResponse))
}

// ======================== HTTP 处理 ========================

func handleHTTP(conn net.Conn, clientAddr string, firstByte byte) {
	reader := bufio.NewReader(io.MultiReader(
		strings.NewReader(string(firstByte)),
		conn,
	))

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
		log.Printf("[HTTP-CONNECT] %s -> %s", clientAddr, requestURL)
		if err := handleTunnel(conn, requestURL, clientAddr, modeHTTPConnect, ""); err != nil {
			if !isNormalCloseError(err) {
				log.Printf("[HTTP-CONNECT] %s 代理失败: %v", clientAddr, err)
			}
		}

	case "GET", "POST", "PUT", "DELETE", "HEAD", "OPTIONS", "PATCH", "TRACE":
		log.Printf("[HTTP-%s] %s -> %s", method, clientAddr, requestURL)

		var target string
		var path string

		if strings.HasPrefix(requestURL, "http://") {
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
			target = headers["host"]
			path = requestURL
		}

		if target == "" {
			conn.Write([]byte("HTTP/1.1 400 Bad Request\r\n\r\n"))
			return
		}

		if !strings.Contains(target, ":") {
			target += ":80"
		}

		var requestBuilder strings.Builder
		requestBuilder.WriteString(fmt.Sprintf("%s %s %s\r\n", method, path, httpVersion))

		for _, line := range headerLines {
			key := strings.Split(line, ":")[0]
			keyLower := strings.ToLower(strings.TrimSpace(key))
			if keyLower != "proxy-connection" && keyLower != "proxy-authorization" {
				requestBuilder.WriteString(line)
				requestBuilder.WriteString("\r\n")
			}
		}
		requestBuilder.WriteString("\r\n")

		if contentLength := headers["content-length"]; contentLength != "" {
			var length int
			fmt.Sscanf(contentLength, "%d", &length)
			if length > 0 && length < 10*1024*1024 {
				body := make([]byte, length)
				if _, err := io.ReadFull(reader, body); err == nil {
					requestBuilder.Write(body)
				}
			}
		}

		firstFrame := requestBuilder.String()

		if err := handleTunnel(conn, target, clientAddr, modeHTTPProxy, firstFrame); err != nil {
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

const (
	modeSOCKS5      = 1
	modeHTTPConnect = 2
	modeHTTPProxy   = 3
)

func handleTunnel(conn net.Conn, target, clientAddr string, mode int, firstFrame string) error {
	targetHost, _, err := net.SplitHostPort(target)
	if err != nil {
		targetHost = target
	}

	if shouldBypassProxy(targetHost) {
		log.Printf("[分流] %s -> %s (直连，绕过代理)", clientAddr, target)
		return handleDirectConnection(conn, target, clientAddr, mode, firstFrame)
	}

	log.Printf("[分流] %s -> %s (通过代理)", clientAddr, target)
	wsConn, err := dialWebSocketWithECH(2)
	if err != nil {
		sendErrorResponse(conn, mode)
		return err
	}
	defer wsConn.Close()

	var mu sync.Mutex
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

	conn.SetDeadline(time.Time{})

	if firstFrame == "" && mode == modeSOCKS5 {
		_ = conn.SetReadDeadline(time.Now().Add(100 * time.Millisecond))
		buffer := make([]byte, 32768)
		n, _ := conn.Read(buffer)
		_ = conn.SetReadDeadline(time.Time{})
		if n > 0 {
			firstFrame = string(buffer[:n])
		}
	}

	connectMsg := fmt.Sprintf("CONNECT:%s|%s", target, firstFrame)
	mu.Lock()
	err = wsConn.WriteMessage(websocket.TextMessage, []byte(connectMsg))
	mu.Unlock()
	if err != nil {
		sendErrorResponse(conn, mode)
		return err
	}

	_, msg, err := wsConn.ReadMessage()
	if err != nil {
		sendErrorResponse(conn, mode)
		return err
	}

	response := string(msg)
	if strings.HasPrefix(response, "ERROR:") {
		sendErrorResponse(conn, mode)
		return errors.New(response)
	}
	if response != "CONNECTED" {
		sendErrorResponse(conn, mode)
		return fmt.Errorf("意外响应: %s", response)
	}

	if err := sendSuccessResponse(conn, mode); err != nil {
		return err
	}

	log.Printf("[代理] %s 已连接: %s", clientAddr, target)

	done := make(chan bool, 2)

	go func() {
		buf := make([]byte, 32768)
		for {
			n, err := conn.Read(buf)
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

func handleDirectConnection(conn net.Conn, target, clientAddr string, mode int, firstFrame string) error {
	host, port, err := net.SplitHostPort(target)
	if err != nil {
		host = target
		if mode == modeHTTPConnect || mode == modeHTTPProxy {
			port = "443"
		} else {
			port = "80"
		}
		target = net.JoinHostPort(host, port)
	}

	targetConn, err := net.DialTimeout("tcp", target, 10*time.Second)
	if err != nil {
		sendErrorResponse(conn, mode)
		return fmt.Errorf("直连失败: %w", err)
	}
	defer targetConn.Close()

	if err := sendSuccessResponse(conn, mode); err != nil {
		return err
	}

	if firstFrame != "" {
		if _, err := targetConn.Write([]byte(firstFrame)); err != nil {
			return err
		}
	}

	done := make(chan bool, 2)

	go func() {
		io.Copy(targetConn, conn)
		done <- true
	}()

	go func() {
		io.Copy(conn, targetConn)
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
		_, err := conn.Write([]byte{0x05, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00})
		return err
	case modeHTTPConnect:
		_, err := conn.Write([]byte("HTTP/1.1 200 Connection Established\r\n\r\n"))
		return err
	case modeHTTPProxy:
		return nil
	}
	return nil
}

// --- END OF FILE ---