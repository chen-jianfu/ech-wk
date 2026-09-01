const WS_READY_STATE_OPEN = 1;
const WS_READY_STATE_CLOSING = 2;
const CF_FALLBACK_IPS = ['ProxyIP.CMLiussss.net'];// cm维护

// 复用 TextEncoder，避免重复创建
const encoder = new TextEncoder();

// 伪装页面：nginx 默认欢迎页
async function nginx() {
    return `
    <!DOCTYPE html>
    <html>
    <head>
    <title>Welcome to nginx!</title>
    <style>
        body {
            width: 35em;
            margin: 0 auto;
            font-family: Tahoma, Verdana, Arial, sans-serif;
        }
    </style>
    </head>
    <body>
    <h1>Welcome to nginx!</h1>
    <p>If you see this page, the nginx web server is successfully installed and
    working. Further configuration is required.</p>

    <p>For online documentation and support please refer to
    <a href="http://nginx.org/">nginx.org</a>.<br/>
    Commercial support is available at
    <a href="http://nginx.com/">nginx.com</a>.</p>

    <p><em>Thank you for using nginx.</em></p>
    </body>
    </html>
    `
}

// 统一伪装响应：所有非法请求返回 200 + nginx 页面
async function disguiseResponse() {
    const html = await nginx();
    return new Response(html, {
        status: 200,
        headers: { 'Content-Type': 'text/html; charset=utf-8' }
    });
}

import { connect } from 'cloudflare:sockets';

// 传输参数，取自 GrainTCP优化.js
const CFG = { chunk: 64 * 1024, dnPack: 32 * 1024, dnTail: 512, dnQr: 4, upPack: 20 * 1024, concur: 4 };

// ==================== 移植自 GrainTCP优化.js 的传输优化内核 ====================

const begin = (f, h, p) => { const s = f.connect({ hostname: h, port: p }); return s.opened.then(() => s); };

// 连接竞速：直连目标并发 CFG.concur 条，最快的胜出，其余关闭
const raceSprout = (f, h, p) => {
  const ts = Array.from({ length: CFG.concur }, () => begin(f, h, p));
  return Promise.any(ts).then(w => { for (const t of ts) t.then(s => { try { if (s !== w) s.close(); } catch {} }, () => {}); return w; });
};

// 直连竞速失败后，回退 IP 逐个串行尝试（不竞速）
const connectTo = async (f, h, p) => {
  try {
    return await raceSprout(f, h, p);
  } catch (err) {
    let lastErr = err;
    for (const fb of CF_FALLBACK_IPS) {
      try { return await begin(f, fb, p); } catch (e) { lastErr = e; }
    }
    throw lastErr;
  }
};

// 字节队列内核：小包合并为大包，减少写入次数
const mkK = (cap, cpy = 0) => { let q = [], h = 0, b = 0, buf = null;
  const e = () => h >= q.length, trim = () => { h > 32 && h * 2 >= q.length && (q = q.slice(h), h = 0); }, clear = () => { q = []; h = 0; b = 0; };
  const take = () => { if (e()) return null; const d = q[h]; q[h++] = undefined; b -= d.byteLength; trim(); return d; };
  const sow = d => { const n = d?.byteLength || 0; return !n || (q.push(d), b += n, 1); };
  const pack = d => { d ||= take(); if (!d || e()) return [d, 0];
    let n = d.byteLength, j = h; while (j < q.length) { const x = q[j], nn = n + x.byteLength; if (nn > cap) break; n = nn; j++; }
    if (j === h) return [d, 0]; const out = buf ||= new Uint8Array(cap); out.set(d);
    for (let o = d.byteLength; h < j;) { const x = q[h]; q[h++] = undefined; b -= x.byteLength; out.set(x, o); o += x.byteLength; }
    trim(); const u = out.subarray(0, n); return [cpy ? u.slice() : u, 1]; };
  return { e, get b() { return b; }, clear, take, sow, pack }; };

const mkQ = cap => { const k = mkK(cap); return { get empty() { return k.e(); }, clear: k.clear, sow: k.sow, bundle: d => k.pack(d) }; };

// 下行微批发送：1ms 定时器把小包攒到 dnPack 上限才发，大包直通
const mkDn = w => { const cap = CFG.dnPack, tail = CFG.dnTail, low = Math.max(4096, tail * 12), k = mkK(cap, 1); let tp = 0, gen = 0, qk = 0, qr = 0;
  const reap = () => { tp && clearTimeout(tp); tp = 0; qr = 0; for (;;) { const [u] = k.pack(); if (!u) break; w.send(u); } };
  const ripen = () => { if (k.e() || tp) return; if (k.b >= cap || cap - k.b < tail) return reap(); tp = setTimeout(() => {
    tp = 0; if (k.e()) return; if (k.b >= cap || cap - k.b < tail) return reap();
    if (qr < CFG.dnQr && (gen !== qk || k.b < low)) { qr++; qk = gen; return ripen(); } reap(); }, 1); };
  return { send(u) { let o = 0, n = u?.byteLength || 0; if (!n) return; while (o < n) { const m = Math.min(cap - k.b, n - o); if (!m) { reap(); continue; }
      k.sow(o || m !== n ? u.subarray(o, o + m) : u); gen++; o += m; if (k.b >= cap || cap - k.b < tail) reap(); else ripen(); } }, reap }; };

// BYOB 读泵：远端 → WebSocket，大块零拷贝直通，小块微批
const mill = async (rd, w, done) => { const r = rd.getReader({ mode: 'byob' }), tx = mkDn(w); let buf = new ArrayBuffer(CFG.chunk);
  try { for (;;) { const { done: d, value: v } = await r.read(new Uint8Array(buf, 0, CFG.chunk)); if (d) break; if (!v?.byteLength) continue; if (v.byteLength >= (CFG.chunk >> 1)) tx.reap(), w.send(v), buf = new ArrayBuffer(CFG.chunk); else tx.send(v.slice()), buf = v.buffer; } tx.reap(); } catch {} finally { try { tx.reap(); } catch {} try { r.releaseLock(); } catch {} }
  done && done(); };

export default {
  async fetch(request, env, ctx) {
    try {
      const token = '';
      const upgradeHeader = request.headers.get('Upgrade');

      // 非 WebSocket 请求 → 伪装响应
      if (!upgradeHeader || upgradeHeader.toLowerCase() !== 'websocket') {
        return disguiseResponse();
      }

      // Token 验证失败 → 伪装响应（不返回 401）
      if (token && request.headers.get('Sec-WebSocket-Protocol') !== token) {
        return disguiseResponse();
      }

      const [client, server] = Object.values(new WebSocketPair());
      server.accept({ allowHalfOpen: true });
      server.binaryType = 'arraybuffer';

      handleSession(server).catch(() => safeCloseWebSocket(server));

      // 修复 spread 类型错误
      const responseInit = {
        status: 101,
        webSocket: client
      };

      if (token) {
        responseInit.headers = { 'Sec-WebSocket-Protocol': token };
      }

      return new Response(null, responseInit);

    } catch (err) {
      // 任何异常 → 伪装响应（不返回 500）
      return disguiseResponse();
    }
  },
};

async function handleSession(webSocket) {
  let sock = null, curW = null, connecting = false, closed = false, busy = false;
  const uq = mkQ(CFG.upPack);

  const wither = () => {
    if (closed) return;
    closed = true;
    uq.clear();
    try { curW?.releaseLock(); } catch {}
    try { sock?.close(); } catch {}
    curW = sock = null;
    safeCloseWebSocket(webSocket);
  };

  const onRemoteEnd = () => {
    if (closed) return;
    try { webSocket.send('CLOSE'); } catch {}
    wither();
  };

  const drain = async () => {
    if (busy || closed) return;
    busy = true;
    try {
      while (!closed && sock && curW) {
        const [d] = uq.bundle();
        if (!d) break;
        await curW.write(d);
      }
    } catch { wither(); } finally {
      busy = false;
      if (!closed && sock && curW && !uq.empty) drain();
    }
  };

  const sow = (u) => {
    if (!u?.byteLength) return;
    if (uq.sow(u)) drain();
    else wither();
  };

  const parseAddress = (addr) => {
    if (addr[0] === '[') {
      const end = addr.indexOf(']');
      return {
        host: addr.substring(1, end),
        port: parseInt(addr.substring(end + 2), 10)
      };
    }
    const sep = addr.lastIndexOf(':');
    return {
      host: addr.substring(0, sep),
      port: parseInt(addr.substring(sep + 1), 10)
    };
  };

  webSocket.addEventListener('message', async (event) => {
    if (closed) return;

    try {
      const data = event.data;

      if (typeof data === 'string') {
        if (data.startsWith('CONNECT:')) {
          if (sock || connecting) return;
          connecting = true;
          const sep = data.indexOf('|', 8);
          try {
            const { host, port } = parseAddress(data.substring(8, sep));
            const w = await connectTo({ connect }, host, port);
            curW = w.writable.getWriter();
            sock = w;
            const firstFrame = data.substring(sep + 1);
            if (firstFrame) await curW.write(encoder.encode(firstFrame));
            webSocket.send('CONNECTED');
            mill(sock.readable, webSocket, onRemoteEnd);
            drain();
          } catch (err) {
            connecting = false;
            try { curW?.releaseLock(); } catch {}
            try { sock?.close(); } catch {}
            curW = sock = null;
            try { webSocket.send('ERROR:' + (err.errors?.[0]?.message || err.message)); } catch {}
            wither();
          }
          return;
        }
        if (data.startsWith('DATA:')) { sow(encoder.encode(data.substring(5))); return; }
        if (data === 'CLOSE') { wither(); return; }
        return;
      }

      if (data instanceof ArrayBuffer) sow(new Uint8Array(data));
    } catch (err) {
      try { webSocket.send('ERROR:' + err.message); } catch {}
      wither();
    }
  });

  webSocket.addEventListener('close', wither);
  webSocket.addEventListener('error', wither);
}

function safeCloseWebSocket(ws) {
  try {
    if (ws.readyState === WS_READY_STATE_OPEN ||
        ws.readyState === WS_READY_STATE_CLOSING) {
      ws.close(1000, 'Server closed');
    }
  } catch {}
}
