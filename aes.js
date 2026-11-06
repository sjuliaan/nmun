/* aes.js — compact AES-128 ECB encrypt/decrypt + PKCS#7, no dependencies.
 * Tables (S-box, inverse S-box, Rcon) are generated at load time from
 * GF(2^8) arithmetic, so there are no hand-typed tables to mistype.
 * Used by NetMod .nm unlocker (NetMod_4.2.0 mod, key "_netsyna_netmod_").
 */
(function (global) {
  'use strict';

  function gfMul(a, b) {
    let p = 0;
    for (let i = 0; i < 8; i++) {
      if (b & 1) p ^= a;
      b >>>= 1;
      a = (a << 1) ^ (a & 0x80 ? 0x11b : 0);
    }
    return p;
  }

  const SBOX = new Uint8Array(256);
  const INV_SBOX = new Uint8Array(256);
  const RCON = new Uint8Array(10);
  (function buildTables() {
    /* Generator 3 (0x03) is primitive in GF(2^8)/0x11B; 2 has order 51. */
    const exp = new Array(255);
    const log = new Array(256);
    let x = 1;
    for (let i = 0; i < 255; i++) { exp[i] = x; log[x] = i; x = gfMul(x, 3); }
    const inv = (v) => (v === 0 ? 0 : exp[(255 - log[v]) % 255]);
    const rotl = (v, n) => ((v << n) | (v >>> (8 - n))) & 0xff;
    for (let i = 0; i < 256; i++) {
      const s = inv(i);
      const out = s ^ rotl(s, 1) ^ rotl(s, 2) ^ rotl(s, 3) ^ rotl(s, 4) ^ 0x63;
      SBOX[i] = out;
      INV_SBOX[out] = i;
    }
    let rc = 1;
    for (let i = 0; i < 10; i++) { RCON[i] = rc; rc = gfMul(rc, 2); }
  })();

  function keyExpansion(key) {
    const w = new Uint32Array(44);
    for (let i = 0; i < 4; i++) w[i] = (key[4 * i] << 24) | (key[4 * i + 1] << 16) | (key[4 * i + 2] << 8) | key[4 * i + 3];
    for (let i = 4; i < 44; i++) {
      let t = w[i - 1];
      if (i % 4 === 0) {
        const b0 = (t >>> 24) & 0xff, b1 = (t >>> 16) & 0xff, b2 = (t >>> 8) & 0xff, b3 = t & 0xff;
        t = (SBOX[b1] << 24) | (SBOX[b2] << 16) | (SBOX[b3] << 8) | SBOX[b0];
        t ^= RCON[i / 4 - 1] << 24;
      }
      w[i] = w[i - 4] ^ t;
    }
    const rk = new Uint8Array(176);
    for (let i = 0; i < 44; i++) {
      rk[4 * i] = (w[i] >>> 24) & 0xff;
      rk[4 * i + 1] = (w[i] >>> 16) & 0xff;
      rk[4 * i + 2] = (w[i] >>> 8) & 0xff;
      rk[4 * i + 3] = w[i] & 0xff;
    }
    return rk;
  }

  function subShift(state) {
    const t = new Uint8Array(16);
    for (let r = 0; r < 4; r++) {
      for (let c = 0; c < 4; c++) {
        t[c * 4 + r] = SBOX[state[((c + r) % 4) * 4 + r]];
      }
    }
    return t;
  }

  function invSubShift(state) {
    const t = new Uint8Array(16);
    for (let r = 0; r < 4; r++) {
      for (let c = 0; c < 4; c++) {
        t[c * 4 + r] = INV_SBOX[state[((c - r + 4) % 4) * 4 + r]];
      }
    }
    return t;
  }

  function mixColumns(s) {
    const t = new Uint8Array(16);
    for (let c = 0; c < 4; c++) {
      const i = c * 4;
      const a0 = s[i], a1 = s[i + 1], a2 = s[i + 2], a3 = s[i + 3];
      const xt = (v) => ((v << 1) ^ (v & 0x80 ? 0x11b : 0)) & 0xff;
      t[i] = xt(a0) ^ (xt(a1) ^ a1) ^ a2 ^ a3;
      t[i + 1] = a0 ^ xt(a1) ^ (xt(a2) ^ a2) ^ a3;
      t[i + 2] = a0 ^ a1 ^ xt(a2) ^ (xt(a3) ^ a3);
      t[i + 3] = (xt(a0) ^ a0) ^ a1 ^ a2 ^ xt(a3);
    }
    return t;
  }

  function invMixColumns(s) {
    const t = new Uint8Array(16);
    for (let c = 0; c < 4; c++) {
      const i = c * 4;
      const a0 = s[i], a1 = s[i + 1], a2 = s[i + 2], a3 = s[i + 3];
      t[i] = gfMul(a0, 0x0e) ^ gfMul(a1, 0x0b) ^ gfMul(a2, 0x0d) ^ gfMul(a3, 0x09);
      t[i + 1] = gfMul(a0, 0x09) ^ gfMul(a1, 0x0e) ^ gfMul(a2, 0x0b) ^ gfMul(a3, 0x0d);
      t[i + 2] = gfMul(a0, 0x0d) ^ gfMul(a1, 0x09) ^ gfMul(a2, 0x0e) ^ gfMul(a3, 0x0b);
      t[i + 3] = gfMul(a0, 0x0b) ^ gfMul(a1, 0x0d) ^ gfMul(a2, 0x09) ^ gfMul(a3, 0x0e);
    }
    return t;
  }

  function encryptBlock(rk, inp, out) {
    let s = inp.slice(0, 16);
    for (let i = 0; i < 16; i++) s[i] ^= rk[i];
    for (let r = 1; r <= 9; r++) {
      s = subShift(s);
      s = mixColumns(s);
      const k = r * 16;
      for (let i = 0; i < 16; i++) s[i] ^= rk[k + i];
    }
    s = subShift(s);
    for (let i = 0; i < 16; i++) out[i] = s[i] ^ rk[160 + i];
  }

  function decryptBlock(rk, inp, out) {
    let s = inp.slice(0, 16);
    for (let i = 0; i < 16; i++) s[i] ^= rk[160 + i];
    for (let r = 9; r >= 1; r--) {
      s = invSubShift(s);
      const k = r * 16;
      for (let i = 0; i < 16; i++) s[i] ^= rk[k + i];
      s = invMixColumns(s);
    }
    s = invSubShift(s);
    for (let i = 0; i < 16; i++) out[i] = s[i] ^ rk[i];
  }

  /* ---- public API ---- */

  const AesECB = function (key) {
    if (!(key instanceof Uint8Array) || key.length !== 16) throw new Error('AES-128 requires a 16-byte key');
    this.encRk = keyExpansion(key);
  };

  AesECB.prototype.encrypt = function (data) {
    if (data.length % 16 !== 0) throw new Error('input must be a multiple of 16 bytes');
    const out = new Uint8Array(data.length);
    const blk = new Uint8Array(16);
    for (let i = 0; i < data.length; i += 16) {
      encryptBlock(this.encRk, data.subarray(i, i + 16), blk);
      out.set(blk, i);
    }
    return out;
  };

  AesECB.prototype.decrypt = function (data) {
    if (data.length % 16 !== 0) throw new Error('input must be a multiple of 16 bytes');
    const out = new Uint8Array(data.length);
    const blk = new Uint8Array(16);
    for (let i = 0; i < data.length; i += 16) {
      decryptBlock(this.encRk, data.subarray(i, i + 16), blk);
      out.set(blk, i);
    }
    return out;
  };

  const pkcs7Pad = (data) => {
    const n = 16 - (data.length % 16);
    const out = new Uint8Array(data.length + n);
    out.set(data);
    out.fill(n, data.length);
    return out;
  };

  const pkcs7Unpad = (data) => {
    if (data.length === 0) throw new Error('empty data');
    const n = data[data.length - 1];
    if (n < 1 || n > 16 || n > data.length) throw new Error('bad pad length');
    for (let i = data.length - n; i < data.length; i++) if (data[i] !== n) throw new Error('bad pad bytes');
    return data.slice(0, data.length - n);
  };

  /* base64 on Uint8Array (browser-safe, chunked) */
  const B64_CHARS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
  const toBase64 = (data) => {
    const chunks = [];
    const len = data.length;
    for (let o = 0; o < len; o += 0x8000) {
      let s = '';
      const end = Math.min(o + 0x8000, len);
      for (let i = o; i < end; i++) s += String.fromCharCode(data[i]);
      chunks.push(btoa(s));
    }
    return chunks.join('');
  };
  const fromBase64 = (str) => {
    str = str.replace(/[\s\r\n]+/g, '');
    if (typeof global.Buffer !== 'undefined') return new Uint8Array(global.Buffer.from(str, 'base64'));
    const bin = atob(str);
    const out = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  };

  const Netsyn = {
    AES_KEY: new Uint8Array(16).map((_, i) => '_netsyna_netmod_'.charCodeAt(i)),
    KEY_CANDIDATES: [
      '<n3t5yn4^n3tm0d>',
      '_netsyna_netmod_',
      'nicetrybuddygoon',
    ].map((s) => {
      const k = new Uint8Array(16);
      for (let i = 0; i < 16; i++) k[i] = s.charCodeAt(i);
      return k;
    }),
    LOCKED_SCHEMES: [
      'nm-http://', 'nm-ss://', 'nm-ssh://', 'nm-wireguard://',
      'nm-dns://', 'nm-socks://', 'nm-ssr://', 'nm-trojan://',
      'nm-trojan-go://', 'nm-vless://', 'nm-vmess://', 'nm-xray-json://',
    ],
    decryptContainer(data) {
      for (const key of this.KEY_CANDIDATES) {
        const aes = new AesECB(key);
        let pt;
        try { pt = pkcs7Unpad(aes.decrypt(data)); } catch (e) { continue; }
        const text = new TextDecoder().decode(pt);
        try { return { text, key, obj: JSON.parse(text) }; } catch (e) { continue; }
      }
      throw new Error('decryption failed with all candidate keys');
    },
    encryptContainer(text) {
      const data = new TextEncoder().encode(text);
      return toBase64(new AesECB(this.AES_KEY).encrypt(pkcs7Pad(data)));
    },
    decryptValue(str) {
      let data;
      try { data = fromBase64(str); } catch (e) { return null; }
      for (const key of this.KEY_CANDIDATES) {
        const aes = new AesECB(key);
        let pt;
        try { pt = pkcs7Unpad(aes.decrypt(data)); } catch (e) { continue; }
        try { return new TextDecoder().decode(pt); } catch (e) { continue; }
      }
      return null;
    },
    unlockString(v) {
      if (typeof v !== 'string') return v;
      for (const scheme of this.LOCKED_SCHEMES) {
        if (v.startsWith(scheme)) {
          const dec = this.decryptValue(v.slice(scheme.length));
          return dec !== null ? scheme.slice(3) + dec : v;
        }
      }
      return v;
    },
    /* Unlock one link line.
     * Locked URI:  nm-<scheme>:// + Encrypt(uri-without-scheme)
     * (SSH additionally re-encrypts the query string inside.)
     * Plain URI:   passed through unchanged.
     * Returns {locked, plain, scheme?, error?} or null for empty line. */
    unlockUriLine(line) {
      const s = String(line).trim();
      if (!s) return null;
      for (const scheme of this.LOCKED_SCHEMES) {
        if (s.startsWith(scheme)) {
          const enc = s.slice(scheme.length);
          const dec = this.decryptValue(enc);
          if (dec === null) {
            return { locked: true, scheme, plain: s, error: 'decryption failed (not a valid locked link?)' };
          }
          let plain = scheme.slice(3) + dec;
          if (scheme === 'nm-ssh://' && plain.includes('?')) {
            /* SSH outer decrypt leaves an inner Encrypt(query) blob. */
            const q = plain.indexOf('?');
            const query = plain.slice(q + 1);
            if (!query.includes('&')) {
              let decQ = null;
              try { decQ = this.decryptValue(decodeURIComponent(query)); } catch (e) { decQ = null; }
              if (decQ !== null && /[=&]/.test(decQ)) plain = plain.slice(0, q + 1) + decQ;
            }
          }
          return { locked: true, scheme, plain };
        }
      }
      return { locked: false, plain: s };
    },
    /* Unlock a block of text: URI links (one per line) and/or pasted .nm
     * base64. Returns { nm: {name,text,obj,unlocked} | null, links: [...] }. */
    unlockText(text) {
      const src = String(text);
      const trimmed = src.trim();
      const compact = trimmed.replace(/[\s\r\n]+/g, '');
      const isNmBlob = /^[A-Za-z0-9+/=]+$/.test(compact) && compact.length >= 40;
      if (isNmBlob) {
        try {
          const res = this.decryptContainer(this.fromBase64(compact));
          return {
            nm: { obj: res.obj, unlocked: this.unlockJson(JSON.parse(JSON.stringify(res.obj))) },
            links: [],
          };
        } catch (e) { /* not an .nm container - fall through to links */ }
      }
      const links = [];
      for (const line of src.split(/\r?\n/)) {
        const r = this.unlockUriLine(line);
        if (r) links.push(r);
      }
      return { nm: null, links };
    },
    unlockJson(obj) {
      if (Array.isArray(obj)) return obj.map((x) => this.unlockJson(x));
      if (obj && typeof obj === 'object') {
        const out = {};
        for (const k of Object.keys(obj)) out[k] = this.unlockJson(obj[k]);
        if ('Locked' in obj) out.Locked = false;
        if (Array.isArray(out.Common)) out.Common = out.Common.map((c) => this.unlockJson(c));
        if (out.Payload && typeof out.Payload === 'object') out.Payload.Locked = false;
        if (out.SNI && typeof out.SNI === 'object') out.SNI.Locked = false;
        if (out.RR && typeof out.RR === 'object') out.RR.Locked = false;
        if (Array.isArray(out.Proxy)) out.Proxy = out.Proxy.map((p) => this.unlockJson(p));
        if (Array.isArray(out.SSH)) out.SSH = out.SSH.map((s) => this.unlockJson(s));
        delete out.HwIds;
        if ('Prevent Wifi' in obj) out['Prevent Wifi'] = false;
        return out;
      }
      return this.unlockString(obj);
    },
  };

  global.Netsyn = Netsyn;
  global.AesECB = AesECB;
  Netsyn.fromBase64 = fromBase64;
  Netsyn.toBase64 = toBase64;
})(typeof globalThis !== 'undefined' ? globalThis : this);
