#!/usr/bin/env node
/**
 * merge.js — Standalone CC balance consolidator untuk RootsFi bridge (chore-utxo deployment).
 *
 * Fungsi: Merge/consolidate semua UTXO amulet CC untuk tiap akun di accounts.json supaya
 *         balance tidak split — mengurangi kegagalan TX send akibat insufficient single-UTXO.
 *
 * Catatan penting:
 *  - Endpoint cc-consolidate hanya tersedia di deployment khusus (chore-utxo-roots), BUKAN
 *    di production (bridge.rootsfi.com). Karena itu base URL & session dipisahkan dari
 *    tokens.json → disimpan ke merge_tokens.json.
 *  - Login flow: send-otp → (input OTP manual via stdin) → verify-otp → pending → (kalau
 *    alreadyActive) finalize-returning → balances → cc-consolidate.
 *  - Session di-reuse dari merge_tokens.json kalau cookie `cantonbridge_session` masih valid.
 */

"use strict";

const fs = require("fs");
const fsp = require("fs/promises");
const path = require("path");
const readline = require("readline");
const crypto = require("crypto");

// Lazy-loaded puppeteer (hanya diload kalau diperlukan untuk Vercel challenge)
let _puppeteer = null;
function getPuppeteer() {
  if (_puppeteer) return _puppeteer;
  try {
    const pe = require("puppeteer-extra");
    try {
      const stealth = require("puppeteer-extra-plugin-stealth");
      pe.use(stealth());
    } catch {
      /* stealth optional */
    }
    _puppeteer = pe;
  } catch {
    _puppeteer = require("puppeteer");
  }
  return _puppeteer;
}

// ─────────────────────────────────────────────────────────────────────────────
// Konstanta
// ─────────────────────────────────────────────────────────────────────────────

const BASE_URL =
  "https://cantonbridge-by-roots-git-chore-utxo-roots-ac3fe32c.vercel.app";

const PATHS = {
  onboard: "/onboard",
  send: "/send",
  bridge: "/bridge",
  sendOtp: "/api/auth/email/send-otp",
  verifyOtp: "/api/auth/email/verify-otp",
  pending: "/api/auth/pending",
  finalizeReturning: "/api/auth/finalize-returning",
  syncAccount: "/api/auth/sync-account",
  balances: "/api/wallet/balances",
  ccConsolidate: "/api/wallet/cc-consolidate",
  offers: "/api/wallet/offers"
};

const DEFAULT_HEADERS = {
  userAgent:
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.0.0 Safari/537.36",
  acceptLanguage: "id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7",
  secChUa: '"Google Chrome";v="147", "Not.A/Brand";v="8", "Chromium";v="147"',
  secChUaMobile: "?0",
  secChUaPlatform: '"macOS"',
  secFetchDest: "empty",
  secFetchMode: "cors",
  secFetchSite: "same-origin",
  priority: "u=1, i"
};

const REQUEST_TIMEOUT_MS = 60_000;
const CC_CONSOLIDATE_TIMEOUT_MS = 180_000; // consolidate bisa makan 14s+
const DELAY_BETWEEN_ACCOUNTS_MS = 4000;

const ACCOUNTS_PATH = path.join(__dirname, "accounts.json");
const TOKENS_PATH = path.join(__dirname, "merge_tokens.json");

// ─────────────────────────────────────────────────────────────────────────────
// Util
// ─────────────────────────────────────────────────────────────────────────────

function log(tag, ...args) {
  const ts = new Date().toISOString().slice(11, 19);
  console.log(`[${ts}] ${tag}`, ...args);
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

function maskEmail(email) {
  if (!email) return "";
  const [user, domain] = email.split("@");
  if (!domain) return email;
  const head = user.slice(0, 2);
  const tail = user.slice(-1);
  return `${head}***${tail}@${domain}`;
}

function uuidv4() {
  if (typeof crypto.randomUUID === "function") return crypto.randomUUID();
  const b = crypto.randomBytes(16);
  b[6] = (b[6] & 0x0f) | 0x40;
  b[8] = (b[8] & 0x3f) | 0x80;
  const hex = b.toString("hex");
  return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
}

async function readJson(filePath) {
  const txt = await fsp.readFile(filePath, "utf8");
  return JSON.parse(txt);
}

async function writeJsonAtomic(filePath, data) {
  const tmp = `${filePath}.tmp`;
  await fsp.writeFile(tmp, JSON.stringify(data, null, 2), "utf8");
  await fsp.rename(tmp, filePath);
}

// ─────────────────────────────────────────────────────────────────────────────
// Cookie jar (simple, per-client)
// ─────────────────────────────────────────────────────────────────────────────

class CookieJar {
  constructor() {
    this.map = new Map();
  }

  loadFromHeader(cookieHeader) {
    if (!cookieHeader) return;
    for (const piece of cookieHeader.split(";")) {
      const eq = piece.indexOf("=");
      if (eq > 0) {
        const name = piece.slice(0, eq).trim();
        const value = piece.slice(eq + 1).trim();
        if (name) this.map.set(name, value);
      }
    }
  }

  // Parse Node 18+ undici Headers.getSetCookie() (Array of raw Set-Cookie strings)
  ingestResponseHeaders(headers) {
    let setCookies = [];
    if (typeof headers.getSetCookie === "function") {
      setCookies = headers.getSetCookie() || [];
    } else {
      const raw = headers.get("set-cookie");
      if (raw) setCookies = splitCombinedSetCookie(raw);
    }
    for (const sc of setCookies) {
      const firstPart = sc.split(";")[0];
      const eq = firstPart.indexOf("=");
      if (eq > 0) {
        const name = firstPart.slice(0, eq).trim();
        const value = firstPart.slice(eq + 1).trim();
        if (name) this.map.set(name, value);
      }
    }
  }

  header() {
    if (this.map.size === 0) return "";
    const pairs = [];
    for (const [n, v] of this.map) pairs.push(`${n}=${v}`);
    return pairs.join("; ");
  }

  has(name) {
    return this.map.has(name);
  }

  toObject() {
    return Object.fromEntries(this.map);
  }

  loadFromObject(obj) {
    if (!obj) return;
    for (const [n, v] of Object.entries(obj)) {
      if (typeof v === "string") this.map.set(n, v);
    }
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Vercel browser challenge (ambil _vcrcs)
// ─────────────────────────────────────────────────────────────────────────────

async function readAllCookiesFromPage(page) {
  const merged = new Map();
  try {
    const a = await page.cookies();
    for (const c of a || []) if (c?.name) merged.set(c.name, c.value);
  } catch {
    /* ignore */
  }
  try {
    const ctx = page.browserContext();
    if (ctx && typeof ctx.cookies === "function") {
      const b = await ctx.cookies();
      for (const c of b || []) if (c?.name) merged.set(c.name, c.value);
    }
  } catch {
    /* ignore */
  }
  try {
    const client = await page.target().createCDPSession();
    const { cookies } = await client.send("Network.getAllCookies");
    for (const c of cookies || []) if (c?.name) merged.set(c.name, c.value);
    await client.detach().catch(() => {});
  } catch {
    /* ignore */
  }
  return merged;
}

async function solveBrowserChallenge({ jar, userAgent, headless = true }) {
  const puppeteer = getPuppeteer();
  log("[browser]", `Launch ${headless ? "headless" : "visible"} untuk Vercel challenge…`);

  const browser = await puppeteer.launch({
    headless,
    args: [
      "--no-sandbox",
      "--disable-setuid-sandbox",
      "--disable-blink-features=AutomationControlled",
      "--disable-infobars",
      "--disable-dev-shm-usage",
      "--window-size=1280,800"
    ],
    defaultViewport: null
  });

  try {
    const page = await browser.newPage();
    await page.setUserAgent(String(userAgent || DEFAULT_HEADERS.userAgent));
    await page.setExtraHTTPHeaders({ "accept-language": "en-US,en;q=0.9" });

    const targetUrl = new URL(PATHS.onboard, BASE_URL).toString();
    log("[browser]", `Navigate ${targetUrl}`);
    let resp;
    try {
      resp = await page.goto(targetUrl, { waitUntil: "domcontentloaded", timeout: 30000 });
    } catch (e) {
      log("[browser]", `Navigation issue: ${e.message}`);
    }
    const initialStatus = resp ? resp.status() : 0;
    log("[browser]", `Initial status: ${initialStatus}`);

    // Tunggu network settle dulu (challenge JS butuh waktu run)
    try {
      await page.waitForNetworkIdle({ idleTime: 1500, timeout: 20000 });
    } catch {
      /* ignore */
    }

    const maxAttempts = initialStatus === 429 ? 30 : 20;
    let cookiesMap = new Map();
    for (let i = 0; i < maxAttempts; i++) {
      cookiesMap = await readAllCookiesFromPage(page);
      const hasVc = Array.from(cookiesMap.keys()).some((n) => n.startsWith("_vc"));
      log("[browser]", `Attempt ${i + 1}: cookies=${cookiesMap.size} _vc=${hasVc}`);
      if (hasVc) break;

      if (i === 3 || i === 10) {
        try {
          log("[browser]", "Reload page…");
          await page.reload({ waitUntil: "domcontentloaded", timeout: 30000 });
          try {
            await page.waitForNetworkIdle({ idleTime: 1500, timeout: 15000 });
          } catch {
            /* ignore */
          }
        } catch (e) {
          log("[browser]", `Reload issue: ${e.message}`);
        }
      }
      await sleep(2000);
    }

    await sleep(500);
    cookiesMap = await readAllCookiesFromPage(page);
    log("[browser]", `Extracted ${cookiesMap.size} cookies total`);
    for (const [name, value] of cookiesMap) {
      const preview = value.length > 40 ? value.slice(0, 40) + "…" : value;
      log("[browser]", `  ${name}=${preview}`);
      jar.map.set(name, value);
    }
    const gotVc = Array.from(cookiesMap.keys()).some((n) => n.startsWith("_vc"));
    if (!gotVc) {
      throw new Error(
        "Browser challenge tidak menghasilkan cookie _vcrcs. Coba jalankan ulang dengan MERGE_BROWSER_VISIBLE=1 agar browser terlihat dan solve manual."
      );
    }
  } finally {
    try {
      await browser.close();
    } catch {
      /* ignore */
    }
  }
}

function splitCombinedSetCookie(headerValue) {
  const out = [];
  let cur = "";
  let inExpires = false;
  for (let i = 0; i < headerValue.length; i++) {
    if (headerValue.slice(i, i + 8).toLowerCase() === "expires=") inExpires = true;
    const ch = headerValue[i];
    if (ch === "," && !inExpires) {
      const t = cur.trim();
      if (t) out.push(t);
      cur = "";
      continue;
    }
    cur += ch;
    if (inExpires && ch === ";") inExpires = false;
  }
  const last = cur.trim();
  if (last) out.push(last);
  return out;
}

// ─────────────────────────────────────────────────────────────────────────────
// HTTP client
// ─────────────────────────────────────────────────────────────────────────────

class MergeClient {
  constructor({ accountName, email, deviceId, cookieJar }) {
    this.accountName = accountName;
    this.email = email;
    this.deviceId = deviceId || uuidv4();
    this.jar = cookieJar || new CookieJar();
    this.browser = null;
    this.page = null;
  }

  async openBrowser() {
    if (this.browser) return;
    const puppeteer = getPuppeteer();
    const headless = !process.env.MERGE_BROWSER_VISIBLE;
    log("[browser]", `Launch ${headless ? "headless" : "visible"}`);
    this.browser = await puppeteer.launch({
      headless: headless ? "new" : false,
      args: [
        "--no-sandbox",
        "--disable-setuid-sandbox",
        "--disable-blink-features=AutomationControlled",
        "--disable-infobars",
        "--disable-dev-shm-usage",
        "--window-size=1280,800"
      ],
      defaultViewport: null
    });
    this.page = await this.browser.newPage();
    await this.page.setUserAgent(DEFAULT_HEADERS.userAgent);
    await this.page.setExtraHTTPHeaders({
      "accept-language": DEFAULT_HEADERS.acceptLanguage
    });

    // Seed cookies dari jar (dari merge_tokens.json) sebelum navigate
    if (this.jar.map.size > 0) {
      const cookiesToSet = [];
      for (const [name, value] of this.jar.map) {
        cookiesToSet.push({
          name,
          value,
          domain: new URL(BASE_URL).hostname,
          path: "/",
          httpOnly: name === "_vcrcs" || name.startsWith("cantonbridge"),
          secure: true
        });
      }
      try {
        await this.page.setCookie(...cookiesToSet);
      } catch (e) {
        log("[browser]", `Seed cookie warning: ${e.message}`);
      }
    }

    log("[browser]", `Navigate ${BASE_URL}/onboard`);
    const resp = await this.page.goto(new URL(PATHS.onboard, BASE_URL).toString(), {
      waitUntil: "domcontentloaded",
      timeout: 30000
    });
    log("[browser]", `Page status: ${resp ? resp.status() : "?"}`);
    try {
      await this.page.waitForNetworkIdle({ idleTime: 1000, timeout: 10000 });
    } catch {
      /* ignore */
    }
    await this.syncCookiesFromBrowser();
  }

  async closeBrowser() {
    if (this.browser) {
      try {
        await this.syncCookiesFromBrowser();
      } catch {
        /* ignore */
      }
      try {
        await this.browser.close();
      } catch {
        /* ignore */
      }
      this.browser = null;
      this.page = null;
    }
  }

  async syncCookiesFromBrowser() {
    if (!this.page) return;
    try {
      const cdp = await this.page.target().createCDPSession();
      const { cookies } = await cdp.send("Network.getAllCookies");
      for (const c of cookies || []) {
        if (c?.name) this.jar.map.set(c.name, c.value);
      }
      await cdp.detach().catch(() => {});
    } catch {
      /* ignore */
    }
  }

  buildHeaders({ method, refererPath, hasBody, accept = "*/*" }) {
    const h = {
      accept,
      "accept-language": DEFAULT_HEADERS.acceptLanguage,
      referer: new URL(refererPath, BASE_URL).toString(),
      "user-agent": DEFAULT_HEADERS.userAgent,
      "sec-ch-ua": DEFAULT_HEADERS.secChUa,
      "sec-ch-ua-mobile": DEFAULT_HEADERS.secChUaMobile,
      "sec-ch-ua-platform": DEFAULT_HEADERS.secChUaPlatform,
      "sec-fetch-dest": DEFAULT_HEADERS.secFetchDest,
      "sec-fetch-mode": DEFAULT_HEADERS.secFetchMode,
      "sec-fetch-site": DEFAULT_HEADERS.secFetchSite,
      priority: DEFAULT_HEADERS.priority,
      "x-device-id": this.deviceId
    };
    const cookie = this.jar.header();
    if (cookie) h.cookie = cookie;
    if (method !== "GET") {
      h.origin = BASE_URL;
      if (hasBody) h["content-type"] = "application/json";
    }
    return h;
  }

  async request({
    method,
    endpointPath,
    refererPath,
    body,
    accept = "*/*",
    timeoutMs = REQUEST_TIMEOUT_MS,
    allowNon200 = false
  }) {
    if (!this.page) {
      await this.openBrowser();
    }

    const hasBody = body !== undefined && body !== null;

    // Run fetch from within the browser page (TLS/JA3 fingerprint = real Chrome)
    const evalResult = await this.page.evaluate(
      async ({ url, method, headers, bodyJson, timeoutMs }) => {
        const controller = new AbortController();
        const timer = setTimeout(() => controller.abort(), timeoutMs);
        try {
          const r = await fetch(url, {
            method,
            headers,
            body: bodyJson === null ? undefined : bodyJson,
            credentials: "include",
            signal: controller.signal
          });
          const text = await r.text();
          return { ok: r.ok, status: r.status, statusText: r.statusText, text };
        } catch (e) {
          return { ok: false, status: 0, error: String(e && e.message ? e.message : e) };
        } finally {
          clearTimeout(timer);
        }
      },
      {
        url: endpointPath, // relative path — fetch resolves against page origin
        method,
        headers: {
          accept,
          ...(hasBody ? { "content-type": "application/json" } : {}),
          "x-device-id": this.deviceId
        },
        bodyJson: hasBody ? JSON.stringify(body) : null,
        timeoutMs
      }
    );

    // Sync cookies back (in case API updated cantonbridge_session, etc.)
    await this.syncCookiesFromBrowser();

    if (evalResult.status === 0) {
      const err = new Error(
        `Network error on ${method} ${endpointPath}: ${evalResult.error || "unknown"}`
      );
      err.status = 0;
      throw err;
    }

    const text = evalResult.text || "";
    let parsed = null;
    if (text) {
      try {
        parsed = JSON.parse(text);
      } catch {
        /* not json */
      }
    }

    if (!evalResult.ok && !allowNon200) {
      const err = new Error(
        `HTTP ${evalResult.status} ${evalResult.statusText || ""} on ${method} ${endpointPath}: ${
          parsed ? JSON.stringify(parsed).slice(0, 300) : text.slice(0, 300)
        }`
      );
      err.status = evalResult.status;
      err.payload = parsed;
      err.rawBody = text;
      throw err;
    }

    return {
      status: evalResult.status,
      json: parsed,
      text
    };
  }

  // ────── Flow helpers ──────

  async touchOnboard() {
    // GET the onboard page to warm cookies (optional — /api/wallet/offers ok too)
    await this.request({
      method: "GET",
      endpointPath: PATHS.offers,
      refererPath: PATHS.onboard
    });
  }

  async sendOtp() {
    const r = await this.request({
      method: "POST",
      endpointPath: PATHS.sendOtp,
      refererPath: PATHS.onboard,
      body: { email: this.email }
    });
    const otpId = r.json?.data?.otpId;
    if (!otpId) throw new Error("send-otp tidak mengembalikan otpId");
    return otpId;
  }

  async verifyOtp(otpId, otpCode) {
    const r = await this.request({
      method: "POST",
      endpointPath: PATHS.verifyOtp,
      refererPath: PATHS.onboard,
      body: { email: this.email, otpId, otpCode }
    });
    return r.json?.data || {};
  }

  async syncAccount(refererPath) {
    const r = await this.request({
      method: "POST",
      endpointPath: PATHS.syncAccount,
      refererPath,
      body: {},
      allowNon200: true
    });
    return r.json?.data || {};
  }

  async getPending(refererPath) {
    const r = await this.request({
      method: "GET",
      endpointPath: PATHS.pending,
      refererPath
    });
    return r.json?.data || {};
  }

  async finalizeReturning() {
    // Body kosong (content-length 0) sesuai HAR
    const r = await this.request({
      method: "POST",
      endpointPath: PATHS.finalizeReturning,
      refererPath: PATHS.onboard
      // no body → hasBody false
    });
    return r.json?.data || {};
  }

  async getBalances() {
    const r = await this.request({
      method: "GET",
      endpointPath: PATHS.balances,
      refererPath: PATHS.send
    });
    return r.json?.data || {};
  }

  async ccConsolidate() {
    const idempotencyKey = uuidv4();
    const r = await this.request({
      method: "POST",
      endpointPath: PATHS.ccConsolidate,
      refererPath: PATHS.send,
      body: { idempotencyKey },
      timeoutMs: CC_CONSOLIDATE_TIMEOUT_MS
    });
    return r.json?.data || {};
  }

  hasSession() {
    return this.jar.has("cantonbridge_session");
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// OTP prompt (stdin)
// ─────────────────────────────────────────────────────────────────────────────

function prompt(question) {
  return new Promise((resolve) => {
    const rl = readline.createInterface({
      input: process.stdin,
      output: process.stdout
    });
    rl.question(question, (answer) => {
      rl.close();
      resolve(String(answer || "").trim());
    });
  });
}

async function promptOtp(email) {
  for (;;) {
    const code = await prompt(`  OTP code untuk ${email}: `);
    if (/^\d{4,8}$/.test(code)) return code;
    log("[warn]", "OTP harus numerik 4-8 digit. Ulangi.");
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tokens file (merge_tokens.json)
// ─────────────────────────────────────────────────────────────────────────────

async function loadMergeTokens() {
  try {
    const data = await readJson(TOKENS_PATH);
    if (!data || typeof data !== "object") throw new Error("invalid file");
    if (!data.accounts || typeof data.accounts !== "object") data.accounts = {};
    return data;
  } catch (e) {
    if (e.code === "ENOENT") {
      return { version: 1, updatedAt: new Date().toISOString(), accounts: {} };
    }
    throw e;
  }
}

async function saveMergeTokens(tokens) {
  tokens.updatedAt = new Date().toISOString();
  await writeJsonAtomic(TOKENS_PATH, tokens);
}

function snapshotClientToToken(client) {
  return {
    email: client.email,
    deviceId: client.deviceId,
    cookies: client.jar.toObject(),
    updatedAt: new Date().toISOString()
  };
}

function hydrateClientFromToken(token, accountName, email) {
  const jar = new CookieJar();
  if (token?.cookies) jar.loadFromObject(token.cookies);
  return new MergeClient({
    accountName,
    email,
    deviceId: token?.deviceId,
    cookieJar: jar
  });
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-account runner
// ─────────────────────────────────────────────────────────────────────────────

function printBalance(bal) {
  const canton = bal?.balances?.canton || {};
  const eth = bal?.balances?.ethereum || {};
  const holdings = Array.isArray(canton.tokenHoldings) ? canton.tokenHoldings : [];

  let ccAmount = null;
  let ccUtxoCount = 0;
  for (const h of holdings) {
    if (h?.metadata?.symbol === "CC" || h?.instrumentId === "Amulet") {
      if (ccAmount == null) ccAmount = h.amount;
      ccUtxoCount += 1;
    }
  }
  // Hitung juga otherHoldings sebagai info jumlah UTXO split lain
  const otherHoldings = Array.isArray(canton.otherHoldings) ? canton.otherHoldings : [];
  const otherCcCount = otherHoldings.filter(
    (h) => h?.metadata?.symbol === "CC" || h?.instrumentId === "Amulet"
  ).length;

  const fmt = (v) => (v == null || v === "" ? "-" : String(v));
  log(
    "[bal]",
    `CC=${fmt(ccAmount)} (utxo=${ccUtxoCount}, other=${otherCcCount}) | USDCx=${fmt(
      canton.usdcx
    )} | ETH=${fmt(eth.eth)} | USDC(base)=${fmt(eth.usdc)}`
  );
}

async function ensureLogin(client) {
  await client.openBrowser();

  if (client.hasSession()) {
    // Coba reuse session
    try {
      const bal = await client.getBalances();
      return { reused: true, balances: bal };
    } catch (e) {
      if (e.status === 401 || e.status === 403) {
        log("[info]", "Session tidak valid, login ulang…");
      } else {
        throw e;
      }
    }
  }

  log("[step]", "Warm cookies (GET /api/wallet/offers)");
  await client.touchOnboard();

  log("[step]", `Send OTP ke ${maskEmail(client.email)}`);
  const otpId = await client.sendOtp();

  const otpCode = await promptOtp(client.email);

  log("[step]", "Verify OTP");
  const verify = await client.verifyOtp(otpId, otpCode);
  log("[info]", `verify-otp nextStep=${verify?.nextStep || "unknown"}`);

  log("[step]", "Sync account (onboard)");
  await client.syncAccount(PATHS.onboard);

  const pending = await client.getPending(PATHS.onboard);
  log("[info]", `pending=${Boolean(pending.pending)} alreadyActive=${Boolean(pending.alreadyActive)}`);

  if (pending.pending) {
    if (pending.alreadyActive === true) {
      log("[step]", "Finalize returning account");
      const fin = await client.finalizeReturning();
      log("[info]", `Finalized as username=${fin?.username || pending.existingUsername || "unknown"}`);
    } else {
      throw new Error(
        "Akun masih pending & bukan returning. Skrip ini hanya handle returning flow."
      );
    }
  }

  log("[step]", "Sync account (bridge)");
  await client.syncAccount(PATHS.bridge);

  return { reused: false };
}

async function runAccount(account, tokens) {
  const { name, email } = account;
  if (!email) {
    log("[skip]", `Akun ${name} tidak punya email.`);
    return { name, success: false, reason: "no-email" };
  }

  log("[acct]", `=== ${name} (${maskEmail(email)}) ===`);

  const existingToken = tokens.accounts[name];
  const client = hydrateClientFromToken(existingToken, name, email);

  try {
    await ensureLogin(client);

    log("[step]", "GET balances (before)");
    const before = await client.getBalances();
    printBalance(before);

    log("[step]", "POST cc-consolidate (ini bisa ~15-60 detik)");
    const result = await client.ccConsolidate();
    log(
      "[ok]",
      `consolidate: rounds=${result?.roundsExecuted ?? "?"} remaining=${
        result?.remainingAmuletContracts ?? "?"
      } done=${result?.done ?? "?"}`
    );

    log("[step]", "GET balances (after)");
    const after = await client.getBalances();
    printBalance(after);

    tokens.accounts[name] = snapshotClientToToken(client);
    await saveMergeTokens(tokens);

    return { name, success: true, result };
  } catch (e) {
    log("[err]", `${name}: ${e.message || e}`);
    // Tetap simpan cookie progress (biar kalau cuma gagal di consolidate, session tetap kepakai next run)
    tokens.accounts[name] = snapshotClientToToken(client);
    try {
      await saveMergeTokens(tokens);
    } catch {
      /* ignore */
    }
    return { name, success: false, reason: e.message || String(e) };
  } finally {
    await client.closeBrowser();
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Main
// ─────────────────────────────────────────────────────────────────────────────

function printBanner() {
  console.log("");
  console.log("═══════════════════════════════════════════════════════");
  console.log("  CC Balance Merge / Consolidate Tool");
  console.log("  Deployment: chore-utxo-roots (bukan bridge.rootsfi)");
  console.log("═══════════════════════════════════════════════════════");
}

async function selectAccountsInteractive(allAccounts, tokens) {
  console.log("\nDaftar akun di accounts.json:\n");
  allAccounts.forEach((a, i) => {
    const has = tokens.accounts?.[a.name]?.cookies?.cantonbridge_session;
    const mark = has ? "✓" : " ";
    const idx = String(i + 1).padStart(2, " ");
    console.log(`  ${mark} [${idx}] ${a.name.padEnd(22)} ${maskEmail(a.email)}`);
  });
  console.log("\n  ✓ = punya session tersimpan (tidak perlu OTP)\n");

  console.log("Pilihan menu:");
  console.log("  1) Proses SEMUA akun");
  console.log("  2) Pilih akun tertentu (nomor, dipisah koma. contoh: 1,3,5)");
  console.log("  3) Pilih by nama (nama, dipisah koma. contoh: muhimuhi,riviga)");
  console.log("  4) Skip akun tertentu (nomor/nama, sisanya diproses)");
  console.log("  5) Keluar");
  console.log("");

  const choice = (await prompt("Pilih [1-5]: ")).trim();

  if (choice === "5" || choice === "") {
    return null;
  }

  if (choice === "1") {
    return allAccounts;
  }

  if (choice === "2") {
    const raw = (await prompt("Nomor akun (contoh 1,3,5): ")).trim();
    const indices = raw
      .split(/[,\s]+/)
      .map((s) => parseInt(s, 10))
      .filter((n) => Number.isInteger(n) && n >= 1 && n <= allAccounts.length);
    if (indices.length === 0) {
      console.log("Tidak ada nomor valid. Batal.");
      return [];
    }
    return indices.map((n) => allAccounts[n - 1]);
  }

  if (choice === "3") {
    const raw = (await prompt("Nama akun (contoh muhimuhi,riviga): ")).trim();
    const wanted = new Set(
      raw.split(/[,\s]+/).map((s) => s.trim()).filter(Boolean)
    );
    const picked = allAccounts.filter((a) => wanted.has(a.name));
    if (picked.length === 0) {
      console.log("Tidak ada nama yang cocok. Batal.");
      return [];
    }
    return picked;
  }

  if (choice === "4") {
    const raw = (await prompt("Skip akun (nomor atau nama, dipisah koma): ")).trim();
    const tokens2 = raw.split(/[,\s]+/).map((s) => s.trim()).filter(Boolean);
    const skipNames = new Set();
    for (const t of tokens2) {
      const n = parseInt(t, 10);
      if (Number.isInteger(n) && n >= 1 && n <= allAccounts.length) {
        skipNames.add(allAccounts[n - 1].name);
      } else {
        skipNames.add(t);
      }
    }
    return allAccounts.filter((a) => !skipNames.has(a.name));
  }

  console.log("Pilihan tidak dikenali. Batal.");
  return [];
}

async function main() {
  printBanner();
  log("[boot]", `Base URL: ${BASE_URL}`);
  log("[boot]", `Accounts: ${ACCOUNTS_PATH}`);
  log("[boot]", `Tokens:   ${TOKENS_PATH}`);

  if (!fs.existsSync(ACCOUNTS_PATH)) {
    throw new Error(`accounts.json tidak ditemukan di ${ACCOUNTS_PATH}`);
  }

  const accountsFile = await readJson(ACCOUNTS_PATH);
  const allAccounts = Array.isArray(accountsFile?.accounts) ? accountsFile.accounts : [];
  if (allAccounts.length === 0) {
    console.log("accounts.json kosong. Tidak ada akun untuk diproses.");
    return;
  }

  const tokens = await loadMergeTokens();

  const accounts = await selectAccountsInteractive(allAccounts, tokens);
  if (accounts === null) {
    console.log("Keluar.");
    return;
  }
  if (accounts.length === 0) {
    return;
  }

  console.log("\nAkun yang akan diproses:");
  accounts.forEach((a, i) => {
    console.log(`  ${i + 1}. ${a.name.padEnd(22)} ${maskEmail(a.email)}`);
  });
  const confirm = (await prompt(`\nLanjutkan proses ${accounts.length} akun? [Y/n]: `))
    .trim()
    .toLowerCase();
  if (confirm === "n" || confirm === "no") {
    console.log("Dibatalkan.");
    return;
  }

  log("[boot]", `Jumlah akun untuk diproses: ${accounts.length}`);

  const summary = [];
  for (let i = 0; i < accounts.length; i++) {
    const acc = accounts[i];
    const res = await runAccount(acc, tokens);
    summary.push(res);
    if (i < accounts.length - 1) {
      log("[wait]", `Delay ${DELAY_BETWEEN_ACCOUNTS_MS}ms sebelum akun berikutnya…`);
      await sleep(DELAY_BETWEEN_ACCOUNTS_MS);
    }
  }

  await saveMergeTokens(tokens);

  console.log("\n─────────── SUMMARY ───────────");
  for (const s of summary) {
    if (s.success) {
      console.log(
        `  ✓ ${s.name}  rounds=${s.result?.roundsExecuted ?? "?"} remaining=${
          s.result?.remainingAmuletContracts ?? "?"
        } done=${s.result?.done ?? "?"}`
      );
    } else {
      console.log(`  ✗ ${s.name}  ${s.reason}`);
    }
  }
  const ok = summary.filter((s) => s.success).length;
  console.log(`\nDone. ${ok}/${summary.length} akun sukses.`);
}

main().catch((e) => {
  console.error("[fatal]", e);
  process.exit(1);
});
