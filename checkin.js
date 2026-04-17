#!/usr/bin/env node
// ============================================================================
// RootsFi Daily Check-In Bot
// ============================================================================
// Standalone script that reuses tokens.json and accounts.json from the main bot.
// Usage: node checkin.js
//
// - Reads accounts.json + tokens.json from the same directory
// - Logs in via session reuse (no OTP) with Vercel browser challenge fallback
// - Calls POST /api/rewards/check-in for each account
// - Repeats every day at 00:00 UTC
// ============================================================================

"use strict";

const fs = require("fs/promises");
const path = require("path");
const crypto = require("crypto");

// ---------------------------------------------------------------------------
// Optional dependencies
// ---------------------------------------------------------------------------
let puppeteer = null;
try {
  puppeteer = require("puppeteer-extra");
  const StealthPlugin = require("puppeteer-extra-plugin-stealth");
  puppeteer.use(StealthPlugin());
} catch {
  // Will fallback to non-browser mode
}

let undiciModule = null;
try {
  undiciModule = require("undici");
} catch {
  // Connection pool reset will use soft fallback
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------
const ACCOUNTS_FILE = "accounts.json";
const TOKENS_FILE = "tokens.json";
const BASE_URL = "https://bridge.rootsfi.com";

const PATHS = {
  onboard: "/onboard",
  bridge: "/bridge",
  rewards: "/rewards",
  syncAccount: "/api/auth/sync-account",
  walletBalances: "/api/wallet/balances",
  rewardsCheckin: "/api/rewards/check-in",
  rewardsMain: "/api/rewards",
  rewardsLottery: "/api/rewards/lottery",
  rewardsSendLoyaltyDailyTaper: "/api/rewards/send-loyalty-daily-taper",
};

const HTTP_TIMEOUT_MS = 30000;
const HTTP_MAX_RETRIES = 2;
const HTTP_RETRY_BASE_DELAY_MS = 800;
const PACING_MIN_DELAY_MS = 450;
const PACING_JITTER_MS = 250;

const BROWSER_LAUNCH_TIMEOUT_MS = 120000;
const BROWSER_CHALLENGE_MAX_ATTEMPTS = 20;
const BROWSER_CHALLENGE_MAX_ATTEMPTS_429 = 20;
const BROWSER_CHALLENGE_RETRY_DELAY_MS = 15000;
const BROWSER_CHALLENGE_RETRY_ATTEMPTS_429 = 10;

const CHECKIN_RETRY_ATTEMPTS = 3;
const CHECKIN_RETRY_BASE_DELAY_S = 30;
const ACCOUNT_DELAY_MS = 5000;

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------
let connectionPoolResetInFlight = null;
let tokensSaveQueue = Promise.resolve();

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const isObject = (v) => v !== null && typeof v === "object" && !Array.isArray(v);
const clamp = (v, fallback) => {
  const n = Number(v);
  return Number.isFinite(n) && n >= 0 ? Math.floor(n) : Math.max(0, Math.floor(Number(fallback) || 0));
};
const randInt = (min, max) => Math.floor(Math.random() * (max - min + 1)) + min;

function ts() {
  return new Date().toLocaleTimeString("en-GB", { hour12: false, timeZone: "Asia/Jakarta" });
}

function log(tag, msg) {
  console.log(`[${ts()}] ${tag}  ${msg}`);
}

// ---------------------------------------------------------------------------
// Connection pool reset (undici-aware)
// ---------------------------------------------------------------------------
async function resetConnectionPool() {
  if (connectionPoolResetInFlight) return connectionPoolResetInFlight;
  connectionPoolResetInFlight = (async () => {
    try {
      if (undiciModule && typeof undiciModule.Agent === "function") {
        const agent = new undiciModule.Agent({
          keepAliveTimeout: 10000,
          keepAliveMaxTimeout: 30000,
          connections: 50,
          pipelining: 1,
        });
        undiciModule.setGlobalDispatcher(agent);
        log("POOL", "Connection pool reset via undici");
        return true;
      }
      const sym = Symbol.for("undici.globalDispatcher.1");
      if (globalThis[sym]) {
        try { await globalThis[sym].close(); } catch {}
        log("POOL", "Connection pool soft reset");
        return true;
      }
      return false;
    } catch { return false; }
  })();
  try { return await connectionPoolResetInFlight; }
  finally { connectionPoolResetInFlight = null; }
}

// ---------------------------------------------------------------------------
// File I/O
// ---------------------------------------------------------------------------
async function readJson(filePath, label) {
  let text;
  try { text = await fs.readFile(filePath, "utf8"); }
  catch (e) {
    if (e && e.code === "ENOENT") throw new Error(`${label} file not found: ${filePath}`);
    throw e;
  }
  try { return JSON.parse(text); }
  catch (e) { throw new Error(`Invalid JSON in ${label}: ${e.message}`); }
}

async function readOptionalJson(filePath, label) {
  try { return JSON.parse(await fs.readFile(filePath, "utf8")); }
  catch (e) {
    if (e && e.code === "ENOENT") return null;
    if (e instanceof SyntaxError) throw new Error(`Invalid JSON in ${label}: ${e.message}`);
    throw e;
  }
}

async function saveTokens(tokensPath, state) {
  const payload = { ...state, version: 1, updatedAt: new Date().toISOString() };
  await fs.writeFile(tokensPath, JSON.stringify(payload, null, 2), "utf8");
}

async function saveTokensSerial(tokensPath, state) {
  tokensSaveQueue = tokensSaveQueue.then(() => saveTokens(tokensPath, state));
  return tokensSaveQueue;
}

// ---------------------------------------------------------------------------
// Token profile helpers (mirrors index.js)
// ---------------------------------------------------------------------------
function generateBrowserHeaders(deviceId) {
  // Diverse fingerprint generator (mirrors index.js)
  const hashBytes = crypto.createHash("sha256").update(String(deviceId || "")).digest();
  const seed = (idx) => hashBytes[idx % hashBytes.length];

  const platforms = [
    { platform: "macOS", uaPlatform: "(Macintosh; Intel Mac OS X 10_15_7)", secChUaPlatform: '"macOS"', secChUaMobile: "?0" },
    { platform: "Windows", uaPlatform: "(Windows NT 10.0; Win64; x64)", secChUaPlatform: '"Windows"', secChUaMobile: "?0" },
    { platform: "Linux", uaPlatform: "(X11; Linux x86_64)", secChUaPlatform: '"Linux"', secChUaMobile: "?0" },
  ];
  const chosenPlatform = platforms[seed(0) % platforms.length];

  const chromeVersions = [
    { major: 131, build: "0.6778.140" }, { major: 132, build: "0.6834.110" },
    { major: 133, build: "0.6943.127" }, { major: 134, build: "0.6998.89" },
    { major: 135, build: "0.7049.85" },  { major: 136, build: "0.7103.114" },
    { major: 137, build: "0.7151.70" },  { major: 138, build: "0.7204.93" },
    { major: 139, build: "0.7258.68" },  { major: 140, build: "0.7310.105" },
    { major: 141, build: "0.7365.81" },  { major: 142, build: "0.7420.97" },
    { major: 143, build: "0.7473.63" },  { major: 144, build: "0.7528.109" },
    { major: 145, build: "0.7582.72" },  { major: 146, build: "0.7636.88" },
  ];
  const chosenVersion = chromeVersions[seed(1) % chromeVersions.length];
  const chromeFull = `${chosenVersion.major}.${chosenVersion.build}`;

  const languages = [
    "en-US,en;q=0.9", "en-US,en;q=0.9,id;q=0.8", "en-GB,en;q=0.9,en-US;q=0.8",
    "en-US,en;q=0.9,de;q=0.7", "en,en-US;q=0.9", "en-US,en;q=0.9,fr;q=0.7",
    "en-US,en;q=0.9,ja;q=0.8", "en-US,en;q=0.9,es;q=0.8",
  ];
  const chosenLang = languages[seed(2) % languages.length];

  const brandVersions = [
    { brand: "Not-A.Brand", version: "24" }, { brand: "Not/A)Brand", version: "8" },
    { brand: "Not_A Brand", version: "99" },
  ];
  const chosenBrand = brandVersions[seed(3) % brandVersions.length];
  const secChUa = `"Chromium";v="${chosenVersion.major}", "${chosenBrand.brand}";v="${chosenBrand.version}", "Google Chrome";v="${chosenVersion.major}"`;

  const userAgent = `Mozilla/5.0 ${chosenPlatform.uaPlatform} AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${chromeFull} Safari/537.36`;

  return {
    userAgent,
    acceptLanguage: chosenLang,
    sendBrowserClientHints: true,
    secChUa,
    secChUaMobile: chosenPlatform.secChUaMobile,
    secChUaPlatform: chosenPlatform.secChUaPlatform,
    secFetchDest: "empty",
    secFetchMode: "cors",
    secFetchSite: "same-origin",
    priority: "u=1, i",
    extra: { "x-device-id": deviceId },
  };
}

function normalizeTokenProfile(raw) {
  // Use data from tokens.json as-is — do NOT regenerate headers/fingerprints.
  // All device/security data is generated and managed by index.js.
  const input = isObject(raw) ? raw : {};
  const deviceId = String(input.deviceId || "").trim();
  const hi = isObject(input.headers) ? input.headers : {};
  const si = isObject(input.security) ? input.security : {};
  const now = new Date().toISOString();

  // If no headers exist at all (fresh account), generate fallback
  const hasExistingHeaders = Boolean(hi.userAgent);
  const headers = hasExistingHeaders
    ? { ...hi, extra: { ...(isObject(hi.extra) ? hi.extra : {}), "x-device-id": deviceId } }
    : { ...generateBrowserHeaders(deviceId || crypto.randomUUID()), extra: { "x-device-id": deviceId || crypto.randomUUID() } };

  return {
    cookie: String(input.cookie || "").trim(),
    deviceId: deviceId || (headers.extra && headers.extra["x-device-id"]) || crypto.randomUUID(),
    headers,
    security: {
      strategy: "browser-challenge-cookie-reuse",
      antiBotNonce: String(si.antiBotNonce || ""),
      createdAt: String(si.createdAt || now),
      updatedAt: String(si.updatedAt || now),
      lastVercelRefreshAt: String(si.lastVercelRefreshAt || "").trim(),
      hasSecurityCookie: Boolean(si.hasSecurityCookie),
      hasSessionCookie: Boolean(si.hasSessionCookie),
      checkpointRefreshCount: clamp(si.checkpointRefreshCount, 0),
    },
  };
}

function normalizeTokens(raw, accounts) {
  const r = isObject(raw) ? raw : {};
  const ra = isObject(r.accounts) ? r.accounts : {};
  const map = {};
  for (const a of accounts) map[a.name] = normalizeTokenProfile(ra[a.name]);
  for (const [k, v] of Object.entries(ra)) {
    if (!Object.prototype.hasOwnProperty.call(map, k)) map[k] = normalizeTokenProfile(v);
  }
  return { version: 1, updatedAt: String(r.updatedAt || new Date().toISOString()), accounts: map };
}

function applyTokenProfileToConfig(config, profile) {
  const th = isObject(profile.headers) ? profile.headers : {};
  config.headers = { ...config.headers, ...th, extra: { ...(isObject(th.extra) ? th.extra : {}), "x-device-id": profile.deviceId }, cookie: String(profile.cookie || "").trim() };
}

function applyClientStateToTokenProfile(profile, client, checkpointCount, lastRefresh) {
  const next = normalizeTokenProfile(profile);
  const now = new Date().toISOString();
  const cookie = client.getCookieHeader();
  if (cookie) next.cookie = cookie;
  next.headers.extra = { ...(isObject(next.headers.extra) ? next.headers.extra : {}), "x-device-id": next.deviceId };
  next.security = {
    ...next.security,
    updatedAt: now,
    lastVercelRefreshAt: String(lastRefresh || next.security.lastVercelRefreshAt || "").trim(),
    hasSecurityCookie: client.hasSecurityCookie(),
    hasSessionCookie: client.hasAccountSessionCookie(),
    checkpointRefreshCount: clamp(next.security.checkpointRefreshCount, 0) + clamp(checkpointCount, 0),
  };
  return next;
}

// ---------------------------------------------------------------------------
// Accounts loader
// ---------------------------------------------------------------------------
function normalizeAccounts(raw) {
  if (!isObject(raw) || !Array.isArray(raw.accounts) || raw.accounts.length === 0) {
    throw new Error("accounts.json must contain a non-empty accounts array");
  }
  const accounts = raw.accounts.map((e, i) => {
    if (!isObject(e)) throw new Error(`accounts[${i}] must be an object`);
    const name = String(e.name || "").trim();
    const email = String(e.email || "").trim();
    if (!name) throw new Error(`accounts[${i}].name is required`);
    if (!email || !email.includes("@")) throw new Error(`accounts[${i}].email is invalid`);
    return { name, email };
  });
  return accounts;
}

// ---------------------------------------------------------------------------
// API Client (minimal, mirrors RootsFiApiClient from index.js)
// ---------------------------------------------------------------------------
class ApiClient {
  constructor(headers) {
    this.headers = headers;
    this.cookieJar = new Map();
    if (headers.cookie) this.parseCookieString(headers.cookie);
  }

  parseCookieString(str) {
    if (!str) return;
    for (const pair of str.split(";")) {
      const eq = pair.indexOf("=");
      if (eq > 0) {
        const name = pair.slice(0, eq).trim();
        const value = pair.slice(eq + 1).trim();
        if (name) this.cookieJar.set(name, value);
      }
    }
  }

  parseSetCookieHeaders(headers) {
    const values = typeof headers.getSetCookie === "function" ? headers.getSetCookie() : [];
    const list = values.length > 0 ? values : (headers.get("set-cookie") || "").split(/,(?=[^ ])/);
    for (const sc of list) {
      const parts = sc.split(";")[0];
      const eq = parts.indexOf("=");
      if (eq > 0) {
        const name = parts.slice(0, eq).trim();
        const value = parts.slice(eq + 1).trim();
        if (name) this.cookieJar.set(name, value);
      }
    }
  }

  mergeCookies(map) { for (const [k, v] of map) this.cookieJar.set(k, v); }
  hasSecurityCookie() { return this.cookieJar.has("_vcrcs"); }
  hasAccountSessionCookie() { return this.cookieJar.has("cantonbridge_session"); }
  hasValidSession() { return this.hasSecurityCookie() || this.hasAccountSessionCookie(); }

  getCookieHeader() {
    if (this.cookieJar.size === 0) return "";
    return Array.from(this.cookieJar.entries()).map(([k, v]) => `${k}=${v}`).join("; ");
  }

  buildUrl(ep) { return new URL(ep, BASE_URL).toString(); }

  buildHeaders(method, refererPath, hasBody) {
    const h = {
      accept: "*/*",
      "accept-language": this.headers.acceptLanguage,
      referer: this.buildUrl(refererPath),
      "user-agent": this.headers.userAgent,
    };
    if (this.headers.sendBrowserClientHints) {
      h["sec-ch-ua"] = this.headers.secChUa;
      h["sec-ch-ua-mobile"] = this.headers.secChUaMobile;
      h["sec-ch-ua-platform"] = this.headers.secChUaPlatform;
      h["sec-fetch-dest"] = this.headers.secFetchDest;
      h["sec-fetch-mode"] = this.headers.secFetchMode;
      h["sec-fetch-site"] = this.headers.secFetchSite;
      h.priority = this.headers.priority;
    }
    const cookie = this.getCookieHeader();
    if (cookie) h.cookie = cookie;
    if (isObject(this.headers.extra)) {
      for (const [k, v] of Object.entries(this.headers.extra)) h[k] = v;
    }
    if (method !== "GET") {
      h.origin = BASE_URL;
      if (hasBody) h["content-type"] = "application/json";
    }
    return h;
  }

  async requestJson(method, endpoint, opts = {}) {
    const referer = opts.refererPath || PATHS.onboard;
    const body = opts.body;
    const timeoutMs = opts.timeoutMs || HTTP_TIMEOUT_MS;
    const maxAttempts = 1 + HTTP_MAX_RETRIES;
    let lastError = null;

    for (let attempt = 1; ; attempt++) {
      const ac = new AbortController();
      const tid = setTimeout(() => ac.abort(new Error("Request timed out")), timeoutMs);
      try {
        const resp = await fetch(this.buildUrl(endpoint), {
          method,
          headers: this.buildHeaders(method, referer, body !== undefined),
          body: body === undefined ? undefined : JSON.stringify(body),
          signal: ac.signal,
        });
        clearTimeout(tid);
        this.parseSetCookieHeaders(resp.headers);

        const vercelMitigated = String(resp.headers.get("x-vercel-mitigated") || "").toLowerCase();
        const text = await resp.text();
        let payload = {};
        if (text) {
          try { payload = JSON.parse(text); }
          catch {
            if (text.trim().startsWith("<")) {
              if (vercelMitigated === "challenge") {
                throw Object.assign(new Error(`Vercel Security Checkpoint at ${endpoint} (HTTP ${resp.status})`), { code: "VERCEL_CHECKPOINT" });
              }
              throw new Error(`HTML response from ${endpoint} (HTTP ${resp.status})`);
            }
            throw new Error(`Non-JSON from ${endpoint}: ${text.slice(0, 100)}`);
          }
        }
        if (!resp.ok) {
          const msg = isObject(payload) && payload.error && payload.error.message ? payload.error.message : `HTTP ${resp.status}`;
          throw Object.assign(new Error(`${endpoint}: ${msg}`), { status: resp.status });
        }
        await sleep(PACING_MIN_DELAY_MS + randInt(0, PACING_JITTER_MS));
        return payload;
      } catch (e) {
        clearTimeout(tid);
        lastError = e;
        const msg = String(e && e.message || "").toLowerCase();
        const isTimeout = msg.includes("timed out") || msg.includes("timeout") || msg.includes("aborted");
        const isFetchFailed = msg.includes("fetch failed") || msg.includes("econnreset") || msg.includes("socket hang up");
        const status = Number(e && e.status);
        const isRetryable = isTimeout || isFetchFailed || status === 429 || (status >= 500 && status < 600);

        if (attempt < maxAttempts && isRetryable) {
          const backoff = HTTP_RETRY_BASE_DELAY_MS * Math.pow(2, attempt - 1) + randInt(0, 400);
          await sleep(backoff);
          continue;
        }
        throw e;
      }
    }
  }

  async syncAccount() {
    return this.requestJson("POST", PATHS.syncAccount, { refererPath: PATHS.bridge });
  }

  async checkin() {
    // HAR shows POST /api/rewards/check-in with content-length: 0, no body
    const referer = PATHS.rewards;
    const ac = new AbortController();
    const tid = setTimeout(() => ac.abort(new Error("Request timed out")), HTTP_TIMEOUT_MS);
    try {
      const resp = await fetch(this.buildUrl(PATHS.rewardsCheckin), {
        method: "POST",
        headers: {
          ...this.buildHeaders("POST", referer, false),
          "content-length": "0",
        },
        body: null,
        signal: ac.signal,
      });
      clearTimeout(tid);
      this.parseSetCookieHeaders(resp.headers);
      const text = await resp.text();
      let payload = {};
      if (text) { try { payload = JSON.parse(text); } catch {} }
      if (!resp.ok) {
        const msg = isObject(payload) && payload.error && payload.error.message ? payload.error.message : `HTTP ${resp.status}`;
        throw Object.assign(new Error(`check-in: ${msg}`), { status: resp.status });
      }
      await sleep(PACING_MIN_DELAY_MS + randInt(0, PACING_JITTER_MS));
      return payload;
    } catch (e) {
      clearTimeout(tid);
      throw e;
    }
  }

  async getRewards() {
    return this.requestJson("GET", PATHS.rewardsMain, { refererPath: PATHS.rewards, timeoutMs: 15000 });
  }

  async getRewardsLottery() {
    return this.requestJson("GET", PATHS.rewardsLottery, { refererPath: PATHS.rewards, timeoutMs: 15000 });
  }

  async getRewardsDailyTaper() {
    return this.requestJson("GET", PATHS.rewardsSendLoyaltyDailyTaper, { refererPath: PATHS.rewards, timeoutMs: 15000 });
  }

  async preflightOnboard() {
    const ac = new AbortController();
    const tid = setTimeout(() => ac.abort(new Error("Request timed out")), HTTP_TIMEOUT_MS);
    try {
      const resp = await fetch(this.buildUrl(PATHS.onboard), {
        method: "GET",
        headers: {
          accept: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
          "accept-language": this.headers.acceptLanguage,
          "user-agent": this.headers.userAgent,
          ...(this.getCookieHeader() ? { cookie: this.getCookieHeader() } : {}),
        },
        signal: ac.signal,
      });
      this.parseSetCookieHeaders(resp.headers);
      if (resp.body && typeof resp.body.cancel === "function") {
        try { await resp.body.cancel(); } catch {}
      }
      if (!resp.ok) throw Object.assign(new Error(`Preflight HTTP ${resp.status}`), { status: resp.status });
    } finally { clearTimeout(tid); }
  }
}

// ---------------------------------------------------------------------------
// Browser challenge solver (mirrors index.js)
// ---------------------------------------------------------------------------
async function solveBrowserChallenge(userAgent) {
  if (!puppeteer) throw new Error("Puppeteer not available");

  let browser = null;
  try {
    log("BROWSER", "Launching headless browser for Vercel challenge...");
    browser = await puppeteer.launch({
      headless: true,
      timeout: BROWSER_LAUNCH_TIMEOUT_MS,
      args: ["--no-sandbox", "--disable-setuid-sandbox", "--disable-blink-features=AutomationControlled",
             "--disable-infobars", "--disable-dev-shm-usage", "--window-size=1280,800"],
      defaultViewport: null,
    });

    const page = await browser.newPage();
    await page.setUserAgent(userAgent);
    await page.setExtraHTTPHeaders({ "Accept-Language": "en-US,en;q=0.9" });

    const targetUrl = new URL(PATHS.onboard, BASE_URL).toString();
    log("BROWSER", `Navigating to ${targetUrl}`);

    let response;
    try { response = await page.goto(targetUrl, { waitUntil: "domcontentloaded", timeout: 30000 }); }
    catch (e) { log("BROWSER", `Navigation issue: ${e.message}`); }

    const status = response ? response.status() : 0;
    const maxAttempts = status === 429 ? BROWSER_CHALLENGE_MAX_ATTEMPTS_429 : BROWSER_CHALLENGE_MAX_ATTEMPTS;
    if (status === 429) log("BROWSER", "429 detected, extended challenge mode");

    for (let i = 0; i < maxAttempts; i++) {
      await sleep(2000);
      const cookies = await page.cookies();
      if (cookies.some((c) => c.name.startsWith("_vc"))) { log("BROWSER", "Vercel cookies obtained!"); break; }
      if (page.url().includes("/onboard") && cookies.length > 0) { log("BROWSER", "Page loaded with cookies"); break; }
    }

    await sleep(1000);
    let cookies = await page.cookies();

    if (cookies.length === 0 && status === 429) {
      log("BROWSER", `No cookies on 429, cooling ${Math.round(BROWSER_CHALLENGE_RETRY_DELAY_MS / 1000)}s...`);
      await sleep(BROWSER_CHALLENGE_RETRY_DELAY_MS);
      try { await page.reload({ waitUntil: "domcontentloaded", timeout: 30000 }); } catch {}
      for (let i = 0; i < BROWSER_CHALLENGE_RETRY_ATTEMPTS_429; i++) {
        await sleep(2000);
        cookies = await page.cookies();
        if (cookies.some((c) => String(c.name || "").startsWith("_vc")) || cookies.length > 0) break;
      }
    }

    const cookieMap = new Map();
    for (const c of cookies) cookieMap.set(c.name, c.value);
    log("BROWSER", `Extracted ${cookieMap.size} cookies`);
    return cookieMap;
  } finally {
    if (browser) { try { await browser.close(); } catch {} }
  }
}

// ---------------------------------------------------------------------------
// Session reuse + check-in logic for one account
// ---------------------------------------------------------------------------
async function checkinAccount(account, profile, tag) {
  const config = {
    baseUrl: BASE_URL,
    paths: PATHS,
    headers: { ...generateBrowserHeaders(profile.deviceId) },
  };
  applyTokenProfileToConfig(config, profile);

  const client = new ApiClient(config.headers);
  let checkpointRefreshCount = 0;
  let lastVercelRefreshAt = profile.security.lastVercelRefreshAt || "";

  // --- Ensure we have security cookies ---
  if (!client.hasValidSession()) {
    log(tag, "No session cookies, launching browser challenge...");
    try {
      const cookies = await solveBrowserChallenge(config.headers.userAgent);
      if (cookies && cookies.size > 0) {
        client.mergeCookies(cookies);
        checkpointRefreshCount++;
        lastVercelRefreshAt = new Date().toISOString();
        log(tag, "Browser cookies merged");
      } else {
        return { ok: false, reason: "browser-no-cookies" };
      }
    } catch (e) {
      log(tag, `Browser challenge failed: ${e.message}`);
      return { ok: false, reason: "browser-failed" };
    }
  }

  // --- Session reuse: sync-account validates session ---
  const maxSessionAttempts = 3;
  let sessionOk = false;

  for (let attempt = 1; attempt <= maxSessionAttempts; attempt++) {
    try {
      log(tag, `Session reuse attempt ${attempt}/${maxSessionAttempts}...`);
      await client.syncAccount();
      sessionOk = true;
      log(tag, "Session valid!");
      break;
    } catch (e) {
      const msg = String(e && e.message || "").toLowerCase();
      const status = Number(e && e.status);
      const isFetchFailed = msg.includes("fetch failed") || msg.includes("econnreset");
      const isVercelBlock = msg.includes("vercel security checkpoint") || (e && e.code === "VERCEL_CHECKPOINT");

      if (isVercelBlock && puppeteer) {
        log(tag, "Vercel checkpoint detected, refreshing browser cookies...");
        try {
          await resetConnectionPool();
          const cookies = await solveBrowserChallenge(config.headers.userAgent);
          if (cookies && cookies.size > 0) {
            client.mergeCookies(cookies);
            checkpointRefreshCount++;
            lastVercelRefreshAt = new Date().toISOString();
            // Validate with preflight
            try { await client.preflightOnboard(); } catch {}
          }
        } catch (be) {
          log(tag, `Browser refresh failed: ${be.message}`);
        }
        await sleep(3000);
        continue;
      }

      if (isFetchFailed || status === 429) {
        log(tag, `Transient error (${isFetchFailed ? "fetch failed" : `HTTP ${status}`}), resetting pool...`);
        await resetConnectionPool();
        const delay = CHECKIN_RETRY_BASE_DELAY_S + randInt(5, 15);
        log(tag, `Waiting ${delay}s before retry...`);
        await sleep(delay * 1000);
        continue;
      }

      if (status === 401 || status === 403) {
        log(tag, "Session invalid (401/403). Cannot recover without OTP.");
        return { ok: false, reason: "invalid-session" };
      }

      log(tag, `Session error: ${e.message}`);
      if (attempt < maxSessionAttempts) {
        await sleep(10000);
        continue;
      }
    }
  }

  if (!sessionOk) {
    return { ok: false, reason: "session-failed" };
  }

  // --- Step 0: GET /api/rewards/send-loyalty-daily-taper (pre-check, matches browser flow) ---
  try {
    const taperResp = await client.getRewardsDailyTaper();
    const taperData = isObject(taperResp && taperResp.data) ? taperResp.data : {};
    log(tag, `Daily taper: accrualsToday=${taperData.accrualsToday || 0}, rewardsPaused=${taperData.rewardsPaused || false}`);
  } catch (e) {
    log(tag, `Daily taper check failed: ${e.message} (non-critical)`);
  }

  // --- Step 1: GET /api/rewards to check current status ---
  let alreadyCheckedIn = false;
  let rewardInfo = {};
  try {
    const rewardsResp = await client.getRewards();
    const data = isObject(rewardsResp && rewardsResp.data) ? rewardsResp.data : {};
    const tp = isObject(data.tierProgress) ? data.tierProgress : {};
    const today = isObject(tp.today) ? tp.today : {};
    const wq = isObject(tp.weeklyQuality) ? tp.weeklyQuality : {};
    alreadyCheckedIn = Boolean(today.checkedIn);
    rewardInfo = {
      tier: tp.currentTierDisplayName || "-",
      points: today.totalPoints || 0,
      streak: today.streakDays || 0,
      score: wq.score !== undefined ? `${wq.score}/100 ${wq.bandLabel || ""}`.trim() : "-",
      earnedThisWeek: extractRewardLabel(rewardsResp),
    };
    if (alreadyCheckedIn) {
      log(tag, `Already checked in today (streak: ${rewardInfo.streak}, points: ${rewardInfo.points}, score: ${rewardInfo.score})`);
    }
  } catch (e) {
    log(tag, `Rewards status check failed: ${e.message} (will try check-in anyway)`);
  }

  // --- Step 2: POST /api/rewards/check-in ---
  let checkinResult = null;
  if (!alreadyCheckedIn) {
    try {
      const resp = await client.checkin();
      const data = isObject(resp && resp.data) ? resp.data : {};
      checkinResult = {
        checkedIn: Boolean(data.checkedIn),
        alreadyCheckedIn: Boolean(data.alreadyCheckedIn),
        streakDays: data.streakDays || 0,
        pointsAwarded: data.pointsAwardedToday || 0,
      };
      log(tag, `Check-in response: checkedIn=${checkinResult.checkedIn}, streak=${checkinResult.streakDays}, points=${checkinResult.pointsAwarded}`);
    } catch (e) {
      log(tag, `Check-in POST failed: ${e.message}`);
    }
  } else {
    checkinResult = { checkedIn: true, alreadyCheckedIn: true, streakDays: rewardInfo.streak, pointsAwarded: 0 };
  }

  // --- Step 3: GET /api/rewards again to refresh status ---
  if (checkinResult && checkinResult.checkedIn) {
    try {
      const refreshResp = await client.getRewards();
      const data = isObject(refreshResp && refreshResp.data) ? refreshResp.data : {};
      const tp = isObject(data.tierProgress) ? data.tierProgress : {};
      const today = isObject(tp.today) ? tp.today : {};
      const wq = isObject(tp.weeklyQuality) ? tp.weeklyQuality : {};
      rewardInfo = {
        tier: tp.currentTierDisplayName || rewardInfo.tier || "-",
        points: today.totalPoints || rewardInfo.points || 0,
        streak: today.streakDays || checkinResult.streakDays || 0,
        score: wq.score !== undefined ? `${wq.score}/100 ${wq.bandLabel || ""}`.trim() : (rewardInfo.score || "-"),
        earnedThisWeek: extractRewardLabel(refreshResp),
      };
    } catch (e) {
      // Non-critical, we already have checkin result
    }
  }

  const checkinOk = checkinResult !== null && checkinResult.checkedIn;

  // Save updated token state
  const updatedProfile = applyClientStateToTokenProfile(profile, client, checkpointRefreshCount, lastVercelRefreshAt);

  return {
    ok: checkinOk,
    reason: checkinOk ? (checkinResult.alreadyCheckedIn ? "already-checked-in" : "ok") : "checkin-failed",
    streak: checkinResult ? checkinResult.streakDays : 0,
    points: checkinResult ? checkinResult.pointsAwarded : 0,
    tier: rewardInfo.tier || "-",
    score: rewardInfo.score || "-",
    reward: rewardInfo.earnedThisWeek || "-",
    updatedProfile,
  };
}

function extractRewardLabel(payload) {
  const data = isObject(payload && payload.data) ? payload.data : {};
  const candidates = [
    data.earnedThisWeekCc, data.thisWeekCc, data.rewardThisWeekCc,
  ];
  if (isObject(data.tierProgress)) {
    candidates.push(data.tierProgress.earnedThisWeekCc, data.tierProgress.thisWeekRewardCc,
                     data.tierProgress.rewardThisWeekCc, data.tierProgress.thisWeekCc);
  }
  candidates.push(data.thisWeekRewardCc, data.thisWeekReward, data.weeklyRewardCc, data.weeklyReward);
  if (isObject(data.thisWeek)) candidates.push(data.thisWeek.cc, data.thisWeek.amount, data.thisWeek.reward);
  if (isObject(data.weekly)) candidates.push(data.weekly.cc, data.weekly.amount, data.weekly.reward);
  candidates.push(data.accrualsWeek, data.accrualsThisWeek, data.accrualsToday);

  for (const v of candidates) {
    if (v === null || v === undefined || v === "" || v === false) continue;
    const s = String(v).trim();
    if (!s || s === "0" || s === "null" || s === "undefined") continue;
    return /^cc/i.test(s) ? s.toUpperCase() : `CC${s}`;
  }
  return "-";
}

// ---------------------------------------------------------------------------
// Dashboard (simple terminal UI)
// ---------------------------------------------------------------------------
function renderDashboard(accounts, results, state) {
  const now = new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" }) + " WIB";

  const lines = [];
  lines.push("");
  lines.push("=".repeat(80));
  lines.push(`  RootsFi Daily Check-In  |  ${now}  |  ${accounts.length} accounts`);
  lines.push(`  State: ${state}`);
  lines.push("=".repeat(80));
  lines.push("");
  lines.push(
    "  " +
    pad("Account", 16) +
    pad("Status", 12) +
    pad("Streak", 10) +
    pad("Points", 10) +
    pad("Score", 18) +
    pad("Tier", 12) +
    "Detail"
  );
  lines.push("  " + "-".repeat(80));

  for (const acc of accounts) {
    const r = results[acc.name];
    let status = "PENDING";
    let streak = "-";
    let points = "-";
    let tier = "-";
    let detail = "waiting...";

    let score = "-";

    if (r) {
      if (r.ok) {
        status = r.reason === "already-checked-in" ? "DONE" : "OK";
        streak = String(r.streak || 0) + "d";
        points = String(r.points || 0);
        score = r.score || "-";
        tier = r.tier || "-";
        detail = r.reason === "already-checked-in" ? "Already checked in" : "Check-in success!";
      } else {
        status = "FAILED";
        detail = r.reason || "unknown";
      }
    }

    lines.push(
      "  " +
      pad(acc.name, 16) +
      pad(status, 12) +
      pad(streak, 10) +
      pad(points, 10) +
      pad(score, 18) +
      pad(tier, 12) +
      detail
    );
  }

  lines.push("");
  lines.push("=".repeat(80));
  lines.push("");

  // Clear screen and redraw
  process.stdout.write("\x1B[2J\x1B[H");
  console.log(lines.join("\n"));
}

function pad(str, len) {
  const s = String(str || "");
  return s.length >= len ? s.slice(0, len) : s + " ".repeat(len - s.length);
}

// ---------------------------------------------------------------------------
// Run one full check-in cycle for all accounts
// ---------------------------------------------------------------------------
async function runCheckinCycle() {
  const cwd = process.cwd();
  const accountsPath = path.resolve(cwd, ACCOUNTS_FILE);
  const tokensPath = path.resolve(cwd, TOKENS_FILE);

  // Load files
  const rawAccounts = await readJson(accountsPath, "accounts");
  const rawTokens = await readOptionalJson(tokensPath, "tokens");
  const accounts = normalizeAccounts(rawAccounts);
  const tokens = normalizeTokens(rawTokens, accounts);

  const results = {};
  renderDashboard(accounts, results, "RUNNING");

  for (let i = 0; i < accounts.length; i++) {
    const acc = accounts[i];
    const tag = `A${i + 1}/${accounts.length}`;
    const profile = tokens.accounts[acc.name] || normalizeTokenProfile({});

    log("INFO", `--- ${acc.name} (${acc.email}) ---`);

    let result = null;
    for (let attempt = 1; attempt <= CHECKIN_RETRY_ATTEMPTS; attempt++) {
      try {
        result = await checkinAccount(acc, profile, tag);
        if (result.ok) break;

        // If session invalid, don't retry
        if (result.reason === "invalid-session") break;

        if (attempt < CHECKIN_RETRY_ATTEMPTS) {
          const delay = CHECKIN_RETRY_BASE_DELAY_S * attempt + randInt(5, 15);
          log(tag, `Check-in attempt ${attempt} failed (${result.reason}). Retrying in ${delay}s...`);
          await resetConnectionPool();
          await sleep(delay * 1000);
        }
      } catch (e) {
        log(tag, `Unexpected error: ${e.message}`);
        result = { ok: false, reason: e.message.slice(0, 50) };
        if (attempt < CHECKIN_RETRY_ATTEMPTS) {
          await resetConnectionPool();
          await sleep(CHECKIN_RETRY_BASE_DELAY_S * 1000);
        }
      }
    }

    if (!result) result = { ok: false, reason: "all-retries-exhausted" };

    // Update token profile if we got an updated one
    if (result.updatedProfile) {
      tokens.accounts[acc.name] = result.updatedProfile;
      await saveTokensSerial(tokensPath, tokens);
    }

    results[acc.name] = result;
    renderDashboard(accounts, results, "RUNNING");

    if (result.ok) {
      log(tag, `Check-in OK! Streak: ${result.streak}d | Points: +${result.points} | Tier: ${result.tier} | Week: ${result.reward}`);
    } else {
      log(tag, `Check-in FAILED: ${result.reason}`);
    }

    // Delay between accounts
    if (i < accounts.length - 1) {
      await sleep(ACCOUNT_DELAY_MS + randInt(1000, 3000));
    }
  }

  // Final summary
  const okCount = Object.values(results).filter((r) => r.ok).length;
  const failCount = Object.values(results).filter((r) => !r.ok).length;

  renderDashboard(accounts, results, "DONE");
  log("INFO", `Cycle complete: ${okCount} ok, ${failCount} failed out of ${accounts.length} accounts`);

  return { okCount, failCount, total: accounts.length };
}

// ---------------------------------------------------------------------------
// Scheduler: run at 00:00 UTC every day
// ---------------------------------------------------------------------------
function msUntilNextUtcMidnight() {
  const now = new Date();
  const next = new Date(Date.UTC(now.getUTCFullYear(), now.getUTCMonth(), now.getUTCDate() + 1, 0, 0, 0));
  return next.getTime() - now.getTime();
}

function formatDuration(ms) {
  const totalSec = Math.floor(ms / 1000);
  const h = Math.floor(totalSec / 3600);
  const m = Math.floor((totalSec % 3600) / 60);
  const s = totalSec % 60;
  return `${h}h ${m}m ${s}s`;
}

async function main() {
  console.log("");
  console.log("=".repeat(60));
  console.log("  RootsFi Daily Check-In Bot");
  console.log("  Runs check-in for all accounts, repeats at 00:00 UTC");
  console.log("=".repeat(60));
  console.log("");

  // Verify required files exist
  const cwd = process.cwd();
  try {
    await fs.access(path.resolve(cwd, ACCOUNTS_FILE));
  } catch {
    console.error(`[ERROR] ${ACCOUNTS_FILE} not found in ${cwd}`);
    process.exit(1);
  }
  try {
    await fs.access(path.resolve(cwd, TOKENS_FILE));
  } catch {
    console.error(`[ERROR] ${TOKENS_FILE} not found in ${cwd}`);
    console.error("Run the main bot (node index.js) first to generate tokens.json");
    process.exit(1);
  }

  // Run immediately on startup
  log("INFO", "Running initial check-in cycle...");
  try {
    await runCheckinCycle();
  } catch (e) {
    log("ERROR", `Initial cycle failed: ${e.message}`);
  }

  // Then schedule at 00:00 UTC
  while (true) {
    const waitMs = msUntilNextUtcMidnight() + randInt(30000, 300000); // +0.5~5min jitter
    const waitLabel = formatDuration(waitMs);
    const nextUtc = new Date(Date.now() + waitMs).toISOString();
    log("SCHED", `Next check-in in ${waitLabel} (approx ${nextUtc})`);
    log("SCHED", "Waiting... (Ctrl+C to stop)");

    await sleep(waitMs);

    log("INFO", "=== Starting scheduled check-in cycle ===");
    try {
      await resetConnectionPool();
      await runCheckinCycle();
    } catch (e) {
      log("ERROR", `Scheduled cycle failed: ${e.message}`);
      // Don't crash, wait for next cycle
    }
  }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------
main().catch((e) => {
  console.error(`[FATAL] ${e.message}`);
  process.exit(1);
});
