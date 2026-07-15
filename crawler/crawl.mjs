// ============================================================
// NRD JP Radar - crawler (GitHub Actions daily)
// whoisds の新規登録ドメインから「日本語サイト」を検出。
// 未公開ドメインは監視リストで追い、公開した瞬間に新規公開として記録。
// 状態は Netlify Blobs（ダッシュボードと共有）に保存。
// ============================================================
import { getStore } from "@netlify/blobs";
import AdmZip from "adm-zip";
import { lookup } from "node:dns/promises";
import { execFile } from "node:child_process";
import { writeFileSync, unlinkSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const SITE_ID = process.env.BLOBS_SITE_ID;
const TOKEN = process.env.BLOBS_TOKEN;
let store = null;
function initStore() {
  if (process.env.NRD_MOCK) { store = makeMockStore(); return; }
  if (!SITE_ID || !TOKEN) { console.error("BLOBS_SITE_ID / BLOBS_TOKEN が未設定"); process.exit(1); }
  store = getStore({ name: "nrd-radar", siteID: SITE_ID, token: TOKEN });
}
function makeMockStore() {
  const mem = new Map();
  return {
    async get(k, o) { const v = mem.get(k); return v == null ? null : (o?.type === "json" ? JSON.parse(v) : v); },
    async setJSON(k, v) { mem.set(k, JSON.stringify(v)); },
    async delete(k) { mem.delete(k); },
    _mem: mem,
  };
}

// ---------------- 設定 ----------------
const CONCURRENCY = 45;        // 並列プローブ数
const FETCH_TIMEOUT = 6000;     // 1ドメインのタイムアウト(ms)
const PROBE_BUDGET_MS = 140 * 60 * 1000; // プローブ全体の時間上限(超過分は明日回し)
const BODY_CAP = 65536;         // HTML読み取り上限(バイト)

// 監視の階層:
//  strong = .jp/かな/日本語気配 (②日本っぽい未公開) → 60日じっくり追う
//  weak   = 正体不明ダーク       (③不明な未公開)    → 30日追う(頻度は粗めに間引き)
const WATCH_MAX = { strong: 60, weak: 30 };
const SCHEDULE = {
  strong: new Set([1,2,3,5,7,10,14,21,28,35,42,49,56]),  // 序盤は密、後半は週1
  weak:   new Set([1,2,4,7,14,21,28]),                   // 不明は粗く(公開は登録直後が多い)
};

// 捨てるTLD（スパム系・日本企業がまず使わない）
const JUNK_TLD = new Set(("xyz top sbs cyou icu buzz click vip cfd bond rest lol bid win loan gdn men date racing " +
  "review stream trade party download webcam wang mom lat hair skin makeup quest beauty monster").split(" "));
// 外国のccTLD（日本狙いでは除外）
const FOREIGN_CC = new Set(("cn ru in fr de uk br it es nl pl tr id vn th kr tw hk sg my ph ua kz by ar mx cl au ca us nz za " +
  "ir sa ae eu se no fi dk cz gr pt ro hu at ch be ie il eg ng pk bd lk np mm kh la md rs bg sk si lt lv ee hr ba mk al ge am az uz").split(" "));

const KANA_RE = /[\u3041-\u3096\u30A1-\u30FA\u30FC\u31F0-\u31FF]/;
const HAN_RE = /[\u4E00-\u9FFF\u3400-\u4DBF]/;
const FOREIGN_SCRIPT_RE = /[\uAC00-\uD7A3\u1100-\u11FF\u0400-\u04FF\u0600-\u06FF\u0E00-\u0E7F]/; // ハングル/キリル/アラビア/タイ

const PARKED_RE = new RegExp([
  "coming\\s*soon", "under\\s*construction", "準備中", "工事中", "近日公開", "ただいま準備",
  "domain\\s+is\\s+parked", "parked\\s+free", "sedoparking", "buy\\s+this\\s+domain", "domain\\s+for\\s+sale",
  "このドメインは", "お名前\\.com", "ムームードメイン", "エックスサーバー.*初期", "さくらのレンタルサーバ.*標準",
  "welcome\\s+to\\s+nginx", "apache2\\s+ubuntu\\s+default", "iis\\s+windows\\s+server", "it\\s+works!",
  "default\\s+(web\\s+)?page", "plesk", "cpanel", "index\\s+of\\s*/"
].join("|"), "i");

const CN_RE = /charset\s*=\s*["']?\s*(gb2312|gbk|gb18030|big5)|lang\s*=\s*["']?zh|(备案|ICP备|公安备)/i;
const JA_META_RE = /lang\s*=\s*["']?ja|charset\s*=\s*["']?\s*(shift_jis|x-sjis|euc-jp)|og:locale["'][^>]*ja_JP/i;

// ---------------- ユーティリティ ----------------
const todayISO = () => new Date().toISOString().slice(0, 10);
const dayDiff = (a, b) => Math.round((new Date(b) - new Date(a)) / 86400000);

function puny(label) {
  if (!label.startsWith("xn--")) return label;
  try { return punycodeDecode(label.slice(4)); } catch { return null; }
}
// punycode decoder (RFC 3492 minimal)
function punycodeDecode(input) {
  const base = 36, tmin = 1, tmax = 26, skew = 38, damp = 700, initialBias = 72, initialN = 128;
  let output = [], i = 0, n = initialN, bias = initialBias;
  const b = input.lastIndexOf("-");
  for (let j = 0; j < (b > 0 ? b : 0); j++) output.push(input.charCodeAt(j));
  let idx = b > 0 ? b + 1 : 0;
  const adapt = (delta, numPoints, first) => {
    delta = first ? Math.floor(delta / damp) : delta >> 1;
    delta += Math.floor(delta / numPoints);
    let k = 0;
    while (delta > ((base - tmin) * tmax) >> 1) { delta = Math.floor(delta / (base - tmin)); k += base; }
    return k + Math.floor(((base - tmin + 1) * delta) / (delta + skew));
  };
  while (idx < input.length) {
    const oldi = i; let w = 1;
    for (let k = base; ; k += base) {
      if (idx >= input.length) throw new Error("bad");
      const c = input.charCodeAt(idx++);
      const digit = c - 48 < 10 ? c - 22 : c - 65 < 26 ? c - 65 : c - 97 < 26 ? c - 97 : base;
      if (digit >= base) throw new Error("bad");
      i += digit * w;
      const t = k <= bias ? tmin : k >= bias + tmax ? tmax : k - bias;
      if (digit < t) break;
      w *= base - t;
    }
    bias = adapt(i - oldi, output.length + 1, oldi === 0);
    n += Math.floor(i / (output.length + 1));
    i %= output.length + 1;
    output.splice(i++, 0, n);
  }
  return String.fromCodePoint(...output);
}

function decodeDomain(d) {
  return d.split(".").map(puny).map(x => x ?? "\uFFFD").join(".");
}

// ---------------- whoisds ダウンロード ----------------
async function downloadNRD() {
  for (let back = 1; back <= 3; back++) {
    const dt = new Date(Date.now() - back * 86400000).toISOString().slice(0, 10);
    const b64 = Buffer.from(`${dt}.zip`).toString("base64");
    const url = `https://whoisds.com//whois-database/newly-registered-domains/${b64}/nrd`;
    try {
      const res = await fetch(url, { headers: { "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)" }, signal: AbortSignal.timeout(60000) });
      if (!res.ok) continue;
      const buf = Buffer.from(await res.arrayBuffer());
      if (buf.length < 10000) continue;
      const zip = new AdmZip(buf);
      const entry = zip.getEntries().find(e => e.entryName.endsWith(".txt"));
      if (!entry) continue;
      const list = entry.getData().toString("utf8").split(/\r?\n/).map(s => s.trim().toLowerCase()).filter(Boolean);
      console.log(`whoisds ${dt}: ${list.length} domains`);
      return { date: dt, list };
    } catch (e) { console.warn(`download ${dt} failed: ${e.message}`); }
  }
  return null;
}

// ---------------- フィルタ ----------------
function preFilter(domains) {
  const kept = [];
  for (const d of domains) {
    if (!/^[a-z0-9.-]+$/.test(d)) continue;
    const parts = d.split(".");
    if (parts.length < 2) continue;
    const tld = parts[parts.length - 1];
    if (JUNK_TLD.has(tld) || FOREIGN_CC.has(tld)) continue;
    const uni = d.includes("xn--") ? decodeDomain(d) : d;
    const isJpTld = tld === "jp" || d.endsWith(".jp");
    const hasKana = KANA_RE.test(uni);
    if (!isJpTld && !hasKana && FOREIGN_SCRIPT_RE.test(uni)) continue;       // 外国文字IDN除外
    if (!isJpTld && !hasKana && d.includes("xn--") && HAN_RE.test(uni) && !KANA_RE.test(uni)) {
      // 漢字だけIDNは中国の可能性大だが、日本の可能性も残る → プローブ対象として残す
    }
    kept.push({ d, uni, jpHint: isJpTld || hasKana ? 1 : 0 });
  }
  return kept;
}

// ---------------- プローブ ----------------
async function readCapped(res) {
  const reader = res.body.getReader();
  const chunks = []; let total = 0;
  try {
    while (total < BODY_CAP) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value); total += value.length;
    }
  } catch {}
  try { await reader.cancel(); } catch {}
  return Buffer.concat(chunks.map(c => Buffer.from(c)));
}

function sniffDecode(buf, headerCT) {
  const ascii = buf.toString("latin1");
  let cs = (headerCT.match(/charset=["']?\s*([\w-]+)/i) || ascii.match(/charset\s*=\s*["']?\s*([\w-]+)/i) || [])[1];
  cs = (cs || "utf-8").toLowerCase();
  if (cs === "x-sjis" || cs === "shift-jis" || cs === "sjis") cs = "shift_jis";
  try { return { text: new TextDecoder(cs, { fatal: false }).decode(buf), cs }; }
  catch { return { text: buf.toString("utf8"), cs: "utf-8" }; }
}

async function probeOnce(url) {
  const res = await fetch(url, {
    redirect: "follow",
    headers: { "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36", "accept-language": "ja,en;q=0.8" },
    signal: AbortSignal.timeout(FETCH_TIMEOUT),
  });
  const buf = await readCapped(res);
  return { status: res.status, ct: res.headers.get("content-type") || "", buf };
}

async function probe(domain) {
  // DNS事前チェック: 引けないドメインはHTTPを試さず即DEAD（大量の未公開ドメインを高速処理）
  // DNS lookup自体にタイムアウトがなくハングすることがあるため明示的に打ち切る
  try {
    await Promise.race([
      lookup(domain),
      new Promise((_, rej) => setTimeout(() => rej(new Error("dns timeout")), 2500)),
    ]);
  } catch { return { state: "DEAD" }; }
  let r = null;
  for (const url of [`http://${domain}/`, `https://${domain}/`]) {
    try { r = await probeOnce(url); break; } catch { r = null; }
  }
  if (!r) return { state: "DEAD" };
  const { text, cs } = sniffDecode(r.buf, r.ct);
  const size = r.buf.length;
  const title = (text.match(/<title[^>]*>([^<]{0,120})/i) || [])[1]?.trim().replace(/\s+/g, " ") || "";
  const kana = KANA_RE.test(text) || KANA_RE.test(title);
  const jaMeta = JA_META_RE.test(text) || /^(shift_jis|euc-jp)$/.test(cs);
  const cn = !kana && CN_RE.test(text);
  const parked = PARKED_RE.test(text);

  if (r.status >= 500 || size === 0) return { state: "DEAD" };
  if (cn) return { state: "CN" };
  if (parked) return { state: "PARKED", jp: kana || jaMeta ? 1 : 0, title };
  if (size < 900 || r.status === 401 || r.status === 403 || r.status === 404) return { state: "TINY", jp: kana || jaMeta ? 1 : 0, title };
  if (kana || jaMeta) return { state: "LIVE_JP", title, ev: kana ? "kana" : "meta" };
  return { state: "LIVE_OTHER" };
}

async function pool(items, worker, size, ctx = {}) {
  const results = new Array(items.length);
  const { offset = 0, total = items.length, deadline = Infinity } = ctx;
  let idx = 0, done = 0, skipped = 0;
  const t0 = Date.now();
  await Promise.all(Array.from({ length: Math.min(size, items.length) }, async () => {
    while (idx < items.length) {
      const i = idx++;
      if (Date.now() > deadline) { results[i] = { state: "DEAD" }; skipped++; continue; } // 時間切れ分は明日回し
      results[i] = await worker(items[i]).catch(() => ({ state: "DEAD" }));
      const g = offset + ++done;
      if (g % 2000 === 0) console.log(`  probed ${g}/${total} (${Math.round((Date.now() - t0) / 1000)}s in chunk)`);
    }
  }));
  if (skipped) console.warn(`時間上限により ${skipped} 件をスキップ（監視リストで明日再チェック）`);
  return results;
}

// ---------------- Blobs I/O ----------------
// ---------------- Blobs I/O（自動リトライ付き：一時的な通信エラーで成果を失わない） ----------------
async function withRetry(fn, label, tries = 5) {
  let last;
  for (let i = 0; i < tries; i++) {
    try { return await fn(); }
    catch (e) {
      last = e;
      const wait = Math.min(2000 * 2 ** i, 90000); // 2s,4s,8s,...上限90s
      console.warn(`${label} 失敗 (${i + 1}/${tries}): ${e.message} → ${wait / 1000}s後に再試行`);
      await new Promise(r => setTimeout(r, wait));
    }
  }
  throw last;
}
async function getJSON(key, fallback) {
  // キーが無い場合は null → fallback。通信エラーはリトライし、最終的に失敗なら run を止める
  // （台帳を読めないまま上書き保存して過去データを消すのを防ぐ）
  return withRetry(async () => { const v = await store.get(key, { type: "json" }); return v ?? fallback; }, `get ${key}`);
}
const setJSON = (key, val) => withRetry(() => store.setJSON(key, val), `set ${key}`);

// まっさらな別プロセスで保存する（プローブで溜まった接続の影響を受けない）
function saveViaWorker(payload) {
  return new Promise((resolve, reject) => {
    const file = join(tmpdir(), `nrd-save-${Date.now()}-${Math.random().toString(36).slice(2)}.json`);
    writeFileSync(file, JSON.stringify(payload));
    execFile(process.execPath, ["save-worker.mjs", file],
      { env: process.env, timeout: 15 * 60 * 1000, maxBuffer: 10 * 1024 * 1024 },
      (err, stdout, stderr) => {
        try { unlinkSync(file); } catch {}
        if (stdout?.trim()) console.log(stdout.trim());
        if (stderr?.trim()) console.warn(stderr.trim());
        if (err) reject(new Error(`save-worker exit ${err.code ?? err.message}`));
        else resolve();
      });
  });
}

// ---------------- メイン ----------------
// 起動時カナリア: 確実に生きている日本サイトが1つも検出できない = ランナーのネットワーク不調。
// 全件DEAD誤判定で1日を無駄にする前に、台帳に触らず中止する。
async function canaryCheck() {
  const canaries = ["www.yahoo.co.jp", "www.google.co.jp", "www.nhk.or.jp"];
  const rs = await Promise.all(canaries.map(d => probe(d)));
  const ok = rs.filter(r => r.state === "LIVE_JP").length;
  console.log(`canary: ${ok}/${canaries.length} 検出`);
  if (ok === 0) {
    console.error("カナリア全滅: ランナーのネットワークが不調のため中止（台帳は無変更・次回の定時実行で自動リトライ）");
    process.exit(1);
  }
}

async function main() {
  initStore();
  await canaryCheck();
  const today = todayISO();
  console.log(`=== NRD JP Radar crawl ${today} ===`);

  // 1) 当日の新規ドメイン
  const nrd = await downloadNRD();
  if (!nrd) { console.error("whoisdsのダウンロードに失敗"); process.exit(1); }
  const fresh = preFilter(nrd.list);
  console.log(`filter: ${nrd.list.length} -> ${fresh.length} probe対象`);
  // 日本っぽい(.jp/かな)ドメインを最優先で処理 → 時間切れで打ち切っても本命は必ず処理される
  fresh.sort((a, b) => (b.jpHint || 0) - (a.jpHint || 0));
  if (process.env.NRD_SAMPLE) { fresh.length = Math.min(fresh.length, +process.env.NRD_SAMPLE); console.log(`(sample mode: ${fresh.length})`); }

  // 2) 監視リスト読込（日別ファイル）— エントリ単位で階層別に「今日調べる/据え置き/期限切れ」を判定
  const watchIndex = await getJSON("watch/index.json", []);
  const watchDue = [];        // 今日再チェックする分
  const keepByReg = {};       // regDate -> 据え置きエントリ
  let expired = 0, carried = 0;
  for (const regDate of watchIndex) {
    const age = dayDiff(regDate, today);
    const entries = await getJSON(`watch/${regDate}.json`, []);
    for (const e of entries) {
      const tier = e.jp ? "strong" : "weak";
      if (age > WATCH_MAX[tier]) { expired++; continue; }           // 期限切れ → 破棄
      if (SCHEDULE[tier].has(age)) watchDue.push({ ...e, reg: regDate });
      else { (keepByReg[regDate] ||= []).push(e); carried++; }      // 今日は据え置き
    }
  }
  console.log(`watch: ${watchIndex.length}日分 / 今日の再チェック ${watchDue.length} / 据え置き ${carried} / 期限切れ破棄 ${expired}`);

  // 3) 台帳の先読み（ネットワークが健全なプローブ前に読み込みを済ませ、後半は書き込みだけにする）
  const month = today.slice(0, 7);
  const results = await getJSON(`results/${month}.json`, []);
  const stats = await getJSON("meta/stats.json", { days: [] });
  const known = new Set(results.map(r => r.d));

  // 4) クラッシュ耐性のある監視台帳: 先に全対象を「保留」として登録し、判定のたびに更新/削除。
  //    どの時点で保存が走っても台帳として一貫しており、途中で死んでも翌日拾い直せる。
  const watchMap = new Map(); // d -> {d, uni?, jp, st, reg}
  for (const [regDate, entries] of Object.entries(keepByReg))
    for (const e of entries) watchMap.set(e.d, { ...e, reg: regDate });
  const newItems = fresh.map(f => ({ d: f.d, uni: f.uni, jpHint: f.jpHint, reg: nrd.date, isNew: true }));
  const all = [...newItems, ...watchDue];
  for (const it of all)
    watchMap.set(it.d, { d: it.d, uni: it.uni !== it.d ? it.uni : undefined, jp: it.jpHint || 0, st: it.st || "PEND", reg: it.reg });

  let cJp = 0, cDrop = 0;
  function dispatch(item, r) {
    const jpHint = item.jpHint || r.jp || 0;
    if (r.state === "LIVE_JP") {
      watchMap.delete(item.d);
      if (!known.has(item.d)) {
        results.push({
          d: item.d, uni: item.uni !== item.d ? item.uni : undefined,
          reg: item.reg, pub: today, t: (r.title || "").slice(0, 90),
          fresh: item.isNew ? 1 : 0,   // 登録初日から公開済み or 監視から公開転換(点灯)
        });
        known.add(item.d); cJp++;
      }
    } else if (r.state === "CN" || r.state === "LIVE_OTHER") {
      watchMap.delete(item.d); cDrop++;   // 公開済みだが日本語なし → 恒久除外
    } else {
      const w = watchMap.get(item.d);
      if (w) { w.st = r.state; w.jp = w.jp || jpHint; }  // DEAD/PARKED/TINY → 監視継続
    }
  }

  // 保存一式: 全キーを1つのペイロードにまとめ、まっさらな別プロセスで書き込む
  const oldDates = new Set(watchIndex);
  async function saveAll(final) {
    const byReg = {};
    for (const w of watchMap.values()) (byReg[w.reg] ||= []).push({ d: w.d, uni: w.uni, jp: w.jp, st: w.st });
    const dates = Object.keys(byReg).sort();
    results.sort((a, b) => (a.pub < b.pub ? 1 : -1));
    let watchTotal = 0;
    const payload = {};
    payload[`results/${month}.json`] = results;
    for (const dt of dates) { payload[`watch/${dt}.json`] = byReg[dt]; watchTotal += byReg[dt].length; }
    payload["watch/index.json"] = dates;
    if (final) {
      const keepSet = new Set(dates);
      for (const dt of oldDates) if (!keepSet.has(dt)) payload[`watch/${dt}.json`] = null; // 削除指示
      stats.watchTotal = watchTotal;
      stats.days.unshift({ date: today, src: nrd.list.length, probed: all.length, jp: cJp, watch: watchTotal, drop: cDrop });
      stats.days = stats.days.slice(0, 60);
      stats.updated = new Date().toISOString();
      payload["meta/stats.json"] = stats;
    }
    await saveViaWorker(payload);
    return watchTotal;
  }

  // 5) チャンク処理: 15,000件ごとにプローブ→振り分け→途中保存
  //    (終盤にランナーのNAT枯渇で保存不能になっても、成果の大半が既に保存済みになる)
  const CHUNK = +(process.env.NRD_CHUNK || 15000);
  console.log(`probing ${all.length} domains @${CONCURRENCY} parallel, checkpoint every ${CHUNK} ...`);
  const deadline = Date.now() + PROBE_BUDGET_MS;
  let processed = 0;
  for (let off = 0; off < all.length; off += CHUNK) {
    const chunk = all.slice(off, off + CHUNK);
    const res = await pool(chunk, item => probe(item.d), CONCURRENCY, { offset: off, total: all.length, deadline });
    chunk.forEach((item, i) => dispatch(item, res[i]));
    processed += chunk.length;
    if (processed < all.length) {
      try { await saveAll(false); console.log(`  checkpoint保存 @${processed}/${all.length} (JP累計${cJp})`); }
      catch (e) { console.warn(`  checkpoint保存失敗(続行・次回持越): ${e.message}`); }
    }
  }

  // 6) 最終保存: 別プロセスがクリーンな接続で書き込む（親の接続汚染の影響を受けない）
  console.log("最終保存(別プロセス) ...");
  const watchTotal = await saveAll(true);

  console.log(`=== done: JP公開 ${cJp} / 監視 ${watchTotal} / 除外 ${cDrop} ===`);
}

if (!process.env.NRD_TEST) {
  main().catch(e => { console.error(e); process.exit(1); });
}
export { probe, preFilter, decodeDomain };
