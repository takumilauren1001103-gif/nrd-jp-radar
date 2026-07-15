// ============================================================
// save-worker: まっさらな別プロセスで Netlify Blobs へ保存する。
// 親(crawl.mjs)が大量プローブで接続を溜め込んだ環境から切り離すことで、
// 保存時の api.netlify.com への接続が常にクリーンな状態から始まる。
//
// 使い方: node save-worker.mjs <payload.json>
//   payload.json = { "<key>": <value>, ... }  (key ごとに setJSON)
// 成功で exit 0 / 失敗で exit 1
// ============================================================
import { getStore } from "@netlify/blobs";
import { readFileSync } from "node:fs";

const SITE_ID = process.env.BLOBS_SITE_ID;
const TOKEN = process.env.BLOBS_TOKEN;

async function withRetry(fn, label, tries = 6) {
  let last;
  for (let i = 0; i < tries; i++) {
    try { return await fn(); }
    catch (e) {
      last = e;
      const wait = Math.min(3000 * 2 ** i, 60000);
      console.warn(`  [worker] ${label} 失敗 (${i + 1}/${tries}): ${e.message} → ${wait / 1000}s後`);
      await new Promise(r => setTimeout(r, wait));
    }
  }
  throw last;
}

async function main() {
  if (process.env.NRD_MOCK) {
    // テスト用: 受け取ったペイロードのキー数だけ報告して終了（実際の保存はしない）
    const payload = JSON.parse(readFileSync(process.argv[2], "utf8"));
    console.log(`  [worker] mock: ${Object.keys(payload).length} keys received`);
    return;
  }
  if (!SITE_ID || !TOKEN) { console.error("[worker] creds未設定"); process.exit(1); }
  const store = getStore({ name: "nrd-radar", siteID: SITE_ID, token: TOKEN });
  const payload = JSON.parse(readFileSync(process.argv[2], "utf8"));
  for (const [key, value] of Object.entries(payload)) {
    if (value === null) { try { await store.delete(key); } catch {} continue; }
    await withRetry(() => store.setJSON(key, value), `set ${key}`);
  }
  console.log(`  [worker] saved ${Object.keys(payload).length} keys`);
}

main().catch(e => { console.error("[worker] fatal:", e.message); process.exit(1); });
