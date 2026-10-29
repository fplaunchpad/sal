import { readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
import { extract } from './extract.mjs';
import { replayCases } from './replay.mjs';

const [cache, output, demoCache] = process.argv.slice(2);
if (!cache || !output) throw new Error('Usage: node run-replays.mjs PINNED_CACHE OUTPUT_JSON [PINNED_DEMO_CACHE]');
const manifest = JSON.parse(readFileSync(new URL('./sources.json', import.meta.url)));
const extracted = extract(cache);
const variants = [
  { name: 'original-session-order', sessions: {} },
  { name: 'reversed-session-order', sessions: { A: 'B', B: 'A', C: 'D', D: 'C' } },
];
const records = variants.flatMap(v => replayCases(extracted, v.sessions).map(r => ({ variant: v.name, ...r })));
let originalDemo;
if (demoCache) {
  const temporary = mkdtempSync(join(tmpdir(), 'notion-demo-comparison-'));
  try {
    const results = join(temporary, 'demo.jsonl');
    const script = fileURLToPath(new URL('../../artifact/paper1/scripts/reproduce-notion.py', import.meta.url));
    const reproduced = spawnSync('python3', [script, '--vendor-cache', demoCache, '--output', results], { encoding: 'utf8' });
    if (reproduced.status !== 0) throw new Error(`Demo control failed: ${reproduced.stderr || reproduced.stdout}`);
    const demoRecords = readFileSync(results, 'utf8').trim().split('\n').map(JSON.parse);
    assert.equal(demoRecords.length, 6);
    assert.equal(demoRecords.filter(r => r.specAgreement === false).length, 5);
    assert.equal(demoRecords.filter(r => r.specAgreement === true).length, 1);
    const sourceManifest = JSON.parse(readFileSync(new URL('../../artifact/paper1/notion/sources.json', import.meta.url)));
    originalDemo = { summary: reproduced.stderr.trim(), sourceManifest, records: demoRecords };
    console.log(originalDemo.summary);
  } finally { rmSync(temporary, { recursive: true, force: true }); }
}
const checked = records.flatMap(r => r.replicas).flatMap(r => r.actions).filter(a => a.localContract !== undefined);
const summary = { schedules: records.length, localContracts: checked.length,
  localFailures: checked.filter(a => a.localContract === false).length,
  rejectedSchedules: records.filter(r => r.status === 'trace-rejected').length,
  demoLayoutsReached: records.filter(r => r.demoLayoutReached).length,
  handlerFailures: records.filter(r => r.status === 'handler-contract-failure').length };
writeFileSync(output, JSON.stringify({ scope: 'Original request-builder / shared record-handler replay; fixture stores and transaction sink; not live production',
  summary, sourceAssets: manifest.assets, records, ...(originalDemo ? { originalDemo } : {}) }, null, 2) + '\n', { flag: 'wx' });
for (const r of records) console.log(r.variant, r.id, r.status, r.message ?? JSON.stringify(r.actual));
