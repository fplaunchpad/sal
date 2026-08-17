// Normalize schema-versioned raw benchmark results into plot-ready JSON/CSV.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..', 'results');
const RAW = join(ROOT, 'raw'), TABLES = join(ROOT, 'tables');
mkdirSync(RAW, { recursive: true }); mkdirSync(TABLES, { recursive: true });
const rows = readdirSync(RAW).filter((f) => f.endsWith('.json'))
  .map((f) => JSON.parse(readFileSync(join(RAW, f), 'utf8')))
  // Ignore pre-matrix Peritext artifacts whose filenames/configuration did
  // not identify a workload family.
  .filter((r) => r.suite !== 'peritext' || r.config?.matrixVersion === 3)
  // Ignore pre-schema focused-kernel artifacts. Current kernel results name
  // both the implementation and topology through system/workload.
  .filter((r) => r.suite !== 'peritext-kernel-gc' || (r.system && r.workload));
for (const r of rows) {
  if (r.schemaVersion !== 1 || !r.suite || !r.workload || !r.system || !r.metrics || !r.gates)
    throw new Error(`invalid raw result schema: ${JSON.stringify(r).slice(0, 120)}`);
  if (!Object.values(r.gates).every(Boolean)) throw new Error(`failed semantic gate: ${r.mode ?? r.system}`);
}
const flat = rows.map((r) => ({ suite: r.suite, workload: r.workload, system: r.system,
  mode: r.mode ?? '', preset: r.preset ?? '', ...r.metrics }));
const cols = [...new Set(flat.flatMap(Object.keys))];
const csv = [cols.join(','), ...flat.map((r) => cols.map((c) => JSON.stringify(r[c] ?? '')).join(','))].join('\n');
writeFileSync(join(TABLES, 'results.csv'), csv + '\n');
const gcRows = flat.filter((r) => r.workload === 'concurrent-gc-ablation');
const gcCsv = [cols.join(','), ...gcRows.map((r) => cols.map((c) => JSON.stringify(r[c] ?? '')).join(','))].join('\n');
writeFileSync(join(TABLES, 'plain-gc.csv'), gcCsv + '\n');
const peritextRows = flat.filter((r) => r.suite === 'peritext');
const peritextCsv = [cols.join(','), ...peritextRows.map((r) => cols.map((c) => JSON.stringify(r[c] ?? '')).join(','))].join('\n');
writeFileSync(join(TABLES, 'peritext.csv'), peritextCsv + '\n');
writeFileSync(join(ROOT, 'summary.json'), JSON.stringify({ schemaVersion: 1, generatedAt: new Date().toISOString(), results: rows }, null, 2));
console.log(`normalized ${rows.length} raw results -> results/summary.json + results/tables/{results,plain-gc,peritext}.csv`);
