import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

const raw = new URL('../results/raw/', import.meta.url).pathname;
const rows = readdirSync(raw).filter((f) => f.startsWith('peritext-') && f.endsWith('.json'))
  .map((f) => JSON.parse(readFileSync(join(raw, f), 'utf8')))
  .filter((r) => r.config?.scenario);
for (const key of new Set(rows.map((r) => `${r.workload}:${r.preset}`))) {
  const rs = rows.filter((r) => `${r.workload}:${r.preset}` === key);
  const digests = new Set(rs.map((r) => r.metrics.renderDigest));
  if (digests.size !== 1) throw new Error(`Peritext ablations changed the render for ${key}`);
}
console.log(`Peritext ablation render gate passed for ${rows.length} results`);
