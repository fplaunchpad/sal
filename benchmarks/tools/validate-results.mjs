import { readdirSync, readFileSync, statSync } from 'node:fs';
import { join } from 'node:path';

const root = new URL('../results/', import.meta.url);
const files = [];
function walk(path) {
  for (const name of readdirSync(path)) {
    const child = join(path, name);
    if (statSync(child).isDirectory()) walk(child);
    else if (name.endsWith('.json')) files.push(child);
  }
}
walk(root.pathname);

let checked = 0;
for (const path of files) {
  const value = JSON.parse(readFileSync(path, 'utf8'));
  // Aggregates and representation-model artifacts have their own shapes.
  // Raw benchmark rows opt into the public schema with schemaVersion = 1.
  if (value?.schemaVersion !== 1 || !('suite' in value)) continue;
  for (const field of ['suite', 'workload', 'system']) {
    if (typeof value[field] !== 'string' || value[field].length === 0)
      throw new Error(`${path}: invalid ${field}`);
  }
  if (typeof value.config !== 'object' || value.config === null)
    throw new Error(`${path}: invalid config`);
  if (typeof value.environment !== 'object' || value.environment === null)
    throw new Error(`${path}: invalid environment`);
  if (typeof value.gates !== 'object' || value.gates === null ||
      Object.values(value.gates).some((gate) => typeof gate !== 'boolean'))
    throw new Error(`${path}: invalid gates`);
  if (typeof value.metrics !== 'object' || value.metrics === null)
    throw new Error(`${path}: invalid metrics`);
  checked++;
}
if (checked === 0) throw new Error('no schema-versioned raw benchmark results found');
console.log(`validated ${checked} schema-versioned benchmark results`);
