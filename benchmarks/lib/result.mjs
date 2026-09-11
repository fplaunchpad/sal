// Canonical schema-v1 result writer. Workers may keep their detailed legacy
// payload while exposing common identity, environment, gates, and metrics.

import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

export function writeRawResult(resultsDir, file, record) {
  const raw = join(resultsDir, 'raw');
  mkdirSync(raw, { recursive: true });
  const value = { schemaVersion: 1, ...record };
  writeFileSync(join(raw, file), JSON.stringify(value, null, 2));
  return value;
}
