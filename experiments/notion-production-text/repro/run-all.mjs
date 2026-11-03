// Runs every reproduction in this directory; exit status 1 when any differs
// from its documented outcome. Needs NOTION_PRODUCTION_LIBRARY.
import { spawnSync } from 'node:child_process';
import { readdirSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
let failed = 0;
for (const f of readdirSync(here).filter((f) => /^(NT|P)-\d\.mjs$/.test(f)).sort()) {
  const r = spawnSync(process.execPath, [join(here, f)], { encoding: 'utf8' });
  process.stdout.write(`== ${f}\n${r.stdout}${r.stderr}`);
  if (r.status !== 0) failed++;
}
console.log(failed ? `${failed} reproductions differ` : 'every reproduction shows its documented outcome');
process.exitCode = failed ? 1 : 0;
