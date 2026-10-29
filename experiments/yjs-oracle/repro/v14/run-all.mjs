// Runs every reproduction and prints whether it reproduces on the installed yjs.
import { spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
const version = createRequire(import.meta.url)('@y/y/package.json').version;
console.log(`yjs ${version}`);
let shown = 0;
for (const id of ['Y-001', 'Y-002', 'Y-003', 'Y-004', 'Y-005', 'Y-006', 'Y-007', 'skip-plain']) {
  const r = spawnSync(process.execPath, [new URL(`./${id}.mjs`, import.meta.url).pathname], { encoding: 'utf8' });
  const crashed = r.stderr.trim() !== '';
  const reproduces = !crashed && r.status !== 0;
  shown += reproduces;
  console.log(`${id}: ${crashed ? 'error' : reproduces ? 'reproduces' : 'does not reproduce'}`);
  console.log((crashed ? r.stderr : r.stdout).trim().split('\n').map((l) => '    ' + l).join('\n'));
}
console.log(`${shown}/8 reproduce on yjs ${version}`);
