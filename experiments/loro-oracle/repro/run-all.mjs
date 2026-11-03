// Runs every reproduction and prints whether it reproduces on the installed Loro.
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
const version = JSON.parse(readFileSync(new URL('./node_modules/loro-crdt/package.json', import.meta.url), 'utf8')).version;
console.log(`loro-crdt ${version}`);
let shown = 0;
const ids = ['L-001', 'L-002', 'L-003', 'L-004', 'L-005'];
for (const id of ids) {
  const r = spawnSync(process.execPath, [new URL(`./${id}.mjs`, import.meta.url).pathname], { encoding: 'utf8' });
  const crashed = r.stderr.trim() !== '';
  const reproduces = !crashed && r.status !== 0;
  shown += reproduces;
  console.log(`${id}: ${crashed ? 'error' : reproduces ? 'reproduces' : 'does not reproduce'}`);
  console.log((crashed ? r.stderr : r.stdout).trim().split('\n').map((l) => '    ' + l).join('\n'));
}
console.log(`${shown}/${ids.length} reproduce on loro-crdt ${version}`);
