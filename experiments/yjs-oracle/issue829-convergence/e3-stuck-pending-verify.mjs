// The stuck-pending shape of e3-stuck-pending-replay.mjs rebuilt from scratch
// against any installed package, with the two-struct update split and
// omitted as controls, and probes of what a stale replica does next.
// Usage: node stuck-verify.mjs <package dir> <entry: src/index.js | dist/yjs.mjs> <14|13>
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
const [dir, entry, major] = process.argv.slice(2);
const pkg = JSON.parse(readFileSync(dir + '/package.json'));
const Y = await import(pathToFileURL(dir + '/' + entry).href);
const text = (d) => (major === '14' ? d.get('t') : d.getText('t'));
const mk = (id) => { const d = new Y.Doc({ gc: false }); d.clientID = id; const own = []; d.on('update', (u, _o, _d, tr) => { if (tr.local) own.push(u); }); text(d); return { d, own }; };
const state = (d) => `${JSON.stringify(text(d).toString())} pending=${d.store.pendingStructs ? JSON.stringify([...d.store.pendingStructs.missing]) : 'none'}`;
function build({ separate = false, withK = true } = {}) {
  const A = mk(1), B = mk(2), C = mk(3);
  text(C.d).insert(0, 'xyz'); const base = C.own[0];
  Y.applyUpdate(A.d, base); Y.applyUpdate(B.d, base);
  text(A.d).insert(0, 'A'); const a1 = A.own[0];
  text(A.d).insert(3, 'a'); const a2 = A.own[1];
  Y.applyUpdate(B.d, a1); Y.applyUpdate(B.d, a2);
  text(B.d).insert(0, 'q'); const q = B.own[0];
  Y.applyUpdate(A.d, q);
  let tail;
  if (separate) { if (withK) text(A.d).insert(6, 'k'); text(A.d).insert(1, 'w'); tail = A.own.slice(2); }
  else { A.d.transact(() => { if (withK) text(A.d).insert(6, 'k'); text(A.d).insert(1, 'w'); }); tail = [A.own[2]]; }
  for (const u of tail) Y.applyUpdate(B.d, u);
  return { A, B, C, seq: [a2, q, ...tail, a1] };
}
console.log(pkg.name, pkg.version);
for (const [label, opts] of [['one transaction k+w', {}], ['k and w as separate updates', { separate: true }], ['no k, w alone', { withK: false }]]) {
  const { A, B, C, seq } = build(opts);
  for (const u of seq) Y.applyUpdate(C.d, u);
  const ok = text(C.d).toString() === text(A.d).toString() && !C.d.store.pendingStructs;
  console.log(`  ${label.padEnd(30)} A=${JSON.stringify(text(A.d).toString())} C=${state(C.d)} ${ok ? 'converged' : 'STUCK'}`);
  if (!ok) {
    text(C.d).insert(0, 'L'); console.log(`    after a local edit on C:      C=${state(C.d)}`);
    Y.applyUpdate(A.d, C.own.at(-1)); text(A.d).insert(0, 'e'); Y.applyUpdate(C.d, A.own.at(-1)); console.log(`    after a further A edit:       C=${state(C.d)} A=${JSON.stringify(text(A.d).toString())}`);
  }
}
