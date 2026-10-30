// E1: after a clock gap is integrated (v14: behind a Skip; v13: pending),
// does state-vector sync alone recover the withheld update, and does a
// replica that joins from the gap-bearing one catch up? A state vector
// that counted the Skip would make y-protocols sync skip the predecessor
// for good. Usage: node e1-state-vector-sync.mjs <13|14>
import { load } from './lib.mjs';
const version = process.argv[2] ?? '14';
const L = await load(version);
const { Y, text } = L;
const show = (d) => `${JSON.stringify(text(d).toString())} sv=${L.sv(d)} pending=${L.pending(d).structs} skips=${d.store.skips ? d.store.skips.clients.size : 'n/a'}`;
let failures = 0;
for (const gc of [false, true]) {
  const a = L.doc(100, { gc }), b = L.doc(101, { gc });
  text(a.d).insert(0, 'y');                                           // withheld: client 100 clock 0
  text(b.d).insert(0, 'b'); L.sync(b.d, a.d);
  text(a.d).insert(text(a.d).toString().indexOf('b') + 1, 'h');       // client 100 clock 1
  Y.applyUpdate(b.d, a.updates.at(-1));                               // b gets h without y
  console.log(`v${version} gc=${gc} gap: a=${show(a.d)} b=${show(b.d)}`);
  for (let i = 0; i < 3; i++) { L.sync(a.d, b.d); L.sync(b.d, a.d); }
  const ok1 = L.equal([a.d, b.d]);
  console.log(`v${version} gc=${gc} after state-vector sync only: b=${show(b.d)} ${ok1 ? 'converged' : 'DIVERGED'}`);
  const c = L.doc(102, { gc });
  L.sync(b.d, c.d); for (let i = 0; i < 3; i++) { L.sync(a.d, c.d); L.sync(c.d, a.d); }
  const ok2 = L.equal([a.d, c.d]);
  console.log(`v${version} gc=${gc} newcomer from b, then a: c=${show(c.d)} ${ok2 ? 'converged' : 'DIVERGED'}`);
  if (!ok1 || !ok2) failures++;
  for (const x of [a, b, c]) x.d.destroy();
}
process.exit(failures ? 1 : 0);
