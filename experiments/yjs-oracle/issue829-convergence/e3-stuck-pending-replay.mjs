// Standalone replay, package only (no lib.mjs): a v14 replica that holds a
// Skip for a withheld struct receives every update exactly once, the withheld
// struct last, and keeps pending structs with a stale view. The same sequence
// converges on 13.6.31. Exit code 1 means the replica stayed pending.
//
// Usage: node e3-stuck-pending-replay.mjs [14|13]
import { readFileSync } from 'node:fs';
const version = process.argv[2] || '14';
const root = new URL(version === '14' ? '../repro/v14/node_modules/@y/y/' : '../repro/node_modules/yjs/', import.meta.url);
const pkg = JSON.parse(readFileSync(new URL('package.json', root)));
const Y = await import(new URL(version === '14' ? 'src/index.js' : 'dist/yjs.mjs', root));
const text = (d) => (version === '14' ? d.get('t') : d.getText('t'));
const replica = (clientID) => { const d = new Y.Doc({ gc: false }); d.clientID = clientID; const updates = []; d.on('update', (u) => updates.push(u)); text(d); return { d, updates, last: () => updates[updates.length - 1] }; };
const sv = (d) => JSON.stringify([...Y.decodeStateVector(Y.encodeStateVector(d)).entries()].sort((x, y) => x[0] - y[0]));
const missing = (d) => (d.store.pendingStructs ? JSON.stringify([...d.store.pendingStructs.missing.entries()]) : 'none');
const show = (tag, d) => console.log(tag.padEnd(44), JSON.stringify(text(d).toString()).padEnd(11), 'sv', sv(d).padEnd(20), 'pending missing', missing(d));
console.log(pkg.name, pkg.version, 'node', process.version);

const A = replica(1), B = replica(2), C = replica(3);
text(C.d).insert(0, 'xyz'); const base = C.last();                 // 3:0..3:2
Y.applyUpdate(A.d, base); Y.applyUpdate(B.d, base);
text(A.d).insert(0, 'A'); const a1 = A.last();                      // 1:0, right origin 3:0; withheld from C
text(A.d).insert(3, 'a'); const a2 = A.last();                      // 1:1, origins 3:1 and 3:2
Y.applyUpdate(B.d, a1); Y.applyUpdate(B.d, a2);                     // B complete: "Axyaz"
text(B.d).insert(0, 'q'); const q = B.last();                       // 2:0, right origin 1:0 (A)
Y.applyUpdate(A.d, q);                                              // A: "qAxyaz"
// One transaction, so one update carries both structs (as a format or a paste would).
A.d.transact(() => { text(A.d).insert(6, 'k'); text(A.d).insert(1, 'w'); });
const kw = A.last();                                                // 1:2 origin 3:2 (z); 1:3 origin 2:0 (q), right origin 1:0 (A)
Y.applyUpdate(B.d, kw);
console.log('A and B:', JSON.stringify(text(A.d).toString()), JSON.stringify(text(B.d).toString()));

// C receives each of the four foreign updates exactly once; a1 is the last to arrive.
show('C after base (own)', C.d);
Y.applyUpdate(C.d, a2); show('C after a2 (a1 withheld)', C.d);
Y.applyUpdate(C.d, q); show('C after q (right origin A)', C.d);
Y.applyUpdate(C.d, kw); show('C after kw (k integrates, w parks)', C.d);
Y.applyUpdate(C.d, a1); show('C after a1: every update delivered once', C.d);
const stuck = C.d.store.pendingStructs != null || text(C.d).toString() !== text(A.d).toString();
console.log('C converged after complete delivery?', !stuck);
console.log('clientIDs unchanged:', [A.d.clientID, B.d.clientID, C.d.clientID].join(','));

// What clears it. Each probe starts from a fresh copy of C's state (its own clientID, so no collision).
const copy = (seq) => { const X = replica(9); for (const u of seq) Y.applyUpdate(X.d, u); return X; };
const stuckSeq = [base, a2, q, kw, a1];
{ const X = copy(stuckSeq); for (const u of stuckSeq) Y.applyUpdate(X.d, u); show('probe: same updates delivered again', X.d); }
{ const X = copy(stuckSeq); Y.applyUpdate(X.d, Y.encodeStateAsUpdate(A.d, Y.encodeStateVector(X.d))); show('probe: state-vector sync from A', X.d); }
text(A.d).insert(0, 'e'); const e = A.last(); Y.applyUpdate(B.d, e);
{ const X = copy(stuckSeq); Y.applyUpdate(X.d, e); show('probe: a further A edit (client 1)', X.d); }
text(B.d).insert(0, 'z'); const z = B.last(); Y.applyUpdate(A.d, z);
{ const X = copy(stuckSeq); Y.applyUpdate(X.d, z); show('probe: a further B edit (client 2)', X.d); }
console.log('A and B now:', JSON.stringify(text(A.d).toString()), JSON.stringify(text(B.d).toString()));
{ const X = copy([base, a2, q, a1, kw]); show('control: a1 before kw', X.d); }
{ const X = copy([base, a2, kw, q, a1]); show('control: kw before q, a1 last', X.d); }
{ const X = copy([base, a1, a2, q, kw]); show('control: no gap', X.d); }
process.exit(stuck ? 1 : 0);
