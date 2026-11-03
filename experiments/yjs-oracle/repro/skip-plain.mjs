// Plain text, partial delivery: a replica shows an insert whose issuer had
// an earlier update the replica has not received. The v14 store fills the
// clock gap with a Skip and integrates the struct because its origins exist;
// 13.x holds the struct pending until the gap is filled.
import * as Y from 'yjs';
const show = (doc) => doc.getText('t').toString();
const updatesOf = (doc) => { const us = []; doc.on('update', (u) => us.push(u)); return us; };

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
const u1 = updatesOf(d1); const u2 = updatesOf(d2); // u1[1] is d1 re-emitting b
d1.getText('t').insert(0, 'y');                                 // 1:0
d2.getText('t').insert(0, 'b');                                 // 2:0
Y.applyUpdate(d1, u2[0]);                                   // d1 has y and b
d1.getText('t').insert(d1.getText('t').toString().indexOf('b') + 1, 'h'); // 1:1, placed after b
Y.applyUpdate(d2, u1[2]);                                   // d2 receives 1:1 but not 1:0

console.log('d2 after receiving only the second update of client 1:', JSON.stringify(show(d2)),
  'pending structs:', d2.store.pendingStructs === null ? 'none' : 'some');
console.log('causally closed states at d2: "b" (no update of client 1), or ones containing "y" (both updates)');
const wrong = show(d2).includes('h') && !show(d2).includes('y');
Y.applyUpdate(d2, u1[0]);
console.log('after the first update arrives:', JSON.stringify(show(d2)), '(converges)');
process.exit(wrong ? 1 : 0);
