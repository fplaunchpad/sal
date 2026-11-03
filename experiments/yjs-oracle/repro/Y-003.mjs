// Y-003: deleting a bold character removes the bold span's markers, so a
// concurrent bold insert placed after that character comes out plain.
import * as Y from 'yjs';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.getText('t').insert(0, 'wv');
d1.getText('t').insert(2, 'b', { bold: true });
sync(d1, d2);
// concurrently:
d1.getText('t').delete(2, 1);                           // user 1 deletes the bold "b"
d2.getText('t').insert(3, 'z', { bold: true });         // user 2 types bold "z" after "b"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'wv' }, { insert: 'z', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(delete then insert, or insert then delete: both give this)');
process.exit(show(d1) === expected ? 0 : 1);
