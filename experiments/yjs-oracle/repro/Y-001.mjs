// Y-001: an insert that relies on an existing bold opener loses its bold when
// a concurrent unbold of a different range deletes that opener's closer.
import * as Y from 'yjs';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.getText('t').insert(0, 'et', { bold: true });
sync(d1, d2);
// concurrently:
d1.getText('t').insert(2, 'd', { bold: true });        // user 1 types bold "d" after "et"
d2.getText('t').format(0, 2, { bold: null });           // user 2 unbolds "et"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'et' }, { insert: 'd', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(unbold then insert, or insert then unbold: both give this)');
process.exit(show(d1) === expected ? 0 : 1);
