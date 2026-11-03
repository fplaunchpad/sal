// Y-002: two concurrent bolds, one nested in the other; the outer bold's
// opening marker is deleted as redundant by the cleanup pass, and the
// characters it alone covered come out plain.
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'au');
sync(d1, d2);
// concurrently:
d1.get('t').format(0, 2, { bold: true });           // user 1 bolds "au"
d2.get('t').format(0, 1, { bold: true });           // user 2 bolds "a"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'au', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(both orders bold both characters)');
process.exit(show(d1) === expected ? 0 : 1);
