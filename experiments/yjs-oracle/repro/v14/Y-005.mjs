// Y-005: two concurrent bolds of overlapping ranges leave the last character
// plain (the shape of issue #382).
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'abc');
sync(d1, d2);
// concurrently:
d1.get('t').format(0, 2, { bold: true });           // user 1 bolds "ab"
d2.get('t').format(1, 2, { bold: true });           // user 2 bolds "bc"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'abc', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(both orders bold all three)');
process.exit(show(d1) === expected ? 0 : 1);
