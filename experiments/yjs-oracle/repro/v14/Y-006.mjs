// Y-006: the same delete on the same document gives different results on a
// replica that obtained the text type after loading the state (as a client
// loading from a server or store does) and on one that held it from the start.
// No concurrency is involved.
import * as Y from '@y/y';
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const src = new Y.Doc({ gc: false }); src.clientID = 1;
src.get('t').insert(0, 'abc');
src.get('t').format(0, 2, { bold: true });           // a b bold, c plain
const bytes = Y.encodeStateAsUpdate(src);

const created = new Y.Doc({ gc: false }); created.clientID = 2;
created.get('t');                                     // text type taken before the state arrives
Y.applyUpdate(created, bytes);
created.get('t').delete(1, 1);                        // delete "b"

const opened = new Y.Doc({ gc: false }); opened.clientID = 2;
Y.applyUpdate(opened, bytes);                             // state first
opened.get('t').delete(1, 1);                         // text type taken after, then delete "b"

const expected = JSON.stringify([{ insert: 'a', attributes: { bold: true } }, { insert: 'c' }]);
console.log('created', show(created));
console.log('opened ', show(opened));
console.log('expected', expected, '(deleting a plain-adjacent bold character changes nothing else)');
process.exit(show(created) === expected && show(opened) === expected ? 0 : 1);
