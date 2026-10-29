// Y-004: a format spreads over a character concurrently inserted at its
// left boundary (the shape of issue #385).
import * as Y from 'yjs';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.getText('t').insert(0, 'a');
sync(d1, d2);
// concurrently:
d1.getText('t').format(0, 1, { italic: true });         // user 1 italicises "a"
d2.getText('t').insert(0, 'h');                         // user 2 types plain "h" before "a"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'h' }, { insert: 'a', attributes: { italic: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(user 2 never formatted "h"; both orders give this)');
process.exit(show(d1) === expected ? 0 : 1);
