// Y-007: an update that carries only a delete set (an unbold that removes
// markers) is applied as soon as the markers exist, before the insert it
// causally follows has arrived, and the replica shows a document that no
// causally closed set of operations produces. Yjs holds nothing pending.
import * as Y from '@y/y';
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const updates = [];
d1.on('update', (u) => updates.push(u));
d1.get('t').insert(0, 'a', { bold: true });          // u0: bold "a"
d1.get('t').insert(1, 'b');                          // u1: plain "b" after it
d1.get('t').format(0, 2, { bold: null });            // u2: unbold "ab" (deletes the two markers)

const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
Y.applyUpdate(d2, updates[0]);
Y.applyUpdate(d2, updates[2]);                           // u2 arrives before u1
console.log('received u0 and u2 only:', show(d2), 'pending structs:', d2.store.pendingStructs, 'pending ds:', d2.store.pendingDs);
console.log('every causally closed state: ', JSON.stringify([{ insert: 'a', attributes: { bold: true } }]), '(u0 alone),',
  JSON.stringify([{ insert: 'a', attributes: { bold: true } }, { insert: 'b' }]), '(u0 u1), or', JSON.stringify([{ insert: 'ab' }]), '(all three)');
const wrong = show(d2) === JSON.stringify([{ insert: 'a' }]);
Y.applyUpdate(d2, updates[1]);
console.log('after u1 arrives:', show(d2), '(converges)');
process.exit(wrong ? 1 : 0);
