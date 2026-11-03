// L-002: single replica, no concurrency. Highlight "ab", remove the
// highlight (expand both), type "X" at 0: "X" comes out highlighted.
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ hl: { expand: 'both' } });
const t = d.getText('t');
t.insert(0, 'ab'); d.commit();
t.mark({ start: 0, end: 2 }, 'hl', true); d.commit();
t.unmark({ start: 0, end: 2 }, 'hl'); d.commit();
t.insert(0, 'X'); d.commit();
console.log('observed', show(d));
console.log('expected', JSON.stringify([{ insert: 'Xab' }]), '(nothing is highlighted any more)');
process.exit(/hl/.test(show(d)) ? 1 : 0);
