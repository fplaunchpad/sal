// L-004: single replica. Link "a" and link "b" separately with one value,
// so the display shows one link over "ab"; type "X" at 1: "X" is not
// linked. The control, one link over "ab", gives a linked "X".
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (split) => {
  const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ link: { expand: 'none' } });
  const t = d.getText('t');
  t.insert(0, 'ab'); d.commit();
  if (split) { t.mark({ start: 0, end: 1 }, 'link', 'u'); t.mark({ start: 1, end: 2 }, 'link', 'u'); } else t.mark({ start: 0, end: 2 }, 'link', 'u');
  d.commit();
  const before = show(d);
  t.insert(1, 'X'); d.commit();
  return [before, show(d)];
};
const [b1, observed] = run(true), [b2, control] = run(false);
console.log('display before, split marks:', b1); console.log('display before, one mark:  ', b2);
console.log('observed (two marks, one value)', observed);
console.log('control  (one mark)             ', control);
console.log('expected in both: X linked, since both neighbours are');
process.exit(/"insert":"X"\}|"insert":"X","attributes":\{\}/.test(observed) && b1 === b2 ? 1 : 0);
