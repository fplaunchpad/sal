// L-003: single replica. Link "abc" (expand none), unlink "b", type "X" at
// index 1, the left edge of the hole: "X" comes out linked, though a link
// expands in neither direction. The control with bold (expand after) is as
// expected: "X" bold.
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (key, expand) => {
  const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ [key]: { expand } });
  const t = d.getText('t');
  t.insert(0, 'abc'); d.commit();
  t.mark({ start: 0, end: 3 }, key, true); d.commit();
  t.unmark({ start: 1, end: 2 }, key); d.commit();
  t.insert(1, 'X'); d.commit();
  return show(d);
};
const observed = run('link', 'none'), control = run('bold', 'after');
console.log('observed (link, expand none)', observed);
console.log('control  (bold, expand after)', control);
console.log('expected: X plain for the link; X bold for the bold');
process.exit(/"insert":"aX","attributes":\{"link"|"insert":"X","attributes":\{"link"/.test(observed) ? 1 : 0);
