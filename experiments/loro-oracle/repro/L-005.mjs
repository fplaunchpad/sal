// L-005: two replicas. User 1 bolds "y" (expand after) while user 2 makes
// it superscript (expand before); user 2's change reaches user 1, who then
// types "X" before "y": "X" should be superscript and not bold. With the
// peers as given it is neither; with the keys swapped it is superscript.
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const CONFIG = { bold: { expand: 'after' }, sup: { expand: 'before' } };
const run = (k1, k2) => {
  const d1 = new LoroDoc(); d1.setPeerId(1); d1.configTextStyle(CONFIG);
  d1.getText('t').insert(0, 'y'); d1.commit();
  const d2 = new LoroDoc(); d2.setPeerId(2); d2.configTextStyle(CONFIG);
  d2.import(d1.export({ mode: 'snapshot' }));
  d1.getText('t').mark({ start: 0, end: 1 }, k1, true); d1.commit();   // user 1
  d2.getText('t').mark({ start: 0, end: 1 }, k2, true); d2.commit();   // user 2, concurrently
  d1.import(d2.export({ mode: 'update', from: d1.oplogVersion() }));
  d1.getText('t').insert(0, 'X'); d1.commit();                          // user 1 types before y
  return show(d1);
};
const observed = run('bold', 'sup'), control = run('sup', 'bold');
console.log('observed (user 1 bold, user 2 sup)', observed);
console.log('control  (user 1 sup, user 2 bold)', control);
console.log('expected in both: X superscript, not bold');
process.exit(/"insert":"X"\}/.test(observed) && /"insert":"X","attributes":\{"sup":true\}/.test(control) ? 1 : 0);
