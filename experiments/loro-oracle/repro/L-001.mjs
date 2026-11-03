// L-001: a character typed concurrently at a mark boundary takes the mark
// or not according to peer id, whatever the expand setting. User 1 bolds
// "a" (expand after: text typed before it should not be bold); user 2
// concurrently types "h" before "a". Shown with the peer ids both ways.
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (p1, p2) => {
  const d1 = new LoroDoc(); d1.setPeerId(p1); d1.configTextStyle({ bold: { expand: 'after' } });
  d1.getText('t').insert(0, 'a'); d1.commit();
  const d2 = new LoroDoc(); d2.setPeerId(p2); d2.configTextStyle({ bold: { expand: 'after' } });
  d2.import(d1.export({ mode: 'snapshot' }));
  d1.getText('t').mark({ start: 0, end: 1 }, 'bold', true); d1.commit();   // user 1 bolds a
  d2.getText('t').insert(0, 'h'); d2.commit();                              // user 2 types h before a
  const u1 = d1.export({ mode: 'update', from: d2.oplogVersion() }), u2 = d2.export({ mode: 'update', from: d1.oplogVersion() });
  d1.import(u2); d2.import(u1);
  return show(d1) === show(d2) ? show(d1) : `${show(d1)} / ${show(d2)}`;
};
const a = run(1, 2), b = run(2, 1);
console.log('peers 1,2:', a); console.log('peers 2,1:', b);
console.log('expected either way: h plain, a bold');
const hBold = (v) => /"insert":"h(a)?","attributes":\{"bold":true\}/.test(v);
process.exit(hBold(a) || hBold(b) ? 1 : 0);
