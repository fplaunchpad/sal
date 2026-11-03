// A-001 at a non-expanding end: a link grows over text another user types
// concurrently after its last character, when that user's insert has the
// larger counter (raised here by an earlier, still undelivered insert "z").
// The control without "z" shows "x" outside the link.
import * as A from '@automerge/automerge';
const show = (d) => JSON.stringify(A.spans(d, ['t']));
const run = (withZ) => {
  let d1 = A.from({ t: '' }, { actor: 'aaaa' });
  d1 = A.change(d1, (doc) => { A.splice(doc, ['t'], 0, 0, 'ab'); });
  let d2 = A.clone(d1, { actor: 'bbbb' });
  if (withZ) d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], 0, 0, 'z'); });   // z raises user 2's counter; not yet delivered
  const off = withZ ? 1 : 0;
  d1 = A.change(d1, (doc) => { A.mark(doc, ['t'], { start: 0, end: 2, expand: 'none' }, 'link', 'u'); }); // link ab, no expansion
  d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], off + 2, 0, 'x'); });        // concurrently type x after b
  const m1 = show(A.merge(A.clone(d1), d2)), m2 = show(A.merge(A.clone(d2), d1));
  return m1 === m2 ? m1 : `${m1} / ${m2}`;
};
const observed = run(true), control = run(false);
console.log('observed (with z)   ', observed);
console.log('control  (without z)', control);
console.log('expected in both: x outside the link');
const xLinked = (v) => /"value":"[a-z]*x","marks":\{"link":"u"\}/.test(v);
process.exit(xLinked(observed) && !xLinked(control) ? 1 : 0);
