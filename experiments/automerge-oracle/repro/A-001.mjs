// A-001: a concurrent insert at a non-expanding mark boundary is covered by
// the mark or not according to operation counters, not the expand policy.
// User 1 deletes "x" (which raises the counter) and bolds "a" with a
// non-expanding start; user 2 concurrently types "h" before "a". Peritext's
// rule: an inserted character inherits the formatting of the character
// before it, so "h" is plain. The control without the delete shows that.
import * as A from '@automerge/automerge';
const show = (d) => JSON.stringify(A.spans(d, ['t']));
const run = (withDelete) => {
  let d1 = A.from({ t: '' }, { actor: 'aaaa' });
  d1 = A.change(d1, (doc) => { A.splice(doc, ['t'], 0, 0, 'ax'); });
  let d2 = A.clone(d1, { actor: 'bbbb' });
  d1 = A.change(d1, (doc) => {
    if (withDelete) A.splice(doc, ['t'], 1, 1);                                  // delete x
    A.mark(doc, ['t'], { start: 0, end: 1, expand: 'after' }, 'bold', true);    // bold a; start does not expand
  });
  d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], 0, 0, 'h'); });             // concurrently type h before a
  const m1 = show(A.merge(A.clone(d1), d2)), m2 = show(A.merge(A.clone(d2), d1));
  return m1 === m2 ? m1 : `${m1} / ${m2}`;
};
const observed = run(true), control = run(false);
console.log('observed (with the delete)   ', observed);
console.log('control  (without the delete)', control);
console.log('expected in both: h plain, a bold');
const hBold = (v) => /"value":"ha","marks":\{"bold":true\}|"value":"h","marks":\{"bold":true\}/.test(v);
process.exit(hBold(observed) && !hBold(control) ? 1 : 0);
