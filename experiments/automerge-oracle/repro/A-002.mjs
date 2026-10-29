// A-002: one replica, no concurrency. Type a bold "q", link it, delete it,
// then type "i" into the now empty text: "i" comes out bold. Without the
// link it is plain. The link's non-expanding end is the sticky boundary
// that places the new character inside the deleted bold span.
import * as A from '@automerge/automerge';
const show = (d) => JSON.stringify(A.spans(d, ['t']));
const run = (withLink) => {
  let d = A.from({ t: '' }, { actor: 'aaaa' });
  d = A.change(d, (doc) => { A.splice(doc, ['t'], 0, 0, 'q'); A.mark(doc, ['t'], { start: 0, end: 1, expand: 'after' }, 'bold', true); });
  if (withLink) d = A.change(d, (doc) => { A.mark(doc, ['t'], { start: 0, end: 1, expand: 'none' }, 'link', 'u'); });
  d = A.change(d, (doc) => { A.splice(doc, ['t'], 0, 1); });      // delete q: the text is empty
  d = A.change(d, (doc) => { A.splice(doc, ['t'], 0, 0, 'i'); }); // type i into the empty text
  return show(d);
};
const observed = run(true), control = run(false);
console.log('observed (with the link)   ', observed);
console.log('control  (without the link)', control);
console.log('expected in both: i plain');
process.exit(/bold/.test(observed) && !/bold/.test(control) ? 1 : 0);
