// P-4 (outside the delivery contract, in the shipped out-of-order path): a
// backfill can hold the first part of a multi-character insertion only, and
// the insertion itself, arriving later, is then judged already applied, so
// the rest of its text is never inserted.
// s2 types "hw" (ids s2:1, s2:2), then "j" after h, which splits the item
// "hw" into h | w, then "x" after h. The insertion of x lists its origin
// chain in prevItems: the item h alone. s1 receives the insertion of x
// first: h is backfilled, x is inserted. The insertion of "hw" then
// arrives: an item starting with s2:1 and the same origin exists, the
// operation is reported as likely already applied and dropped without an
// error, and w (s2:2) is lost on s1. s2 shows h x j w, s1 h x j.
// Control: without "j" no split precedes x, prevItems lists "hw" whole, and
// both replicas show h x w.
import { created, issue, show, expect, done, block } from './common.mjs';

function run(withJ) {
  const a = created('s1');
  const b = created('s2');
  const ops = [issue(b, b.prepareInsert(block, 0, 'hw'))];
  if (withJ) ops.push(issue(b, b.prepareInsert(block, 1, 'j')));
  const x = issue(b, b.prepareInsert(block, 1, 'x'));
  a.apply(x);
  for (const o of ops) a.apply(o);
  return [show(a), show(b), x[0].args.prevItems.map((p) => (p.type === 'text' ? `${p.id.join(':')}+${p.length}` : p.type)).join(' ')];
}

const [a1, b1, prev1] = run(true);
expect('prevItems of x after the split', prev1, 's2:1+1 start');
expect('s2', b1, 'hxjw');
expect('s1, the insertion of x first', a1, 'hxj');
const [a2, b2, prev2] = run(false);
expect('control: prevItems of x without the split', prev2, 's2:1+2 start');
expect('control: s2', b2, 'hxw');
expect('control: s1, the insertion of x first', a2, 'hxw');
done();
