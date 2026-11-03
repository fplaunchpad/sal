// NT-2: concurrent insertions are ordered as RGA siblings, by id, not by
// their right neighbours. s1 types "c" then "f" at 0 (f's right neighbour
// is c); s2, concurrently, types "x" into an empty block. Ids are
// [session, Lamport counter]: c s1:1, f s1:2, x s2:1. Every replica shows
// f x c, so x separates f from the character it was typed before.
// Control: s2 receives c before typing x (x becomes s2:2): x f c.
import { created, issue, show, expect, done, block } from './common.mjs';

function run(xSeesC) {
  const a = created('s1');
  const b = created('s2');
  const c = issue(a, a.prepareInsert(block, 0, 'c'));
  if (xSeesC) b.apply(c);
  const f = issue(a, a.prepareInsert(block, 0, 'f'));
  const x = issue(b, b.prepareInsert(block, 0, 'x'));
  if (!xSeesC) b.apply(c);
  b.apply(f);
  a.apply(x);
  return [show(a), show(b)];
}

const [a1, b1] = run(false);
expect('concurrent head inserts, s1', a1, 'fxc');
expect('concurrent head inserts, s2', b1, 'fxc');
const [a2, b2] = run(true);
expect('control: x typed after c arrived, s1', a2, 'xfc');
expect('control: x typed after c arrived, s2', b2, 'xfc');
done();
