// P-3 (outside the delivery contract): an insertion that arrives before the
// insertion of its origin is preceded by a backfill of the items its
// operation lists in prevItems, with their content, deletion flag and
// annotation operations; the origin's own insertion, arriving later, is
// recognised as already applied. The two replicas converge.
// s1 types "ab", bolds b, deletes a and types "z" after b; s2 receives only
// the last insertion, then the rest in order.
// Control: s3 receives everything in order.
import { created, issue, show, expect, done, block } from './common.mjs';

const a = created('s1');
const ops = [
  issue(a, a.prepareInsert(block, 0, 'ab')),
  issue(a, a.prepareBold(block, 1, 2, true)),
  issue(a, a.prepareDelete(block, 0, 1)),
];
const z = issue(a, a.prepareInsert(block, 1, 'z'));

const b = created('s2');
b.apply(z);
expect('s2 after the backfilled insertion alone', show(b), 'b*z*');
for (const o of ops) b.apply(o);
expect('s2 after the rest', show(b), 'b*z*');
expect('s1', show(a), 'b*z*');
const c = created('s3');
for (const o of [...ops, z]) c.apply(o);
expect('control: causal order', show(c), 'b*z*');
done();
