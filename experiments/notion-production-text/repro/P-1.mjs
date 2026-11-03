// P-1 (outside the delivery contract): a deletion that arrives before the
// insertion it deletes is applied as a no-op and never takes effect.
// s1 types "a" and deletes it; s2 receives the deletion first, then the
// insertion. s1 shows nothing, s2 shows a, permanently: applying the
// deletion again is refused as nothing changes and no error is raised.
// Control: the same operations in causal order leave both empty.
import { created, issue, show, expect, done, block } from './common.mjs';

const a = created('s1');
const insert = issue(a, a.prepareInsert(block, 0, 'a'));
const remove = issue(a, a.prepareDelete(block, 0, 1));

const b = created('s2');
let threw = false;
try {
  b.apply(remove);
} catch {
  threw = true;
}
expect('the early deletion raises no error', String(threw), 'false');
b.apply(insert);
expect('s1 after both operations', show(a) || '(empty)', '(empty)');
expect('s2 after the same operations, deletion first', show(b) || '(empty)', 'a');

const c = created('s3');
c.apply(insert);
c.apply(remove);
expect('control: causal order', show(c) || '(empty)', '(empty)');
done();
