// P-2 (outside the delivery contract): a bold that arrives before the
// insertion of its anchor character is refused with an error; the client
// keeps no record of it, so it takes effect only if the transport delivers
// it again after the insertion.
// Control: redelivering the refused bold after the insertion converges.
import { created, issue, show, expect, done, block } from './common.mjs';

const a = created('s1');
const insert = issue(a, a.prepareInsert(block, 0, 'a'));
const bold = issue(a, a.prepareBold(block, 0, 1, true));

const b = created('s2');
let message = 'none';
try {
  b.apply(bold);
} catch (e) {
  message = e.message;
}
expect('the early bold is refused', message, 'Unable to apply annotation operation due to start missing');
b.apply(insert);
expect('without redelivery', show(b), 'a');
expect('s1', show(a), 'a*');
b.apply(bold);
expect('control: redelivered after the insertion', show(b), 'a*');
done();
