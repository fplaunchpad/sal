// NT-1: a typed character takes the bold of its left neighbour.
// A single replica: "d", bold it, type "e" after it. The positional request
// semantics inserts plain text (d* e); the shipped code shows d* e*.
// Control: type "e" before d, where it is plain under both meanings.
import { created, issue, show, expect, done, block } from './common.mjs';

const a = created('s1');
issue(a, a.prepareInsert(block, 0, 'd'));
issue(a, a.prepareBold(block, 0, 1, true));
issue(a, a.prepareInsert(block, 1, 'e'));
expect('type after a bold character', show(a), 'd*e*');

const c = created('s1');
issue(c, c.prepareInsert(block, 0, 'd'));
issue(c, c.prepareBold(block, 0, 1, true));
issue(c, c.prepareInsert(block, 0, 'e'));
expect('control: type before it', show(c), 'ed*');
done();
