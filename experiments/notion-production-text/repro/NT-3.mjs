// NT-3: a bold's end anchor sits before the item that follows the last
// selected character, so text placed into that gap concurrently is bold.
// "a" is shared; s1 bolds it while s2 types a plain "h" after it. Both show
// a* h*, whichever session bolds; a reading in which a bold covers exactly
// the characters selected and a typed character keeps the bold its typist
// saw expects a* h.
// Control: s2 types "h" before a: h a*.
import { created, issue, show, expect, done, block } from './common.mjs';

function run(bolder, typist, index) {
  const s = { s1: created('s1'), s2: created('s2') };
  const seed = issue(s.s1, s.s1.prepareInsert(block, 0, 'a'));
  s.s2.apply(seed);
  const b = issue(s[bolder], s[bolder].prepareBold(block, 0, 1, true));
  const t = issue(s[typist], s[typist].prepareInsert(block, index, 'h'));
  s[typist].apply(b);
  s[bolder].apply(t);
  return [show(s.s1), show(s.s2)];
}

for (const [bolder, typist] of [['s1', 's2'], ['s2', 's1']]) {
  const [x, y] = run(bolder, typist, 1);
  expect(`${bolder} bolds, ${typist} types after a (${bolder})`, x, 'a*h*');
  expect(`${bolder} bolds, ${typist} types after a (${typist})`, y, 'a*h*');
}
const [x, y] = run('s1', 's2', 0);
expect('control: s2 types before a (s1)', x, 'ha*');
expect('control: s2 types before a (s2)', y, 'ha*');
done();
