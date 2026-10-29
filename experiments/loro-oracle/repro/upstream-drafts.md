# Upstream drafts for loro-dev/loro

One comment and one issue, posted from KC's account on 2026-10-29: the
comment is on loro-dev/loro#1009, the issue is loro-dev/loro#1240. Scripts
are the ones in this directory; each exits non-zero when the defect shows
and the control does not.

---

## Comment on #1009

Still present on loro-crdt 1.17.1, and the absorption is not specific to expand-after starts: whether a concurrently typed character at a style boundary takes the style is decided by peer id, for every expand setting including `none`, and at either end. Minimal form, user 1 bolds `a` (expand after) while user 2 types `h` before it; swapping the two peer ids flips the result:

```js
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (p1, p2) => {
  const d1 = new LoroDoc(); d1.setPeerId(p1); d1.configTextStyle({ bold: { expand: 'after' } });
  d1.getText('t').insert(0, 'a'); d1.commit();
  const d2 = new LoroDoc(); d2.setPeerId(p2); d2.configTextStyle({ bold: { expand: 'after' } });
  d2.import(d1.export({ mode: 'snapshot' }));
  d1.getText('t').mark({ start: 0, end: 1 }, 'bold', true); d1.commit();   // user 1 bolds a
  d2.getText('t').insert(0, 'h'); d2.commit();                              // user 2 types h before a
  const u1 = d1.export({ mode: 'update', from: d2.oplogVersion() }), u2 = d2.export({ mode: 'update', from: d1.oplogVersion() });
  d1.import(u2); d2.import(u1);
  return show(d1) === show(d2) ? show(d1) : `${show(d1)} / ${show(d2)}`;
};
const a = run(1, 2), b = run(2, 1);
console.log('peers 1,2:', a); console.log('peers 2,1:', b);
console.log('expected either way: h plain, a bold');
const hBold = (v) => /"insert":"h(a)?","attributes":\{"bold":true\}/.test(v);
process.exit(hBold(a) || hBold(b) ? 1 : 0);
```

Output on 1.17.1:

```
peers 1,2: [{"insert":"ha","attributes":{"bold":true}}]
peers 2,1: [{"insert":"h"},{"insert":"a","attributes":{"bold":true}}]
```

Cause: a style's start and end anchors are ordinary list elements (`diff_calc.rs`, `new_style_anchor`), and an anchor and a concurrent insert with the same neighbours are ordered by peer (`tracker/crdt_rope.rs`, the `other_elem.id.peer > content.id.peer` comparisons). The expand setting is consulted only when the typing replica places its own text (`richtext_state.rs`, `find_best_insert_pos`), which is why the local case in the report is right and the merged one is not. The `ExpandType` documentation says text inserted before a style that does not expand before "should **not** inherit this style", without restricting that to the local replica.

Found while checking Loro text against a sequential specification of styled text for a verification project on replicated data types at IIT Madras (FP Launchpad); the shape comes from a property-based testing harness, minimised and checked by hand against the source, with the harness built with AI assistance. The same class exists in Yjs (yjs/yjs#385) and Automerge (automerge/automerge#1649); of the concurrent formatting classes found in Yjs, this is the only one Loro shares.

---

## Issue

**Title:** Local insert takes styles from anchors no displayed character carries

**Describe the bug**

Four shapes, three of them on a single replica with no concurrency, in which a locally typed character gets styles that neither displayed neighbour has, or misses one both have. The common cause is how the insertion point is chosen among the style anchors between the two neighbours: one scan serves every style name, anchors of removed or deleted styles still count, and after an unmark the expand setting is reversed.

Shape 1, a style no displayed character carries. Highlight `ab` (expand both), remove the highlight, type `X` at 0: `X` is highlighted. The same with bold (expand after) is correct, and so is the variant where the only highlighted character is deleted and a character is typed into its place.

```js
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ hl: { expand: 'both' } });
const t = d.getText('t');
t.insert(0, 'ab'); d.commit();
t.mark({ start: 0, end: 2 }, 'hl', true); d.commit();
t.unmark({ start: 0, end: 2 }, 'hl'); d.commit();
t.insert(0, 'X'); d.commit();
console.log('observed', show(d));
console.log('expected', JSON.stringify([{ insert: 'Xab' }]), '(nothing is highlighted any more)');
process.exit(/hl/.test(show(d)) ? 1 : 0);
```

Output on 1.17.1:

```
observed [{"insert":"X","attributes":{"hl":true}},{"insert":"ab"}]
```

Shape 2, the left edge of an unstyled hole. Link `abc` (expand none), unlink `b`, type `X` at 1: `X` is linked, though a link expands in neither direction. With bold (expand after) the result is bold, as expected.

```js
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (key, expand) => {
  const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ [key]: { expand } });
  const t = d.getText('t');
  t.insert(0, 'abc'); d.commit();
  t.mark({ start: 0, end: 3 }, key, true); d.commit();
  t.unmark({ start: 1, end: 2 }, key); d.commit();
  t.insert(1, 'X'); d.commit();
  return show(d);
};
const observed = run('link', 'none'), control = run('bold', 'after');
console.log('observed (link, expand none)', observed);
console.log('control  (bold, expand after)', control);
console.log('expected: X plain for the link; X bold for the bold');
process.exit(/"insert":"aX","attributes":\{"link"|"insert":"X","attributes":\{"link"/.test(observed) ? 1 : 0);
```

Output on 1.17.1:

```
observed (link, expand none) [{"insert":"aX","attributes":{"link":true}},{"insert":"b"},{"insert":"c","attributes":{"link":true}}]
control  (bold, expand after) [{"insert":"aX","attributes":{"bold":true}},{"insert":"b"},{"insert":"c","attributes":{"bold":true}}]
```

Shape 3, two adjacent spans with one value. Link `a` and `b` separately with the same value, so the display is one link over `ab`; type `X` at 1: `X` is not linked. With one link over `ab`, it is. Two documents with the same display give different results for the same request.

```js
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const run = (split) => {
  const d = new LoroDoc(); d.setPeerId(1); d.configTextStyle({ link: { expand: 'none' } });
  const t = d.getText('t');
  t.insert(0, 'ab'); d.commit();
  if (split) { t.mark({ start: 0, end: 1 }, 'link', 'u'); t.mark({ start: 1, end: 2 }, 'link', 'u'); } else t.mark({ start: 0, end: 2 }, 'link', 'u');
  d.commit();
  const before = show(d);
  t.insert(1, 'X'); d.commit();
  return [before, show(d)];
};
const [b1, observed] = run(true), [b2, control] = run(false);
console.log('display before, split marks:', b1); console.log('display before, one mark:  ', b2);
console.log('observed (two marks, one value)', observed);
console.log('control  (one mark)             ', control);
console.log('expected in both: X linked, since both neighbours are');
process.exit(/"insert":"X"\}|"insert":"X","attributes":\{\}/.test(observed) && b1 === b2 ? 1 : 0);
```

Output on 1.17.1:

```
observed (two marks, one value) [{"insert":"a","attributes":{"link":"u"}},{"insert":"X"},{"insert":"b","attributes":{"link":"u"}}]
control  (one mark)             [{"insert":"aXb","attributes":{"link":"u"}}]
```

Shape 4, concurrent styles of two names at one boundary. User 1 bolds `y` (expand after) while user 2 makes it superscript (expand before). After receiving user 2's change, user 1 types `X` before `y`: `X` should be superscript and not bold. It is neither; with the two names swapped between the users it is superscript.

```js
import { LoroDoc } from 'loro-crdt';
const show = (doc) => JSON.stringify(doc.getText('t').toDelta());
const CONFIG = { bold: { expand: 'after' }, sup: { expand: 'before' } };
const run = (k1, k2) => {
  const d1 = new LoroDoc(); d1.setPeerId(1); d1.configTextStyle(CONFIG);
  d1.getText('t').insert(0, 'y'); d1.commit();
  const d2 = new LoroDoc(); d2.setPeerId(2); d2.configTextStyle(CONFIG);
  d2.import(d1.export({ mode: 'snapshot' }));
  d1.getText('t').mark({ start: 0, end: 1 }, k1, true); d1.commit();   // user 1
  d2.getText('t').mark({ start: 0, end: 1 }, k2, true); d2.commit();   // user 2, concurrently
  d1.import(d2.export({ mode: 'update', from: d1.oplogVersion() }));
  d1.getText('t').insert(0, 'X'); d1.commit();                          // user 1 types before y
  return show(d1);
};
const observed = run('bold', 'sup'), control = run('sup', 'bold');
console.log('observed (user 1 bold, user 2 sup)', observed);
console.log('control  (user 1 sup, user 2 bold)', control);
console.log('expected in both: X superscript, not bold');
process.exit(/"insert":"X"\}/.test(observed) && /"insert":"X","attributes":\{"sup":true\}/.test(control) ? 1 : 0);
```

Output on 1.17.1:

```
observed (user 1 bold, user 2 sup) [{"insert":"X"},{"insert":"y","attributes":{"bold":true,"sup":true}}]
control  (user 1 sup, user 2 bold) [{"insert":"X","attributes":{"sup":true}},{"insert":"y","attributes":{"bold":true,"sup":true}}]
```

**Expected behavior**

A typed character takes, for each style name, what the expand setting says given its two displayed neighbours: the style of the left neighbour if the style expands after, of the right neighbour if it expands before, and nothing from a style no displayed neighbour carries. That gives `X` plain in shape 1, plain in shape 2, linked in shape 3 and superscript only in shape 4. Two documents that display the same text with the same styles should give the same result for the same request (shape 3).

**Where it happens**

`find_best_insert_pos` (`container/richtext/richtext_state.rs`) walks the style anchors between the neighbours and stops at the last anchor whose style is sticky on that side. It does not distinguish anchors of styles that are still in effect from anchors of removed or deleted ones, and it uses one position for every style name, so a sticky anchor of one name carries the character past a non-sticky anchor of another (shapes 2 and 4), and two spans of one value leave a gap between the first's end anchor and the second's start that one span does not have (shape 3). An unmark is written as a style with the expand setting reversed (`ExpandType::reverse`, `container/richtext.rs`), so a removed both-expanding highlight leaves a non-expanding pair whose end anchor the scan passes, which puts the character back inside the original highlight's anchors (shape 1).

**Environment**

* `loro-crdt` 1.17.1, Node 26.3.1, macOS

**How this was found**

While checking Loro text against a sequential specification of styled text, as part of a verification project on replicated data types at IIT Madras (FP Launchpad). The shapes come from a property-based testing harness, were minimised, and were checked by hand against the Rust source; the harness was built with AI assistance. For what it is worth, Loro's list, delivery and convergence behaviour passed every check in the same runs: every change with missing dependencies is held back, deletes and unmarks included, and the Fugue list satisfies the strong list specification over 800 plain-text trials.
