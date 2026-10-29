# Upstream drafts for automerge/automerge

Two issues, posted from KC's account on 2026-10-29: issue A is
automerge/automerge#1649, issue B is automerge/automerge#1650. Scripts are
the ones in this directory; each exits non-zero when the defect shows and
the control does not.

---

## Issue A

**Title:** Expand policy ignored for concurrent inserts at a mark boundary

**Describe the bug**

Whether a character inserted concurrently at the boundary of a mark ends up inside the mark depends on operation counters, not on the mark's expand policy. The same two operations give different documents depending on which replica happens to have the larger counter, and the control that differs only in a counter is correct.

Two shapes.

Shape 1, a non-expanding start. User 1 deletes `x` from `ax` (which raises their counter) and bolds `a` with `expand: 'after'`, so the start does not expand. User 2 concurrently types `h` before `a`. After merging, both replicas show `h` bold. Without the delete, `h` is plain.

```js
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
```

Output on 3.5.0:

```
observed (with the delete)    [{"type":"text","value":"ha","marks":{"bold":true}}]
control  (without the delete) [{"type":"text","value":"h"},{"type":"text","value":"a","marks":{"bold":true}},{"type":"text","value":"x"}]
```

Shape 2, a non-expanding end. User 1 links `ab` with `expand: 'none'`. User 2, who has an undelivered earlier insert `z` (which raises their counter), concurrently types `x` after `b`. After merging, `x` is inside the link. Without `z`, it is outside.

```js
import * as A from '@automerge/automerge';
const show = (d) => JSON.stringify(A.spans(d, ['t']));
const run = (withZ) => {
  let d1 = A.from({ t: '' }, { actor: 'aaaa' });
  d1 = A.change(d1, (doc) => { A.splice(doc, ['t'], 0, 0, 'ab'); });
  let d2 = A.clone(d1, { actor: 'bbbb' });
  if (withZ) d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], 0, 0, 'z'); });   // z raises user 2's counter; not yet delivered
  const off = withZ ? 1 : 0;
  d1 = A.change(d1, (doc) => { A.mark(doc, ['t'], { start: 0, end: 2, expand: 'none' }, 'link', 'u'); }); // link ab, no expansion
  d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], off + 2, 0, 'x'); });        // concurrently type x after b
  const m1 = show(A.merge(A.clone(d1), d2)), m2 = show(A.merge(A.clone(d2), d1));
  return m1 === m2 ? m1 : `${m1} / ${m2}`;
};
const observed = run(true), control = run(false);
console.log('observed (with z)   ', observed);
console.log('control  (without z)', control);
console.log('expected in both: x outside the link');
const xLinked = (v) => /"value":"[a-z]*x","marks":\{"link":"u"\}/.test(v);
process.exit(xLinked(observed) && !xLinked(control) ? 1 : 0);
```

Output on 3.5.0:

```
observed (with z)    [{"type":"text","value":"z"},{"type":"text","value":"abx","marks":{"link":"u"}}]
control  (without z) [{"type":"text","value":"ab","marks":{"link":"u"}},{"type":"text","value":"x"}]
```

**Expected behavior**

The documentation says expand "allows you to decide whether new text inserted at the start/end of your mark should also inherit the mark" and points to the Peritext essay for the rule, which is that "an inserted character inherits the bold/non-bold status of the preceding character", with anchors that are positions in the document. Under that rule `h` before a non-expanding bold is plain and `x` after a non-expanding link is outside it, whoever inserted them and whenever. Both shapes also fail the weaker requirement that the merged document equal the result of applying the two concurrent operations in one of the two orders: in each shape both orders give the control's document.

If expand is meant to be a rule for the local cursor only, so that concurrent inserts at a boundary are placed by operation order, I would like to know, since then the documented semantics is narrower than Peritext's and worth stating.

**Where it happens**

`TransactionInner::mark` (`rust/automerge/src/transaction/inner.rs`) writes a mark as two insert operations, `MarkBegin(expand.before())` and `MarkEnd(expand.after())`, list elements like characters. Remote integration (`op_set2/change/batch.rs`, the untangler) orders an insert after its reference among its siblings by operation id, and the expand flags take no part in that. They are read only when a replica places its own insert (`op_set2/op_set.rs`, `scan_for_sticky_marks`; `op_set2/op_set/insert.rs`, `identify_valid_insertion_spot`). So a concurrent insert into the gap at a boundary lands inside or outside according to which operation has the larger counter.

**Environment**

* `@automerge/automerge` 3.5.0 (release commit 4d2a8f6), Node 26.3.1, macOS

**How this was found**

While checking Automerge text with marks against a sequential specification of formatted text, as part of a verification project on replicated data types at IIT Madras (FP Launchpad). The shapes come from a property-based testing harness, were minimised, and were checked by hand against the Rust source; the harness was built with AI assistance. For comparison, Automerge passes every concurrent formatting shape on which Yjs fails (yjs/yjs#828); this boundary case is the one place the two differ in Automerge's disfavour.

---

## Issue B

**Title:** Insert after deleting a bold, linked character comes out bold

**Describe the bug**

Single replica, no concurrency. Type `q`, bold it, link it, delete it, then type `i` into the now empty text: `i` comes out bold. Without the link, `i` is plain.

```js
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
```

Output on 3.5.0:

```
observed (with the link)    [{"type":"text","value":"i","marks":{"bold":true}}]
control  (without the link) [{"type":"text","value":"i"}]
```

**Expected behavior**

`i` plain in both cases: there is no visible text, and the only bold character was deleted.

**Where it happens**

A local insert is placed after the last sticky boundary between its displayed neighbours, a begin that expands before or an end that does not expand after (`op_set2/op_set/insert.rs`, `identify_valid_insertion_spot`; `op_set2/op_set.rs`, `scan_for_sticky_marks`). One insertion point serves every mark name. After deleting the bold, linked character, the link's non-expanding end sits beyond the tombstone, and the new character is placed after it, which is inside the bold's begin and end. Without the link there is no sticky boundary past the bold's end, and the character lands outside.

**Environment**

* `@automerge/automerge` 3.5.0 (release commit 4d2a8f6), Node 26.3.1, macOS

**How this was found**

As in the previous report: a property-based testing harness built for a verification project at IIT Madras (FP Launchpad), with the shape minimised and checked by hand against the source; the harness was built with AI assistance.
