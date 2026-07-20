# A document-order read model for Peritext marks, and the leak the tree-ancestry read hides

Task #55, design and validation phase. Companion executable model:
`whiteboard/litmus/peritext_read_model.py` (imports the embed model, modifies
nothing existing). This note is self-contained.

## 1. What this settles

Peritext (Litt, Lim, Kleppmann, van Hardenberg, CSCW 2022) promises that rich
text formatting stays where the author put it: deleting a character never
reformats another, and a mark boundary tracks the reading position it was placed
at. The paper keeps this promise with tombstones (a deleted character stays in
place as a tombstone, so a boundary anchored to it never moves).

Our sequence CRDT is the tombstone-free embedded-chain RGA, so a deleted
character's position is physically gone. An earlier attempt recovered a mark
boundary by climbing the anchor's frozen recorded RGA path with the RGA's own
`resolve`, and a theorem `mark_*_no_leak` claimed this never leaks formatting.
That theorem was FALSE and has been retracted (see
`Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Composed/MarkIntent.lean`,
now carrying only the honest containment bound
`mark_*_within_recorded_ancestry`). The reason: `resolve` climbs TREE ancestry,
and a tree ancestor sits EARLIER in reading order than its descendants (a parent
precedes its children in the depth-first read). So when a boundary anchor is
deleted, the frozen-path boundary migrates BACKWARD in the document and formats
text that was never in the span.

This note builds the paper-faithful alternative, a DOCUMENT-ORDER read model
(a dead boundary anchor rehomes to the nearest SURVIVING neighbour in reading
order, on the side dictated by its gravity), validates it against the Litt
examples, exhibits the retracted leak concretely against it as a control, and
records the price the tombstone-free substrate charges (the mark-positioning
trilemma). The Python battery passes end to end; the exact statements for the
Lean phase are in section 8.

## 2. The document layer

Characters live in the embed-RGA reading order. The embed model
(`whiteboard/litmus/embed_tree.py`) has the property that makes a
document-order read well defined: a live read after deletes equals the immutable
BIRTH order filtered to survivors (property P3 there, coordinates are birth
constants, delete is an isometric fold that never re-decides an order). The
model keeps a no-delete shadow of every insert (the immutable birth order and
the birth parents) plus a `deleted` set; `live_order()` is the birth order minus
`deleted`. This is verified against the real embed delete-and-refold read in
`_selfcheck()` (P3 holds on the tested cases). The birth order and birth parents
are exactly the data a boundary needs to rehome and (for the control) to climb.

## 3. The mark record and the two resolvers

A mark is immutable data:

```
Mark = (mid, mtype, value, op, start_id, end_id, startSide, endSide)
```

`mid` is the mark's creation timestamp (its opId, in the same Lamport space as
character ids). `op` is `add` or `remove` (removeMark); for a given character
and `mtype` the covering mark with the highest `mid` wins (last writer wins,
paper section 4.4), an `add` formats and a `remove` does not. `start_id` and
`end_id` are the boundary anchor character ids; `startSide` and `endSide` are the
gravity bits (section 4).

Both resolvers take the SAME record and return the covered character set.

**Document-order resolver (paper-faithful).** Resolve each boundary to a
position in the CURRENT live reading order. If the anchor character is dead,
rehome to the nearest SURVIVING neighbour in birth order on the gravity side:

* start `before` (inner, the first span character): scan RIGHT into the span.
* start `after` (outer, the character before the span): scan LEFT.
* end `after` (inner, the last span character): scan LEFT into the span.
* end `before` (outer, the character after the span): scan RIGHT.

If the scan finds no survivor on that side the span collapses (empty) or pins to
the document edge, as appropriate. The rehome target is always a nearest
survivor, so a single-replica rehome can only shrink or hold a span, never
migrate it backward over unrelated text.

**Tree-ancestry resolver (the retracted control).** Each boundary carries the
FROZEN recorded RGA ancestor path (anchor, birth parent, grandparent, ..., root)
snapshotted at mark issue. Resolution climbs that path to the nearest live
ancestor. Coverage is the plain inclusive interval between the two resolved
anchors. Side bits are ignored (the frozen-path design had no positional
gravity). This is the read whose no-leak claim was retracted.

The two resolvers AGREE while nothing on a boundary is deleted. They diverge
exactly when a boundary anchor dies: the document-order resolver rehomes
sideways to a surviving neighbour, the tree-ancestry resolver climbs backward to
a surviving ancestor.

## 4. startSide and endSide as gravity

The side bits are the expand versus no-expand behaviour, keyed to what happens to
text typed AT a boundary. A character is "newer than the mark" when its id
exceeds `mid` (the RGA opId tiebreak, so concurrent inserts at a boundary resolve
deterministically):

* end `after` (inner): GROWS right. The last covered index extends over the
  contiguous run of newer-than-mark characters immediately after the anchor. So
  typing at the end of a bold span extends the bold (Ex 7).
* end `before` (outer): does NOT grow. The last covered index steps back over
  the newer run just left of the anchor. So typing after a link is not part of
  the link (Ex 8).
* start `after` (outer): does NOT grow. The first covered index steps forward
  over the newer run just right of the anchor (a non-growing link start).
* start `before` (inner): STABLE. It includes exactly from the anchor character
  and does NOT grow left. Text typed before the first styled character is not
  retroactively formatted, which is the common editor convention and, decisively,
  avoids grabbing an unrelated newer sibling that merely happens to read to the
  left. Growth is an end-side phenomenon in this model.

Bold uses `startSide=before, endSide=after` (inner anchors, grows at the end).
A link uses `startSide=after, endSide=before` (outer anchors, no growth).

## 5. The leak, made concrete

Chain `W, A, B, C` (each the sole child of the previous, so reading order is the
id order). Bold spans `[A, B]` with `startSide=before, endSide=after`. Delete
the start anchor `A`.

* Document-order: the start rehomes to the nearest surviving neighbour to the
  right, which is `B`. Bold renders as `{B}`. `W` stays plain.
  `[(W,false), (B,true), (C,false)]`.
* Tree-ancestry: `A`'s frozen path is `[A, W, root]`; `A` is dead so it climbs
  to `W`. Bold renders as `{W, B}`. `W`, which was never in the span, is now
  bold. `[(W,true), (B,true), (C,false)]`.

The skip-a-sibling variant: `W` has children `Q` (a plain sibling) and `A`, `A`
has child `B`, bold spans `[A, B]`, reading order `W, Q, A, B`. Delete `A`. The
document-order start rehomes to `B` and leaves `W` and `Q` plain. The
tree-ancestry read climbs `A` to `W`, so the span becomes `[W .. B]` and formats
BOTH `W` and the surviving sibling `Q`: the climb skips `Q` and leaks onto it.

This is the retracted `mark_*_no_leak` error exhibited on a concrete trace, and
it is exactly why tree ancestry is the wrong notion of position.

## 6. The Litt examples (subset tracked in `docs/peritext-vs-paper.md`)

Every rendering below is hand-derived and asserted in the Python (a bold view is
`[(codepoint, is-bold)]` in reading order; a set view lists mark types).

* **Ex 1, insertion within a span (section 3.1).** `a, c` bold, insert `b`
  between them. `b` is inside the interval, so it is bold:
  `[(a,true), (b,true), (c,true)]`. Both resolvers agree (no deletion). Pinned
  against the degenerate reading where the inserted character stays plain.
* **Ex 2, overlapping bold and italic (section 3.2).** `bold[a,c]`,
  `italic[b,d]`. The overlap carries both:
  `a={bold}, b={bold,italic}, c={bold,italic}, d={italic}`.
* **Ex 3, mark then delete the whole span then reinsert.** Bold `[a,c]`, delete
  `a, b, c`, reinsert `d`. Document-order: the span collapses (both boundaries
  find no survivor inside), so the fresh text is plain, `[(d,false)]`. This is
  the paper's behaviour. Tree-ancestry LEAKS: both boundaries climb to the dead
  root, the span becomes the whole document, and the brand-new `d` renders bold,
  `[(d,true)]`. A clean example where the paper differs and the control leaks.
* **Ex 5, concurrent add versus removeMark (section 3.2.1).** Resolved last
  writer wins by `mid`. Remove wins (`mid` 20 over add `mid` 10):
  `[(a,false), (b,false)]`. Add wins (`mid` 20 over remove `mid` 10):
  `[(a,true), (b,true)]`.
* **Ex 7, bold boundary insertion expands (section 3.3).** Bold `[a,b]`,
  `endSide=after`, type `x` after `b` with `x` newer than the mark:
  `[(a,true), (b,true), (x,true)]`. A concurrent insert OLDER than the mark at
  the same boundary is not grabbed: `[(a,true), (b,true), (x,false)]` (the mark
  wins the opId tiebreak).
* **Ex 8, link boundary insertion does not expand (section 3.3).** Same
  document and same typed `x`. Link `endSide=before` (anchored to the character
  after the link): `[(a,true), (b,true), (x,false), (z,false)]`. Bold
  `endSide=after` on the same insertion DOES grab `x`:
  `[(a,true), (b,true), (x,true), (z,false)]`. The directed gravity contrast.

Ex 4 and Ex 6 (per-value colours and comments-by-distinct-type) are unchanged
from `docs/peritext-vs-paper.md`: Ex 6 reduces to distinct `mtype` coexistence
(Ex 2 machinery), and Ex 4 needs a per-mark value (present here as the `value`
field, though the directed battery does not exercise the colour LWW separately).

## 7. The trilemma and the atomicity cost

The three properties {tombstone-free, no backward leak, atomicity of formatting
under unrelated edits} cannot all hold; this read model keeps the first two and
pays the third, observably.

Concrete witness (single replica, no concurrency). Bold spans `[A, B]` with
`endSide=after`. A character `C` OLDER than the mark sits right after `B` and
blocks the growth run; a character `D` NEWER than the mark is a child of `C`, so
it reads after `C` and is plain. Render: `A, B` bold, `C, D` plain. Now delete
the plain `C`. `D` becomes the character immediately after `B` in the live
reading order, and the `endSide=after` growth run now reaches it, so `D` is
re-formatted to bold. The delete touched neither `D` nor any boundary.

`[(A,true), (B,true), (C,false), (D,false)]` becomes
`[(A,true), (B,true), (D,true)]`.

This is not a leak of the retracted kind (no boundary migrated backward); it is a
membership re-span caused by losing the deleted character's separating position.
It is the exact analogue of the fused embed model's inherited residual
`fused_delete_moves_char_into_span`
(`Peritext_Rehoming/Peritext_Read.lean` section 10) and of
`del_can_reorder_survivors`: the tombstone-free substrate cannot keep `C`
between `B` and `D`, so a tombstoned Peritext (which would keep `C` as a
tombstone and break the run) renders `D` plain here while this model renders it
bold.

Is it observable in an Ex? Not in Ex 1, 2, 3, 5, 7, 8 as stated (their deletes
either remove whole spans or touch no separating character). It is a distinct
directed witness, and it surfaces in the randomized battery (section below) as
the over-format divergences. Honest verdict: the document-order model is
paper-faithful on the no-backward-leak intent and on convergence, and it pays
atomicity on interior deletes, precisely the trilemma horn the fused design also
pays.

Randomized battery (400 executions of mixed insert, delete, addMark, removeMark
over bold and italic, compared to a naive eager oracle that stamps marks onto
characters at addMark time and inherits from the left on insert):

* Delete-free runs: all 23 of 23 agree with the naive oracle. Absent deletion
  the document-order read IS the naive marked-text semantics.
* With-delete runs: 367 of 377 agree. Of the 10 divergences, 7 are the trilemma
  atomicity re-span (the document-order read over-formats, as above), and 3 are
  cases where the document-order read correctly DROPS a mark that the naive
  oracle staleley retains (an anchor died and the span collapsed or rehomed, and
  the eager stamp was never revised). No divergence is a backward leak.
* Convergence: 0 of 400 mark-permutation failures. The read is a pure function
  of the live character set and the mark set, so replicas that reach the same
  event set by different merge orders render identically (mark sets union,
  removeMark is last writer wins, character order converges by the embed
  capstone `embed_ra_linearizable3`).

## 8. Exact intent-theorem statements for the Lean phase

The Lean phase adds a document-order resolver `resolveMarkDoc` and its render
`renderMarksDoc` beside the existing frozen-path `resolveMark`
(`Peritext_Composed/`), then discharges the following. Each concrete statement is
a `native_decide` SPOT on a `do_` or `eUpdate` trace; each general statement is a
kernel theorem. Notation: `⟦render⟧` is the bold-or-typed view
`(id, codepoint, isFormatted)` in reading order.

Concrete (per example, PASS shaped, expected values from section 6):

* `ex1_doc`: `renderMarksDoc (ins b within [a,c]) [bold a c] = [(a,T),(b,T),(c,T)]`.
* `ex2_doc`: `renderMarksDoc chan [bold a c, italic b d]` gives
  `a↦{bold}, b↦{bold,italic}, c↦{bold,italic}, d↦{italic}`.
* `ex3_doc`: `renderMarksDoc (del a,b,c ; ins d) [bold a c] = [(d,F)]`,
  and the LEAK COMPANION `ex3_tree`:
  `renderMarksTree (del a,b,c ; ins d) [bold a c] = [(d,T)]`,
  with `ex3_doc ≠ ex3_tree` (the retracted read formats fresh text).
* `ex5_doc`: remove-wins gives `[(a,F),(b,F)]`, add-wins gives `[(a,T),(b,T)]`.
* `ex7_doc`: `renderMarksDoc (type x after b) [bold a b (endAfter)] =
  [(a,T),(b,T),(x,T)]`; older-insert variant gives `x↦F`.
* `ex8_doc`: link view `[(a,T),(b,T),(x,F),(z,F)]` and bold view
  `[(a,T),(b,T),(x,T),(z,F)]` on the same insertion.

The leak refuted (the replacement for the retracted `mark_*_no_leak`):

* `leak_doc_shrinks` (concrete): with the chain `W,A,B,C` and `bold[A,B]`, after
  `del A`, `renderMarksDoc = [(W,F),(B,T),(C,F)]` and
  `renderMarksTree = [(W,T),(B,T),(C,F)]`, and the two differ on `W`. The
  document-order read does not format `W`; the frozen-path read does.
* `doc_no_backward_leak` (general, the intended positive theorem): for any state
  and any mark, every character formatted by the mark's document-order coverage
  lies at or after the mark's rehomed start position in the current reading
  order. Equivalently, a character strictly before the rehomed start boundary
  carries no activation of that mark. This is the document-order analogue of
  `render_span_before` in `Peritext_Rehoming/Peritext_Read.lean` and is provable
  by the same open-set decomposition, now with the boundary a rehomed live
  position rather than a boundary node.
* `tree_backward_leak_refutes_noleak` (general negative, on the control): there
  exists a reachable state and a mark whose frozen-path coverage formats a
  character positioned before the mark's surviving span, so the retracted
  `mark_*_no_leak` is refuted by the `leak_doc_shrinks` witness lifted to the
  resolver level.

The atomicity cost stated honestly (so no future no-atomicity claim is made):

* `doc_delete_can_respan` (concrete, the trilemma witness of section 7):
  `renderMarksDoc (del C) [bold A B (endAfter)] ≠
  (renderMarksDoc [bold A B]) filtered to remove C`, i.e. deleting the plain
  separating `C` re-formats the untouched survivor `D`. This is the
  document-order analogue of `fused_delete_reformats_survivor`, and its presence
  is the model's declared trilemma horn.

Convergence (transported, not re-proved):

* `renderMarksDoc_convergent`: `≈`-converged states render the same rich text,
  since `renderMarksDoc` is a function of `document s ids` (converges by
  `document_convergent`) and the mark set (converges by union plus LWW). This is
  the read-side analogue of `renderRichText_convergent`.

## 9. Lean-readiness verdict

The design is Lean-ready. No example forces a model change. The document-order
resolver is a small function over the existing embed read (`document` and the
birth order), the render reuses the open-set fold already in
`Peritext_Rehoming/Peritext_Read.lean`, the leak refutation is a concrete SPOT
plus one general no-backward-leak theorem shaped exactly like `render_span_before`,
and the atomicity cost is stated as an explicit witness rather than hidden. The
one design decision to record is that growth is an end-side phenomenon (a
`before` start is stable), which is what keeps the read equal to the naive
marked-text semantics absent deletion and avoids the unrelated-sibling over-grab;
if a growing start is later wanted it needs a befores relation the RGA does not
give directly, and it should be added as a separate, tested behaviour rather than
folded into the start `before` case.

## 10. How to run

```
cd whiteboard/litmus
python3 peritext_read_model.py        # examples, gravity, leak, trilemma, PBT
python3 peritext_read_model.py -v     # with the per-example detail lines
```

Exit code 0 means every directed check passed, the delete-free PBT agreed with
the oracle on all runs, and convergence had zero failures.
