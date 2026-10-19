# A verifiable block merge for the Notion core

## Research question

The verified Notion core covers create, insert, erase and split. The demo's
merge-block request is outside it, and all five recorded demo bugs
([the bug catalogue](notion-bugs.md)) need that request. Two of them lose
text: a merge into a removed block hides the whole document (N-004), and a
merge whose move is skipped as a cycle still removes the block holding the
text (N-005).

Is there a block merge for the same slice-tree and RGA design whose
concurrent behaviour has a sequential meaning, so that the core theorem
extends to create, insert, erase, split and merge? If so, the demo's failures
should be exactly the proof obligations its merge does not meet.

## The demo's merge

`Replica.mergeBlock(block)` chooses the previous alive block as target,
reserves twenty unused clock ticks, then emits one transaction of three
operations: split the source's root slice at its start marker, move the right
part under the target's last slice (found by its end item), and remove the
source block. On replay, `#moveTextSlice` does not check that the block
holding the target slice is alive, and if the move would create a cycle it
restores the slice and continues; the removal runs regardless.

Three consequences, each the root of a recorded bug:

1. The split leaves an empty left slice in the removed block. Concurrent
   insertions at position zero of the source have ids above the split marker,
   sort before it, and stay in the removed block (hidden).
2. A target slice in a removed block accepts the moved subtree, which is then
   hidden (N-004).
3. Removal is independent of the move, so a skipped move still removes the
   block (N-005).

## The design

State is the core's: per-instance RGA tables, a slice forest, a display
order. One change of representation and one new operation.

**Liveness is derived.** A block is alive iff its root node has no parent.
There is no separate alive flag and no remove operation.

**Merge.** The request records what the demo records: the anchor, which is
the instance and end item of the target block's last slice at issue time.
`merge source anchor` moves the source block's whole tree, root included, to
become the last child of the last preorder node of the tree that holds the
slice ending at the anchor. If that slice is still in the target, that is the
target's own tree; if a concurrent split has carried it into a fresh block,
or the target has itself been merged away, it is the tree that holds it at
replay time, however many splits and merges later. The merge is a no-op when
the source is not alive, or when the tree holding the anchored slice is the
source's own tree, which is the only way a cycle could arise. The anchor
chooses the tree; the attachment point within it is determined at replay
time.

An earlier version of this design skipped any merge whose target was not
alive. The executable gate showed both rules conserve text and both agree
with their sequential specification on every archive seen; the liveness
check is a choice of meaning, not an obligation. Absorbing gives the
expected result when two adjacent merges are concurrent: `a · b · c` with `b` merged into `a` and `c` into `b` shows
`abc` whichever merge replays first, where skipping leaves `ab · c` in one
order.

Rendering is unchanged: a block's text is the preorder text of its tree, and
the display lists alive blocks in display order. A merged source's root slice
and all its descendants render inside the target.

Why each demo defect disappears:

1. The root is moved, so there is no left-over slice. A concurrent insertion
   at position zero of the source lands in the root slice, inside the moved
   tree.
2. A merge into a merged-away block attaches under a node that is itself
   rendered through its absorber, so the text stays visible.
3. Removal is the move. A skipped move removes nothing.

Defects 2 and 3 are one defect seen from two sides: in the demo, removal is
a separate operation from the move, so text can sit in a block that is
removed but not absorbed. Once removal is the move, nothing hides.

The cycle case is reachable with honest clients. After `S` is merged into
`T`, a split of `T` inside the absorbed part carries `S`'s root into a
fresh block `F`. A replica that has not yet seen the merge still shows `S`
alive and may merge `F` into it; on replay the holder of `S`'s root is `F`
itself. The design makes that merge a no-op and loses nothing. The demo's
version of the same no-op, with removal separate, is N-005.

The twenty-tick clock reservation is dropped; it only served the split at
the root's start.

**Targeting and placement are separate choices.** The demo attaches the
moved tree directly under the node that ends at the anchor. An earlier form
of this design ignored the anchor and attached under the last node of the
tree holding the target block's root. The three rules differ when a
concurrent split has moved the target's last slice: from `ab · cd`, merging
the second block into the first while the first is split after `a` gives
`a · bcd` under the demo's targeting and `acd · b` under root-following
(recorded in
[the gate](../experiments/notion-merge-design/results/review-target-placement.json)).
Neither loses text, and `a · bcd` is the result both sequential orders of
the two client requests give.

The gate separates the two choices. Slice-following, the demo's rule with
derived removal, gives `a · bcd` and loses no text, but two merges issued
concurrently into one target record the same anchor, and the anchored node
then has two children. Trees stop being chains, a split no longer moves the
whole displayed suffix, and the N-001 failure returns; the unmodified demo
fails the same split checks. So the demo has two independent defects:
removal separate from the move loses text, and attaching under the anchored
node lets trees branch. This design uses the anchor only to find the holder
tree and attaches at that tree's last node. On the gate's archives it agrees
with its flat slot specification everywhere, keeps every tree a chain,
conserves text and gives `a · bcd` in both orders.

**Every tree is a chain.** The core's split gives the right node all of the
old children and makes it the only child of the left node; the split's move
takes the suffix chain into the new block; merge attaches a chain under the
last node of a chain. So no node ever has two children, a block's text is the
concatenation of its chain's slices, and a split of a chain is exactly the
cut `cutAfter` performs in the specification. The core's shape invariant,
a lone root or a root with one leaf, becomes the chain invariant.

**Removed blocks keep their place in the display order.** A merged source
stays in the order as a tombstone and is filtered out of the display. A
create after a removed block, which is what a concurrent split of that block
emits, lands at the tombstone's position. The demo instead drops the entry
and sends such a block to the front.

**Erase spans instances.** After a merge a block's visible text comes from
several text instances. One erase request emits one erase operation per
instance in a single transaction, as the demo's `deleteText` does.

**Scope.** The extension targets the replay-based reference carrier
`NotionCoreMRDT`. The fact-set structural carrier and the runtime query keep
the no-merge fragment: the facts they retain record no merge, and a merge's
effect depends on which blocks are alive when it replays. A fact carrier
that recorded merges and folded them in id order is not ruled out.
The partition invariant's per-instance uniqueness of owners is dropped: a
block split and merged back owns two cells of one instance, and no proof
consumes that conjunct.

## Sequential specification

Positions are retained slots. Besides the root slot and the characters, a
block's slots hold two invisible kinds that mark where slices end: the close
of the slice that ends at a split marker, and the finish of an instance. A
created block is `[root, finish]`; a split at origin `o` with marker `m`
leaves `close m` at the end of the prefix block and puts `m :: suffix` in the
fresh block. The anchor of a merge is the address of such a slot.

`NotionCoreSpec.Command` gains `merge (source : Nat) (anchor : Address)`, and
blocks gain an `alive` flag and record their text instance. The holder is the
block whose slots contain the anchor; since close slots move with splits and
merges and tombstones hold no slots, the holder is the live block that holds
the end of the anchored slice at replay time. If the source is alive and the
holder exists and is not the source, the holder's slots become
`holder.slots ++ source.slots`, and the source keeps its place in the list
with no slots and `alive = false`. Otherwise the document is unchanged. The
view lists alive blocks only. A create after a block, alive or not, places
the fresh block after it. The source's root slot is invisible and keeps its
address, so slot addresses remain unique. The issuer's anchor is the last
slot of the target block it sees, which is always a close or finish slot.

The local positional meaning, for the issuer's next query after its own
merge: the target shows its old text followed by the source's old text, and
the source is gone from the display.

## Hypotheses and falsifiers

- **H1 (RA-linearizability).** For every honestly reachable archive, the
  design's rendered display equals the view of the sequential specification
  folded over the decoded identity commands in replay order. Falsifier: one
  archive where the two differ.
- **H2 (conservation).** No reachable display loses or duplicates a visible
  character relative to the identity-command fold. H1 implies H2; H2 is
  checked separately because it is what the demo violates.
- **H3 (local effect).** The issuer's own merge has the positional meaning
  above whenever the request is valid.
- **H4 (obligation correspondence).** Making removal independent of the
  move, as the demo does, reintroduces text loss; no other single change to
  the design does. Under the absorb rule the loss appears only through the
  cycle no-op, the N-005 shape; the N-004 shape, text moved into a block
  that is removed and never absorbed, needs the skip rule as well.

An earlier form of H4 held that the target-liveness check and the derived
removal each answered one bug. The executable gate refuted it: with removal
derived from the move, dropping the liveness check loses no text in any
archive. The two demo bugs are one defect.

Negative controls for the executable gate: the unmodified demo must still
fail the N-004 and N-005 regressions; "remove independently" must lose text
under absorb and, combined with skip, must fail both regressions; the
design must pass every control that the demo passes. Results and counts are
in [the experiment](../experiments/notion-merge-design/README.md).

## Plan

1. Executable gate: a patched copy of the pinned demo implementing the design,
   a JavaScript identity-command specification, and the existing search
   harnesses (seeds 27002 and 17102, the regression traces, and the
   complete-exchange campaign), with the controls above.
2. `NotionCoreSpec`: the `merge` command and its conservation lemmas.
3. The machine: a `merge` payload and operation, tree move on the forest,
   derived liveness with tombstoned display order, per-instance erase
   operations, and the chain invariant replacing the root-plus-one-leaf shape
   `Normal`, which merge-derived trees violate.
4. The protocol: issuance guard and the version-witness and
   RA-linearizability theorems for the extended request set.
5. Documentation and the paper's boundary statement.

Step 1 gates the rest. A failure there is a result about the design, and the
specification is revised before any Lean is written.

**Anchored merge.** The gate's anchor-absorb variant replaces the target
block by the demo's anchor: the instance and end item of the target's last
slice at issue time. Moving the Lean development to it:

6. `NotionCoreSpec`: slots gain two invisible kinds, the close of the slice
   ending at a marker and the finish of an instance. A created block is
   `[root, finish]`; a split leaves the marker's close at the end of the
   prefix. `Command.merge source anchor` takes the anchor's close address,
   and the holder is the block owning it. This is the gated `sliceFollow`
   specification.
7. The materialised slice ends with its close slot. The forest's holder
   lookup finds the node whose instance and stop match the anchor, and
   the machine's merge payload carries the anchor; issuance reads it from
   the target's last node.
8. The theorems keep their statements with the anchor in the request; the
   issuer's merge effect is unchanged because the issuer's anchor is owned
   by the target it sees.

Steps 6 to 8 are checked against the gate's litmus values: the review case
must give `a · bcd` in both orders as a specification-level control.

## Results

**Executable gate.** In 162,373 archive comparisons across the existing
search harnesses and the litmus families, deduplicated within each run, the
design's display equals the specification fold in every archive, no
character is lost or duplicated, every locally issued merge has its
positional meaning, every slice tree is a chain, block order never differs
between archives, and the review case gives `a · bcd` in both replay orders.
The demo's split failure (N-001) also does not occur: with chains a split
always moves the whole displayed suffix. The two formatting failures remain.
Counts, the variants (the demo's targeting, root-following and the
controls) and the shrunk witnesses are in
[the experiment](../experiments/notion-merge-design/README.md), where this
design is the variant `anchor-absorb`.

**Sequential specification.** `NotionCoreSpec.LocalId` has the close and
finish positions; `Block` carries its instance and an `alive` flag;
`Command.merge source anchor` implements the rule; `Rooted` states that
alive blocks are root-headed and tombstones empty. `NotionCoreSpecMerge`
proves the rule's cases (`merge_anchor_owner`, `merge_absorbed_owner`,
`merge_cycle_noop`, `merge_no_owner_noop`), conservation of the visible text
as a permutation (`merge_text_conserved`), address uniqueness, and
preservation of `WellFormed` and `Rooted`; `create_after_tombstone` fixes
the placement rule, and `split_then_merge_control` pins the review case at
the specification level: the finish anchor gives `a · bcd`, the close of the
split marker gives `acd · b`. `NotionCoreInvariant.Admissible.merge` admits
merges and `reachable_rooted` shows every reachable document is rooted.

**Machine.** A slice node is identified by its instance and stop item
(`NotionCoreSliceForest.Anchor`), and the forest invariant keeps these
anchors unique and every stop the start of some node. `appendLast`,
`holderOf` (by anchor) and `mergeForest` implement the merge, with
`merge_preserves` for the invariant; `Chain` replaces the root-plus-one-leaf
shape and liveness is per node. `Payload.merge` carries the source, the
anchor's instance and its optional stop, and `prepareMerge` reads the anchor
from the last node of the previous visible block. A materialised slice ends
with its close slot, so the materialised document is the specification's.
The display keeps tombstones, `Payload.erase` carries one group of targets
per instance, and the partition invariant `Covers` is owner-free.
`NotionCoreMachineDocumentMerge.holder_owner` shows the holder found by
anchor materialises to the owner of the anchor's close slot, and
`canonical_merge_execution_version` connects the machine's merge to the
specification's; `SPOT.concurrent_split_merge_control` is the review case on
the machine.

**Theorems.** `NotionCoreProtocol.specification_ra` and `versions_witness`
keep their statements over the request set create, insert, erase, split and
merge, with no new premise. `NotionCoreMRDTClient.merge_effect` gives the
issuer's merge its positional meaning. `insert_effect` and `split_effect`
now assume the addressed block is alive, since materialised documents contain
tombstones. The research ledger `NotionCoreLedger.entry` records all four
effects. Every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Scope.** `NotionCoreMergeFree.MergeFree` names archives without a merge.
The result below is about the current fact projection, which records no
merge; it does not show that every non-replaying implementation must fail.
The fact-set structural carrier is verified on that fragment; the executable
runtime refuses a merge transaction on receipt, so every archive it holds is
merge-free (`NotionCoreRuntimeRefinement.received_merge_free`), and `NotionCoreStructuralRender.SPOT.merge_outside_scope`
shows the restriction is necessary: splitting `ab` after `a` and merging the
new block back adds no fact, while replay changes the document, so no query
over the facts agrees with replay on both archives. Search-label correctness
(`NotionCoreMachineSearchLabels.honest_mapping_guard`) holds with merge.

**What the demo gets wrong, restated.** The demo's merge needs one change:
removal must be the move. Its split at the root's start, its unchecked
target and its cycle no-op are all harmless once a block is removed exactly
when its tree has moved. Formatting is the remaining unverified request.
