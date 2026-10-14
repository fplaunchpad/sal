# Published Notion demo: source and model boundary

This audit concerns the public educational demo, not Notion production. All seven modules in `experiments/notion-oracle/sources.json` were downloaded separately to `/private/tmp/notion-source-audit` and SHA-256 checked on 2026-10-14. Third-party source is not included in this repository. Function names below refer to those exact pinned bytes.

## Research question and falsifier

Can a faithful MRDT adaptation satisfy an independent sequential specification of ordinary positional block editing? The candidate claim is that a faithful identity-aware MRDT adaptation admits an independent sequential command specification, with a separate theorem that local preparation realizes the numerical client request. The selected ordering and visibility criterion must hold on the same history witness. Replaying original numerical requests unchanged is a baseline to test, not the required identity-aware target. The executable demo is the reality oracle; a checked counterexample to the independently defined positional spec is the formal oracle. Convergence of transaction sets is a separate question.

## Article evidence

The [article](https://www.notion.com/blog/how-notion-handles-concurrent-editing-with-crdts) describes stable character identities, tombstones, Lamport ordering, annotation anchors, and slices retaining their text-instance identity across blocks. It motivates routing concurrent edits to moved text and labels for locating descendant slices. It presents the widget as an illustration. These statements motivate the audit but do not establish equivalence between the widget and production. The article also discusses annotation types absent from the widget. Its production deployment statement is not a source-correspondence argument.

## Exact source references

Use the manifest URLs to retrieve each file. These hashes identify the audited version independently of line numbers.

| Module | SHA-256 | Load-bearing functions |
| --- | --- | --- |
| `replica.js` | `ab2edb0c424469e79bfec1aa8e53fbb208769d33aa86f17af89aa28af4da9336` | `Replica.receive`, `document`, `insertText`, `deleteText`, `splitBlock`, `mergeBlock`, `toggleBold` |
| `document.js` | `5c710856463c4941991b4f0fba348b7ea2ab1b3f6212558f0c3698733df37616` | `CrdtDocument.constructor`, `#apply`, `#splitText`, `#moveTextSlice`, `locateInsertion`, `annotationAnchors`, `transactionClockMax` |
| `ids.js` | `f4d40e440f574e3446b9b40f280d5d4684f6c0556fb9aaadb4d08bec893fd8e5` | `compareOpIds`, `compareItemIds`, `idKey`, `LamportClock.reserve`, `observe` |
| `rga.js` | `03327f7b34d161ba010c248fd5ed653a14a1d236b0efee329bc03165b5abed0b` | `RgaText.insertRun`, `insertSplit`, `delete`, `traversal` |
| `text-slice-tree.js` | `c5167ec9fa2aee3a3264f0f0888cfeb821a09224f41f970818797b1dda808f91` | `sliceItemBounds`, `splitTextSliceTreeNode`, `TextSliceTreeNode.appendChild` |
| `rich-text.js` | `ef2ceb935466d5db73394b18c0b113700311260a13f6882e9875c2f95ee91db9` | `anchorPosition`, `resolveRichText` |
| `search-labels.js` | `b9cd62692c8b73060fb5c47ac0799cd6ec4f3a02077e150755f41c2b13b25c09` | `splitSearchLabel`, `searchBounds`, `isDescendantLabel` |

## Requests, messages, and atomicity

Client requests are `insertText(block,index,content)`, `deleteText(block,start,end)`, `splitBlock(block,index)`, `mergeBlock(block)`, `createBlock(afterBlock)`, and `toggleBold(block,start,end)`. Positions count JavaScript string-iterator elements (Unicode code points), not UTF-16 code units or grapheme clusters. Generated messages are identified transactions containing arrays of operations. Positional requests are not the messages replayed by the document.

`insertText` resolves the visible predecessor, text instance, and search label, then reserves one ID per code point. `deleteText` snapshots the currently visible selected characters, groups them by text instance, and emits compressed ranges of stable character IDs. It never deletes a numerical interval during replay. A selection can therefore affect characters which have since moved to several blocks. Empty insertions and empty selections issue no transaction.

`splitBlock` emits, in one transaction, create-block, insert-split-marker, and move-new-right-slice operations. The new block ID is session plus reserved counter; its initially empty title instance differs from the moved text instance. `mergeBlock` similarly emits split, move, remove-block in one transaction. `toggleBold` emits one operation per contiguous text-instance segment; its first operation ID is the transaction ID.

`Replica.receive` admits the whole transaction into a map keyed by ID. Identical repeated payloads return false; reused transaction IDs with unequal JSON payloads throw. `CrdtDocument.constructor` sorts whole transactions and applies each operation array contiguously, rebuilding mappings after each transaction and asserting invariants at the end. No intermediate operation state is exposed by this constructor. This is atomic replay, not rollback: an exception aborts document construction, while `receive` has already stored the transaction. General malformed-message safety is not established.

## Ordering and issuance assumptions

`compareOpIds` orders ascending counter, then lexicographic session ID. Replay uses this order. RGA siblings use the reverse order and preorder traversal. Run characters chain origins and consecutive counters. Split markers inhabit the same RGA identity space as characters; marker ordering therefore determines which side receives an insertion at the exact split boundary.

`receive` observes the maximum reserved operation/run counter in the transaction, using `transactionClockMax`; subsequent local reservations exceed it. Thus well-issued transactions respect causal receipt order under the replay order. Transaction IDs alone are not enough to reconstruct a vector-clock causal relation. The source does not buffer missing causal predecessors before rendering: externally supplied incomplete or malformed sets can fail. A proof must derive causal closure from the execution model, rather than infer it from convergence tests.

Assumptions needed for a clean model include globally fresh sessions, noncolliding IDs, safe finite clock arithmetic, immutable payloads, and causally closed reachable transaction sets. Local insertion validates range bounds but deletion uses JavaScript `slice` and consequently clamps oversized endpoints and accepts negative indices. A natural sequential spec should explicitly choose valid request ranges rather than accidentally inherit this permissive behavior.

## Text identities, routing, and conflict behavior

`CrdtDocument.#apply` routes insertion/deletion/annotations directly by `args.textInstanceId`; the operation pointer block, path, version, and search label do not determine their effect. `#splitText` inserts a marker, searches all block trees for the slice containing it, then divides that slice. Slices exclude their boundary markers. Deleted characters remain structural RGA ancestors. Stable text identities survive movement and deletion.

Slice splitting puts all previous child slices below the new right slice. Movement attaches that entire subtree. Blocks render slice trees in preorder. `#assertInvariants` checks root ownership and partition of every instance's visible characters over all blocks, including dead blocks; it does not prove every character occurs in an alive block. Search labels are maintained and checked for uniqueness, but the demo's effects scan all nodes and do not use label-range lookup. Removing labels from an abstraction needs a projection argument; copying their encoding into a sequential editing spec has no demonstrated semantic necessity.

`#createBlock` inserts immediately after the named block in the current replay list; later same-origin creates therefore precede earlier ones. `#removeBlock` marks dead and removes its order entry. Recreating an existing block marks it alive but does not reinsert its order entry. The issued API does not generally exercise arbitrary recreation; do not claim properties over arbitrary message sets without checking this distinction.

`Replica.mergeBlock` chooses the previous alive block locally, reserves 20 unused clock ticks, splits at the source root's start marker, and moves the resulting subtree to the target's last slice. The clock gap affects concurrent replay order and must be preserved in a faithful issuance model unless proved irrelevant. `#moveTextSlice` catches cycle-producing attachment failures and reattaches the source to the end of its original parent's children; although the comment calls this a no-op, sibling order restoration is not literally implemented. There is no public arbitrary block-move request in `Replica`; only the lower-level slice move used for merge. Generic movement is a separate extension.

Formatting is only boolean bold in this demo. Local toggle removes when every selected character is already bold, otherwise adds. `annotationAnchors` chooses before-first and before-next-visible-in-instance (or end-of-instance), not necessarily the next character in the block. `resolveRichText` chooses the greatest annotation ID covering each RGA item. Anchors are interpreted on the complete RGA traversal before slice projection, so formatting follows identities across splits and merges. Other annotation types, hyperlink affinity, and production Peritext equivalence are outside the established boundary.

## Independent sequential-specification critique

An ordinary sequential state can be an ordered list of identified blocks, each containing a sequence of characters and formatting. In that spec, insert/delete/split are requests addressed to a current block and numerical range; split moves the suffix into a fresh successor block; merge concatenates the preceding block and removes the source. Transaction logs, replay sorting, and search labels are representation machinery and should not define this spec.

Stable character IDs may be justified for a distinct identity-addressed command specification: they express deletion of the characters selected in the issuer's view even after those characters move. The user explicitly requests this distinction between numerical preparation and identity-addressed execution. It does not require replaying a numerical request against an unrelated later view. Its local preparation theorem and visibility conditions must be stated separately. A sequential witness may not borrow preparation from one ordering and observation from another.

A hand-derived obstruction already follows from the initial discovery trace. Start with `abcd`; concurrently request `split(original,2)` and `delete(original,1,3)`. The pinned demo reports `a | d`. In a positional sequential spec, delete then split yields `ad | empty`; split then delete either rejects the oversized range or, with clamping, yields `a | cd`. Neither yields `a | d`. This refutes the unqualified original-request sequential-serialization claim, rather than demonstrating failed convergence.

The numerical-replay counterexample rules out one baseline. It does not rule out the requested identity-aware specification. The next obligation is to justify stable character and cut identities independently, prove local preparation, and connect command execution to the selected sequential-history criterion. A set-union MRDT may faithfully retain transaction evidence, but set-union convergence alone discharges none of these obligations.


## Measured local formatting counterexamples

These two traces use only issued `Replica` methods and valid visible indices. They challenge local preparation itself, independently of any concurrent-history serialization definition. They were executed against the seven hash-checked modules on 2026-10-14. The expected selection behavior is derived from ordinary local bolding: selected unbold characters become bold, and unselected characters in other blocks retain their marks.

Start with a fresh `Replica("seed",...,[])`; call `createBlock()` and insert `abc` at zero. Character IDs are `seed@2`, `seed@3`, `seed@4`. Fork replicas A and B from those transactions. A splits the original block at 1; B concurrently splits it at 2. Both transactions have counter 5. Deliver B's split to A. A now displays `a | c | b`, with blocks `seed-block-1`, `B-block-5`, `A-block-5`.

1. **Leaks formatting to another block.** A merges `B-block-5` into its predecessor, producing `ac | b`, all unbold. A toggles bold on original block range `[0,2)`. The issued annotation starts before `seed@2` and ends before `end`; the result is bold `ac` **and bold `b`**. The independent expected local result is bold `ac` with unbold `b`.
2. **Fails to format selected characters.** From the shared `a | c | b` state instead, A merges `A-block-5` into its predecessor, producing `a | cb`, all unbold. A toggles bold on `B-block-5` range `[0,2)`. The issued annotation's start and end both equal before `seed@4`; the result leaves **both selected characters unbold**. The independent expected result is unbold `a` and bold `cb`.

In both traces the merge transaction is `A@26` and the annotation is `A@27`. No concurrent transaction arrives during the toggle. The cause is source-local: `contiguousSegments` groups adjacent displayed characters by text-instance equality, while `annotationAnchors` interprets the first and last selected characters in instance RGA order. Slice movement can make display order a noncontiguous subsequence or reverse the selected endpoints in that instance. `resolveRichText` then faithfully applies the overly broad or empty interval.

These are measured counterexamples to ordinary local formatting preparation in the public demo. They are not evidence about Notion production. They do not refute the split/insert/delete-only milestone. A faithful extension cannot simultaneously preserve these outputs and claim the ordinary local bold-selection contract on unrestricted reachable merge states. Restricting states or repairing preparation would change the stated comparison scope and must be explicit.


The empty-interval failure minimizes further to two characters when boundary splits are admitted. Seed `ab` with character IDs `seed@2`, `seed@3`. Concurrently issue A's split at zero and B's split at one, both counter 4. After A receives B's transaction, the view is `empty | b | a`. Merge `A-block-4` into predecessor `B-block-4`, yielding `empty | ba`; the merge ID is `A@25`. Toggle bold on `B-block-4` range `[0,2)`. Annotation `A@26` starts and ends before `seed@3`, so the view remains unbold `empty | ba`. Both numerical indices are valid at issuance. Two characters are necessary for this particular reversal mechanism; no global minimality claim over all formatting failures is made.
