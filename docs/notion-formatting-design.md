# Bold intervals, exact selection, and insertion inheritance

The public demo's bold renderer uses dynamic intervals in one text instance's
RGA order. The client prepares those intervals from a displayed selection.
These orders can disagree after split and merge. N-002 and N-003 refute the
claim that the existing preparation always changes exactly the selected visible
characters, including with the corrected block-merge design. An immediate
selected-identity specification can express the desired local effect, but it
does not specify how later inserted text inherits bold.

The subsequent end-to-end attempt found a separate obstruction in the
maximal-run candidate: per-segment priorities can fracture one atomic toggle
under concurrency. The [atomicity note](notion-formatting-atomicity.md)
records a reachable typed caller, the actual finite-carrier observation,
an independent all-history invariant and a pinned JavaScript reproduction.
The intended atomic rich-text bridge is therefore **refuted for this
candidate**, even though its immediate coverage theorem is true.

## Positive atomic repair

The [rich-text protocol certificate](notion-rich-text-certificate.md) now proves
insertion inheritance and atomic whole-selection updates. The repaired model
assigns one arbitration priority to every segment of a transaction while
retaining each segment's distinct allocation ID. One Boolean value is chosen
from the issuer's complete selection and retained by the issued operation.

The immediate falsifier is a reachable execution whose observation cannot be
explained by any ordering of these whole updates. The existing `10011` trace
is the first regression; concurrent overlapping selections and edits that
change interval boundaries supply further tests. Passing that trace alone
does not establish the target.

The formal oracle relates the repaired interpreter to an independent
incremental rich-document specification and derives the same-event history
witness from actual protocol reachability. The abstract state retains physical
cells and current character/sticky-gap marks. It contains no annotation log or
replay sorting. The reality oracle is the pinned JavaScript with an explicitly
separate temporary repair; original source and original-demo failures remain
unchanged. The guide records the public theorem and its exact scope.

## Research enquiry

- **Goal:** identify a formatting preparation rule that changes exactly the
  currently selected visible identities while retaining a stated insertion
  inheritance policy across split and merge.
- **Candidate claim:** the demo's one-interval-per-adjacent-instance-segment
  preparation achieves the exact current selection effect.
- **Falsifier:** a selected character remains unchanged, or an unselected
  character changes. N-002 and N-003 are executable falsifiers.
- **Formal oracle:** an exact current-selection coverage premise can connect
  scalar interval evaluation to a selected-identity sequential specification.
  The premise itself must be checked against exported source fixtures.
- **Reality oracle:** the seven hash-pinned cached public demo modules in
  `experiments/notion-oracle/sources.json`, executed offline. Production Notion
  correspondence is unvalidated.

The open question is how much stable boundary information a repaired exact
selection operation needs to preserve the demo's inheritance choices. A set of
selected IDs alone cannot express these choices without an additional rule
relating future insertions to the selection.

## Source-function evidence

| Source function | Claim | Evidence and limitation |
| --- | --- | --- |
| `rga.js: RgaText.traversal` | Traverse reachable items in preorder; siblings sort by descending item ID. Record item entry and exclusive subtree exit. Keep split markers and deleted text in this coordinate order. | Source inspection and exported entry/exit fixtures. Missing-origin items are unreachable. |
| `rich-text.js: anchorPosition` | START maps to zero; END maps to traversal length. Before maps to entry; every other side maps to subtree exit. `anchor` takes precedence over legacy `affinity`. | Raw fixtures distinguish subtree exit from entry plus one. The typed export targets well-shaped before/after sides. |
| `rich-text.js: operationContainsItem` | Cover index `i` exactly when both endpoints resolve and `start ≤ i < end`. | Empty, reversed, and missing-endpoint controls. The helper is private; fixtures export its source-derived scalar interpretation. |
| `rich-text.js: resolveRichText` | Sort annotation IDs by ascending counter then session ID. Start each live text item as plain; the last covering operation supplies its Boolean value. Filter deleted text and split markers only when producing characters. | Direct raw-module tests reverse the input operation list and exercise a session-ID tie. |
| `replica.js: contiguousSegments` | Group adjacent displayed characters only by equal text-instance ID. Returning to an earlier instance starts another segment. This does not check adjacency in instance preorder. | An `aXb` display drawn from instances A, B, A emits three operations. |
| `replica.js: toggleBold` | Decide add/remove once for the entire selection: remove only if every selected character is bold. Reserve one ID per segment; emit all segment operations in one transaction, whose ID is the first segment ID. | Mixed two-instance selection adds throughout; all-bold selection removes throughout. Fixtures preserve the complete atomic transaction. |
| `document.js: annotationAnchors` | Start before the first selected item. End before the next globally visible item in that instance after the segment's last selected item; use END if absent. Ignore display block and slice boundaries when finding that successor. | N-002 and N-003 expose the resulting selection mismatch. |
| `document.js: blockCharacters` | Resolve formatting in each whole instance first, then project through displayed slices. | N-003: an unselected character in a different displayed block becomes bold. |

`richTextTokens` only coalesces adjacent equal-bold characters. Token compression
is not part of the identity or interval semantics studied here.

## Small distinguishing executions

All expected values below are hand-derived. The offline runner checks each
positive result and a nearby rejected output on both the original demo and the
corrected merge design. A bit string gives each displayed character's bold flag.

| Execution | Expected result | Rejected explanation |
| --- | --- | --- |
| Bold `b` in `abc`; insert `X` immediately before `b` | `aXbc`, `0010` | Both boundaries grow symmetrically (`0110`). |
| Bold `b` in `abc`; insert `X` immediately after `b` | `abXc`, `0110` | Mark only the originally selected IDs (`0100`). |
| Bold `bc` in `abcd`; insert between `b` and `c` | `abXcd`, `01110` | New interior identities stay plain (`01010`). |
| Bold final `c`; append `X` | `abcX`, `0011` | END remains fixed before future text (`0010`). |
| Bold `b`; delete `b`; insert `X` after `a` | `aXc`, `000` | A deleted start anchor becomes the visible gap (`010`). |
| Bold `b`; delete successor `c`; insert after `b` | `abX`, `011` | Deleting the successor destroys the interval (`010`). |
| Bold `bc`; split `abcd` at two; insert at start of suffix | `ab` / `Xcd`, `01` / `110` | The split loses the mark or the inserted suffix prefix stays plain. |
| Concurrently bold `b` and insert `X` after `b`, without observing the mark | `abXc`, `0110` in both receipt orders | Inheritance requires observing the annotation at insertion time. |

After anchors refer to whole subtrees. For root sibling `X` after the chain
`a → b → c`, `before(START)..after(a)` covers `abc` and excludes `X`.
`after(a)..END` covers only `X`. Replacing `after(a)` with `entry(a)+1`
misclassifies both examples.

Insertion inheritance follows the resulting RGA position. These examples do not
establish a universal user-interface boundary policy under arbitrary concurrent
restructuring. Stable IDs and surviving tombstones matter: a deleted endpoint
still has a coordinate.

## Exact-selection counterexamples

The N-002 fixture displays `ba` although its instance order has `a` before `b`.
Selecting both gives first item `b`, last item `a`. The next globally visible
item after `a` is `b`, so preparation emits
`before(b)..before(b)`. Its scalar endpoints both equal three. It covers
nothing; both selected characters remain plain. The problem is an empty
interval caused by reordered selection endpoints, rather than a numerically
reversed interval.

The N-003 fixture displays `ac` in the first block and `b` in the second. The
selected first block contains addresses `S:2` and `S:4`. Its RGA preorder is:

| Index | Item |
| --- | --- |
| 0 | `a`, ID `S:2` |
| 1 | split marker `A:5` |
| 2 | `b`, ID `S:3` |
| 3 | split marker `B:5` |
| 4 | `c`, ID `S:4` |

Preparation groups `a,c` into one segment because their instance IDs agree.
It emits `before(a)..END`, scalar interval `[0,5)`. That interval also covers
`b` at index two. The observed display bits are `11` / `1`; the desired exact
selection effect is `11` / `0`.

Both failures reproduce with the original demo and the corrected merge variant.
The recorded N-002 passing control still passes. Correcting block attachment
does not repair the formatting request compiler.

## Export contract and current evidence

`experiments/notion-formatting/fixture-types.d.ts` defines the export interface.
Per-instance fixtures contain tagged IDs, full preorder item records, scalar
entry and exclusive exit positions, sorted operation IDs, resolved interval
endpoints, covered indices, and visible resolved characters. A missing anchor
position is JSON `null`. Per-replica fixtures retain the original transactions,
including each toggle's complete multi-operation transaction.

Run the experiment with:

```sh
python3 experiments/notion-formatting/run.py --cache /private/tmp/notion-report-20261023
```

The run on Node v26.3.1 checks 18 client cases, five direct renderer cases, and
two exact-selection counterexamples per variant. Every case has a positive
assertion and a distinct negative companion: 25 pairs per variant, 50 across
both. The existing merge-design gate separately replays N-002, its passing
control, and N-003. All seven cache hashes match the pinned manifest before and
after execution. The runner has no network path and patches only temporary
copies. Results live under `experiments/notion-formatting/results/`.

These are **measured** source results and **execution-refuted** local correctness
claims. A source-derived coordinate export is not independent proof of the
coordinate algorithm. Importing it into Lean can test that the independently
defined evaluator agrees on these literal fixtures; it does not establish a
general refinement theorem.

## Source compiler and local refinement

### A concrete candidate compiler

Prepare a toggle from the current display as follows:

1. Record the selected stable IDs, grouped by text instance. Choose the Boolean
   once: false if all selected characters are bold, true otherwise.
2. For each participating instance, traverse its globally visible text items in
   instance order. Partition selected items into maximal runs containing no
   unselected visible item. Display order does not determine these runs.
3. For each run, emit the existing interval shape: before its first item through
   before its next globally visible successor, or END if no successor exists.
4. Reserve a fresh operation ID for every run and publish every run operation in
   one transaction. Its transaction ID is the first reserved ID.

For N-002, the selected IDs are `a,b` despite the `ba` display. The plan emits
`before(a)..END`, scalar `[1,4)`, and covers both selected characters. For
N-003, it emits `before(a)..before(b)` and `before(c)..END`, scalar `[0,2)` and
`[4,5)`. These cover `a,c` and exclude `b`; the split marker at index one is
harmless because it is not a displayed text character.

This candidate preserves the existing interval shape and its ordinary
before-next-visible growth rule. A future insertion inside a run or before its
original successor belongs to that interval. It receives the run's value when
no later covering annotation overrides it; the greatest covering annotation
determines the final bold flag. An insertion that sorts before the run's first
anchor stays outside. Splitting a displayed selection into physical runs gives
each run this policy. In particular, newly inserted text between two
selected display characters may be plain when its physical instance location is
outside all runs. That policy is a design choice requiring an explicit claim,
not an implication of immediate exactness.

`experiments/notion-formatting/candidate-planner.mjs` implements this candidate
as an isolated pure planner. It does not replace the pinned client compiler.
The offline harness applies the resulting transactions through the source's
ordinary annotation operation path in temporary workspaces.

Its first obligation is finite current coverage: the union of run intervals
intersects the current live text items exactly at the selected IDs. The harness
checks that condition for every candidate source fixture using full current
preorder coordinates. A separate bounded gate checks 304 combinations of
nonempty subsets of four ordered IDs, selection permutations, deletion masks
on unselected IDs, and add/remove values. The 21 source-applied cases per
variant include both counterexamples, left/right/interior/END growth,
tombstone endpoints, mixed multi-instance toggles, repeated instances, and
concurrent right-boundary insertion in both receipt orders. The final six
cases apply a toggle concurrently with deletion, split, or block merge and
check both receipt orders. Each case has a distinct
rejected output. The N-003 candidate still leaves `b` plain after insertions at
both displayed gaps around `c`.

These runtime results are **measured on the stated finite scope**. The Lean
planner now has a separate **machine-checked** immediate-coverage theorem,
described below. Arbitrary concurrent-history refinement remains unproved.
The original source failures are reported separately and continue to reproduce.

### Checked planner and evolution results

`NotionCoreFormattingPlanner.planToggle` implements the same maximal-run
scanner on typed inputs from the adapter's distinct instance enumeration
(`Map.values`). The Lean function can process repeated instance keys, but its
raw output then differs from JavaScript, which consumes each pending selection
only once. Such enumerations are outside the source-correspondence claim;
they do not invalidate the more general immediate-coverage theorem.
The planner groups raw source IDs rather than
assuming they are semantic addresses. `selectedAt_decoded` proves that the
existing injective session encoding preserves selection membership.

| Result | Lean declaration | Required evidence |
| --- | --- | --- |
| Each before-item anchor resolves to its physical entry | `anchor_before_entry` | Unique IDs in the full source forest |
| Run intervals cover exactly selected visible items | `segments_exact` | Unique IDs; order and bounds are derived from the actual forest walk |
| The complete atomic plan has exact displayed coverage | `planToggle_exact_coverage` | `DisplayCoordinates`: source IDs, current walk positions, and represented instances for every displayed slot |
| One plan implements the independent local toggle | `planToggle_refines` | The structural coordinate relation and agreement on the issuer's single add/remove verdict |
| Display permutations leave the plan unchanged | `planToggle_selection_perm` | A permutation of the selected character records |

The coordinate relation is a structural source/core relation, not an assumed
exact-coverage conclusion. The theorem checks all displayed slots, including
unselected slots in other blocks. The planner theorem itself does not derive
that relation from every reachable rich-text protocol state. The later
executable rich caller computes the selection, source-instance traversal and
anchors from its current query; the atomicity witness uses these actual
computations rather than assuming coverage or choosing an arbitrary Boolean
verdict. The repaired protocol now derives the full dynamic relation in
`NotionCoreRichCanonicalHistory`; the original per-segment compiler remains
outside that positive theorem. The original
compiler cannot satisfy this
theorem: `SourceSPOT` retains the exact N-002 and N-003 counterexamples, while
`PlannerSPOT` proves the repaired results and invokes the general refinement
theorem on a nonempty reversed-display fixture.

`NotionCoreFormattingEvolution` adds three general results. Actual forest
tombstoning preserves anchor coordinates and annotation resolution
(`anchorPosition_erase`, `resolveAt_erase`). A gap insertion preserves old
interval membership; new positions inherit exactly when the gap is strictly
after the left endpoint and at or before the right endpoint (`old_membership`,
`new_membership`). This positional result still needs a concrete insertion's
anchor-coordinate embedding; it is not a universal rich-history theorem.
Finally, `resolve_fresh_unsorted` proves that a uniform fresh batch overwrites
exactly its covered positions even with existing annotations. Its premises
require fresh Lamport IDs and one payload per operation ID.
`NotionCoreRichNetwork` now reserves full transaction widths at issuance and
derives disjoint allocations and annotation freshness from reachability
(`allocation_reachable`, `new_annotations_fresh`). The original demo's archive
check alone still only rejects conflicting transaction IDs; the typed issuer's
allocation proof supplies the stronger annotation-ID integrity result.

### Original integration and the repaired bridge

`NotionCoreFormattingMachine` now supplies a separate executable extension of
the actual editing interpreter. Each edit delegates to
`NotionCoreMachine.applyTransaction`; a format request appends its complete
batch atomically. Rich rendering obtains displayed atoms from the existing
slice-tree query and resolves source annotations against each instance's
current origin forest. `instanceForest_traversal` proves the traversal matches
the editing machine's physical traversal.

`replay_core_projection` proves that erasing formatting requests from any run
recovers exactly the existing core run. `render_forget` and
`replay_render_forget` prove equality with the actual plain-text query,
including failures. The ten `MachineSPOT` controls exercise bootstrap, the
candidate planner, boundary insertion, tombstoned anchors, split, corrected
merge, multi-instance atomic batches, overlapping removal, and query/edit
failure. `NotionCoreRichPayload`, `NotionCoreRichNetwork` and
`NotionCoreRichMRDT` extend this executable integration with whole-transaction
transport, actual positional request preparation, reachability-derived fresh
IDs and a finite carrier. The carrier's five VCs establish ordinary and
canonical recursive-base convergence. They do not supply the missing atomic
sequential bridge or enlarge the existing plain editing certificate.

The initial address-mark wrapper around the structural `Spec.step` keeps old
address marks while structural requests run. It can state immediate selected
effects. It does not calculate a new inserted character's inherited value, so
it cannot establish full rich-text sequential semantics or a full
RA-linearizability extension.

The repaired extension retains a dynamic relation between anchors and insertion
structure. Its source-facing state includes per-instance origin trees,
stable item IDs, split markers, tombstones, and anchored annotation operations.
Recompute scalar entry/exit coordinates after insertion; a coordinate snapshot
alone cannot be reused as a stable anchor. A smaller abstract state is possible
only with a separate theorem showing it preserves all relevant insertion and
subtree-exit observations.

The checked integration relation connects displayed core slot addresses to
source instance/item IDs and their current preorder coordinates. It preserves
unselected characters in other displayed blocks and relates one client toggle
to one atomic core step even when its transaction contains several intervals.
The [certificate guide](notion-rich-text-certificate.md) records the independent
character/gap state and the derived whole-history result.

### Proof boundary

The typed planner's immediate coverage and local refinement are proved.
The intended full atomic rich-text bridge is **refuted for the current
per-segment-priority candidate**. `NotionCoreRichAtomicCounterexample`
constructs a reachable caller and observes flags `10011` on identities
`abcde`. Every atomic formatting request treats `b` and `d` alike, so no
atomic ordering explains the observation. This remains true with arbitrary
prepared verdicts and interleaved structural reshapes; the witness contains
no later visible insertions. Inheritance choices therefore cannot repair it.

The independent atomic oracle proves a necessary uniform-selection property,
not a theorem negating a named framework RA predicate or a certified
version-DAG counterexample. The separate shared-priority repair now has a full
dynamic character/gap specification, derived actual caller-selection theorem,
canonical rich-history simulation and positive per-version/head RA certificate.
`NotionCoreRichProtocolCertificate` consumes actual protocol reachability;
it does not assume a completed state relation or rich-query agreement.
Ordinary and canonical recursive-base merge steps use the same proof.

Arbitrary JavaScript/protocol correspondence and production Notion equivalence
remain unproved. The supported typed API uses natural clipped indices and
before-item/END formatting boundaries, with one value fixed at issuance.
Its independent state retains the physical origin distinction needed for
different inheritance at an empty root and a moved split marker. The repair
leaves the pinned demo and existing plain editing certificate unchanged.

Root verification used a fresh combined Lean build and an independent offline
rerun of both JavaScript variants. The latter passed 25 original-source controls,
21 candidate controls and 304 bounded coverage cases per variant; both original
formatting failures still reproduce. Standard Lean axioms are the only
dependencies reported for the checked proof results. The production release
gate builds the new research ledger without changing its registered runtime
datatype inventory. The separate atomicity runner records both corrected
merge variants, both delivery orders and all six format orderings.
