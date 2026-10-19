# Notion split proof enquiry

## Current checked endpoint

`NotionCoreMRDT` is the concrete finite-transaction MRDT with actual typed
replay/render query. Its five-VC representation feeds the separate independent
history bridge. `NotionCoreProtocol.versions_witness` now derives a single
witness for every registered version's event permutation, required order,
specification visibility and actual query admission; `specification_ra` gives
full-input RA-linearizability for current heads. Neither common-archive
coupling, carrier equality, accepted next steps nor desired query answers are
supplied as proof premises.

The protocol refines actual Sal steps: fork copies source receipts, ordinary
and canonical recursive merge import current-head receipts, explicit factory
initialization establishes bootstrap, and the local ordinary issuance guard
derives actual gap/reservation/emission. The factory phase is separate because
one global initialization cannot be enforced by inspecting a local carrier.
Empty forks before factory initialization and bootstrap after lower-key creates
in canonical replay are retained. The result does not assert correctness of
unrestricted carrier-True issuance executions.

Actual bounded valid insert/delete/split/merge request theorems derive issuance,
reconstruction and the immediate requested visible effect. `MRDTClient` proves
exact transport of issued transactions to concrete MRDT update/query. Ranges
are bounded natural-number ranges, insertion is nonempty, and source early
no-ops intentionally emit nothing. Concurrent histories use prepared semantic
identities, not unchanged numeric request replay.

Focused kernel checks and the final research gate (3,515 Lean jobs, all 17
pinned oracle groups) support these endpoints. The production gate also passed
3,694 jobs, exact-contract/axiom checks and 187 runtime tests. The typed source model is supported by the
pinned JavaScript audit and distinguishing executable traces. Mathematical
name/range codecs and actual labeled replay uniqueness are checked, but
JavaScript JSON decoding, safe-number printing, and opaque atom/string
extraction are not proved program translations. No Notion production claim is
made. Block merge is part of the request set in the corrected form described
below; unrestricted movement and formatting remain a separate,
counterexample-bearing extension.

## Block merge extension

The [merge design note](notion-merge-block-design.md) asks whether a block
merge over the same slice-tree and RGA state has a sequential meaning. Its
answer is a merge whose removal of the source is the move itself: the source's
whole chain attaches under the last node of the tree holding the slice at
which the request was anchored, the end of the target's last slice when
issued, and the source stays in the display order as a tombstone. The
sequential specification gains `Command.merge` with an absorb rule (a merge into a
merged-away target lands in its absorber) and `NotionCoreSpecMerge` proves
conservation of visible text (`merge_text_conserved`) and preservation of the
document invariants. On the machine, every slice tree is a chain
(`NotionCoreSliceForest.ChainForest`), and `NotionCoreMRDTClient.merge_effect`
gives the issuer's local effect. `NotionCoreProtocol.versions_witness` and
`specification_ra` keep their statements over the larger request set. The
structural fact-set carrier keeps the merge-free fragment
(`NotionCoreMergeFree.MergeFree`), and
`NotionCoreStructuralRender.SPOT.merge_outside_scope` proves that restriction
is forced. The executable gate in
[experiments/notion-merge-design](../experiments/notion-merge-design/README.md)
tests the same design on a patched copy of the pinned demo, with negative
controls.

## Chronological proof record

The remaining sections preserve discovery and intermediate theorem scopes.
Statements that an obligation is open refer to the checkpoint being described,
not the current endpoint above. The initial fragment and storage shell remain
limited artifacts even though later typed-core modules close their missing
bridges.

## Question and falsifiers

**Goal:** connect a faithful MRDT adaptation of the pinned published demo to an independent block/text sequential specification through the existing five merge VCs and a separate history bridge.

**Candidate claims:** (1) replaying positional client requests explains the crossing-delete observation; (2) retaining semantic character identities and split gaps explains that observation without retaining transactions; (3) the full adaptation meets the ordinary editing contract on every honestly reachable issuance state.

**Falsifiers:** for (1), one two-request result outside both sequential orders; for (2), a split/delete order mismatch or boundary insertion outcome outside the independent identity specification; for (3), a locally issued ordinary edit with the wrong visible effect, or a version with no legal witness satisfying both required orders.

**Formal oracle:** the `Sal/MRDTs/Instances/Notion*.lean` modules, built by `scripts/check-notion-research.sh`. The initial `NotionSplitSpec` fragment and the later full core machine have different scopes, described below.

**Reality oracle:** the separately fetched, hash-pinned published JavaScript demo and the literal traces in `experiments/notion-oracle/`. The independent specifications and source-shaped typed models have distinct roles; neither constitutes a proved translation or verification of that JavaScript.

## Initial small fragment

The positional specification stores a list of blocks, each a list of characters. A split replaces the addressed original block by its prefix and suffix. A delete removes the requested range in that block, with clamping. The concrete theorem `no_positional_serialization` checks both orders of splitting `abcd` at 2 and deleting `[1,3)`. The resulting serial documents are `a | cd` and `ad | empty`; neither is the measured `a | d`. A strict bounds discipline would reject one or both orders and cannot restore a witness. This refutes this request-level replay contract. It does not refute an identity-addressed message specification or the framework.

The independent identity fragment stores ordered semantic character slots, each with an identity, value, and visibility. A deletion names character identities and hides their slots across all blocks. A split names the character immediately before its gap. Hidden slots remain available as gap anchors. These identities express an editing distinction: deleting the character before a prepared gap does not erase the gap. They are not transaction identifiers, replay keys, sorting labels, slice records, or a transaction log.

`splitByAnchor_erase_commute` proves for every document, anchor, and target list that identity deletion commutes with splitting the first block at that retained anchor. `identity_anchor_crossing_delete` checks `a | d` in both orders, including a negative control against `ad | empty`. `boundary_insert_orders` checks both boundary placements with opposite sequential orders: split then insertion gives `abX | cd`; insertion then split gives `ab | Xcd`. Its negative control proves these outcomes differ. This establishes that identity-dependent boundary placement alone is not a non-linearizability counterexample.

`cut_erase_commute` additionally checks the simpler retained-slot-index fragment. `local_delete_preparation_control` checks one hand-derived concrete range preparation. It is not a universal client-preparation theorem. Every concrete scenario has a negative control. The file uses no added axioms or admissions; reported dependencies are Lean's standard `propext` and `Quot.sound` where used.

## Exact boundary of the fragment

The identity fragment is executable but is not a complete specification of the published demo. It currently addresses the first block, uses a single left character as its gap anchor, and lacks insertion at the beginning, block identities, concurrent split ownership, slice restoration/duplication, block merges, movement, formatting, transaction atomicity, and message preparation. The later core machine adds block merges; see [Block merge extension](#block-merge-extension). Missing-anchor behavior is totalized, so issuance must separately establish presence and uniqueness before any claim of ordinary editing legality. Insertions assume fresh semantic identities; this invariant has not been derived from an issuer.

No faithful demo MRDT adaptation is defined by this fragment. The generic transaction-storage shell below supplies convergence only. No Notion-specific editing representation invariant, replay-policy proof, sequential-history bridge, or end-to-end correctness certificate is claimed. The fragment's checked commutation theorem supplies a candidate local lemma, not the whole requested milestone.

## What the actual five-VC interface requires

The relevant current interface is `Sal/MRDTs/Paper1/ConcreteJoin.lean`, `Raw.MergeVCs`, not the historical 24-VC skill template. Its five fields are `merge_comm`, `init`, `causal_delta`, `local_redistribute`, and `shared`. They are guarded by a context-indexed representation, semantic support, and metadata closure. Instantiating them alone is insufficient.

`VCReplayConditions` in `ConcreteVCExecution.lean` additionally requires replay laws, unique representation, initial representation, finite event enumeration, canonical states, support, a `Raw.ReplaySupply`, and represented versions derived from issuance-certified executions. Replay supply must reconstruct both the semantic event past and the remainder after a jointly semantic-maximal and metadata-maximal event. One cannot assume this reconstruction from convergence of transaction-set union.

For an independent natural specification, `ScopedVCConditions` adds `ExecutionHistoryAdequacy`; the total alternative `VCConditions` adds `CommutationCompatibility` and `EventFoldHistorySound`. `ConcreteHistoryBridge.lean` preserves a single witness's event permutation, paper order, specification visibility, and accepted independent query history. A transaction-set carrier with `Either` updates can establish storage convergence while failing the compatibility condition: independent text operations can interfere even when insertion into the carrier commutes. Sorting transactions again inside the specification would conceal this gap.

The framework offers ordinary and recursive execution theorems (`executions` and `executionsV`). Applying either requires the corresponding issuance-established representation and history premises. The natural editing fragment currently has neither instance, so it covers neither execution theorem. The generic storage shell below has a separate, narrower scope. Recursive bases cannot be claimed merely because a union carrier ignores the supplied base.

## Status

The positional-request bridge is **refuted** by a kernel-checked finite counterexample. The identity split/delete law and the boundary insertion controls are **machine-checked** within the explicitly limited independent fragment. Agreement with the source is **measured** on the external traces, not proved. The later independent core machine below proves universal local preparation effects. Source issuance correspondence, reachable execution invariants, and full sequential-history refinement remain **staged**. See `docs/notion-research.md` for the investigation's overall conclusion and source/oracle evidence.

## Reachable local formatting obstruction

`NotionFormattingCounterexample.lean` isolates the source's single-instance annotation interval rule on fixtures with no hidden characters or pre-existing marks. The source groups displayed selections by text-instance identity, then formats an interval in the instance's order from before the selected first character to after the selected last character. Display and instance order can diverge after block splits and merges.

The source audit reproduces a two-character trace: start with `ab`; concurrently split at 0 and 1; obtain `empty | b | a`; merge `a` into `b`; obtain `empty | ba`; request bold on all of `ba`. In the underlying instance order `ab`, before `b` equals after `a`, so the interval is empty. `two_character_reversal` kernel-checks this finite interval calculation and its inequality with ordinary formatting of both selected characters. `contiguous_selection_control` shows the rule works on a nearby contiguous selection and is not constantly empty. `noncontiguous_selection_overformats` checks the complementary `ac` fixture: spanning the instance-order interval also formats `b`, displayed in another block.

These theorems use hand-derived inputs and do not prove that the JavaScript generates the fixture or implements the modeled interval rule. The separately pinned executable traces and source audit provide that evidence. Together they identify an obstruction to simultaneously preserving the demo's measured behavior and proving ordinary exact-selection local formatting on all honestly reachable split/merge states. Five merge VCs cannot repair a failed local client effect. This does not settle the narrower split/insertion/deletion-only milestone.

The additional `local_split_zero` theorem states the independent ordinary split-at-zero rule for every text. `minimized_split_zero_rejects_ordinary_contract` checks the minimized target block `aX` against the observed `X | a`. The unchanged preceding empty block is outside this first-block fragment. Source reachability remains external evidence; this is a semantic counterpart, not a mechanization of the source execution.

## Generic transaction-storage shell

`NotionTransactionSet.lean` now instantiates the existing finite-store port with an arbitrary immutable transaction type. `fiveVCs` exposes the actual current `Raw.MergeVCs` bundle; `storageJoin` consumes its representation and replay-supply package; `same_events_render` derives equality for any deterministic renderer on two registered versions with the same event set. Its ordinary and canonical recursive-base specializations are checked. This reuses `SimpleConcretePorts.Finite.conditions`, whose represented execution states are constructed through `CommutingPort.automatedReplayConditions` and the five-VC induction.

The theorem is about storage convergence. Its renderer is an arbitrary parameter; it has no natural-text history or correctness contract. The issuance policy is unrestricted transaction insertion, not a verified translation of the demo's client. `adapter_union_agrees` checks equality with the runtime adapter's base-inclusive union when its accepted-input base-subset guard holds. It does not verify JavaScript parsing, object equality, or the guard implementation.

`Consistent`, `consistent_insert`, and `consistent_union` separately express the runtime adapter's key/payload discipline. The whole-value finite set can otherwise contain different payloads with one key. `identity_collision_control` checks individually consistent branches whose union conflicts. Deriving this property from fresh sessions and the actual issuer remains absent. These generic shell results establish neither a faithful Notion adaptation nor its independent sequential-history bridge.

## Full independent core machine and local clients

`NotionCoreSpec.lean` extends the initial fragment to an executable partial sequential machine. A document is an ordered list of identified blocks. Each block contains semantic slots with an instance name, a compound session/counter character or boundary name, a character value, and visibility. Distinct names express stable editing references; their numerical encodings carry no ordering. The framework's outer event time is separate from these payload names.

The machine supports creating a block after another identified block, inserting a character run after an origin found across all blocks, hiding a list of character identities globally, and splitting the current origin-owner block into a separately created target. The target's list position comes from creation after the request's original block. It need not be next to the origin's current owner in a concurrent witness. `concurrent_split_witness_control` pins that distinction with `a | cd | b` and rejects `a | b | cd`.

The machine has no transactions, replay sorting, clocks, source parent trees, source slices, or search labels. A grouped command sequence can represent one client update; it is not retained in the machine's state. `step` and `execute` return `none` on missing owners, absent predecessors/targets, reused block names, a split into its source block, or a visible split marker. Fresh character and marker names remain issuance obligations; the command executor deliberately does not certify them by accepting a command.

The positional preparation APIs are `prepareInsert`, `prepareDeleteRequest`, and `prepareSplit`. They find the requested block, validate visible bounds, and produce semantic commands. The valid deletion contract chooses `0 ≤ start ≤ stop ≤ visible length`; it does not inherit JavaScript's oversized or negative `slice` behavior. Preparation uses a retained head at index zero or the selected visible predecessor at a positive index. `prepareGap_succeeds` derives that the scan returns an address. `prepareInsert_success`, `prepareDelete_success`, and `prepareSplit_success` connect each executable API to its command(s).

`prepared_insert_effect`, `prepared_delete_effect`, and `prepared_split_effect` prove the complete local prepare/execute visible effects over arbitrary surrounding documents. The hypotheses are structural: globally unique semantic addresses and block names, a hidden head anchor, valid indices, and fresh new block/root names for splitting. The insertion theorem compares with the caller's requested character values. The deletion theorem proves exactly `take start ++ drop stop`. The split theorem executes creation followed by splitting and proves exactly the requested prefix/suffix in adjacent blocks. All three preserve the other blocks' displayed values. Their proofs derive ownership separation from address uniqueness and derive fresh-target uniqueness from the original structural conditions; none assumes the editing effect as an invariant.

`PreparedGap` permits a more general source-selected origin: it names an existing retained slot whose prefix contains exactly the requested number of visible characters. `preparedGap_visible` derives the split effect from that count and address uniqueness. This allows the source's active-leaf boundary at visible index zero even when the independent helper chooses the empty title root before it. The canonical helper is an independent local client, not a proof that the published client chooses the same origin under concurrent delivery.

These results do not yet derive the structural invariants from every source-generated execution. In particular they do not establish freshness of each inserted run/marker, global preservation after all generated concurrent histories, full source-document projection, or one RA witness satisfying all history orders. They prove local client correctness of the independent machine under structural hypotheses, rather than source correctness or the whole core milestone. The source normal-form/RGA files and `docs/notion-core-correspondence.md` track the separate correspondence investigation.

Run `lake build Sal.MRDTs.Instances.NotionCoreSpec`. The module includes hand-derived PASS+FAIL controls for split, crossing deletion, boundary insertion, global origin lookup with concurrent splits, and valid/invalid request bounds. It introduces no axioms or admissions; the local-effect theorems depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` where used.

## Derived independent-core structural invariant

`NotionCoreInvariant.lean` defines `Admissible` semantic commands and `Reach` from the empty document using the actual successful `NotionCoreSpec.step`. The guards describe input structure and freshness; none refers to the next document or assumes its visible effect or `WellFormed` status.

Creation requires a fresh block name and a fresh title-root address. Insertion requires a present semantic origin and a `FreshRun`: pairwise distinct inserted addresses disjoint from all current addresses. Deletion needs no additional freshness guard. Splitting requires a known origin-owner, a distinct allocated empty-root destination, a fresh hidden same-instance marker, and the destination's membership. Origins can be hidden. These are sufficient structural conditions, not a complete encoding of source issuance: insertion guards intentionally cover arbitrary fresh slot runs and do not assert source character-run shape; a split destination need not carry a proof that it was created in the same transaction.

`step_preserves` proves that every successful admitted command preserves the independent specification's actual `WellFormed` predicate: unique block names, globally unique slot addresses, and an invisible retained head in every block. The proof handles arbitrary split source/destination positions. Its key lemma, `trim_preserves_and_fresh`, derives that removing the source suffix leaves a well-formed remainder and makes the removed suffix plus a new marker a fresh run relative to that remainder. Appending this run to the empty title-root target then preserves unique ownership. This does not assume a split projection or visible result.

`admissible_progress` separately proves that admitted commands cannot get stuck on a well-formed input. `reachable_wellFormed` derives the invariant for every `Reach` document from `[]`; invariant preservation is not a guard of `Reach`. `hidden_origin_control` exhibits an actual admitted create/insert/delete/create/split execution, splitting after a deleted character and moving the following live character into the new block. Its negative control rejects moving that character into the old block. `freshness_control` accepts fresh character names and rejects reuse of an existing invisible root identity.

Run `lake build Sal.MRDTs.Instances.NotionCoreInvariant`. The theorem dependencies contain only standard Lean logical axioms. The remaining source obligation is to establish these semantic guards and the command projection from allocation and source editing executions. This module derives the invariant for the independent guarded semantic machine; it does not assert that every pinned demo execution maps to `Reach`, nor prove RA histories or a source/MRDT renderer correspondence.

## Source origin guards derived from uniqueness

`NotionCoreSourceGuards.lean` removes the manually supplied `OriginSafe` premise from accepted materialized-source steps. `originSafe_of_active` proves that an active origin cannot equal any attached block's inactive empty-title root: projected address uniqueness excludes both a duplicate within its own block and a collision with another block. `originSafe_of_owner` obtains the needed active membership from a successful owner lookup. Neither theorem requires a live origin.

`accepted_guard` derives the earlier source guard from input projected `WellFormed` and source acceptance. `step_sound` then projects each accepted source command to the exact independent semantic step, without assuming observation equality or supplying origin separation by hand. A source `Reach` relation starts at `[]` and uses semantic `Admissible` input checks plus actual accepted source transitions. `reachable_invariants` derives independent semantic reachability and projected `WellFormed`; it does not put either invariant in a transition guard.

PASS+FAIL controls distinguish a deleted character's active ownership from an attached block's inactive own root, check effective insertion after the hidden character, reject the inactive-root insertion, and exhibit an allocated-root reachable source state. Run `lake build Sal.MRDTs.Instances.NotionCoreSourceGuards`.

This closes one internal correspondence guard. The source `Reach` relation still requires semantic freshness/shape admission, which must be derived from the actual issuer; it does not turn semantic progress into source progress. Extracting the materialized model from the pinned JavaScript origin/endpoint structures and completing the RA history bridge remain separate obligations.

## Grouped physical history refinement

`NotionCoreHistory` gives the independent machine a prefix-closed history
language. Updates are atomic command groups; queries observe the current view
without changing state. `updates_query_iff` identifies acceptance with execution
of those same groups and the resulting answer. No ordering or replay condition
is embedded in this specification.

`NotionCoreSourceHistory` defines a physical renderer directly from text/deletion
and split-marker atoms, then proves `render_projection`. `runs_sound` maps every
guarded physical history to the independent history on the same ordered labels,
preserving queries between arbitrary update groups. `history_sound` lifts this
to language admission. Its source update relation uses the independently defined
physical `Execution`; it does not assume an accepted semantic history or answer
equality. The nonempty create/insert control rejects an empty answer.

This is a refinement theorem for the materialized source model. It has no
premise purporting to be a proved JavaScript extraction, no RA event enumeration,
and no issuance certificate connecting it to the transaction-set store. Those
remain separate from this checked history theorem.

## Source-selected local preparation

`NotionCorePreparation` models the pinned `locateInsertion` rule on the physical
core normal form. At a positive index it selects the preceding visible atom.
At zero it chooses the first slice containing visible text, falling back to the
last slice when every slice is empty. The one/two-node core shape therefore
selects the active slice's starting marker, including when that marker follows
an unused empty title root. This is not always the independent helper's address.

`locate_active_prepared` and `locate_prepared` derive retained-coordinate
membership and the visible prefix count from actual selection. `locate_progress`
proves every legal index produces an address. `delete_targets_projection` proves
that source visible range selection chooses exactly the independent semantic
identities, before ID-range compression.

`source_insert_effect`, `source_delete_effect`, and `source_split_effect` prove
successful physical normal-form execution and the ordinary whole-document
local effects. The split proof derives creation of an empty target, preservation
of the projected invariant after creation, source origin safety and split
progress; physical success is not assumed. It then uses the existing transition
projection to establish the prefix/suffix view. Its two-command split operation
encapsulates marker insertion and movement, so the actual JavaScript three-step
transaction still requires the raw tree/endpoint correspondence argument.

Allocated run and marker names are inputs. Immediate visible-effect theorems
are distinct from future invariant preservation: neither freshness nor exact
clock consumption follows from these results. Source insertion uses the located
instance, but contiguous run allocation and payload construction remain separate.
Empty source insertion/deletion emits no transaction; semantic empty commands
have the same immediate visible effect without proving identical issuance or
clock behavior. Range compression, string-atom encoding and block-key encoding
remain explicit decoder obligations. Atom values are opaque naturals, not an
assumed Unicode-scalar parse of concatenated display strings.

PASS+FAIL controls distinguish the inherited marker from the empty title root,
visible predecessors from tombstones, oversized indices, exact deletion identity
selection, and the physical zero-position split of an attached block. The pinned
four-case preparation oracle separately validates the source boundary, including
bootstrap transaction grouping and source receipt without dependency readiness.
