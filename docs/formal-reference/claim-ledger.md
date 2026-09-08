# Formal reference evidence ledger

This ledger records the evidence boundary for the principal displays and
claims in `main.tex`. The build gate checks declaration existence and
elaboration through
`Sal/MRDTs/Metatheory/FormalReferenceLedger.lean`.

Section 7 presents the sequential specification and its linearizability
predicate before issuance, issued steps, mint honesty, certified reachability,
and the correctness obligation. `MintCertifiedReach.step` explicitly takes
mint honesty before and after the issued step; the document does not infer it
from `CanIssue`. The sufficient `IssuanceEstablishes`/`JoinOn` adapters are
presented at the end of Section 8 after their inputs are defined, alongside the option
of proving replay adequacy directly. The source-order gate checks these
introductions and rejects the former `CanIssue ⇒ MintHonest` display.

| Reference claim | Status | Authoritative evidence |
|---|---|---|
| Events use natural-number replica IDs and timestamps; apply enforces global timestamp freshness and configurations enforce causal monotonicity. | Mechanized | `Framework/Base/UpdateSignature.lean`: `Replica`, `Timestamp`, `Op`; `Framework/Execution.lean`: `Configuration.causal_mono` and `Step.apply`. |
| The public datatype/certificate hierarchy is `D : MRDTSig` followed by `VerifiedMRDT D`; both use the datatype's ternary merge and neither exposes a binary merge. | Mechanized definition | `Framework/Signature.lean`: `MRDTSig`; `Metatheory/Correctness.lean`: `VerifiedMRDT`. |
| Paper notation `do` denotes Lean's `MRDTSig.update` field; the source avoids `do` because Lean reserves it as syntax. | Exact notation correspondence | `Framework/Signature.lean`: `MRDTSig.update`; `Framework/Base/UpdateSignature.lean`: `UpdateSig.update`. |
| Fork creates a fresh child version copied from an existing source head. | Mechanized | `Framework/Execution.lean`: `Step.fork`, `Step.fork_copies_source`, `Step.fork_head_ne_root`. |
| The paper configuration is `\<S,H,P,vis\>`, with `S` and `H` written as partial maps and `H` ranging over `dom(S)`; head state and head events are partial compositions through `H` and `S`. | Exact notation correspondence | `Framework/Execution.lean`: `Configuration.ver`, `head`, `parents`, `vis`, `headState`, `headEvents`, and `head_alloc`. Lean totalizes the partial maps with `Option`; the observations are functions, not stored cache fields. |
| Replay ordering uses only the replica-indexed head-event map, visibility, globally distinct observed timestamps, and visibility comparability of distinct same-replica events. | Mechanized definition and exact projection | `Framework/Base/ReplayContext.lean`: `ReplayContext`, `ReplayContext.events`; `Framework/Execution.lean`: `Configuration.replayContext`. |
| The ordinary merge predicate is a greatest common ancestor, unique when present. A DAG can instead have multiple incomparable maximal common ancestors and no such greatest ancestor. | Mechanized definition and theorem | `Framework/Execution.lean`: `IsGCA` and `IsMaximalCommonAncestor`; `Metatheory/StoreInvariant.lean`: `isGCA_unique`. |
| Ordinary merge uses a registered GCA and ternary merge; virtual merge uses the canonical resolver without allocating a base version. | Mechanized | `Framework/Execution.lean`: `Step.merge`, `StepV.mergeVirtual`; `Metatheory/VirtualMergeBase.lean`: `canonicalVirtualMergeBase`. |
| A stored real GCA has exactly the intersection of branch event sets. | Mechanized | `Metatheory/StoreInvariant.lean`: `StoreInv`, `gca_events_of_storeInv`. |
| Replay arbitration is relative to the event set being replayed. | Mechanized definition | `Metatheory/Join/SetRelativeReplay.lean`: `Foundation.loOn`. |
| Every verified package supplies exactly one `rc` policy. `loOn` retains visibility only for pairs classified as conflicting, and all-`Either` contributes no edge. LWW supplies a timestamp-directed policy. | Mechanized definitions and source concordance | `Metatheory/Correctness.lean`: `VerifiedMRDT.rc`; `Metatheory/Join/HistoricalReplay.lean` and `Metatheory/Join/SetRelativeReplay.lean`: `lo`, `loOn`; `Instances/LWWRegister.lean`: `rc`. |
| Under the sufficient replay laws, respecting enumerations of the same finite event set fold to the same state. Coverage is one-way; conditional swaps use semantic `rc` absorbers; acyclicity excludes every nonempty `rc` cycle. Ordered updates may commute. | Mechanized | `Framework/ReplayLaws.lean`: `ReplayLaws.noncomm_covered`, `ReplayLaws.cond_comm_lift`, `RcAcyclic`, `convergence_on_of_replayLaws`. |
| All-commuting concrete updates support every acyclic semantic `rc`. The merge-law bundles and ordinary/virtual adapters carry the selected policy explicitly. | Mechanized sufficient proof route, not a public semantic axiom | `Framework/ReplayLaws.lean`: `ReplayLaws.of_all_comm`; `Framework/MergeLaws.lean`: `MergeLaws`, `JoinCoreLaws`, `FeasibleDeltaLaws`, `CausalDeltaLaw`, `CanonicalJoinLaws`; `Metatheory/Adequacy.lean`: `causalDeltaLaw_of_all_comm`; `Metatheory/VirtualAdequacy.lean`: `replayWitnessV_of_delta`. |
| `CanonicalConfig` is the inductive invariant over every allocated version; `HasReplayWitness` is its internal projection. | Mechanized | `Metatheory/Adequacy.lean`: `CanonicalConfig`, `HasReplayWitness`, `hasReplayWitness_of_canonical`. |
| `JoinAt` is the single contextual merge-preservation obligation; `Join` requires it at every replay context and `JoinOn` restricts it by an explicit context predicate. | Mechanized definition | `Framework/MergeLaws.lean`: `JoinAt`, `Join`, and `JoinOn`. |
| `CanonicalJoinLaws` is the single reusable canonical-state contract for all-context Join; the arbitrary-state constructor first adapts universal equations to that contract. | Mechanized | `Framework/MergeLaws.lean`: `CanonicalJoinLaws`; `Metatheory/Adequacy.lean`: `CanonicalJoinLaws.join`, `CanonicalJoinLaws.ofArbitrary`, and `JoinProof.ofArbitraryStateLaws`. |
| Internal replay is not the public theorem; public correctness additionally requires sequential legality, a state relation, and equality of every query. | Mechanized definition and theorems | `Metatheory/Correctness.lean`: `IsSpecLinearizable`, `VerifiedMRDT.correct`, `VerifiedMRDT.correctV`. |
| The LWW register uses the same timestamp-directed `rc` in concrete replay laws, Join, and sequential correctness, even though its `max` updates commute. The direction is acyclic, permits nontrivial chains, and a sorted `loOn` witness refines the stored maximum to a total overwrite register. The old concrete-noncommutation biconditional is refuted by ordered commuting writes. | Mechanized | `Instances/LWWRegister.lean`: `rc`, `replayLaws`, `join`, `rc_order_acyclic`, `timestamp_chain`, `canonical_respects`, `verified`, `chronological_winner`, `lower_timestamp_does_not_win`, `ordered_updates_commute`, `concrete_noncomm_iff_rc_refuted`, and `reversed_assignments_wrong_winner`. |
| The retired tagged OR-set fixture proves all-context Join and refines to the ordinary `Finset` specification. Its `rc` gives `Either` to cross-key and same-kind pairs and resolves a same-key remove before an add. | Mechanized positive theorem and controls | `Metatheory/Countermodels/TaggedORSet.lean`: `rc`, `spec`, `setSequentialCorrectness`, `cross_key_rc_either`, `same_key_rc_add_wins`, `observed_remove_removes`. |
| RGA stores grow-only insertion and deletion facts internally, permits insertion only at root or a live anchor, and refines issuance-certified executions to an ordinary `List Nat` specification. Its `rc` covers sibling/dependent insertions and insertion/deletion conflicts. | Mechanized definitions and theorems | `Instances/RGA.lean`: `RGAM`, `join`, `applicable`; `Instances/RGASequential.lean`: `listSpec`, `rc`, `canonical_respects_rc`, `listSequentialCorrectness`, `verified`. |
| Queue uses one `rc`: enqueue/enqueue edges follow the lexicographic enqueue key, and an enqueue precedes a dequeue naming its tag. For the same ordinary or virtual certified execution, the public theorem proves legal FIFO replay with head observation, exact timestamp-ordered surviving contents, and concurrency of duplicate dequeue targets. Linear mint histories refine to the ordinary FIFO value sequence. | Mechanized public certificate and combined contract | `Instances/Queue.lean`: `qRcOrder`, `rc`, `q_join_at`; `Instances/QueueContract.lean`: `clientSpec`, `client_linear_fifo`; `Instances/QueueLegalization.lean`: `queue_legal_witness`, `verified`; `Instances/QueueCorrectness.lean`: `queue_correct`. |
| The enriched FugueMax implementation retains immutable birth/origin metadata for its exact positional issuer. Its sole `rc` orders insertion before deletion of that identity. One witness proves plain-list legality, refinement, query agreement, and maximal non-interleaving for the same ordinary or virtual certified execution, without a separate `MaxReach` premise. The old coordinate-only `FMSig` remains internal. | Mechanized public certificate and same-witness contract | `Instances/FugueMaxImplementation.lean`: `datatype`, `generation`, `rc`; `Instances/FugueMaxContract.lean`: `listSpec`, `listRel`, `verified`, `correct`. |
| MVR's concrete state and public specification are finite sets of live tagged values; the query exposes only values. Its observed-supersession `rc` is used throughout replay and public correctness. For the same ordinary or virtual certified execution, `mvr_correct` proves public linearizability and that live writes are exactly the causally maximal events of every version. Linear mint histories expose the last written value. | Mechanized public certificate and combined contract | `Instances/MVRLive.lean`: `D`, `canIssue`, `rc`, `spec`; `Instances/MVRLiveCertified.lean`: `represented_of_mintCertifiedV`; `Instances/MVRLiveContract.lean`: `verified`, `mvr_correct`, `linear_register`. |
| The typed datatype-state GC registry covers all 22 production packages and distinguishes exact-state baselines, representation-changing certificates, operational protocols, and staged collectors. LWW, Queue, compact MVR, and the efficient OR-set have non-collecting exact-state baselines. RGA has a lossless `(id,parent)`/live-set compactor; its guard rejects insertion after an observed anchor deletion while retained tombstones remain available for concurrent integration. AegisSheet, TreeMove, and rich SidedPeritext carry the other representation-changing proofs. FugueMax remains staged; the tagged OR-set is no longer registered; MVR discards overwritten values during normal updates. | Mechanized coverage classification plus checked collectors | `Metatheory/StateGCCoverage.lean`: `StateGCCoverage`, `Production.StateGC.registry`; `Instances/RGAGC.lean`: `certificate`, `packedWords_pack_lt_of_live_lt_grave`, `future_after_dead_anchor_not_applicable`; `Instances/AegisSheetGC.lean`: `certificate`; `Instances/TreeMoveGC.lean`: `protocol`; `Instances/SidedPeritextProtocol.lean`: `protocol`. |
| TreeMove's sequential state is the ordinary parent tree; the replicated event set is not copied into the specification. | Mechanized | `Instances/TreeMove.lean`: `spec`, `stateRel`, `sequentialSound`. |
| The recursive maximal-common-ancestor fold is canonical for the intersection event set and preserves widened adequacy. | Mechanized | `Metatheory/VirtualAdequacy.lean`: `virtualMergeBaseState_canonical`, `canonicalConfig_reachableV`, `replayWitnessV_of_join`. |
| Root-free compression closed under pairwise maximal common ancestors preserves reachability and GCA answers between retained versions. | Mechanized | `GC/CompressedDAG.lean` and `GC/Distributed.lean`: `Certificate.ofMaximalCommonAncestorClosed`. |
| Distributed commit collection refines the asynchronous no-GC protocol by stuttering. | Mechanized | `GC/Distributed.lean`: `execution_refines_noGC`; `GC/Refinement.lean`: `runtime_refines_core` and `runtime_refines_coreV`. |
| Datatype-state collection refines widened semantics and composes with commit-history collection. | Mechanized | `Framework/StateGC.lean`: `StateGCProtocol.refines`; `GC/StateComposition.lean`: `CombinedSteps.refinesV` and `refinesRaw`. |
| The production boundary contains 22 typed `PackagedMRDT` entries, including complete public certificates for Queue, MVR, and the exact enriched FugueMax implementation. Rejected-target and replay-only companion evidence remains checked. | Mechanized registry and status boundary | `Metatheory/ProductionLedger.lean`: `Production.registry`; `Instances/QueueLegalization.lean`: `verified`; `Instances/MVRLiveContract.lean`: `verified`; `Instances/FugueMaxContract.lean`: `verified`, `correct`; `Metatheory/NegativeLedger.lean`. |
| The historical global-absorber convergence statement and binary-lattice-to-Join implication have checked counterexamples. | Mechanized negative evidence | `Foundation.convergence_over_backward_closed_subsets_false` and `Foundation.binaryLaws_insufficient`, gated through `NegativeLedger.lean`. |
| `UpdateSig` and `MRDTSig.toUpdateSig` are merge-free internal views used for event application, finite replay, and commutation; they are not a second datatype interface. | Mechanized definition | `Framework/Base/UpdateSignature.lean`: `UpdateSig`; `Framework/Signature.lean`: `MRDTSig.toUpdateSig`. |
| Historical binary proofs request `HistoricalBinaryMerge` explicitly and call it through `UpdateSig.historicalMerge`. The MRDT compatibility instance supplies the initial-state slice of ternary merge; binary merge is absent from the live MRDT and verified-MRDT interfaces. | Mechanized definition and source-boundary statement | `Framework/Base/UpdateSignature.lean`: `HistoricalBinaryMerge`, `UpdateSig.historicalMerge`; `Framework/Signature.lean`: `MRDTSig.historicalBinaryMerge`; absence from `MRDTSig` and `VerifiedMRDT`. |

Section 11.1 presents grow-only stores and counters in separate semantic
profiles; their shared universal-law proof route is recorded in Section 11.2.
This is a presentation change, with no change to the underlying contracts.
The profiles introduce operation payloads and the event envelope before use,
then separate `D`, `rc`, issuance, and the sequential specification. The PDF
source gate checks these four blocks in dependency order. The sole OR-set profile
presents Neem's efficient per-replica/per-element implementation. It has a complete public
certificate in `EfficientORSetCertified.lean`, including recursive virtual
merge bases, and is registered as `efficient-or-set`. Its proof
uses causal live-record histories and exact-state sorted replay, not an
all-state Join claim for incompatible replays. The cached source is
`_references/neem_fstar_repo/code/mrdts/OR-set-efficient/App_mrdt.fst`.

The instance-profile presentation audit expands initial states, concrete and
abstract updates, observations, and representation relations beside issuance
and `rc`. In particular, bounded-counter `ClientLegal` checks balance at every
prefix, not membership in a canonical normal form; Boolean grow-only merge
includes the ancestor; OR-set observes membership; and core SidedPeritext
component queries differ from its rich Boolean-formatting query. These are
definition-level claims, checked against `FlatGrowOnly.D`,
`BoundedCounter.ClientLegal`, `ORSet.spec`, `SidedPeritext.clientSpec`, and
`SidedPeritext.richClientSpec`. The reference ledger also checks the expanded
sequence steps, sheet materialization, mark-boundary renderer, and three
FugueMax non-interleaving predicates. The PDF gate checks every profile heading;
heading coverage is not a proof of prose equivalence or human contract review.

The document deliberately makes no implementation-extraction claim. Runtime
correspondence remains a separate validation boundary.

## Whole-document audit and RGA simplification

| Claim | Evidence class | Artifact | Scope / correction |
|---|---|---|---|
| RGA insertion carries only its anchor; the event timestamp is the identifier, and births store `(identifier, anchor)` pairs. | Machine-checked definitions and certificates | `RGA.RGAOp`, `RGA.RGAM`, `RGA.verified`, `RGA.rga_spec_linearizableV` | No separate identifier-equality guard or redundant birth field. The public ordinary-list specification and conflict relation retain their intended meanings. |
| Replacing graves by live IDs is lossless, but not always smaller after the pair simplification. | Machine-checked theorem and positive/negative controls | `RGA.GC.unpack_pack`, `certificate`, `packedWords_pack_lt_of_live_lt_grave`, `all_live_conversion_grows`, `all_deleted_conversion_shrinks` | Savings require fewer live IDs than graves; no identifier reclamation theorem is claimed. |
| Observed dead anchors reject local issuance, while concurrently issued children survive merge. | Machine-checked issuance controls; validated runtime controls | `RGAGC.lean`; `runtime/test/rga.test.js` | The PeritextRGA wrapper has a different shadow-state contract and its erasure counterexample is not a plain-RGA impossibility theorem. |
| Canonicality means existence of a respecting fold; uniqueness and Join are sufficient proof routes, not requirements of every public package. | Machine-checked definitions and counterexample | `IsCanonicalState`, `EfficientORSet.SPOT.three_replay_choices`, `EfficientORSet.verified` | Sections 1, 5, and 6 no longer overstate uniqueness or require the efficient OR-set to satisfy arbitrary-replay Join. |
| Historical `lo` agrees with full-set `loOn` only with supported visibility targets. | Definition-level comparison | `HistoricalReplay.lo`, `SetRelativeReplay.loOn` | Section 4 now states the support condition; projected configurations satisfy it. |
| The binary countermodel refutes `BinaryJoin`, not a displayed ternary Join statement. | Machine-checked negative theorem | `Foundation.binaryLaws_insufficient` | Appendix B narrowed to the theorem's actual conclusion. |
| Every printed anchor resolves and both coverage counts match the public-contract manifest. | Validated build gate | `scripts/check-formal-reference-citations.mjs`, `scripts/test-formal-reference-citations.mjs` | Stale-name, missing-path, malformed-label, and stale-count controls. This does not mechanically establish prose equivalence or human approval. |

The review also corrects the commuting-predecessor explanation (swapping is
not erasure), defines branch compatibility and the embedded-RGA honesty
conditions before use, identifies the mutually recursive virtual-base
definitions, and includes Queue, MVR, and efficient OR-set in the proof-route
table. Sequential legality may impose additional list-order constraints;
the text no longer claims that `rc` is the only place any such constraint
can occur.

The RGA insertion edge is now `(a = b ∨ i = b) ∧ i < j`: siblings or a
forward parent–child dependency. `RGA.rc_insert_iff` checks the displayed
definition, and `RGA.rc_insert_iff_original_of_execution` proves agreement
with the former three-disjunct expression on certified version histories.
The reverse resolver verdict checks the reversed directed condition; controls
cover both argument orders of a parent–child pair. No new conflict predicate
was introduced; the old symmetric helper was removed.

## Completion of the presentation and order-proof review

The order-only core now lives in `Metatheory/Join/SetRelativeReplay.lean`:
`loOnNe_acyclic_of_policy_paths`, `exists_loOn_respecting_perm_of_acyclic`,
and `exists_loOn_maximal_of_acyclic`. Generic finite enumeration is shared
through `Framework/Base/FiniteOrder.lean`. Replay-law, client-correctness,
and historical no-chain results instantiate these helpers instead of
maintaining separate acyclicity and enumeration proofs. Existence needs
acyclicity, not the concrete-update laws required for fold uniqueness.

Section 4 now introduces the directed `rc` relation, then `loOn` and its
absorber, then sufficient replay laws. The mathematical relation is binary;
the executable three-valued carrier alone does not imply reversal coherence.
The certificate theorem has three joint premises, with the selected policy
explicit. Raw reachability takes the step relation as an ordinary argument.
Detailed merge-law adapters are in Appendix D; the TikZ redistribution
diagrams and their law definitions are together in the main text.

The redundancy review distinguishes issued histories from arbitrary raw
inputs. `MVRLive.rc_iff_overwrite_of_execution` proves that the timestamp guard
is implied by issuance for an issued target write. The raw guard remains
necessary to the unrestricted acyclicity argument. LWW and Queue profile
tie breakers are identified as raw-input cases, and efficient OR-set record
uniqueness is stated as a certified-execution invariant. Local live-anchor,
head, and resource-availability checks are issuance requirements, not
discarded as apparent duplicates of resolver conditions.

Validation: both theorem ledgers and the public certificate target build;
the public gate accepts 23 exact ordinary/virtual contracts with its axiom
audit; 291 distinct printed anchors resolve; all three citation/count
mutation tests and the definition-order gate pass. The reference PDF was
rebuilt and inspected. The full `check-working-papers.sh` gate also passes,
including rebuilding all three working-paper PDFs. These checks do not complete the separate human
semantic audit, approve every contract, or establish runtime extraction.

## Explicit sequential definitions for every datatype profile

This follow-up corrects the previous review's weak completeness criterion:
mentioning a step, legality predicate, or query does not define its behavior.
All 15 datatype profile blocks now state the abstract initial state, step,
legality, query, and representation relation with equations or an explicit
specialization of a preceding definition. Concrete state-component meanings
are also made explicit where they were previously implicit.

| Profile | Definition-level source | Edge cases made explicit |
|---|---|---|
| Grow-only stores | `AddStore.spec`, `FinsetStore.spec`, `FlatGrowOnly.spec` | Repeated addition is idempotent; Boolean maps store pairs rather than overwrite keys. |
| Counters | `FlatCounters.spec` | PN decrement can produce negative values. |
| LWW | `LWWRegister.spec`, `stateRel` | Abstract writes always overwrite; key ordering belongs to the witness. |
| MVR | `MVRLive.spec`, `MVR.clientStep`, `clientLegal`, `queryValues`, equality | Previously overwritten targets need not remain live; equal values collapse in the query. |
| Bounded counter | `BoundedCounter.clientSpec`, `ClientLegal` | Total decrement can produce a negative coordinate; prefix legality excludes it. |
| Efficient OR-set | `EfficientORSet.spec`, `stateRel` | Removing an absent element is a no-op. |
| Tagged OR-set | `ORSet.spec`, `stateRel` | Abstract removal ignores observed tags and removes the element idempotently. |
| RGA | `RGA.listStep`, `listLegal`, `listRel` | Missing anchor insertion and absent-target deletion are no-ops; earlier allocation, not continued liveness, is the legality condition. |
| TreeMove | `TreeMove.doMove`, `visibleTree`, `ClientLegal`, `stateRel` | Cyclic moves are no-ops; trash hides a subtree without erasing its bindings. Public legality additionally requires an issuable origin in each replay prefix. |
| AegisSheet | `AegisSheet.Sequential.step`, `view`, `CausalOriginLegal`, `materializedStateRel` | Axis removal retains positions/cells; empty cell writes still keep axes; undo applies the carried action; purge deletion and query masking are distinct. |
| EmbedRGA / Peritext | `EmbedRGA.eSpecStep`, `ProductionRGA.embedLegal`, `embedRel` | Missing anchors and absent deletions; coordinate metadata participates in legality, not abstract insertion. |
| SidedEmbedRGA | `SidedEmbedRGA.sSpecStep`, `ProductionRGA.sidedLegal`, `sidedRel` | Before/after first parent occurrence, absent-parent no-op, root-filtered query. |
| SidedPeritext core/rich | `SidedPeritext.richSpec`, `clientSpec`, `coreRel`, `richClientSpec` | Store additions are idempotent; raw text deletion has a step but issuance forbids it; core and rich queries differ. |
| Queue | `Queue.clientStep`, `clientLegalAux`, `clientSpec` | Wrong-live-head deletion is a no-op but illegal; previously allocated absent targets remain legal. |
| FugueMax | `FugueMax.listStep`, `listLegal`, `listSpec`, `listRel` | Root deletion is a no-op; insertion requires an allocated, not-yet-deleted parent; repeated deletion is allowed. |

Evidence class: definition-level correspondence checked against the cited
Lean sources; no implementation or contract changes in this pass.
`check-formal-reference-profiles.mjs` checks each block, including the nested
SidedPeritext block, for explicit sequential components and Lean citations.
Its mutation tests remove component notation while preserving the headings.
This is a structural regression guard, not a semantic proof of the prose.
The separate citation gate resolves the actual printed names. Human review
of whether these contracts express the desired behavior remains pending.

Validation for this pass: all 15 profile blocks pass the structural check;
its six tests pass; 306 distinct citations resolve; the full working-paper
gate (including Lean ledgers, citation mutation tests, and all three PDF
builds) passes; the public gate still accepts all 23 ordinary/virtual
contracts with its axiom audit. The expanded reference layout was inspected,
including the sheet equations and sequence profiles.

## Redundant AegisSheet freshness check

Removed the explicit timestamp-nonmembership test from `applicableB`.
`ClockedAt.fresh` derives it from the retained strict clock condition.
`applicable_iff_explicit_freshness` proves that the full issuance predicate
is equivalent to reinstating the former Boolean conjunct, on all inputs.
The standalone non-clock helper is intentionally weaker; it is not itself
the complete issuance predicate. GC freshness now uses the clock theorem.
Named controls accept a valid edit and reject timestamp reuse in full
issuance even when the non-clock helper accepts the remaining metadata.
No other resolver, issuance contract, or sequential specification was weakened.
Validation: affected Lean targets and the full working-paper gate pass;
all 23 public contracts pass the certificate/axiom gate; 308 citations resolve.
The equivalence theorem uses only the standard Lean axioms. All PDFs were
rebuilt with the corrected issuance explanation.

## Diagram restoration, TreeMove contract, and integrated catalogue

The two TikZ redistribution diagrams are again adjacent to their laws in
the main text; only the detailed merge-law adapters remain in the appendix.
Generic verification certificates now close Section 8, before collection
uses them. History and datatype-state collection occupy Sections 9 and 10;
the complete datatype catalogue follows in Section 11. Collection profiles
are integrated with each datatype rather than repeated in a separate section.
They distinguish exact-state baselines, local certificates, operational
protocols, and staged work, and state the relevant preservation conditions.

TreeMove preserves its issuance restrictions and ordinary tree state.
`ClientLegal` adds an issuable origin contained in each event's replay
prefix to chronological sorting. The public correctness proof derives these
origins from mint honesty. `clientLegal_origin` is now a required registry
obligation. `clientLegal_firstMove` is a positive control;
`sorting_accepts_reserved` and `clientLegal_rejects_reserved` demonstrate
the strengthening over sorting alone. This supersedes the earlier observation
that issuance was unnecessary for TreeMove's public sequential legality;
the internal sorted-fold theorem remains valid with its weaker premises.

Validation: affected Lean targets compile; the public gate accepts all 23
exact ordinary/virtual contracts and its axiom audit passes. All 15 profile
blocks and seven profile tests pass; all 310 distinct printed citations
resolve. The full working-paper gate passes and rebuilds all three PDFs.
The diagram pages, TreeMove contract, and collection-to-catalogue transition
were visually inspected. Source-order guards now enforce this organization.
Human review of the intended contracts remains pending.

## Compact MVR release

The registered MVR now uses `MVRLive.D`: a finite set of live timestamp/value
pairs. `issued_write_singleton` proves local replacement; replay removes only
the event's observed targets. Merge uses the ancestor-relative set formula.
There is no concrete grow-only write or overwrite-log field.

`MVRLiveHistory.issued_overwrite` derives target presence and causal precedence
from mint honesty. `MVRLiveVirtual.virtualMergeBaseState_represents` covers the
recursive antichain algorithm, and `represented_of_mintCertifiedV` proves the
surviving-write invariant and replay adequacy for every certified widened
execution. `MVRLive.verified` packages the unchanged live-set sequential machine
and legality with equality as the representation relation. Its required
`mvr_correct` and `linear_register` obligations prove causal maximality and
the ordinary register special case for this exact replacement signature.

The production and collection registries now select this certificate. Collection
is classified as exact-state because normal updates already remove overwritten
values; this does not establish collection of commit versions or event payloads.
The former grow-only model remains internal proof/reference material. A new
gate mutation rejects its certificate as evidence for the compact implementation.

Validation: all 23 exact public contracts and their axiom audit pass; all 13
public-gate tests pass. The MVR campaign passes 1,500 generated cases and 1,024
exhaustive binary-choice traces; its union mutation shrinks to `[0,0,0]`.
The paper gate passes, resolving 308 printed citations and rebuilding all three
PDFs. The MVR pages were visually inspected. The principal new theorems use
only the standard Lean axioms. Human semantic review and standalone runtime
correspondence are not claimed by this migration.
The complete `check-mrdt-refactor.sh` release script also passes, including
the existing runtime regression suite and benchmark-result schema validation.

## Tagged OR-set retirement

Removed the tombstone tagged-set profile, its Lean production/collection
entries, its public contract, and its JavaScript release entry. The efficient
OR-set is the sole released OR-set. The registries now contain 22 Lean
packages and four runtime entries; no JavaScript port of the efficient set
is claimed. The former Lean model was moved, with its existing proofs intact,
to `Metatheory/Countermodels/TaggedORSet.lean` for negative controls. The old
JavaScript module remains comparison-only for historical regression tests.

Validation: all 22 exact contracts and 13 public-gate tests pass; the full
refactor script passes, including 187 runtime tests and benchmark-schema
validation. The paper gate checks 14 profiles, eight profile tests, and 303
printed citations. All three PDFs were rebuilt; the efficient-set-to-RGA
transition was visually inspected. A profile mutation test rejects restoration
of the retired tagged-set heading. Earlier validation counts in this ledger
describe their historical passes, not the current registry.
