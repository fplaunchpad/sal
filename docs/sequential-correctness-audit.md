# Sequential correctness API audit

This audit records the redesign of the public MRDT correctness boundary. It
separates executable behavior, origin issuance, abstract sequential meaning,
and proof-local invariants.

## Research question

- **Goal:** Give every public RA witness an independent sequential meaning
  without exposing proof scaffolding as part of the datatype API.
- **Candidate:** `MRDTSig`, `Issuance`, `SequentialSpec`, and `VerifiedMRDT`
  suffice for the public theorem. Datatypes may use invariants and conditioned
  commutation internally, but the framework does not require them as fields.
- **Falsifier:** a production representation needs reachable-state
  commutation to state the arbitration order, even though issuance and
  sequential legality remain independent of implementation state.
- **Formal oracle:** `IsSpecLinearizable`, both RGA capstones, the total
  grow-only canaries, and the issuance/legality SPOTs.
- **Reality oracle:** The RGA specification remains an ordinary list with
  physical deletion, and directed duplicate-delete and deleted-anchor
  scenarios agree with that specification.

## Public API

`Issuance.CanIssue` is the only origin-side premise. A certified apply step
checks it at the issuer's materialized head. `MintHonest` retains the causal
origin witness needed after the issuer advances.

`SequentialSpec` supplies:

- an abstract state, initial state, and deterministic step;
- `Legal`, a predicate over abstract event histories; and
- the abstract query function.

`Legal` cannot inspect `D.State`. This keeps implementation metadata out of
the sequential contract. A total datatype sets `Legal` to `True`.

`VerifiedMRDT` supplies issuance, a public `InteractionSpec`, widened
convergence, the sequential specification, a representation relation, and one
`SequentialCorrectnessCertificate`. Ordinary
certified execution embeds in widened execution, so the package stores no
duplicate ordinary convergence theorem. `VerifiedMRDT.correct` and
`convergesV` both produce
`IsSpecLinearizable`.

`SafetyCertificate` and `StateGCCertificate` are orthogonal optional packages.
Safety likewise stores only widened preservation and derives ordinary
preservation through the execution embedding.

`ReplayAdequateMRDT` retains the older raw-fold theorem under an explicitly
internal name while production datatypes migrate. It does not establish the
public sequential result.

## Removed public fields

The redesign removes these fields:

- `GenerationContract.History`: convergence proofs derive any local history
  invariant directly from `MintHonest`.
- `SemanticConditioning.Inv`: reachable-state invariants belong in local
  proofs or `SafetyCertificate`.
- `SemanticConditioning.Applicable`: sequential legality belongs to
  `SequentialSpec.Legal`.
- `GuardBridge`: the end-to-end theorem never consumed it.
- `ConditionedVerifiedMRDT`: `VerifiedMRDT` now denotes the strengthened
  package directly.

## RGA result

RGA's public sequential state is `List Nat`. Its step inserts after an anchor
and physically removes a deleted identifier. `listSpec.Legal` states only
facts about the abstract event list:

- event timestamps are unique;
- each inserted identifier equals its timestamp;
- every non-root anchor was inserted earlier; and
- every deletion target was inserted earlier.

Deletion does not remove an identifier from the legality predicate's
allocation history. Therefore concurrent duplicate deletes remain legal and
idempotent. The implementation may retain tombstones, but the sequential
state does not.

`rga_spec_linearizable` and `rga_spec_linearizableV` are machine-checked.
They select the exact version event set, respect `lo`, satisfy
`listSpec.Legal`, refine the ordinary list, and agree on query results.

## Checked controls

The gate SPOT shows that two operations can each be issuable at independent
origins while no merged serialization satisfies a resource-consuming
sequential specification. Origin issuance alone therefore cannot establish
sequential legality.

The RGA SPOT shows that reusing the strict origin predicate as sequential
legality rejects two concurrent deletes of the same live identifier. The
public RGA specification accepts the idempotent merged history instead.

The queue SPOT remains a negative result. Two replicas can dequeue the same
observed head. The named-delete implementation retains the second element,
while a plain FIFO replay performs two pops. The current queue must gain an
exactly-once dequeue protocol, adopt another specification, or remain outside
the public `VerifiedMRDT` package.

The EmbedRGA audit found a separate arbitration control.
`unrelated_insert_delete_not_raw_comm` exhibits an insert and a deletion of an
unrelated identifier that fail universal `UpdateSig.commutes` only on an
unsorted representation state. Such states are unreachable by the EmbedRGA
fold. Consequently, a legal all-insertions-before-deletions merged witness can
still fail the current raw-`lo` obligation because `lo` observes conflicts on
malformed states. `embedCanonical_seqOK` proves that the same witness is
prefix-legal for every reachable EmbedRGA version, including concurrent
duplicate deletion. This isolates the remaining issue to arbitration, not
generation or sequential legality.

This control falsified the strongest form of the original candidate API claim:
local proof use of an invariant was not enough while the public correctness
target hard-coded universal raw-state commutation. The repaired API supplies
an explicit `InteractionSpec`. EmbedRGA and SidedEmbedRGA now prove that their
canonical legal witnesses respect those semantic dependence policies without
putting implementation state inside `SequentialSpec.Legal`.

The proof-level replay algebra contains no resolver. The absorber-based
convergence route receives a proof-local `ReplayPolicy`; it is not the public
interaction policy. `InteractionSPOT.LWW.old_no_chain_refuted` checks that a
valid LWW timestamp order contains a length-two edge chain, so the historical
`no_rc_chain` condition cannot be a framework requirement. The add-wins SPOT
checks remove-before-add for concurrent conflict and add-before-remove when
visibility records that the remove observed the add.

The same legalization composes through Sided Peritext. Both its internal
three-component core and its production `RichCore` query signature now have
full `VerifiedMRDT` packages. The latter theorem covers the actual
document-order rich-text render, not only raw component stores.

AegisSheet exposed a different issue. Its old `GuardedChronological` predicate
rechecks an event against the entire serialization prefix. The checked
`concurrent_origins_not_guarded_chronological` example contains two operations
that are each applicable at an empty origin; any serialization makes one
follow an operation it did not observe. The repair validates each event
against its encoded causal origin view. `canonical_causalOriginLegal` derives
those origins for every certified version, while
`causalOriginSequentialSound` proves exact state and observation refinement.
The ordinary and virtual-merge-base capstones are `AegisSheet.spec_linearizable` and
`AegisSheet.spec_linearizableV`.

That repair does not make the reference machine a conventional visible-sheet
ADT. `AegisSheetAbstraction.no_view_only_step` uses two reachable states with
the same complete view and one common causal-origin-legal removal whose views
diverge. Companion checked controls establish the same lower bound for active
cell and range write identities. Observed-remove tokens and active version
identities are therefore semantic history required by the published conflict
and selective-undo behavior. The public theorem targets a causally aware
incremental spreadsheet machine; it does not claim that visible rows, columns,
cells, and ranges alone determine future behavior.

## Production sequential-specification audit

The source-of-truth order for this audit is the typed
`Production.registry`, the `VerifiedMRDT.Spec` and `Rel` definitions named by
each entry, their machine-checked correctness certificates, and finally the
explanatory documents. A sequential state is not rejected merely because it
uses the same mathematical carrier as the implementation. That is appropriate
when the carrier is already the client abstraction, such as an integer counter
or a grow-only set. A specification is an implementation mirror when it keeps
representation-only data that neither determines an abstract transition nor
an abstract observation, or when it interprets a representation payload as
the client operation without a proved abstraction bridge.

| RDT | Sequential state and operation meaning | Audit result |
| --- | --- | --- |
| grow-only-set | Mathematical set; add inserts an element. | Correct abstract carrier. `CanIssue := True`. |
| add-store | Mathematical set; add inserts an element. | Correct abstract carrier. `CanIssue := True`. |
| finite-add-store | Finite mathematical set; add inserts an element. | Correct abstract carrier. `CanIssue := True`. |
| counter | Integer; every operation adds one. | Correct abstract carrier. `CanIssue := True`. |
| increment-only-counter | Integer; increment adds one. | Correct abstract carrier. `CanIssue := True`. |
| pn-counter | Integer; increment/decrement add `+1`/`-1`. | Correct abstract carrier. `CanIssue := True`. |
| flat-grow-only-set | Characteristic function of a mathematical set. | Correct abstract carrier. `CanIssue := True`. |
| flat-grow-only-map | Characteristic function of immutable key/value entries. | Correct abstract carrier. `CanIssue := True`. |
| bounded-counter | Per-replica abstract balances; increment and decrement change the named balance. | Independent of the concrete pair of grow-only component maps. Issuance is load-bearing for rights-respecting legality and safety. |
| rga | Ordinary list of stable identifiers; insert splices after an anchor and delete physically filters an identifier. | Correct abstraction; no tombstones or insertion-edge store. Issuance is load-bearing for list legality. |
| embed-rga | Ordinary list of identifier/payload pairs. | Correct abstraction; no coordinate records. Issuance is load-bearing for anchor legality and the conditioned merge proof. |
| sided-embed-rga | Ordinary list of identifier/value pairs. | Correct abstraction; no coordinate or side records in the public state. Issuance is load-bearing for anchor legality and the conditioned merge proof. |
| peritext-embed-rga | The payload-parametric EmbedRGA list instantiated with characters and mark boundaries. | Correct inherited editor-buffer abstraction. |
| sided-peritext-core | Ordinary sided text list plus mathematical deletion and mark sets. | Correct for the core query, which intentionally exposes the component stores. The text projection is abstracted from coordinate records. |
| sided-peritext-rich-core | The same editor transition state, observed only through rendered rich text. | Correct independent renderer boundary; implementation paths are absent from the sequential state. |
| tree-move | Ordinary parent tree; a move applies once and is rejected exactly when it would create a cycle. | Fixed: the former dead `Finset Event` field was a proof-only mirror and has been removed. `applicable` restricts the issuer API but is not needed by this totalized sequential-refinement proof. |
| aegis-sheet | Incremental causally aware spreadsheet state with observed-remove tokens and active write identities. | Intentionally history-aware, not an event-log mirror. `no_view_only_step` and its companion controls prove that the visible sheet alone cannot determine future behavior. Issuance is load-bearing for causal-origin legality. |
| or-set | Ordinary finite set; add inserts the named element and remove erases it, ignoring the observed-tag payload. | Fixed: the former tagged sequential replay clone was not the intended set ADT. `canIssue` is load-bearing for tagged-to-ordinary refinement. |

Two defects were therefore confirmed and repaired. OR-Set now proves
linearizability to an ordinary add-wins set. The negative control
`omitted_tag_breaks_ordinary_refinement` shows that deleting `canIssue` admits
an omitted-tag history on which the concrete and abstract results disagree.
TreeMove now relates its replicated event set directly to an ordinary tree;
the removed sequential event-set component affected neither transitions nor
queries. No other production entry retains a representation-only component
without either an abstract use or a checked necessity argument.

### OR-Set claim record

- **Claim:** every issuance-certified version is linearizable to the ordinary
  add-wins finite-set machine.
- **Status:** machine-checked.
- **Formal oracle:** `ORSet.verified`, `setSequentialCorrectness`, and
  `versionWellFormed_of_execution`.
- **Falsifier and negative control:** admit `removeConcurrent` after `addA`;
  `omitted_tag_breaks_ordinary_refinement` checks the resulting concrete and
  abstract disagreement.
- **Positive controls:** `observed_remove_ordinary_spec_absent` and
  `concurrent_remove_ordinary_spec_add_wins`.
- **Trusted definition:** `ORSet.spec` is the intended ordinary set ADT.
- **Residual:** correspondence between relational `canIssue` and a runtime
  command generator remains a validation obligation.

### TreeMove claim record

- **Claim:** the replicated event set refines a chronological sequential
  machine whose state is only the ordinary parent tree.
- **Status:** machine-checked.
- **Formal oracle:** `TreeMove.sequentialSound`, `stateRel`, and `verified`.
- **Falsifier:** a future abstract transition or query requires the removed
  event-set copy. The current machine and complete correctness proof do not.
- **Positive and negative controls:** ordinary moves use `doMove`; the checked
  `selfMove_rejected` control exercises cycle rejection.
- **Trusted definition:** `doMove` is the totalized sequential tree operation.
- **Residual:** `applicable` is an issuer-API restriction, not a load-bearing
  premise of the current sequential-refinement theorem.

## Evidence status

- **Machine-checked positive migrations:** total stores/counters, TreeMove,
  BoundedCounter, tombstone RGA, EmbedRGA, SidedEmbedRGA, Peritext, both Sided
  Peritext signatures, AegisSheet, the observed-remove set, and the grow-only
  canary. Every released entry is a typed `PackagedMRDT` in
  `Production.registry`.
- **Refuted:** origin issuance implies merged sequential legality; strict RGA
  issuance is a valid sequential legality predicate; current queue is FIFO;
  and the current MVR refines an ordinary single-value register after two
  concurrent writes.
- **AegisSheet control retained:** the exact whole-prefix issuer guard is not a
  legal predicate for a merge of concurrent histories. The checked negative
  remains as the reason for causal-origin legality, not as an open proof gap.
  A separate checked abstraction negative proves that the complete visible
  sheet is not a transition congruence.
- **Unvalidated:** the relational `Issuance` definitions still require
  differential validation against each executable operation generator.

Replay-only and refuted results are imported by `NegativeLedger`, not the
production registry. In particular, queue and MVR do not satisfy the public
sequential interface, and FugueMax's coordinate-level `FMSig` remains an
internal policy model. The released sided sequence is
`ProductionRGA.sided`.
