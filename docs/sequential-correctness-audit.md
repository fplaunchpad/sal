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
- **Reality oracle:** the editor protocol does not mint an insertion after an
  anchor whose deletion it has observed. Retained tombstones serve only to
  integrate insertions minted concurrently with deletion.

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

`VerifiedMRDT` supplies issuance, one public `rc : ReplayPolicy`, widened
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

RGA's public sequential state is the ordinary visible `List Nat`.
`listSpec.Legal` uses `listLegal`, which states only facts about the abstract
event list:

- event timestamps are unique;
- each inserted identifier equals its timestamp;
- every non-root anchor was inserted earlier; and
- every deletion target was inserted earlier.

Deletion does not remove an identifier from the legality predicate's
allocation history. Therefore concurrent duplicate deletes remain legal and
idempotent.

`rga_spec_linearizable` and `rga_spec_linearizableV` are machine-checked.
They select the exact version event set, respect `loOn`, satisfy
`listSpec.Legal`, refine the ordinary list, and agree on its query. The
implementation's birth/grave state is an internal representation only.

The issuer guard now requires every non-root anchor to be both allocated and
live. The RGA `rc` orders sibling and direct parent/child insertion conflicts
by timestamp. It orders an insertion before a conflicting deletion of its new
identifier or non-root anchor; all other pairs receive `Either`.

## Checked controls

The gate SPOT shows that two operations can each be issuable at independent
origins while no merged serialization satisfies a resource-consuming
sequential specification. Origin issuance alone therefore cannot establish
sequential legality.

The RGA SPOT shows that reusing the strict origin predicate as sequential
legality rejects two concurrent deletes of the same live identifier. The
public RGA specification accepts the idempotent merged history instead.

The historical queue SPOT compares particular folds: two replicas dequeue
the same observed head, retaining the second element, whereas two unconditional
pops remove both. It does not refute every permitted linearization. The public
`Queue.clientSpec` now permits repeated removal of an already absent target
but rejects live non-head and never-enqueued targets. `Queue.verified` proves
legalization for every certified execution; `queue_correct` connects this to
timestamp-ordered surviving contents and proves repeated targets are concurrent.
`client_linear_fifo` gives ordinary FIFO on linear histories. The regression
harness tests the proved witness against actual fork/merge behavior and detects
an extra-pop mutation. No exactly-once suppression protocol is introduced.

The deleted-anchor SPOT has a positive and negative control: insertion is
issuable while the anchor is live and rejected after the issuer observes its
deletion. The tombstone remains in the implementation so that an independently
minted concurrent insertion can still be integrated.

The final single-order design derives conflict from `rc`. `loOn` retains a
visibility edge only for a conflicting pair and uses the same policy for
concurrent direction. EmbedRGA and SidedEmbedRGA carry immutable coordinates,
so their replayed insertions do not need anchor state and commute with deletion
of the anchor. Their public states remain ordinary lists.

`RcSPOT.LWW.old_no_chain_refuted` checks that a valid LWW timestamp order
contains a length-two edge chain, so the historical `no_rc_chain` condition
cannot be a framework requirement. `ReplayLaws` instead asks for acyclicity of
the transitive closure of active `rc` edges.

The production LWW package closes the corresponding end-to-end case. Its raw
timestamped `max` updates commute, while its sole `rc` policy orders writes by
their timestamped keys. `canonical_respects` constructs a sorted witness that
refines the stored maximum to the total overwrite-register specification.

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
| lww-register | Optional value; every sequential write overwrites the register. | Correct total register abstraction. The representation retains the winning timestamped tuple; `stateRel` projects only its value, and the public witness sorts by the timestamped key. |
| rga | Ordinary list of stable identifiers; insert splices after an anchor and delete physically filters an identifier. | Correct abstraction; no tombstones or insertion-edge store. Issuance is load-bearing for list legality and rejects insertion after an observed anchor deletion. |
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

### Tagged OR-set claim record (retired regression fixture)

This is historical audit evidence, not a current production datatype.
The released set is the efficient OR-set; the tagged model lives in
`Metatheory/Countermodels/TaggedORSet.lean` solely for regression controls.

- **Claim:** every issuance-certified version is linearizable to the ordinary
  add-wins finite-set machine.
- **Status:** machine-checked.
- **Formal oracle:** `ORSet.verified`, `sequentialCorrectness`, and
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
- **Public legality:** `ClientLegal` strengthens chronological sorting with
  an issuable origin contained in each event's replay prefix.
  `clientLegal_origin` is a required public-gate obligation; the correctness
  proof obtains these origins from certified mint honesty. The older
  algebraic `sequentialSound` theorem still needs only sorted replay.
- **Contract controls:** `clientLegal_firstMove` accepts an ordinary move;
  `sorting_accepts_reserved` and `clientLegal_rejects_reserved` distinguish
  sorting alone from the strengthened contract on a reserved-node move.

## Evidence status

- **Machine-checked positive migrations:** total stores/counters, TreeMove,
  BoundedCounter, LWW register, tombstone RGA, EmbedRGA, SidedEmbedRGA, Peritext, both Sided
  Peritext signatures, AegisSheet, the observed-remove set, and the grow-only
  canary, Queue, and MVR. Every released entry is a typed `PackagedMRDT` in
  `Production.registry`.
- **Refuted:** origin issuance implies merged sequential legality; strict RGA
  issuance is a valid sequential legality predicate;
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
production registry. Queue's completed public package is now registered;
its older replay-only companion and selected-fold negative remain checked.
MVR's public finite-live-set contract is now certified: the actual query exposes
values, `mvr_correct` proves causal-maximality in the same execution as public
linearizability, and `linear_register` recovers ordinary register behavior.
Its old single-value counterexample remains a rejection of that target.
The registered `MVRLive.verified` now uses a concrete finite live set too;
ordinary and recursively constructed virtual states have a checked
surviving-write invariant. The production gate rejects substituting the old
grow-only certificate for this compact implementation.
FugueMax's coordinate-level `FMSig` remains an internal policy model.
The enriched `FugueMax.datatype` has its own public plain-list certificate,
distinct from `ProductionRGA.sided`. `FugueMax.correct` combines legality,
list refinement, observations, and maximal non-interleaving for one witness
of the same certified execution. Its state collection remains staged; no
independent FugueMax runtime is claimed.
