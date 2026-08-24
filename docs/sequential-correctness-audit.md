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
- **Formal oracle:** `IsSpecRALinearizable`, both RGA capstones, the total
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

`VerifiedMRDT` supplies issuance, a public `ArbitrationSpec`, widened
convergence, the sequential specification, a representation relation, and one
legalization proof. Ordinary
certified execution embeds in widened execution, so the package stores no
duplicate ordinary convergence theorem. `VerifiedMRDT.converges` and
`convergesV` both produce
`IsSpecRALinearizable`.

`SafetyCertificate` and `StateGCCertificate` are orthogonal optional packages.
Safety likewise stores only widened preservation and derives ordinary
preservation through the execution embedding.

`ReplayVerifiedMRDT` retains the older raw-fold theorem under an explicitly
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
unrelated identifier that fail universal `CRDTSig.commutes` only on an
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
an explicit `ArbitrationSpec`. EmbedRGA and SidedEmbedRGA now prove that their
canonical legal witnesses respect those semantic dependence policies without
putting implementation state inside `SequentialSpec.Legal`.

The same legalization composes through Sided Peritext. Both its internal
three-component core and its production `RichCore` query signature now have
full `VerifiedMRDT` packages. The latter theorem covers the actual
document-order rich-text render, not only raw component stores.

AegisSheet exposes a different issue. Its old `GuardedChronological` predicate
rechecks an event against the entire serialization prefix. The checked
`concurrent_origins_not_guarded_chronological` example contains two operations
that are each applicable at an empty origin; any serialization makes one
follow an operation it did not observe. The next specification must validate
each event against its encoded causal origin view and prove the incremental
observer correct for those merged histories.

## Evidence status

- **Machine-checked positive migrations:** total stores/counters, TreeMove,
  BoundedCounter, tombstone RGA, EmbedRGA, SidedEmbedRGA, Peritext, both Sided
  Peritext signatures, and the grow-only canary.
- **Refuted:** origin issuance implies merged sequential legality; strict RGA
  issuance is a valid sequential legality predicate; current queue is FIFO;
  and the current MVR refines an ordinary single-value register after two
  concurrent writes.
- **Staged on merged-history legality:** AegisSheet. Its incremental machine
  and guarded linear-history theorem remain checked, but the exact issuer
  guard is not a legal predicate for a merge of concurrent histories; this is
  now a checked negative rather than an inferred gap.
- **Unvalidated:** the relational `Issuance` definitions still require
  differential validation against each executable operation generator.
