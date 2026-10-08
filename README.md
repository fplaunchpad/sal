# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual merge bases, and garbage collection.

On branch `paper1`, [`Sal/MRDTs/Paper1`](Sal/MRDTs/Paper1) mechanizes the
submission's prefix-closed history specifications and explicit per-query
RA-linearizability criterion. Implementation replay, merge VCs, and canonical
state reconstruction use concrete equality. Soundness retains issuance and
execution evidence, with local sequential simulations or suitable-history
proofs supplying the bridge to specification acceptance. The exact paper
OR-set retains every addition tag and has an ancestor-aware Join proof.

The [paper revision note](docs/paper1-formalism-reconciliation.md) identifies
changes against the current Overleaf manuscript, with numbered references to a
[self-contained formal reference PDF](docs/paper1-formal-reference/main.pdf).
The reference follows the paper’s Sections 3–6 and notation, with an explicit
manuscript-to-reference-to-Lean map. Its direct sequential lifting theorem
uses the same public-order witness as the paper, without extra replay-law
assumptions at that lifting step.

The [correctness audit](docs/paper1-correctness-audit.md) traces both obligations:
five-VC implementation correctness, then the independent sequential-specification
bridge. The ordinary OR-set has unrestricted payload correctness through the new
VC route; Embedded RGA uses that merge route with certified representation and
an exact selected-history bridge. A [reviewable manuscript patch](docs/paper1-manuscript-reconciliation.patch)
provides the corresponding revisions against Overleaf `0450d48`.

The [five-VC automation experiment](experiments/vc-automation/README.md) now
checks all five unchanged VCs for the ten production entries without
state-dependent issuance, the ordinary OR-set example, and the RGA family,
including current Queue (anchored enqueue) and FugueMax. The combined audit
covers 19 named instances including aliases. Finite equations close with Lean
automation; history expansion and evidence adapters were developed manually.
The audit excludes old datatype VC, Join and history-invariant proof reuse.
Production certificates remain unchanged. Fugue's merge VC proof does not
resolve its separate sequential-specification obstruction.

The corrected core uses event-guarded laws in
[`GuardedReplay.lean`](Sal/MRDTs/Paper1/GuardedReplay.lean), direct semantic replay
in `GuardedConvergence`, `GuardedOrder`, and `ConcreteReplay`, and the full-event
history bridge in `ConcreteHistoryBridge`. The typed
[`GuardedCoverage.lean`](Sal/MRDTs/Paper1/GuardedCoverage.lean) matches all 22
production packages: **14 have ordinary and virtual execution certificates,
all using concrete equality; eight have checked global-contract obstructions**.
The ordinary paper OR-set is an additional positive result outside that registry.
Every positive retains its original public datatype and issuance discipline,
with independent sequential histories and specification-conflict visibility.

LWW is positive under an empty operation policy: its max effectors commute,
and a chronological history explains the ordinary overwrite specification.
Only its earlier timestamp-order policy violates no-chain. Queue and MVR have
operation-policy obstructions even with distinct timestamps and replicas. The
six embedded RGA variants also refute the global laws, using inputs excluded
by their original issuers. These are limitations of the globally quantified
contract, not counterexamples to the original certified implementations.

The completed raw-order certified-scope campaign is tracked separately in
[`CertifiedCoverage.lean`](Sal/MRDTs/Paper1/CertifiedCoverage.lean): **14 retained
positive entries, three new scoped execution certificates (MVR, Core, RichCore),
four certified raw-order obstructions, and one certified Queue policy
obstruction**. All six embedded RGA signatures have checked scoped replay laws and five raw VCs, with stored
canonicality through ordinary and recursive virtual merges. MVR, Core, and
RichCore have independent full-event RA history witnesses. The restricted scoped
contract retains no-chain and tests concurrent commutation at represented ready
prefixes.

The four new RGA obstructions use actual original-issuer executions and the
unchanged independent languages. The global raw-state commutation test in
`paperOrder` requires an edge that rules out every explaining history. An
admitted history with the correct query exists when that edge is omitted.
Changing the scope of the algebraic laws alone does not change this witness
order. Fugue's separate three-update counterexample uses its original
preparation after deletion: the replacement refers to a deleted birth, while
the global raw-order edge prevents moving it before the deletion. All four
obstructions preserve the original implementations, queries, and issuers.

**Embedded RGA, Sided Embedded RGA, and native Peritext now have end-to-end
certificates under invariant-scoped commutation.** [`InvariantOrder.lean`](Sal/MRDTs/Paper1/InvariantOrder.lean)
uses concrete equality on a declared state domain in both order clauses.
[`CertifiedRGAInvariantCertificate.lean`](Sal/MRDTs/Paper1/CertifiedRGAInvariantCertificate.lean)
instantiates it with sorted lists whose records have certified insertion
provenance. Initialization, arbitrary eligible updates, ordinary merges, and
recursive virtual merge bases preserve this domain. One insertion-first history
respects the revised order and specification visibility, reconstructs the exact
state, and explains the original independent specification's query result.
The new VC-to-Join route supplies execution correctness; no legacy datatype
Join or final correctness theorem supplies it.

`CertifiedRGAInvariantControls` checks both verdicts on the same four-event
execution: the revised criterion admits the explaining history, while the
retained raw criterion rejects it. Birth/delete dependence remains. The Sided
and Peritext certificates likewise retain their original specifications and
ordinary/recursive-virtual execution semantics. `CertifiedCoverage` still records
the separate raw-order result.

FugueMax also has invariant closure, scoped replay laws, raw merge VCs, and
stored/virtual-base validity. Its original issuer and independent specification
nevertheless conflict under specification visibility: after inserting and deleting
a seed, the issuer can prepare an insertion naming that deleted seed. The list
specification requires a live anchor. `CertifiedFugueInvariantObstruction` proves
that the actual certified trace has no explaining history for **any invariant or
policy**, using specification visibility alone. The relevant effectors now
commute on valid implementation states, so this is a distinct obstruction.

Across the retained and new certificate routes, **20 of 22 production packages
have positive certificates**; ordinary paper OR-set is additional. The remaining
cases are Fugue's specification-visibility obstruction and Queue's policy
obstruction. This count does not reclassify the retained raw-order registry.

`CertifiedQueueMVRQueue` shows that Queue's payload-only/no-chain obstruction
persists in a legal fork/apply/apply execution at a represented empty root.
Replay readiness retains already minted operations; it does not re-run their
issuers on reordered states. `CertifiedMVRControls` checks this distinction.

A **separate anchored-enqueue Queue** now has ordinary and recursive-virtual
certificates in
[`AnchoredQueueCertificate.lean`](Sal/MRDTs/Paper1/AnchoredQueueCertificate.lean).
Original issuance records the observed tail for enqueue and head for dequeue.
The compact implementation stores live records and immutable coordinates,
without a separate birth or tombstone set. Its independent FIFO specification
appends fresh tagged values, ignores enqueue anchors, and allows repeated
removal of already-removed identities while rejecting live non-head removal.
A constructed history reconstructs the exact tagged list and explains the
public tagged-head query, respecting both invariant-scoped implementation
order and specification visibility. Representation uses the new merge VCs and
concrete equality. PASS+FAIL controls include actual public certified execution
and the requested concurrency cases. This additional variant does not change
the original Queue or the 20-of-22 production count; it has no JavaScript port.

The implementation metatheory is concrete throughout.
[`ConcreteFormalism.lean`](Sal/MRDTs/Paper1/ConcreteFormalism.lean) defines
history-indexed representation and exact canonical replay.
[`ConcreteMetadata.lean`](Sal/MRDTs/Paper1/ConcreteMetadata.lean) records causal
metadata dependencies, which may include commuting predecessors needed to
reconstruct identifiers or anchors.
[`ConcreteJoin.lean`](Sal/MRDTs/Paper1/ConcreteJoin.lean) derives representation
Join by strict event-set induction from five concrete merge equations,
representation uniqueness, finite replay supply, and a represented peel witness.
Semantic and metadata maximality are separate obligations. The proof does not
replace concrete equality with equality of query answers.

[`ConcreteVCExecution.lean`](Sal/MRDTs/Paper1/ConcreteVCExecution.lean) packages
these VC obligations with stored-version representation evidence. Join is
derived rather than supplied as a field. `ConcreteCommutingVCReplay` adapts
commuting datatype equations to this induction; `SimpleConcretePorts`,
`IssuedConcretePorts`, and `RGAConcretePort` preserve the existing production
issuers and independent history languages. Ordinary and efficient OR-set
representation, replay construction, metadata, and algebra are developed in
`ConcreteORSetRepresentation`, `ConcreteORSetSorting`, `ConcreteORSetMetadata`,
and `ConcreteORSetAlgebra`.

[`ConcreteHistoryBridge.lean`](Sal/MRDTs/Paper1/ConcreteHistoryBridge.lean)
connects exact stored canonicality to an independent sequential specification.
Its total route requires merge-free fold soundness and commutation
compatibility; its scoped route chooses one admitted history preserving both
implementation order and specification visibility, then transports its answer
by concrete replay uniqueness. `CertifiedHistoryBridge` instead transports an
admitted represented replay by exact representation uniqueness in certified
contexts. `ExecutionTrace` supplies the model-free finite-trace induction.
Independent sequential simulations and specification abstraction functions
remain proof tools relating the implementation to a separate specification;
they do not redefine implementation equality or merge commutation.

`GuardedReplay`, `GuardedConvergence`, and `GuardedOrder` establish direct
semantic-order convergence and finite enumeration. The event guards retain
distinct timestamps and, for noncommutation exactness, distinct replicas.
The conditional law uses actual noncommutation; Neem's guarded F* obligations
alone do not supply it. `GuardedPolicyControls` checks this boundary and the
failure of the earlier uniform-policy order transport.

Both OR-sets have five-VC-derived ordinary and recursive-virtual execution
certificates in `ORSet.RawExecution` and `EfficientORSet.RawCertificate`.
Their independent ordinary-set specifications retain full event inputs and
specification visibility. `storedCanonical` gives exact replay equality and
`convergence` gives equality of concrete stored states. The certificates derive
Join and stored canonicality. Ledger dependency checks require the concrete
Join induction and datatype VC obligations, and reject the earlier direct
Join and history-merge shortcuts.

`GuardedQueueMVR` and `GuardedRGAObstructions` state the eight global-contract
obstructions using concrete equality. Their raw inputs need not be issuable;
these results refute globally quantified laws and do not assert failure of
certified executions. The certified and invariant-scoped results described
above retain their own execution domains and witness orders.

The agreed sequential update interface retains the full
`(timestamp, replica, application operation)` input supplied to MRDT updates.
`Paper1.RGAEventSpec` implements it with an independent ordinary list and
allocation registry: insertion uses its supplied timestamp as the element ID,
and replica metadata has no effect on this datatype's list semantics. It proves
the literal and stronger specification-visible criteria for ordinary and
virtual certified RGA executions, including all stored versions. Sequential
witnesses preserve event inputs while permitting timestamp order to change.

The active manuscript criterion and the separate specification-visibility
criterion are separate definitions. The active criterion admits the no-op
removal mutation: every raw execution has a removals-first explanation, despite
the incorrect sequential behavior. The stronger candidate rejects the checked
reachable mutation. The earlier operation-only RGA investigation is retained
as a counterfactual to the agreed full-input interface. Its language uses independent,
globally fresh nondeterministic allocation because its update label omits the
inserted identifier. Certified RGA executions satisfy the literal criterion.
Both operation-only languages—globally fresh allocation with missing-anchor
no-ops, and strict live-anchor insertion—fail the stronger criterion on a
checked honestly certified eight-event execution from the empty initial
configuration. The proofs exclude every witness order and allocation choice,
including unbounded natural-number allocations. With explicit insertion identifiers in application
labels, independent strict and missing-anchor list languages satisfy the
stronger projected criterion on all ordinary and virtual certified executions.
The projection is explicit and genuinely changes the application alphabet; the
concrete datatype and issuer are unchanged. `Paper1.RGAComparison` checks both
negative and positive criteria on the same reachable read `[5,4,8,7]`.
These paper-facing results do not assert a migration of every
production package to the restricted policy.

`Paper1.EventBridge` exposes full-input simulations, independent fold-history
acceptance, mint-sensitive and execution-sensitive chosen-history premises,
Join/five-VC soundness, and finite-trace guarantees. TreeMove and AegisSheet use
`GuardedHistory` to retain their independent in-place machines and causal-origin
legality. BoundedCounter retains nonnegative account guards; its global
commutation-compatibility VC fails, while its honest causal witnesses prove
specification-visible correctness.

The local Neem F★ interface requires distinct timestamps and different replica
IDs in `rc_non_comm` (`_references/neem_fstar_repo/code/interface/App_mrdt.fsti:64`).
Its efficient OR-set uses concrete equality. `Paper1.NeemScope` proves the
different-replica restricted condition and refutes the unqualified concrete
condition. Neem's displayed paper condition has no such replica guard;
the code and prose therefore have different scopes. This audit does not claim
to establish the source's complete bottom-up soundness theorem.

`Paper1.CommutationBridge` exposes a separate specification-compatibility VC:
concrete commutation must imply observable contextual commutation in the
independent history language. This is the contrapositive of the existing
specification-conflict coverage premise. It makes specification-conflict
visibility follow from the replay order, supports full event inputs, and
combines with the five merge VCs and history acceptance to prove the stronger
criterion. The ordinary OR-set satisfies it; the no-op-removal mutant fails it.
This is a sufficient route, not a requirement on every datatype: certified RGA
continues to use its issuance-based chosen-history proof. The VC does not
silently change the literal RA definition. `appendix_soundness.tex` is excluded
from the manuscript build and is not an included paper appendix.

The current framework is under [`Sal/MRDTs`](Sal/MRDTs). Its raw `MRDTSig`
contains only datatype operations. Client minting discipline is supplied by a
single `Issuance.CanIssue` relation. An independent `SequentialSpec` supplies
the abstract state, legal histories, and queries. A single `ReplayPolicy`,
stored as `VerifiedMRDT.rc`, supplies any design-specific direction between
concurrent events. The sole linearization order `loOn` is derived from that policy and
visibility: visibility is retained exactly for conflicting pairs, while
`Either` contributes no edge. `VerifiedMRDT` combines these with widened convergence, a representation relation, and a
`SequentialCorrectnessCertificate`. Ordinary
convergence is derived by embedding the ordinary trace in the widened
semantics. Safety and datatype-state GC are separate optional certificates.
Proof-local invariants and applicability predicates are not part of the public
API.

The framework supplies:

- ordinary and canonical virtual-merge-base operational semantics;
- the convergence metatheory;
- distributed commit-history GC and its refinement theorem.

`UpdateSig` is a merge-free proof-level algebra projected from `MRDTSig`, not
a second datatype interface. Historical binary proofs request their merge
operation separately through `HistoricalBinaryMerge`.

The verified LWW register shows why `rc` may be nontrivial even when updates
commute. Its timestamped state uses `max` for update and merge, while its sole
`rc` policy orders writes by timestamp. A sorted overwrite history supplies
the ordinary sequential-register explanation.

The verified multi-value register stores only live tagged values. A local
write replaces what it observed; ancestor-relative merge preserves concurrent
writes. `MVRLive.verified` proves the public contract for ordinary and virtual
executions, including causal maximality and ordinary sequential behavior.

`FugueMax.verified` certifies the exact FugueMax issuer and enriched state
against a plain-list specification. One witness establishes list correctness
and maximal non-interleaving for ordinary and virtual executions. Birth/origin
metadata is implementation-side; datatype-state collection remains staged.

A datatype may separately supply state-GC representation and protocol
certificates. RGA has a checked `(id,parent)`/live-set packing
certificate. It retains deleted identifiers internally to integrate operations
minted concurrently with deletion, while issuance permits a new insertion only
at a root or live anchor. Rich SidedPeritext, TreeMove, and
AegisSheet supply the other representation-changing collectors or protocols.
The runtime implementation lives in [`runtime`](runtime).

## Verification

The paper branch has an additional theorem and axiom gate:

```sh
./scripts/check-paper1.sh
```

```sh
./scripts/check-mrdt-refactor.sh
```

This CI gate checks every production package against the explicit selections in
[`public-contracts.json`](public-contracts.json): implementation, issuance,
`rc`, sequential specification (including legality and queries), and state
relation. Lean must connect them through the public certificate for ordinary
and virtual executions. Replay-only packages cannot pass. Registry coverage,
certificate axioms, runtime mappings, and negative controls are also checked.
See [the gate and its review boundary](docs/production-packaging.md).
Passing this gate is not human approval of a specification; the cross-datatype
semantic audit remains open.

The historical conditioned framework and refuted MRDT experiments are retained
on the archive branch `archive/conditioned-mrdts-2026-08-21`, not on `main`.
