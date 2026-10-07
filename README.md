# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual merge bases, and garbage collection.

On branch `paper1`, [`Sal/MRDTs/Paper1`](Sal/MRDTs/Paper1) mechanizes the
submission's prefix-closed history specifications and explicit per-query
RA-linearizability criterion. The original state-equality replay route requires
exact concrete noncommutation and no length-two conflict chain. Soundness retains issuance and
execution evidence, with local sequential simulations or suitable-history
proofs supplying the bridge to specification acceptance. The exact paper
OR-set retains every addition tag and has an ancestor-aware Join proof.

The corrected core uses event-guarded laws in
[`GuardedReplay.lean`](Sal/MRDTs/Paper1/GuardedReplay.lean), direct semantic replay
in `GuardedConvergence` and `GuardedOrder`, and the full-event criterion in
`GuardedHistoryBridge`. The typed
[`GuardedCoverage.lean`](Sal/MRDTs/Paper1/GuardedCoverage.lean) matches all 22
production packages: **14 have ordinary and virtual execution certificates,
all using concrete equality; eight have checked global-contract obstructions**.
The exact paper OR-set is an additional positive result outside that registry.
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
have positive certificates**; exact paper OR-set is additional. The remaining
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

The abstraction development below remains useful proof infrastructure and an
optional generalization. `AbstractFormalism` retains the earlier uniform-law
adapter. Its nontrivial observational models are no longer required by any
positive entry in the corrected registry. The final certificates use identity
models and do not require query completeness; specification refinement remains
separate from implementation-state equality.

[`AbstractMerge.lean`](Sal/MRDTs/Paper1/AbstractMerge.lean) states the five
merge VCs with observational conclusions and explicit history-indexed metadata
representation premises. Representation-preserving Join proves merged
canonicality and equivalence of merge results for represented inputs from the
same histories. [`AbstractSoundness.lean`](Sal/MRDTs/Paper1/AbstractSoundness.lean)
packages the assumptions and proves ordinary/virtual finite-execution
correctness and observable convergence. Both OR-sets have checked
`AbstractSpec.certificate` inhabitants and representation Join proofs.
The five-VC-to-Join derivation includes explicit representation-preserving
substitutions and decompositions. Replacing equalities with equivalence alone
does not suffice.
`MetadataSubstitution` proves the guarded substitution obligation for both
sets independently of Join, and `MetadataInduction` closes the empty-side
case. The nonempty case must distinguish observable conflicts from metadata
dependencies: two same-replica adds commute observationally, but the newer
add's reconstruction needs the older tag in its causal base.
`MetadataPeelControl` checks that omitting it gives the correct membership
while leaving an obsolete tag. `MetadataMaximal` supplies a common semantic
and metadata maximum for both OR-sets. `MetadataReconstruction` proves closure
of metadata pasts and a represented reconstruction choice for the exact set,
without Join. `MetadataRewrite` closes the generic causal reconstruction case
from the observational VC and a directed metadata-preservation obligation.
`EfficientMetadataReconstruction` provides the efficient set's represented
peel choice using both maxima. `EfficientMetadataCausal` discharges its causal
metadata companion by concrete set algebra: every live record killed by the
step is present in the metadata past. Neither proof invokes Join.
`MetadataCausalFrame` checks substitution of a represented smaller-history
result into causal reconstruction. `MetadataRedistribution` proves the generic
local/shared steps from their recursive premises and directed metadata
companions. `MetadataDecomposition` supplies side reconstruction from strictly
smaller Join instances, treating a side equal to the whole union by causal
framing. Both sets discharge the metadata companion for branch symmetry.
`MetadataJoin.representationJoin_of_vcs` now derives representation Join by
strong induction from the observational VCs, directed metadata companions,
and explicit replay supplies. `MetadataSupply` constructs those replay
supplies for both sets without Join. `ORSetRedistribution` discharges both
shared metadata companions by the same unconditional finite-set identity.
`ORSetLocalMetadata` discharges both local metadata companions from tag/history
invariants. `ORSetVCJoin` now supplies the exact set's complete observational
VC package, derived Join, and ordinary/virtual issuance-certified execution
correctness through `vcCertificate`. Its stored-version invariant uses the
VC-derived Join rather than the existing direct proof.
`EfficientORSetVCJoin` now discharges the efficient set's complete observational
VC package and derives its representation Join by the same induction. Add VCs
use observational equality; remove VCs admit concrete equality.
`EfficientVCHistoryMerge`, `EfficientVCVirtual`, and `EfficientVCExecution`
carry this derived Join through stored-version updates and every recursive
virtual-base merge. Both sets' `vcCertificate` inhabitants prove ordinary and
virtual issuance-certified execution correctness through the new route.
`VCExecutionContract.VCConditions` states the complete sufficient conditions
with no assumed Join field; its generic ordinary/virtual execution theorems
apply to both checked `vcConditions` instances. Stored-version evidence and
sequential-history adequacy remain separate, explicit obligations.
`VCReplayConditions` separates those replay and metadata obligations from the
choice of sequential-history bridge. `ScopedHistoryBridge` supplies an
execution-scoped alternative for guarded specifications: an independently
accepted merge-free history explains a stored state using observable
canonical uniqueness. `FutureModel` supplies a general future-query quotient,
and `CommutingVCReplay` adapts existing concrete VC equations to the new
observational induction without assuming the old datatype Join theorem.
The earlier uniform-law production ports and observational reassessment are
implemented in `SimpleAbstractPorts`, `GuardedAbstractPorts`, `RGAAbstractPort`,
and `ObservationalObstructions{,RGA}`. The historical uniform inventory `AbstractCoverage`
records 13 proved production entries, eight global-law obstructions, and the
then-excluded LWW register. `GuardedCoverage` supersedes that classification.
The exact paper OR-set is an additional
proved datatype outside that registry. Each positive entry carries a total or
execution-scoped VC sufficient-condition instance with the original issuer.

Plain RGA retains the independent strict list/registry specification and exact
timestamp/replica inputs. Its global implementation/specification commutation
compatibility is proved impossible; the execution-scoped bridge uses unique
births, causal support, and live-anchor issuance facts to select an accepted
history. The guarded counter, TreeMove, and AegisSheet likewise preserve their
independent guarded languages. Their merge proofs and stored-version invariants
derive from the new VC induction.

These eight obstructions concern the earlier **unguarded, uniform** laws.
They do not establish incompatibility with the intended Neem-style contract:
the user supplies payload-only `rc`, while event exactness is required only
for distinct timestamps and different replicas. The corrected contract now has its own metatheory and coverage; the old
transport to policy-based `loOn` cannot justify the guarded case.

`GuardedReplay`, `GuardedConvergence`, and `GuardedOrder` now establish direct
semantic-order convergence and finite enumeration. `GuardedAbstraction` carries
these results to observational equality and proves canonical existence and
uniqueness. The conditional law explicitly uses the manuscript's actual
noncommutation premise; Neem's guarded F* obligations alone do not supply it.
`GuardedPolicyControls` checks the guard boundary and the failure of the old
order transport.

`GuardedRawJoin` now derives Join from five guarded concrete-equality equations
and finite replay reconstruction. Both OR-sets instantiate this route:
`ORSet.RawExecution` and `EfficientORSet.RawCertificate` prove ordinary and
recursive virtual execution correctness against the independent ordinary-set
specification, including specification visibility and full event inputs.
Their `storedCanonical` theorems give raw replay equality, and `convergence`
gives equality of concrete stored states. Neither certificate assumes Join or
stored canonicality. Recursive ledger checks reject the previous direct and
observational Join routes in these conclusions. Some replay construction still
reuses proved observational helpers; the core interface uses identity abstraction.
See [the manuscript reconciliation note](docs/paper1-formalism-reconciliation.md)
for the equality decision and required paper changes. The complete guarded registry classification is recorded above.

The eight earlier uniform obstructions have now been re-proved with the
corrected event guards in `GuardedQueueMVR` and `GuardedRGAObstructions`.
Observational equality cannot remove these global-contract obstructions.
Queue, compact MVR, and registered FugueMax expose operation-label exactness
failures in their queries. Embedded RGA, sided embedded RGA, Peritext embedded
RGA, and the two sided Peritext cores expose an observable three-operation
conflict triangle incompatible with no-chain. The impossibility proofs cover
every sound abstraction of the unchanged signatures. Their raw tied-coordinate
inputs need not be issuable: these results refute globally quantified laws,
and do not assert failure of certified executions. All datatype verdicts and
the evidence needed for their history bridges are recorded in the canonical
task list.
The joint paper1 gate passes (3,477 build jobs), including guarded-core and raw-VC
dependency checks, standard-axiom,
registry-coverage, and proof-route dependency checks for the completed ports.
The ledger audits the proof dependency graph: these results must use the new
Join induction and datatype VC/metadata obligations, and may not use the
earlier direct Join or direct history merge proofs.
`MetadataDependencies` makes that distinction explicit: metadata edges are
causal and cover observable conflicts; their reconstruction past can retain
additional commuting predecessors. The merge VCs now parameterize this past.

The checked `EfficientORSet.AbstractControls.canonical_only_join_fails`
explains why the metadata premise matters: a fresh-tag state is abstract
canonical for a history containing only an older add, but using that fresh tag
as a merge input can incorrectly survive a causally observed removal.
Abstract canonicality alone therefore cannot serve as representation evidence.

The earlier implementation replay adapter is query-relative throughout:
[`QueryReplay.lean`](Sal/MRDTs/Paper1/QueryReplay.lean) identifies states when
every future update sequence and query gives the same result. Its quotient
algebra uses observational equality for commutation, conditional absorption,
canonical replay, and replay uniqueness. An explicit `Abstraction` interface
can present this equality as `abs s = abs t`. Both the exact and efficient
OR-sets use element membership as their abstraction and the same generic
canonical-history bridge to prove ordinary/virtual certified correctness for
every stored version (`ORSet.QuerySpec`, `EfficientORSet.QuerySpec`).
Efficient OR-set now satisfies operation-level exactness and no-chain for this
observable algebra; same-element adds commute despite different tags.
`QueryReplay.order` uses observable noncommutation in both visibility and
absorber clauses. These results use the specification-visible criterion and
retain full event inputs and independent ordinary-set histories.

Merge still operates on concrete tags. The checked
`EfficientORSet.QuerySpec.merge_congruence_fails` shows that identical element
sets can behave differently when merged against an ancestor and a removal.
Consequently, concrete execution/representation invariants establish
observable canonicality after merge; no tag-erasing merge operation is assumed.
The older state-equality results below remain available as stronger proof
tools. The other production instances have not yet been reclassified under
the new observable algebra.

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

The earlier state-equality full-input migration is checked against the complete 22-entry production
registry in `Paper1.MigrationCoverage`: twelve entries have independent
history-language specifications and ordinary/virtual certified guarantees for
every allocated version, nine have proofs that the paper's operation-only
exact/noncommutation plus no-chain assumptions cannot hold on their unchanged
carriers, and LWW is explicitly excluded. The compatible entries are the three
add/set stores, three flat counters, two flat grow-only stores, bounded counter,
plain RGA, TreeMove, and AegisSheet. Coverage retains each original signature
and issuer and proves equality with the original registry, not just its names.
The exact paper OR-set is an additional checked instance outside that registry.
Including efficient OR-set's direct proof, thirteen of the original twenty-two
entries have the earlier specification-visible history witness clauses proved. Eight
retain their original production verification without that new proof; LWW
remains excluded from this migration.
Those earlier witness predicates did not bundle the manuscript definition's
datatype-side prerequisites. In particular, efficient OR-set's direct concrete
proof does not establish the full original definition: concrete rc-non-comm
fails. Its new abstraction-first certificate proves the full revised criterion.

`Paper1.EventBridge` exposes full-input simulations, independent fold-history
acceptance, mint-sensitive and execution-sensitive chosen-history premises,
Join/five-VC soundness, and finite-trace guarantees. TreeMove and AegisSheet use
`GuardedHistory` to retain their independent in-place machines and causal-origin
legality. BoundedCounter retains nonnegative account guards; its global
commutation-compatibility VC fails, while its honest causal witnesses prove
specification-visible correctness.

The nine exceptions to that state-equality route are efficient OR-set, queue, compact MVR, and six embedded
RGA/editor registry entries. These are obstructions to all-state concrete replay
assumptions, not failures of the sequential specifications or the existing
production certificates. Efficient OR-set additionally has a direct full-input
ordinary-set history proof under its retained policy. `main` already proves
that its all-state replay laws are unavailable; `paper1` strengthens that result
to impossibility for any operation-only exact policy under concrete equality.
That obstruction does not apply to the new observable replay laws. The embedded RGA
obstructions use raw event pairs that need not satisfy honest issuance.

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
criterion. The exact OR-set satisfies it; the no-op-removal mutant fails it.
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
