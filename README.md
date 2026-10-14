# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual merge bases, and garbage collection.

On branch `paper1`, [`Sal/MRDTs/Paper1`](Sal/MRDTs/Paper1) mechanizes the
submission's prefix-closed history specifications and explicit per-query
RA-linearizability criterion. Implementation replay, merge VCs, and canonical
state reconstruction use concrete equality. Soundness retains issuance and
execution evidence, with local sequential simulations or suitable-history
proofs supplying the bridge to specification acceptance. The paper
OR-set retains every addition tag and has an ancestor-aware Join proof.

The [paper revision note](docs/paper1-formalism-reconciliation.md) identifies
changes against the current Overleaf manuscript, with numbered references to a
[self-contained formal reference PDF](docs/paper1-formal-reference/main.pdf).
The reference follows the paper’s Sections 3–6 and notation, with an explicit
manuscript-to-reference-to-Lean map. The [public datatype reference](https://sal-datatype-reference.fizzyearth10.chatgpt.site/)
pairs implementation and sequential definitions with explicit issuance guards.
Its direct sequential lifting theorem
uses the same public-order witness as the paper, without extra replay-law
assumptions at that lifting step.

### Notion core — structured implementation and executable refinement

The integrated `paper1` implementation maintains immutable origin, deletion,
creation-link and cut-owner facts for the typed Notion core.
[`NotionCoreStructuralMRDT`](Sal/MRDTs/Instances/NotionCoreStructuralMRDT.lean)
checks full query correspondence, the five VCs, actual execution transport and
the independent RA specification under the original honest protocol. Queries
traverse structural rows and cuts and fold creation links; they do not replay
transactions. The transaction-set reference supplies the preserved client
protocol and independent specification; the new implementation inherits its
history witness through proved query correspondence. Its structural and native
refinement proofs are additional datatype-specific support, included in the
[paper measurement](experiments/paper-implementation/README.md).

The [research record](docs/notion-incremental-research.md) explains the candidate
and preserved frozen-endpoint counterexample. The [reproducible experiment](experiments/notion-incremental/README.md)
records bounded oracle comparisons and update/query/merge timings, with
memory proxies and validation-overhead limitations. The earlier handwritten JavaScript adapter remains a separate comparison;
the checked indexed core is compiled directly from Lean.

The [executable refinement record](docs/notion-executable-refinement.md) connects
a compiled Lean core to its concrete hash indexes and allocator sidecar.
Receipt/merge representation preservation, honest-domain acceptance and the
native query theorem check. A constructive endpoint receives any ordering of
an honest closed version into the empty engine and returns the reference answer. The pinned native
oracle run passed 10,008 query comparisons. Native query is slower on the
measured mixed workload, so the earlier JavaScript speedups must not be
attributed to this executable. The compiler and tested JSON codec remain
explicit trusted boundaries.

### Notion core — checked protocol entry

The [Notion core catalogue entry](docs/notion-catalogue.md) covers a typed
adaptation of the published demo's create/insert/delete/split fragment.
The source protocol and structural/native refinement ledgers register the
checked theorem chain in the build, separately from the 18 uniform
`PackagedMRDT` entries. Its explicit factory initialization, injective session
assignment, and locally guarded issuance remain part of the theorem's scope.

`NotionCoreProtocol.specification_ra` proves the selected RA criterion for
ordinary and canonical recursive merge bases. One witness supplies event
coverage, required order, specification visibility and query admission to an
independent retained-slot document specification. The specification contains
no transaction log, replay sorting, search labels or physical slice tree.
Local insert/split/delete theorems establish the requested immediate effect
through the actual typed MRDT update and query.

The five VCs reuse the automated finite-store proof machinery. Document
refinement, issuance invariants and the sequential-history bridge use explicit
Lean proofs with routine tactic automation. This result is not included in the
19-case `mrdt_verify` automation measurements below.

The [three recorded demo bugs](docs/notion-bugs.md) obstruct the broader
merge-block/formatting contract; Sal version merges are distinct from the
editor's merge-block request. Pinned executable traces support the source
comparison. JavaScript number/string/JSON extraction and production Notion
correspondence are not proved. See the [research conclusion](docs/notion-research.md)
and [paper-writing handoff](docs/notion-integration.md).

The [natural-specification audit](docs/natural-sequential-specifications.md)
separates client requests from generated replication messages. Simple sets and
counters use set/integer abstract states with exact history-language preservation;
both OR-set implementations share an ordinary-set specification. Queue has a
checked value-only request adapter alongside its concurrent named-head language.
FugueMax now has a checked physical positional refinement and a natural
origin-list RA bridge through the five VCs, including recursive executions and
the same-witness noninterleaving guarantee. RGA reserves ID zero for its root
in both issuance and sequential specifications. Native, Embedded and Sided RGA
also have checked local theorems equating the actual implementation update
with the prepared positional client edit, deriving their invariants from execution.

The [correctness audit](docs/paper1-correctness-audit.md) traces both obligations:
five-VC implementation correctness, then the independent sequential-specification
bridge. The ordinary OR-set has unrestricted payload correctness through the new
VC route; Embedded RGA uses that merge route with certified representation and
an exact selected-history bridge. The [earlier manuscript patch](docs/paper1-manuscript-reconciliation.patch)
targets Overleaf `0450d48`; it must not be applied wholesale to the current
`bd18900` manuscript. The revision note above records the remaining differences;
the [section-by-section writing review](docs/paper-writing-review.md) expands them.

The paper-facing policy now uses Kartik's split formulation: `rc-non-comm`
for distinct operation payloads, plus equal-payload self-commutation.
[`SplitPolicy.lean`](Sal/MRDTs/Paper1/SplitPolicy.lean) proves equivalence with the
combined laws on the same raw, represented-ready and invariant domains.
[`SplitCertificates.lean`](Sal/MRDTs/Paper1/SplitCertificates.lean) exposes the
19 existing cases through the split interfaces. FugueMax's new natural-history
certificate in `FugueMaxNaturalCertificate.lean` closes its former remaining
sequential-bridge gap on the existing invariant domain.
The dependency audit requires the five-VC verifier, merge induction and split
laws; it does not count aliases as independent implementations.

The [five-VC automation interface](experiments/vc-automation/README.md)
now supplies the production proofs for all 19 current named cases through
the common `mrdt_verify` command. Counter now means the single integer increment/decrement implementation;
increment-only duplicates have been removed. The named inventory includes anchored Queue
and representation variants; it differs from the 18-package production registry.
Registered inputs supply finite laws, datatype mappings and existing execution
or issuance evidence. For both OR-sets, `derive_mrdt_input` constructs that input
from proof-free annotations: `PolicyData` records the event comparison;
optional `MaskData` records the record type and carrier, update, birth and kill
maps. The frontend selects witness replay or mask replay, constructs the
finite templates, and discharges their laws from registered implementation
definitions. Embedded and Sided RGA supply an eight-map ordered-record description, raw-equation
annotations and chain/code mappings;
shared derivation constructs their ten finite laws from raw recursive equations,
derives coordinate order and injection, and projects existing issuance/replay
evidence. Anchored Queue, Peritext and Sided Core/RichCore reuse that route. Other families retain
explicit finite laws and evidence projections. Shared templates derive the history arguments, including
Core/RichCore and Fugue; no instance interface contains a bespoke history induction.
Lean selects registered algebra, collection and ordering helpers. The production audit
checks that existing certificate endpoints use the common soundness theorem and
their sequential bridges, excludes earlier correctness paths, and checks
contract preservation. Negative controls check missing obligations and rejected
correctness registrations. The automation README combines local declarations,
annotations and required datatype helpers in each instance's total, and reports
the shared library cost separately. Implementations and client-facing specifications are preserved. Replay-order names
are normalized to the event-order vocabulary; scoped certificate law carriers
use kernel-proved equivalent split-policy interfaces. All other public statement
arguments and premises are preserved.
Against production baseline `7880732`, required author code and annotations for
ordinary OR-set fall from 106 to 8 lines, and efficient OR-set from 219 to 26
lines; retained compatibility proofs are excluded when the generated input does
not use them.
Against the preceding ordered baseline `ffec6e9`, Embedded RGA falls from
378 to 60 required datatype lines and anchored Queue from 413 to 69, including
all required helper proofs, raw-equation wiring and code proof packaging.
Against baseline `7e7ec86`, Sided RGA falls from 424 to 67 required datatype
lines, Core from 430 to 74, RichCore from 434 to 78, and FugueMax from 959 to
322. These totals include raw-equation certificates, data mappings, concrete
code-composition proofs, finite issuance adapters and annotations. Shared
archive, prefix-code and minting proofs replace the retained datatype helper
proofs in the submitted Fugue VC input.
This historical Fugue measurement covers the five-VC proof. The former
live-parent language remains refuted; the separate natural-origin certificate
is now complete and has not been measured.

The historical shared-representation experiment discharged 40 finite equations
across eight input families (including the retired independent-account bounded
counter), covering sets, Boolean functions, scalar counters and
products of integer maps as well as native RGA. The selected kernel proofs
shrink from 70 to 16 lines using a 16-line generic tactic. TreeMove and
AegisSheet also reuse an origin-to-prefix lemma; their sequential correctness
arguments remain explicit. See the [cross-family results](experiments/vc-automation/README.md#shared-reasoning-across-datatype-families)
for full costs, controls and remaining manual work.

A separate [sequential-history bridge experiment](experiments/vc-automation/README.md#sequential-history-bridge-experiment)
reduces the required concrete bridge source from 49 to 23 lines for ordinary
OR-set and from 48 to 24 for efficient OR-set, against `052b8fb`, using a
175-line generic projection/fold library. Embedded RGA remains a boundary
experiment (2,021 to 2,001 lines): ordered-chain insertion adjacency and
execution/issuance legal-history selection retain substantial concrete proofs.
These full bridge closures include ordering and visibility and overlap the VC
invariant costs; their counts should not be added to the VC totals.

The [sequential-bridge table](experiments/vc-automation/README.md#sequential-bridges-beyond-or-sets)
now reports all 21 named cases separately from the VC proofs, including required
concrete helpers and remaining manual arguments. Guarded simulation derives
query/history consequences, while structural rules share freshness and origin
transport. The refreshed fixed-root comparison reduces the complete classified concrete
proof closure by 11 lines (7,799 to 7,788), while the conservative count of all
concrete declaration kinds grows from 9,005 to 9,019. Later framework and instance
changes prevent isolating the original campaign's net whole-source cost.
Embedded RGA's independent production bridge grows.
Further abstraction has limited returns: tree rendering, sheet materialization
and RGA insertion semantics remain manual.

The corrected core uses event-guarded laws in
[`GuardedReplay.lean`](Sal/MRDTs/Paper1/GuardedReplay.lean), direct semantic replay
in `GuardedConvergence`, `GuardedOrder`, and `ConcreteReplay`, and the full-event
history bridge in `ConcreteHistoryBridge`. The typed
[`GuardedCoverage.lean`](Sal/MRDTs/Paper1/GuardedCoverage.lean) matches all 20
production packages: **12 have ordinary and virtual execution certificates,
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
[`CertifiedCoverage.lean`](Sal/MRDTs/Paper1/CertifiedCoverage.lean): **12 retained
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

FugueMax's natural certificate combines invariant closure, scoped replay laws,
the five merge VCs, and a complete independent origin-list history bridge.
`FugueMaxNaturalCertificate` covers ordinary and recursive executions and
preserves maximal noninterleaving on the same history witness. Its physical
client refinement proves the original issuer implements positional edits.
The older live-structural-parent language remains a checked counterexample:
a generated structural parent may be a tombstone. That obstruction concerns
the rejected language, not the new origin-list specification.

The historical unanchored Queue obstruction remains separate from the positive
certificate for the current anchored Queue described below.

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
the original Queue or the 18-of-20 production count; it has no JavaScript port.

The sole bounded counter is the [published Balegas design](Sal/MRDTs/Instances/BalegasBoundedCounter.lean):
a sender–recipient transfer matrix, consumption vector, increment/decrement/transfer,
and componentwise-max merge. Its [five VCs](Sal/MRDTs/Paper1/BalegasBoundedCounterVC.lean)
feed the generic merge induction with full causal metadata. The
[independent sequential bridge](Sal/MRDTs/Paper1/BalegasBoundedCounterCertificate.lean)
proves legal scalar/rights histories and every stored version's lower bound;
the [global theorem](Sal/MRDTs/Paper1/BalegasBoundedCounterGlobal.lean)
covers the union of all issued events. Both ordinary and recursive-merge executions
are covered. Nonnegative amounts, distinct transfer targets, sufficient local rights,
and serialized issuance per replica are explicit. Ten Lean PASS+FAIL controls and
[a bounded exhaustive model check](experiments/vc-automation/balegas-controls.py)
exercise the design. Earlier independent-account and additive-budget experiments
have been removed from the active tree.

Neem's corrected **enable-wins and disable-wins flags** are also verified.
Their per-replica integer-counter/bit implementation shares a
[five-VC proof](Sal/MRDTs/Paper1/EnableWinsFlagVC.lean); both have independent
Boolean sequential specifications and ordinary/recursive execution certificates.
The [audit](Sal/MRDTs/Paper1/NeemFlagAudit.lean) checks both theorem dependencies
and 321 declarations. Nine Lean PASS+FAIL examples and exhaustive small-trace
controls cover both polarities and distinguish the older scalar-flag bug.
Neem's source omits queries; we explicitly supply the surviving-enable query
and its disable-wins dual. These additional cases are not yet measured in the
automation effort tables.

Neem's **remove-wins set** and **set-wins map** also have checked five-VC,
independent sequential-history, and ordinary/recursive execution proofs.
The [remove-wins set](Sal/MRDTs/Paper1/RemoveWinsSetAudit.lean) retains the
source's timestamp-zero initial removal tags and reserves zero through an
explicit positive-timestamp issuance guard. Its finite-universe model includes
Neem's two-element example and uses an ordinary-set sequential specification.
The [set-wins map](Sal/MRDTs/Paper1/SetWinsMapAudit.lean) retains all values
inserted at a key until deletion. Neem supplies no query; our explicit
set-valued lookup is certified against an independent accumulating multimap.
Both audits check that the execution results consume the five VCs and generic
merge induction, and reject nonstandard axioms. Hand-derived PASS+FAIL tests
pin the intended query results and competing incorrect behaviors.

The [Neem optional register](Sal/MRDTs/Paper1/OptionalRegisterCertificate.lean)
preserves its finite partial-map domain, counter/flag arithmetic, and
equal-timestamp averaging branch. A scoped bridge proves an independent scalar
`Option Nat` specification with ordinary `set` and `unset`; the chosen query
returns the greatest-timestamp active value. Reachability derives the payload
coherence needed by the source merge. Positive issued timestamps also establish
the [source state refinement](Sal/MRDTs/Paper1/OptionalRegisterSourceValidity.lean).
Its five-VC-derived execution certificate covers ordinary and recursive bases
with the application policy `unset → set`.

The [add-wins priority queue](docs/add-wins-priority-queue-port.md) ports Sal's
retained-increment variant: the latest live Add supplies an innate priority,
and all historical signed increments contribute to it. Remove preserves those
increments. The application policy orders same-element Remove before Add.
Its five VCs feed the generic merge induction. The public `FullD` interface
certifies empty, membership, priority and maximum queries for ordinary and
recursive executions against an independent finite priority-map model.
Maximum ties choose the greatest element ID; soundness and completeness are
proved. Derived `rmvMax` returns the locally observed maximum pair and issues
ordinary removal of its identity, preserving historical increments. Its local
refinement is proved; two concurrent replicas may return the same pair, so it
makes no atomic global-extraction claim. No additional local issuance guard is
needed. Twenty-three PASS+FAIL controls exercise the implementation, queries
and client. This is Sal's retained-increment variant, not the full Internetware
2023 Most-Change-Win algorithm.

`GSet`'s alias module has been removed: the single mathematical grow-only-set
implementation is `AddStore`, with one coverage entry. `FinsetStore` and
`FlatGrowOnly` provide enumerable and Boolean representations of the same abstract
set datatype. Coverage and automation counts refer to implementation/proof cases,
not distinct abstract datatypes. The public reference groups these representations.

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
concrete updates and merges are unchanged; the issuer now explicitly restores
the source convention that insertion IDs are positive. `Paper1.RGAComparison` checks both
negative and positive criteria on the same reachable read `[5,4,8,7]`.
These paper-facing results do not assert a migration of every
production package to the restricted policy.

`Paper1.EventBridge` exposes full-input simulations, independent fold-history
acceptance, mint-sensitive and execution-sensitive chosen-history premises,
Join/five-VC soundness, and finite-trace guarantees. TreeMove and AegisSheet use
`GuardedHistory` to retain their independent in-place machines and causal-origin
legality. The published bounded counter retains sufficient-local-rights
guards and single-writer causal predecessors. Its independently legal causal
histories prove specification-visible correctness and the global lower bound.

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
the abstract state, legal histories, and queries. The generic `EventOrder`,
stored as `VerifiedMRDT.replayOrder`, supplies an explicitly selected ordering
on complete events. It may inspect timestamps and replica IDs. Its derived
`loOn` relation is used by that generic certificate.

The paper1 conflict policy is instead `OperationPolicy.before`, written `rc`
in the paper. It compares operation payloads; its event lift compares the
payloads of the two events. An independently chosen `EventOrder` need not be
that lift and must not be called the paper's `rc`. The paper1 certificates
state their own policy, semantic order, and sequential-history obligations.

`VerifiedMRDT` combines these with widened convergence, a representation relation, and a
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
