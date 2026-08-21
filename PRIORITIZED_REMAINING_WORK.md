# Prioritized Remaining Work

This is the canonical development backlog for Sal. It owns Lean metatheory,
datatype proofs, runtime implementation, executable validation, benchmarks,
and repository CI. The sibling `Sal_paper` repository owns manuscript prose,
structure, figures, bibliography, paper builds, and paper-specific claim
audits. Paper plans may cite tasks here as evidence dependencies, but must not
duplicate them as paper-owned development tasks. Completed subsystem roadmaps
are historical evidence; this file determines what development comes next.

## Priority order

### 0. Audit end-to-end theorem coverage before further paper claims — immediate

The current evidence has been composed too often at the prose level rather
than at the theorem-signature level. In particular, the following results are
separately complete:

- virtual-LCA commit-GC safety over `Step3V`;
- distributed commit-GC refinement;
- combined distributed fetch, commit GC, Peritext state GC, and visible-step
  refinement over ordinary `Step3`.

They do **not** yet imply a theorem for arbitrary interleavings of distributed
fetch, virtual-LCA merge, commit-history GC, and Peritext state GC. The public
`combinedSteps_refines_Step3` conclusion is `Step3`, not `Step3V`.

Immediate review checklist:

- [x] Build a checked coverage matrix whose axes are ordinary/virtual LCA,
  global/distributed execution, commit/state/both GC, generic/Peritext scope,
  one-step/finite-trace/query result, and Lean/JavaScript realization.
- [x] Resolve every positive matrix cell to an exact declaration and record
  its complete conclusion and load-bearing hypotheses. Do not infer a product
  cell from separate component theorems.
- [x] Audit `ProductionCertificate`, `PeritextFlagshipCertificate`, the
  production ledger, `README.md`, `PRODUCTION_CERTIFICATES.md`, and the
  consolidated/split drafts against that matrix.
- [x] Downgrade or remove every unsupported use of “complete,” “end-to-end,”
  “arbitrary interleavings,” or “ordinary and virtual” found by the audit.
- [x] Add a repository checker that resolves the declarations required by
  each claimed cell and distinguishes `Step3` conclusions from `Step3V`.
- [x] After the audit, plan and prove the known open flagship cell:
  distributed `Step3V` + virtual merge + commit-history GC + Peritext state GC
  + finite-trace erasure/query preservation.
- [ ] Only then restore the corresponding end-to-end paper and certificate
  claims and test the matching JavaScript boundary.

This review is the immediate next task. Do not start another paper-facing
feature until it has produced the coverage matrix and corrected claim ledger.

**First virtual-closure increment (machine-checked 2026-08-21).** The audit
refuted the old `LocalGCCertificate.common_closed` boundary: retaining every
common ancestor forces retention of the root. The certificate now requires
only recursive singleton-MCA closure. The new
`compressed_isLCA_iff_of_mcaClosed` proves exact LCA lookup under that weaker
root-free condition, and a concrete certificate collects the root. The
ordinary catalogue theorem `gc_safety_compressed` is now documented honestly
as a conjunction over independent carriers, not a linked execution theorem.

`DistributedConfigStepV` and `CombinedStepV` now admit virtual merges with
explicit MCA-closure availability. `distributedConfig_refines_Step3V` and
`combinedStepsV_refines_Step3V` prove finite-trace erasure; the latter composes
fetch, both collectors, ordinary or virtual visible steps, and
`combinedTraceV_query_eq`. Fetch-side progress is now explicit:
`stepAvailableV_merge_after_repair` proves that one fetch from an MCA-repair
source enables the merge, while `fetchResult_virtualMerge_ready` also proves
that every required compact Peritext input arrives.

The proposed recursive compact virtual-LCA builder is unnecessary for
Peritext. `HeadOnlyMergeCertificate.related` proves the compact merge result
directly from the two branch heads while the virtual LCA remains ghost state;
`MaterializationDelta.headOnlyMergeInstall` installs that result. These
constructors are exported by `ProductionCertificate.virtualRepairReady` and
`headOnlyVirtualMerge`, closing the Lean certificate-driven composition cell.
The JavaScript virtual-merge path remains open.

The progress audit also refutes plain fetch union as a closure-preserving
protocol. Two independently MCA-closed singleton stores can union their heads
without either cross-head MCA. The virtual protocol must fetch/reconstruct the missing
cross-store MCA closure before head sync. The checked repair theorem is
conditional on locating a peer that has the closure; discovery/reconstruction
across several peers is a runtime liveness task, not an unproved safety step.

**Executable closure increment (2026-08-21).** The shipped
`DistributedReplica` already implements recursive virtual LCAs and
cross-epoch lifting. `runtime/test/combined-virtual-gc.test.js` now proves by a
directed twin execution that Peritext state GC, root-free commit GC, and a
genuine criss-cross merge match a never-collected control. An attempted
arbitrary pairwise recovery test exposed the transport gate:
root-free Lean semantics can read a retained MCA directly, but JavaScript
delta replay still needs its discarded parent chain; do not restore
root/skeleton retention.

**Certified boundary transfer completed (2026-08-21).** The runtime now ships
the original version id, remaining compressed parents, epoch, closed roster,
encoded materialization, fingerprint, and integrity checksum. Under the
trusted-peer threat model this is a checked simulation boundary, not Byzantine
authentication. Corrupted fingerprints/certificates are rejected, bootstrap
and continuation pass, and only datatypes with an explicit proved
`headOnlyMerge` capability can merge disconnected compressed stores. Peritext
has that capability via `HeadOnlyMergeCertificate.related`. The randomized
cross-epoch criss-cross test now runs both collectors with zero deferrals.

### 1. Split `sal-mrdts` into two standalone papers — completed 2026-08-01

- Paper A: corrected and conditioned metatheory, Join doctrines, virtual LCAs,
  and composition.
- Paper B: sequence designs, intent, compaction, runtime, lower bounds, and
  evaluation.
- Extract shared notation and bibliography support.
- Make both papers build independently.

Delivered by `Sal/ConditionedMRDTs/PAPER_SPLIT_PLAN.md` and the two entry
points under `Sal/ConditionedMRDTs/papers/`. Shared notation remains
single-source in the canonical manuscript preamble; both selected papers and
the consolidated manuscript build with Tectonic. This records historical
repository state only. All further paper editing is tracked in the sibling
`Sal_paper` repository.

### 2. Retire the legacy global-`lo` proof route completely — completed 2026-08-01

- Decouple corrected metatheory from `Merge_Linearization.lean`.
- Remove or archive its six remaining proof placeholders.
- Ensure production builds contain no path through legacy `sorryAx` results.

Delivered by the merge-independent
`Sal/CRDTs/Metatheory/Linearization_Basics.lean` and the archived historical
source `Sal/CRDTs/Development/Merge_Linearization_GlobalLo.lean.disabled`.
The corrected set-relative theory no longer imports the global-`lo` attempt;
the active Lean tree contains no `sorry` commands, and the binary corrected
bridge plus the conditioned refactor ledger build successfully.

### 3. Correct the operation-to-state emulator — completed 2026-08-01

- Replace the current `Set Msg` scaffold with Shapiro et al.'s
  `(s_m, M, D)` construction.
- Model preparation, known messages, delivered messages, enabled delivery,
  and internal delivery steps.
- Treat Shapiro et al. 2011 as the construction blueprint and Liittschwager et
  al. 2025 as the formal simulation and transfer target.

Delivered in `Sal/Emulation/Emulation.lean` and
`Sal/Emulation/Conditioned_Emulation.lean`. The emulator now uses the original
materialized/known/delivered tuple, causal schedules, generation preparation,
enabled internal delivery, and causal-downset invariants. Its verification
endpoint is `VerifiedMRDT (shapiroConditionedG ...)`; the old 24-VC/`True`
transfer scaffold was removed.

### 4. Formalize Liittschwager-style emulation — completed 2026-08-01

- Generalize weak simulation from label equality to label morphisms.
- Prove the required weak simulations between the original and emulating
  transition systems.
- Prove weak-trace and representation-independence results.
- Use the grow-only set as the first concrete canary.

Delivered by the label-morphic `WeakSimM`, `LabelMorphism`, `LabelIso`, and
`EmulationEquivalence` interfaces in `Sal/Emulation/Weak_Simulation.lean`.
Weak-step/execution lifting, trace transport, two-way trace equivalence, and
representation independence are proved generically. The grow-only-set canary
proves both simulations between distinct op/state label grammars, including
silent message-delivery/singleton-merge steps. Priority 5 connects this
behavioral layer to the conditioned RA-linearizability certificate.

### 5. Finish the RA-linearizability transfer — completed 2026-08-14

- [x] Define op-based RA-linearizability as a genuine universal weak-trace
  property, parameterized by a concrete RA trace legality judgment.
- [x] Define the explicit conditioned trace-realization obligation connecting
  `VerifiedMRDT.ra_linearizable` to observable state-system traces.
- [x] Prove one-way weak-simulation and two-way emulation transfer theorems.
- [x] Define the actual certificate-scoped conditioned `Step3` system view and
  observable label map: updates/queries are visible; timestamps, replica
  creation, merge, and message delivery are handled through τ-observation.
- [x] Lift packaged `VerifiedMRDT` correctness and trace transfer to the
  widened `Step3V` semantics, so virtual LCAs cannot deadlock emulated state
  delivery after criss-cross synchronization.
- [x] Prove the datatype-generic forward weak simulation from the disciplined
  op semantics to that state system (full label isomorphism is neither
  necessary nor generally available for silent administrative labels).
  This now requires an explicit operational-progress layer: current
  `VerifiedMRDT` certificates prove RA correctness of honest reachable
  configurations but do not construct invariant-laden `Step3V` successors.
  The separate operational/network progress interfaces and their observed
  weak-step adapters keep these constructive deployment assumptions explicit.
  The source is now the well-formed `disciplinedOpLabeledTS`: its update rule
  enforces the trace-side freshness/causal obligations corresponding to
  `EmulatorState.PrepareEnabled`; raw `opLabeledTS` remains available as the
  unconstrained network semantics.
  The target now has a Liittschwager-style snapshot-network envelope:
  broadcasts buffer immutable conditioned version ids, and delivery merges
  exactly that historical version rather than the sender's newer head.
  `SnapshotMerge.storeInv` and `SnapshotMerge.goodConfig` prove that this new
  delivery rule preserves the existing conditioned invariants. The full
  network reachability induction is complete: `networkRALinearizable` proves
  every reachable envelope state's conditioned core is RA-linearizable.
  Network-level constructive progress and the generic coupling-to-`WeakSimM`
  theorem are complete (`ShapiroNetworkCoupling.forward`).
  `ShapiroCouplingWitness` now defines that concrete dynamic correspondence;
  `ShapiroCoupled.initial`, `query_preserved`, and full update/broadcast
  preservation are proved. The source generation discipline now includes the
  missing causal-broadcast law that every issuer-incorporated message happens
  before the new message; without it, historical snapshot delivery can apply
  extra concurrent messages and the claimed simulation is false. For update, bidirectional
  replica correspondence, incorporated/known/delivered correspondence,
  fully-drained preservation, and the fresh version carrying the exact new
  message are proved. Bidirectional post-broadcast packet correspondence is
  also proved, as are generated-message map preservation, causal snapshot
  contents, buffered-packet pendingness, and final witness assembly.
  Delivery/snapshot-merge preservation is now proved as well. The progress
  result is indexed by the exact snapshot it consumes (an earlier target-only
  result type was too weak), and `forwardSimulation` assembles the complete
  datatype-generic weak simulation from explicit constructive progress.
- [x] Construct the trace realizer for the conditioned snapshot network and
  discharge its reachability obligation. `canonicalNetworkRealize` chooses a
  weak-execution endpoint, `canonicalNetworkRealize_reachable` proves network
  reachability, and `network_ra_linearizable` applies the envelope's checked
  historical-delivery induction. Observable adequacy remains an explicit
  datatype/client-spec input, as it cannot be derived from an arbitrary
  `RATraceSpec`.
- [x] Instantiate the complete theorem for a concrete grow-only-set op
  signature in `GSet_Conditioned_Transfer_Canary.lean`, including PASS/FAIL
  operation controls. The canary intentionally exposes certificate, progress,
  and adequacy inputs rather than manufacturing them.

### 6. Make commit GC genuinely bounded — completed 2026-08-15

- Replace commit GC's verbatim retention of the full `parents` skeleton with
  reachability-preserving compression over the retained versions. First
  remove the pinned-root retention requirement from the GC model; then prove
  that eliminating dropped interior versions while shortcutting their paths
  preserves reachability, common ancestors, and `IsLCA` among retained
  versions, and lift `gc_safety` to the compressed DAG. The target should
  retain only keep-set payloads and the ancestry information needed to reach
  them, rather than `O(number of commits ever)` history.
- Formalize the `DistributedReplica` execution model with a separate local
  head, commit store, closed roster, and immutable author provenance at each
  replica; asynchronous fetch/receive steps union commits, derive frontier
  evidence from received ancestry, and keep synchronization with advertised
  current heads as a separate step. The wire must not carry an independent
  frontier-evidence assertion. Define local GC from a replica's head plus
  complete derived evidence for every roster member, and prove a forward
  simulation to the corresponding no-GC
  execution preserving future receives, merges, and reads. The protocol must
  refuse GC when any registered member lacks evidence, specify safe membership
  reconfiguration and parent-free epoch-base ingestion, and justify that an
  evidence commit remains an ancestor of every later head from its author
  under the own-head update discipline. Audit and fix `DistributedReplica.gc()`:
  unlike `stableCut()`, it currently omits missing frontier entries instead of
  refusing collection.

  **Completed evidence (2026-08-15).** `GC_CompressedDAG.lean` removes root
  pinning from the compressed carrier, mentions only retained versions, proves
  exact retained reachability and retained-order `IsLCA`, and packages those
  results with the existing trace/read theorem as `gc_safety_compressed`.
  `Distributed_GC.lean` supplies separate local stores/heads/rosters,
  fetch/ingest by union, refusal on incomplete derived evidence, safe roster
  removal and epoch-base ingestion, fetch/head-sync/read forward-simulation
  lemmas, and the own-head evidence-ancestry theorem. The JavaScript GC now
  removes boundary parent references as well as payloads and
  `DistributedReplica.gc()` refuses when any other roster member lacks
  frontier evidence. Directed tests and the existing 340-trial twin PBT pass.

  **Completed alignment increment (2026-08-15).** `Distributed_GC.lean` now
  models ordinary fetch/ingest separately from head synchronization. A fetch
  transfers immutable commits and their author provenance, never a frontier
  assertion; `DerivedEvidence` computes evidence from locally held authored
  commits that reach the current head. `distributed_execution_refines_noGC`
  proves a finite world-level forward simulation: fetch and head-sync match,
  local collection stutters, final head reads agree, and missing provenance is
  a checked FAIL control. A checked counterexample shows that one asynchronous
  local collection cannot refine one shared global store by exact state
  projection: the collected replica and an uncollected replica have different
  holdings. `coordinated_collect_projects_global` establishes the correct
  quiescent boundary instead: once every replica uses the same certified keep
  set, their stores project exactly to one globally collected carrier. The
  remaining paper-critical link is to identify that coordinated keep set with
  the keep set consumed by the datatype-rich global `Configuration` GC theorem
  and compose their read/trace results. Do not claim direct per-local-step
  refinement to global GC.

  **Datatype-rich direct refinement (2026-08-15).**
  `Distributed_GC_Refinement.lean` overlays separate physical holdings on the
  full conditioned `Configuration`. Fetch and local GC are silent. Visible
  create/apply/merge/query transitions carry actual `Step3` derivations and
  are gated by physical availability: apply/query require the actor's head;
  merge requires both heads and a materialized LCA in the actor's holding.
  Visible store evolution may add only the actor's new head, so it cannot hide
  a fetch by fabricating arbitrary allocated commits.
  `distributedConfig_refines_Step3` proves every finite distributed execution
  erases to a genuine full conditioned execution, label for label after silent
  fetch/GC removal. PASS/FAIL theorems show well-formed heads enable queries
  and missing physical heads disable them. The theorem uses only `propext`.
  This direct result is the paper's primary GC refinement; the coordinated
  global-carrier comparison is secondary.

  **Generic correctness lift completed 2026-08-15.** Strengthen the
  datatype-rich distributed semantics with `GenerationContract` checks and
  mint provenance. Prove one datatype-generic theorem that turns a certified
  `DistributedConfigSteps` execution into `MintCertifiedReach3`, then composes
  with any `UnifiedVerifiedMRDT` to obtain RA-linearizability, safety, and
  history-conditioned sequential refinement. Do not build a Peritext-only
  proof.

  Instantiate the generic theorem for:

  - Peritext as the flagship rich-text result;
  - tombstoned RGA as its sequence substrate;
  - mergeable queue for nontrivial operation honesty;
  - bounded counter for a nontrivial safety invariant and applicability guard;
  - MVR for overwrite/freshness generation discipline; and
  - OR-set as the simple GC baseline.

  The remaining production RDTs should require certificate-only, preferably
  one-line, instantiations. Keep detailed proof development and checks here;
  maintain the paper's selection and summary table only in `Sal_paper`.

  `MintCertifiedDistributedConfigStep` and
  `MintCertifiedDistributedConfigSteps` now reuse the existing guarded step
  and mint-history witnesses. `mintCertifiedReach_of_distributed` maps any
  certified distributed run starting at `initConfig` into the existing
  `MintCertifiedReach3`; `UnifiedVerifiedMRDT.distributed` then packages
  RA-linearizability, safety, and observable consequences. Sequential intent
  remains explicitly history-conditioned through
  `distributedSequential`; the theorem does not invent one total order for a
  concurrent execution. `DistributedUnifiedCertificates.lean` contains
  certificate-only instantiations for both positive Peritext kernels,
  tombstoned RGA, queue, bounded counter, MVR, and OR-set. The production
  ledger checks the complete chain.

  **Fetch-acknowledgement follow-up completed 2026-08-15.** The empty-document audit shows
  that Peritext state GC reaches the fresh-empty representation: no character
  records, tombstones, marks, or coordinate symbols remain. Commit-history
  pruning nevertheless refuses if a quiescent peer fetched the compaction
  epoch but authored no later datatype operation, because current frontier
  evidence advances only through authored commits. Align evidence exchange
  with ordinary remote fetch. `syncReplicas` now records an authenticated
  receipt bound to a locally held content-addressed head and its recomputed
  epoch key; it advances monotonically without manufacturing a document
  operation. `Distributed_GC_Acknowledgements.lean` proves that receipt steps
  stutter in the no-GC semantics, lifts this result to arbitrary finite
  fetch/ack/GC executions, and shows that complete past-cut receipts provide
  datatype-independent pruning evidence. The same receipt now travels over the
  live p2p WebSocket protocol. Its integration SPOT reduces the empty document
  to one epoch-base commit after a quiet peer pulls; the FAIL controls reject a
  forged head and retain history before acknowledgement. Receipts are
  deliberately unpersisted soft state, so restart safely requires a refetch.
  `npm run bench:empty-gc` is the reproducible measurement harness: histories
  of 22, 202, and 2,002 commits each reduce to one epoch-base commit, 9 durable
  datatype bytes, zero coordinate symbols, and zero visible characters.

### 7. Complete conditioned contracts and the intent column — completed 2026-08-14

- Consolidate the split conditioning architecture. The current catalogue
  inconsistently stores the real issuer guard outside
  `ConditionedMRDTSig.applicable` (`qApplicable`, `eApplicable`,
  `sApplicable`), then separately bridges it through instance-specific
  `*Honest` and `*Reach` predicates. Execute this migration in order:
  1. Build a checked ledger for every production capstone recording its local
     issuer guard, configuration-history honesty predicate, state invariant,
     Join hypothesis, reachability hypothesis, and sequential-history
     discipline. Classify by hypotheses actually consumed, not by whether the
     signature fields happen to be `True`.
  2. Define one generic generation-contract interface with a local
     `Guard : Op → State → Prop`, a history predicate, and a proved
     guard-to-history bridge. Support the existential mint-time causal fold
     needed by order-sensitive guards (queue head checks); do not force the
     unsound/overstrong all-enumerations form of `GenHonest`.
  3. Add a guarded execution/reachability layer whose `Apply` transition checks
     the guard against the issuing replica's materialized head state, and prove
     generic provenance and contract-preservation lemmas for ordinary and
     virtual-LCA execution. Keep raw total `Step3` available as the untrusted
     environment semantics.
  4. Separate client safety invariants from structural configuration
     well-formedness. In particular, avoid defining the execution over an
     `Inv`-restricted `Configuration` when preservation of that same invariant
     is the theorem to be proved (the bounded-counter circularity). Provide a
     safety-certificate component with initiality, guarded update preservation,
     merge/version preservation, and an observable safety consequence.
  5. Extend or layer `VerifiedMRDT` so one public conditioned certificate
     packages the guard, guard-to-honesty bridge, Join certificate, guarded
     RA-linearizability, safety invariant, and history-conditioned sequential
     refinement. Preserve `VerifiedMRDT.prod` by defining composition for all
     new contract fields.
  6. Migrate positive canaries in increasing difficulty: bounded counter
     (`bcApplicable`/`BCInv`), mergeable queue (`qApplicable`/`QHonest`),
     EmbedRGA (`eApplicable`/`EHonest`), SidedRGA
     (`sApplicable`/`SHonest`), then canonical Embed-based Peritext. Reuse the
     existing proofs; the first objective is API integration, not reproving
     their algorithms.
  7. Keep BudgetCart gated until its witness transfer is solved. Retire the
     broken rehoming RGA and Shesha designs from production catalogues and
     paper-facing names; keep only their minimized refutations as archived
     negative evidence.
  8. Update the machine-readable catalogue to report conditioning from public
     theorem hypotheses. Add a repository check that flags a nontrivial
     `*Applicable → *Honest/*Reach → capstone` chain when the corresponding
     certificate still advertises a trivial guard.

  **Completed evidence (2026-08-14).** `GenerationContract`, guarded ordinary
  and virtual execution, mint-provenance reachability, global/history safety
  (with optional stronger local laws), `UnifiedVerifiedMRDT`, and explicit
  product policy are machine checked. The bounded counter now has a complete
  unified package, including independent sequential refinement and ordinary
  plus virtual-LCA `BCInv`/non-negativity safety. Queue, EmbedRGA, SidedRGA,
  canonical Embed-Peritext, ORSet/ORSetE, LWW/FWW, GOSet/GOMap,
  Counter/IOC/PN, and AWPQ have checked unified wrappers. FWW deliberately
  retains `Guard := True`; its experimental `fwwApplicable` is not promoted.
  The production ledger and `scripts/check-conditioning-contracts.sh` enforce
  the nontrivial guard chains and negative controls.

  Tombstoned RGA is now positive: `rgaApplicable` checks anchor closure,
  timestamp/id freshness, grave exclusion, and live removes;
  `RGAHistoryOK`, `rgaSequentialSound`, and `rgaUnified` package its genuine
  sequence model independently of the retired experimental designs.

  MVR is now positive through `mvrApplicable`, `MVRMintHistory`,
  `mvrGeneration`, and `mvrUnified`. Tombstoned Peritext is positive through
  `ptApplicable`, `PtHistoryOK`, `ptSequentialSound`, and `ptUnified`; its
  folded state does not retain remove-operation timestamps, so the public
  guard claims target liveness but not freshness against earlier removes.
  EWFlag is positive through the doctrine-faithful `ewflagUnifiedF`, which
  consumes `JoinLemma3F` directly rather than assuming the Gate-G1 converse.
  **Priority 7 completed 2026-08-14.** Every named positive production
  datatype is covered by a public checked package. BudgetCart remains gated on
  witness transfer. Rehoming RGA and Shesha are retired from the active design
  space; their checked counterexamples remain under the refutation/audit
  surface only.

- **Completed:** make the bounded counter the first unified nontrivial conditioned-RDT
  flagship: one public theorem/certificate should connect its existing
  sequential correctness, `bcApplicable`, guarded honest reachability,
  `BCInv`, `bc_version_inv`, and `bc_value_nonneg`.

- **Completed:** tombstoned RGA now exposes anchor closure, timestamp/id
  freshness, grave exclusion/live removal, and the genuine-sequence package
  through `rgaApplicable`, `RGAHistoryOK`, `rgaSequentialSound`, and
  `rgaUnified`.
- **Completed:** OR-set variants, queue, both positive Peritext kernels,
  registers, counters, maps/sets, AWPQ, EWFlag, MVR, and the remaining named
  production datatypes are represented in the checked catalogue.

### 7A. Consolidate conditioning around the successful proof boundary — paper gate

This is the gating development step for the paper's framework presentation and
flagship theorem. It does not block independent GC or benchmark engineering.
Preserve the paper's causal narrative: mechanizing Neem's bottom-up
linearization exposes the broken argument; the corrected join-based
metatheory is the foundation; realistic sequence datatypes then expose the
separate mint-provenance obligation.

- Inventory every public theorem's actual dependence on signature-level
  `Inv`/`applicable`, `GenerationContract.Guard/History`, and
  `SafetyCertificate`. Distinguish convergence/RA, client safety, and
  sequential intent. Do not classify a condition as load-bearing merely
  because a legacy signature field is nontrivial.
- Define, alongside the existing API, the smallest candidate architecture:
  flat MRDT algebra; a first-class generation policy carrying issuer guard,
  causal mint evidence, and its history bridge; a separate client-safety
  policy; and a sequential mint policy that includes the local Lamport-clock
  premise identified by `ConditioningIntentAudit`. Retain raw execution as the
  untrusted environment semantics.
- Repackage EmbedRGA, SidedEmbedRGA, canonical Peritext, queue, and bounded
  counter as canaries. Recover the existing corrected Join/RA, virtual-LCA,
  product, safety, and sequential theorems without weakening their statements
  or inventing one global sequential list for a concurrent execution.
- State the flat-RGA comparison explicitly: flat algebra proves convergence;
  its sequential theorem exposes the generation premise; the generation and
  clock policies discharge that premise for a sequential client. Preserve
  checked negative controls for guard-only timestamps and malformed
  anchor/path generation.
- Prove compatibility or theorem-equivalence adapters between the candidate
  package and `UnifiedVerifiedMRDT`. Do not delete or rewrite the existing
  framework until the canaries and production ledger pass through the new
  interface.
- Decide from the completed dependency audit whether signature-level `Inv` and
  `applicable` remain core, become an optional state-conditioned algebra
  extension, or are retired from the paper-facing interface. Record that the
  rehoming RGA and Shesha supplied genuine algebraic conditioning examples but
  are refuted designs; do not use either as positive evidence.
- Export one public Peritext result that composes the corrected Neem
  metatheory, generation-conditioned distributed correctness, the sound local
  sequential-intent theorem, and both GC refinements with every remaining
  assumption visible. Update the stable theorem manifest and claim checker.

Completion gate: the production ledger builds without `sorryAx`; the public
claims distinguish distributed RA correctness from local sequential
refinement; and the paper no longer relies on a successful production datatype
whose unconditional algebraic VC is false unless the audit actually finds
one.

**Dependency-ledger and canary increment completed 2026-08-19.**
`Development/CONDITIONING_DEPENDENCY_LEDGER.md` records the proof-body audit for
EmbedRGA, SidedEmbedRGA, canonical Peritext, queue, and bounded counter. The
result confirms that generation history is load-bearing for the first four
Join proofs, while bounded-counter conditioning is load-bearing for safety;
none uses signature-level `Inv`/`applicable` to rescue a false production Join
VC. `LinearMintHistory` is now a framework-level local guard-and-clock
judgment. `GenerationVerifiedMRDT` stages the candidate consolidated package
with a lossless adapter to `UnifiedVerifiedMRDT`, ordinary and virtual-LCA RA,
safety, and a separate local sequential conclusion. All five canaries inhabit
it. Checked bridges derive `eSeqOK`, `sSeqOK`, queue `qOK`, bounded-counter
`BCSequentialHonest`, and the rendered Peritext theorem. The production ledger
passes 3,456 jobs with standard axioms only. The runtime now has a separate
trusted generation path backed by an explicit replica slot and persistent
Lamport counter. It stamps every operation (including deletes), observes
accepted remote and raw local timestamps, survives state-GC epochs and
commit-history pruning, and refuses trusted generation when no collision-free
slot assignment is supplied. Raw `commit` remains the untrusted semantics.
Runtime tests include distinct-slot, causal-fetch, missing-slot, operation-
coverage, recovery, post-GC/pruning, and new-replica controls. Remaining gate:
define how a deployment allocates unique persistent slots, then decide whether
signature-level conditioning is an optional extension or compatibility-only
surface before changing the old API.

**Certificate-boundary decision completed 2026-08-19.**
`AlgebraVerifiedMRDT` is the paper-facing algebra and sequential-intent layer;
it has no `Inv` or `applicable` field. `OperationalConditioning` isolates the
initial invariant witness required by the legacy proof-carrying
`Configuration`. Generation and safety remain separate first-class policies.
The checked split/rebuild round trip is lossless, while the boundary control
requires operational evidence explicitly instead of manufacturing it. Thus
signature-level conditioning is a compatibility extension, not the primary
paper interface. `PeritextFlagshipCertificate` now supplies the single public
composition: ordinary and virtual-LCA distributed RA, version safety, local
rendered sequential intent from clocked minting, root-free compressed
commit-history GC, asynchronous distributed commit-GC refinement to no-GC
behavior, and Peritext state-GC render preservation. The production ledger
checks `peritextFlagship`. Remaining 7A work is the stable external claim-
manifest update; deployment-level unique-slot allocation remains an
implementation refinement obligation.

### 7B. Prove the shipped SidedEmbedRGA Peritext architecture — paper gate

The JavaScript production default is `PeritextSidedEmbedRGA`: sided/Fugue text
plus a separate mark store. The current `peritextFlagship` instead certifies
one-sided generic EmbedRGA with fused boundary payloads. Do not present these
as the same datatype. The evidence audit is
`Development/SIDED_PERITEXT_FLAGSHIP_AUDIT.md`.

- Define the exact Lean operation/state correspondence for sided text plus the
  runtime mark store.
- Compose sided Join correctness with a genuine mark-store certificate and a
  nontrivial generation policy.
- Prove rendered refinement to an independent sequential rich-text machine.
  A `True` relation or reuse of convergence as intent evidence is not enough.
- Extend sided policy GC with mark retention roots, guarded mark-pair removal,
  delayed operations, and never-collected-twin render preservation.
- Add PASS/FAIL controls for overlapping marks, boundary deletion, concurrent
  add/remove, sided interleaving, post-GC continuation, and delayed delivery.
- Replace the paper flagship only after the complete production ledger and
  JavaScript differential oracle pass.

Completion gate: one public Sided Peritext certificate supplies ordinary and
virtual distributed correctness, local rendered sequential intent, compressed
and distributed commit GC, and mark-aware sided state GC. Its trusted
definitions agree with the shipped runtime on the stated differential scope.

**First increment completed 2026-08-19.**
`PeritextSided.Core` now models the runtime-shaped reachable representation:
insert-only sided text, a grow-only delete set, and a grow-only unique-`mid`
mark store. `core_join_at` machine-checks the three-component Join layer.
`coreGeneration` adds cross-component live-target, endpoint, timestamp, and
freshness checks and proves that product mint evidence supplies sided history
honesty. PASS/FAIL mark controls are checked.

**Second increment completed 2026-08-20.**
`PeritextSided_SeqSpec.lean` proves that a linearly minted product history
projects to the sided kernel's `LinearMintHistory`, including both the
state-sensitive guard and Lamport-clock premise. Consequently the text
projection is exactly the independent two-sided buffer program.

**Third increment completed 2026-08-20.**
The same module now defines an independent rich-text machine containing only
the ordinary two-sided buffer, deleted-character set, and immutable mark-event
set. `richSequentialSound` proves that every linearly minted runtime-core fold
represents that machine exactly; embedded coordinates and OR-set instances do
not occur in the specification relation. Because rendering is a pure function
of these three observations, local rendered intent follows by congruence. The
next gate is the concurrent/distributed flagship plus mark-aware state GC and
the JavaScript differential correspondence.

**Fourth increment completed 2026-08-20.**
`PeritextSided_Flagship.lean` packages the runtime-shaped core as a
`VerifiedMRDT` and `UnifiedVerifiedMRDT`. `distributedPreGC` now supplies the
generic distributed operational theorem, while `localRichIntent` exposes the
independent editor refinement. The name `preGCUnified` and its visibly trivial
safety field prevent this intermediate certificate from being presented as
the final production result. The remaining theorem gate is mark-aware
per-state GC; the remaining implementation gate is JavaScript differential
correspondence.

**State-GC design gate completed 2026-08-20.**
`PeritextSided_StateGC.lean` reuses the checked Fugue continuation
counterexample to refute naive independent collection of only text, deletions,
and marks. Stable deletion can still affect the next mint and final read.
The compact SidedEmbedRGA state therefore contains retained text plus derived
`LiveGap` observations. Peritext remains the three-component product
`CompactSidedEmbedRGA × DeletedIDs × MarkStore`; the gap summary is private
text metadata, not a fourth logical Peritext datatype. `gapEntryOf_exact`
proves that each entry stores exactly the side/parent and parent-chain
information consumed by Fugue minting.

**State-GC proof package completed 2026-08-20.** Compact minting and its
issuer guard now consult the retained gap summary; `compactInsertOp_exact`
proves equality with uncollected Fugue minting and `compactGapMerge_exact`
reuses the checked union-observation theorem. The three logical layers have
separate render-preservation results: dead text-shadow collection with mark
boundary roots, deletion-evidence trimming, and guarded add/remove mark-pair
collection. `applySeq_s_filter` and
`collectedText_continuation_render` cover later text delivery, while
`FrontierAtomicCertificate.delayedReferencesKept` makes the corresponding
delete/mark reference boundary explicit. `AllHeardSince` is not assumed to
mean stability: `FrontierAtomicCertificate.settled` derives `SettledAt` via
the generic evidence-discharge theorem. `frontier_collectStableBase_safe` is
the one-epoch capstone and `collectStableBase_twoEpoch` composes epochs. The
production ledger checks the complete chain.

**Runtime differential completed 2026-08-20.** The shipped
`compactibleSidedPeritext` uses the matching `LiveGap` text kernel, retains
mark and declared in-flight anchors, runs guarded A3 pair collection, and
derives its cut from the distributed meet. The runtime suite checks the
empty-document anonymous-root summary, snapshot continuation, boundary
retention, certified refuse/fire behavior, multi-epoch delayed delivery, and
never-collected-twin equivalence; the full 179-test suite passes. The final
`PeritextSided_Final.lean` now exposes `productionCertificate`, the public
composition of distributed/unified correctness, independent rich-text intent,
and frontier-backed state GC. `preGCUnified` remains only the clearly named
algebraic subcertificate used inside that final package.

**Distributed/state-GC interaction reopened 2026-08-20 — highest paper
priority.** The package above composes separate results; it is not yet a trace
simulation for arbitrary distributed interleavings of local state GC. The
new `PeritextSided_Interaction.lean` begins the required heterogeneous proof.
`StateRel` relates the ghost uncollected `Core` state to the compact runtime
carrier and retains exact Fugue knowledge, gap observations, live nodes,
delete agreement, mark provenance, and rendering. `StateRel.collect` proves
that a frontier-certified atomic collection preserves this relation, and
`CombinedConfig.WellFormed` now requires every physically held commit to have
a related local materialization. This exposed and fixes a real certificate
gap: the earlier `AtomicBaseCertificate` carried `∃ K, GapMapOK K gaps`, which
could name a history unrelated to the semantic source. The interaction
certificate pins `GapMapOK` to the source version's exact `K`.

Finishing checklist (ordered):

- [x] Prove asynchronous fetch transfers a sender materialization while
  preserving an already-held destination epoch.
- [x] Prove commit-history GC preserves all remaining state materializations.
- [x] Strengthen the epoch invariant with future-id retention derived from the
  frontier certificate; `StateRelAt` alone cannot derive the
  `keep freshId = true` premise consumed by `textProjection_apply`.
- [x] Prove all mixed text/delete/mark applies preserve the strengthened epoch
  invariant.
- [x] Construct common projection frames from retained epoch lineage, then
  discharge ternary text/delete/mark merge preservation.
- [x] Define the combined visible/silent operational semantics and prove its
  one-step erasure theorem.
- [x] Induct over arbitrary finite traces and lift query equivalence into the
  public production certificate and ledger.

The ordinary-`Step3` interaction theorem is now in the production ledger, but
it does not cover virtual-LCA `Step3V` executions. Do not describe
`productionCertificate` as fully end-to-end across virtual merges until
Priority 0 closes that composition.

**Interaction increment 2 (2026-08-20).** `StateRel` now carries an exact
filter projection, and collection composes the old projection with the new
retention plan. `textProjection_apply` proves fresh retained text application
commutes with that projection. `sMergeL_filter` proves same-epoch ternary text
merge commutes with collection; `CommonProjectionFrame.merge_text_exact`
makes the different-epoch obligation explicit by requiring translation of
the LCA and both heads to one projection. Grow-only delete and mark ternary
merges reduce to union, and payload projection distributes over that union.
Each `Materialized` version now records its projection. `StateGCAction` is the
first concrete combined transition: it updates one physical materialization,
preserves `CombinedConfig.WellFormed`, and stutters in the ghost no-GC
distributed semantics. `fetchResult_wellFormed` and
`commitGCResult_wellFormed` now close the two commit-store interactions.

**Frontier repair (machine-checked 2026-08-20).** A materialized epoch now
retains `FrontierProjection keep`: every rejected id is at or below the epoch's
Lamport frontier. Repeated GC composes when the new frontier advances and its
plan rejects only pre-frontier ids. `keep_future` proves every timestamp above
the frontier is retained, and `text_apply_after_frontier` discharges the
formerly missing text-apply premise. This is proof metadata around the scalar
frontier already present in the runtime protocol; it does not retain a set of
reclaimed ids.

The formal oracle also pinned the remaining boundary with a FAIL control:
timestamp inequality/freshness alone does not imply frontier order (for
example, 50 is fresh relative to 100 but is not above it). The JavaScript
`LamportMint.observe`/`next` protocol does supply the stronger rule by observing
fetched payload timestamps before minting. `Step3` currently states store-wide
non-collision only. The combined visible semantics must therefore retain and
check `MintAfterFrontier` (or strengthen the generic mint contract with causal
Lamport monotonicity) before the finite-trace theorem can use
`text_apply_after_frontier`. Do not replace this missing implication with a
post-state relation assumption.

**Causal-clock increment (machine-checked 2026-08-20).**
`GenerationContract.lean` now defines `CausalClockedAt` and
`ClockedGuardedStep3`: an apply records that every event in the issuer's
materialized head has a smaller timestamp. `CutFrontier` identifies the scalar
maximum of the settled epoch cut, and
`mintAfterFrontier_of_causalClock` derives the required strict inequality when
that cut is included in the current head. `ApplyEpochFrame` retains precisely
this epoch-to-descendant-head inclusion, and `ApplyEpochFrame.mintAfter`
connects a clocked Peritext step to compact text application. The remaining
work after mixed-apply closure is to construct the corresponding cross-epoch
merge frame and trace induction.

**Mixed-apply closure (machine-checked 2026-08-20).** `StateRel` now also
retains the guard-derived facts that every semantic deletion names a known
append-only text id and every compact deletion names a retained text id.
`delete_add` and `mark_add` preserve the complete rich-text relation.
`text_insert` extends the exact Fugue knowledge, requires a gap map derived
from that extended knowledge, derives retention of the minted id from the
Lamport frontier, and preserves rendering with deletions and marks.
`CompactApplyCertificate` exposes only operation-time obligations for the
three admitted runtime operations; `StateRelAt.compact_apply` proves that the
concrete compact interpreter simulates their semantic product update. The
common-projection construction is now also checked: `epochFactor` ensures an
epoch constrains only ids present in its semantic text, so an older concurrent
branch cannot veto a future id it never saw. `commonProjectionFrame_of_epochs`
translates all three materializations to this common predicate, and
`merge_text_after_epoch_translation` proves exact text-merge projection. The
next, the interaction closure discharges deletion/mark merge, reconstructs the
full post-merge `StateRelAt`, and proves visible/silent trace erasure.

**Interaction closure (machine-checked 2026-08-20).** `StateRelAt.merge`
reconstructs the complete text/delete/mark relation after a cross-epoch
ternary merge. `MergeCoverageCertificate` is the explicit operational bridge
from frontier/delayed-reference evidence: it requires live-id retention,
deletion-status coverage for retained text, and retained endpoints for the
merged mark set. It does not carry post-state rendering or a post-state
`StateRelAt`; the theorem derives both. This boundary is necessary because a
concurrent mark can make an old endpoint relevant at merge time, including its
deletion status.

`CombinedStep` now includes asynchronous fetch, commit-history GC, local state
GC, and visible distributed steps. `MaterializationDelta` requires existing
commit/version preservation and relation evidence only for newly installed
commits; `introduced_isSome` is the negative control that rules out a missing
physical materialization. `CombinedStep.wellFormed` proves one-step invariant
preservation. `combinedSteps_refines_Step3` erases both GC layers and fetch from
arbitrary finite interleavings, and `combinedTrace_query_eq` lifts rich-text
query equivalence to the final held versions. The production ledger checks the
merge, one-step, finite-trace, and query capstones.

**Physical merge boundary closed (machine-checked and executable
2026-08-20).** `PhysicalMergeEvidence` states the runtime-inspectable form of
merge coverage: live records and mark endpoints are physically present, and
delete bits agree on retained records. `PhysicalMergeEvidence.toCoverage`
derives the abstract `MergeCoverageCertificate` from the epoch translation's
exact-filter theorem; the production ledger checks the derivation and its
axiom audit. `PhysicalMergeEvidence.of_sources` derives live-record presence
from the two pre-merge relations plus the runtime's add-only birth-shadow
union, leaving only deletion propagation and endpoint availability as
frontier-sensitive evidence. The runtime now audits those physical premises after every
same-epoch or cross-epoch Peritext merge and fails closed.

The new concurrent-mark/collected-endpoint test exposed a real implementation
bug: Peritext's logically insert-only birth shadow reused the underlying RGA's
removal-aware ternary merge, so physical GC absence could be mistaken for a
user deletion. Peritext now merges birth shadows add-only (logical deletion
remains solely in `text.deleted`). The adversarial cross-epoch test restores a
collected dead endpoint from the old-epoch branch, preserves its concurrent
mark, and equals a never-compacted control. A negative test confirms that the
runtime audit rejects a mark with a missing physical endpoint. The complete
runtime suite passes 181/181, and the production Lean ledger passes 3469 jobs.

**Public promotion and visible-install closure (2026-08-20).** Visible apply
no longer needs a hand-written post-state relation: `SingleInstallFrame`
restricts a visible store evolution to exactly one fresh version, and
`MaterializationDelta.compactApplyInstall` constructs its physical delta from
the pre-state relation plus `CompactApplyCertificate`. Cross-epoch merge uses
the same `MaterializationDelta.singleInstall` builder with the checked
`StateRelAt.merge` result; its live-record premise is derived by
`PhysicalMergeEvidence.of_sources`. `PeritextSided.productionCertificate` now
exports `interactionWF`, `interactionRefines`, and `interactionQueries`, so the
finite-trace and retained-version query theorems are public rather than only
ledger-internal. The repository checker requires these declarations.

### 7C. Replace the historical framework trees with one production `Sal/MRDTs` — paper gate

The dependency audit has established the target boundary: raw MRDT semantics
is unconditioned; datatype implementers supply generation, convergence,
sequential-refinement, and safety certificates, plus an optional state-GC
capability; the framework supplies distributed commit-history GC once. Make
the repository structure match that result instead of retaining successive
framework generations on `main`.

- Preserve the complete current tree on an archival branch or tag before
  deleting historical material. Perform the reconstruction on a dedicated
  refactoring branch; update `main` only after every release gate below passes.
- Rebuild `Sal/MRDTs` as the sole production tree around plain `MRDTSig`.
  Remove signature-level `Inv` and `applicable` from raw configurations,
  `Step3`/`Step3V`, reachability, and initialization.
- Retarget `GenerationContract`, mint-certified execution,
  `SafetyCertificate`, convergence certificates, and sequential refinement to
  the plain signature. Keep explicit bridges where generation history,
  convergence honesty, and sequential history are intentionally different.
- Define a generic optional state-GC interface over a compact representation
  relation, including collection, query preservation, future apply/merge
  simulation, epochs, and virtual-LCA continuation where applicable. Make the
  existing Sided Peritext state-GC and head-only merge results instantiate it.
- Keep distributed commit-history GC datatype-generic and prove its ordinary
  and virtual-LCA composition with an implementer-supplied state-GC
  certificate directly against the no-GC semantics. Do not restore global/STW
  GC as a public architectural layer.
- Migrate only supported, paper-relevant implementations and reusable lemmas:
  bounded counter, queue, MVR, tombstone RGA, EmbedRGA, SidedEmbedRGA/FugueMax,
  the production Peritext variants, and the remaining ledger-backed positive
  datatypes. Classify old `Sal/MRDTs/RGA_Embed` lemmas before deleting that
  tree because current production proofs still import several of them.
- Do not migrate refuted Rehoming RGA or Shesha positives, known-broken
  fixtures, abandoned bottom-up proof routes, exploratory probes, superseded
  global-GC architecture, or generated research artifacts. Preserve them only
  through Git history/the archival branch.
- Delete the old `Sal/MRDTs` and `Sal/ConditionedMRDTs` trees after migration;
  remove compatibility adapters and reject archived-path imports in the
  repository checker. The final `main` must contain one authoritative
  `Sal/MRDTs`, not parallel legacy and next-generation trees.
- Synchronize root documentation, build scripts, theorem manifests, runtime
  links, and the paper repository only after the new Lean endpoints stabilize.

Completion gate: the production certificate ledger and axiom audit pass from
the new tree; ordinary and virtual-LCA distributed/history-GC plus Sided
Peritext state-GC composition remain checked; required JavaScript tests and
benchmark schemas pass; paper-facing manifests resolve no archived paths; and
`main` contains only the current supported framework and evaluation artifacts.

### 8. Build the unified paper benchmark harness

- [x] **Implement the proved tombstone RGA in JavaScript as the paper's plain-RGA
  baseline.** Mirror `RGA_WithTombstones/RGA_WithTombstones.lean` and its guarded
  intent layer in `RGA_Intent.lean`: retain the grow-only insertion relation and
  tombstone set, enforce `rgaApplicable` at minting, implement the deterministic
  RGA sequence observation, merge by union, and provide lossless snapshot and
  runtime adapters. Validate the JavaScript model against independently pinned
  Lean SPOTs, including missing-anchor, remove-before-add, and reused-timestamp
  failures, then add randomized lockstep tests against EmbedRGA under the
  hypotheses of `rga_read_eq_embed_read`. Add `plain-rga` to the benchmark
  harness so the paper reports the three proved designs separately: explicit-
  tombstone RGA, tombstone-free EmbedRGA with the same visible semantics, and
  sided EmbedRGA/FugueMax with the L19 non-interleaving guarantee. Report state,
  history, snapshot, apply, merge, recovery, and GC costs without conflating the
  plain RGA's tombstones with commit-history metadata.
  **Implementation increment (2026-08-17):** `runtime/src/datatypes/rga.js`
  now provides the persistent-HAMT RGA, transient batches, linear tree reads,
  guarded minting, union merge, deterministic recovery, and Lean-derived
  PASS/FAIL controls. `peritextRGA`/`PeritextRGA` instantiate the generic
  Peritext layer. `compactiblePeritextRGA` performs certified leaf/ancestor
  collection without rewriting anchors. The focused GC harness is
  `benchmarks/workloads/peritext-kernel-gc.mjs`; its interpretation is now
  consolidated into `benchmarks/results/peritext-paper-repeated.md`. The general harness now
  exposes `rga`, `embed-rga`, and `sided-embed-rga`; three repeated isolated
  runs cover all four real traces, frequent and bulk synchronization, and the
  focused Peritext ancestor-spine comparison. Results and exact ranges are in
  `benchmarks/results/kernel-comparison-repeated.{json,md}`. The packed RGA continuation snapshot uses
  delta-coded ids, parent distances, UTF-8 payloads, and tombstones; corruption,
  backward-decoding, and round-trip gates pass. At 21,200 Peritext operations,
  EmbedRGA with both GCs is 3.3 times smaller than RGA because it removes all
  6,000 deleted spine identifiers. Native shared-prefix depth accounting,
  inverse epoch translation, and lossless content fingerprinting reduce state
  GC from 8.36 seconds to a 32.8 ms median (32.4--33.1 ms). A stronger
  60,000-operation stress run now completes under the same 4 GB limit in 87.6
  ms instead of exhausting the heap. The repeated aggregate and report have
  been regenerated after this optimization.

- **Highest-priority runtime prerequisite: implement sided EmbedRGA under the
  plain Fugue generation policy as an experimental kernel, then measure it
  before promotion.** Keep the shipped one-sided EmbedRGA as the default while
  implementing the L/R coordinate encoding and Fugue
  side-selection rule in both the absolute and prefix-shared JavaScript
  representations. Add an experimental Peritext configuration using the same
  sided kernel. Preserve the one-sided implementation as the default,
  benchmark baseline, and differential oracle. Before any default switch, run
  the L1--L27 directed
  controls (especially L19), runtime convergence and offline/multi-epoch GC
  suites, Peritext render/marks-GC suites, snapshot recovery, and the full
  benchmark matrix. Report coordinate bytes, retained bytes, apply/sync/save/
  recovery time, policy-summary bytes, and GC cost against the one-sided
  baseline to test the claim that reusing the framing bit adds no material
  end-to-end overhead. Promote the sided kernel only after every correctness
  gate passes and the measured overhead is acceptable; otherwise keep it
  experimental and report the trade-off. Do not
  port FugueMax into the production path in this task: its right-origin tag
  costs $\Theta(|\text{successor key}|)$ per contested R entry and has no
  JavaScript cost evidence yet.
  The migration must preserve the proved minting semantics: plain Fugue chooses
  a side from the full policy tree, including deleted nodes. The current
  JavaScript operation carries only `anchorId`, and the live-only EmbedRGA state
  discards a deleted leaf, so delivery cannot reconstruct that choice. Extend
  the issuer state with an explicit GC-able Fugue policy summary and put the
  chosen `(side,parent)` in the immutable operation. Prove or validate that
  collecting this summary preserves every future mint decision before enabling
  commit-history GC. A visible-successor or always-left heuristic is not an
  implementation of the verified policy and must remain a negative control.
  **Proof status:** `SidedRGA_FuguePolicyGC.lean` refutes live-only and stable
  dead-leaf erasure, proves the exact finite observation consumed at each live
  gap, and proves delete-transition congruence. The executable compact model
  agrees with the full policy on true-LCA fork/join tests. Before JavaScript
  migration, use the now-checked non-root and root
  `succOf`-argmax-to-immediate-`schainBefore` bridges close the post-insert
  merge congruence; both insert successor equations
  (`post.succ[a] = x`, `post.succ[x] = old.succ[a]`), fresh-chain lookup,
  post-insert anchor `hasR` bit, and delete transition are already proved.
  The compact `mergeLiveGap` operator and observational optional-gap merge are
  checked. `mergeRetainedGap_observation_exact` proves the generic theorem,
  and `mergeRetainedGap_observation_reachable` discharges Fugue geometry and
  chain provenance for reachable replica syncs (taking the ordinary `SWf`
  certificates for the two branch enumerations and their union). The
  exact `MergeSuccLaw` is now refuted as unnecessarily strong: absent-branch
  concurrency can change an unused successor while `hasR = false`. The proved
  theorem instead compares only the mint observation and requires successor
  agreement only when merged `hasR = true`. The formal
  interface now uses `Option LiveGap`: an absent branch anchor contributes
  `none`, and merged-dead anchors are pruned. The randomized check remains a
  refutation oracle, not the proof.
  **Implementation status (2026-08-17):** the experimental absolute and
  prefix-shared JavaScript kernels now freeze `(side,parent)` evidence in
  each insert, retain the GC-able live-gap/chain policy summary, and plug into
  both replica runtimes and an explicit experimental Peritext configuration.
  The production one-sided exports remain unchanged. Directed deleted-successor,
  fork/join representation-equivalence, prepared-batch, and Peritext controls
  pass. The executable JavaScript kernel is now lockstep with the full-policy
  Fugue oracle on every consolidated sequential and two-branch merge fixture;
  L19 is pinned to `[50,30,10,61,41,21,1]`. Lossless candidate snapshots and
  the `sal-sided`/`sal-sided-shared` benchmark adapters have landed, and the
  complete 158-test runtime suite passes. Profiling removed two accidental
  quadratic costs: full chains are no longer copied/compared in every insert,
  and merge now delta-updates the persistent policy maps. On one non-reportable
  canary the shared candidate improved from 12.9 s to about 55--58 ms for a
  26,078-op trace (current shared: about 22 ms), and from 4--6 ms to about
  0.50 ms median sync (current shared: about 0.23 ms). The operation freezes
  `(side,parent)`; the deleted parent's chain is retained in the causal parent
  state and must be protected by the policy-summary GC. Do not promote from
  these canaries. A lossless binary parent-link snapshot now serializes only
  live records, live ancestry, and current gap successors. On the same trace
  it reduced 1.2 MB of provisional JSON to about 306 KB and restored median
  load to about 18 ms (current shared run codec: 59 KB and about 16 ms). The
  remaining structure was compressed without deleting evidence: most
  successors are reconstructed from the retained policy tree, while a sparse
  exception bitset preserves exact observed successors, node parent exceptions and sides are
  bit-packed, and live membership/text-length exceptions are sidecars over the
  node table. The corrected unified snapshot is 63.1 KB versus 59.1 KB for the
  current shared run codec on this trace. Codec profiling removed repeated ancestry walks, HAMT lookups, ASCII
  encoder calls, and a redundant production-time successor validation (the
  validation remains executable in tests); decoded snapshots cache their
  verified policy order. Save/load are now about 20.6/17.9 ms versus
  15.8/15.7 ms for the current shared codec: roughly 30%/14% overhead, down
  from 8x/1.8x. A separate one-HAMT candidate now co-locates live content,
  chain provenance, and gap state. In a first canary it reduces the sided
  trace from about 56 ms to 34 ms, median sync from about 0.49 ms to 0.34 ms,
  and retained heap from about 12.4 MB to 7.5 MB; plain shared remains about
  22 ms, 0.23 ms, and 5.1 MB. Its snapshot bytes are identical (60.4 KB).
  Zero-copy unified encoding plus a shared parser with a direct one-HAMT build
  removes the split-state conversion: save/load are now about 21.4/18.0 ms,
  essentially matching the optimized split-sided codec and close to plain
  shared's 15.8/15.7 ms. Keep the split-map kernel as the differential oracle.
  The one-HAMT kernel is now exported explicitly as
  `sidedEmbedRGAReleaseCandidate`, with `sidedPeritextReleaseCandidate` using
  it. Forty deterministic randomized
  80-step fork/join trials stay read-lockstep with the split oracle and include
  snapshot recovery. Certified policy GC now requires settled insertion and
  deletion evidence, preserves exact live gaps and their ancestor closure, and
  declares its retained coordinate frame to be identity-translated. Directed
  tests cover refusal without frontier evidence, state recovery, and a returning
  old-epoch replica that mints offline and converges after compaction. The full
  165-test runtime suite passes. The public `peritext` export now uses the
  LiveGap-sided kernel; `peritextEmbedRGA` names the one-sided EmbedRGA variant
  used by differential tests and the coordinate-renumbering compactor. Use the
  paper-facing names `PeritextRGA`, `PeritextEmbedRGA`, and
  `PeritextSidedEmbedRGA`; never classify a correct variant by calling it
  "legacy." Finish the L23--L27 gates and run repeated isolated benchmarks
  before removing the release-candidate aliases.
  **LiveGap representation completed 2026-08-17.** The first one-HAMT policy
  state retained identity-bearing records along every live ancestor spine.
  `liveGapSidedEmbedRGA.js` now implements the proved generation-time
  observation instead: one `LiveGap` for root and each retained anchor, plus
  anonymous shared chain nodes. Directed L1--L27 fixtures (including L19),
  1,200 randomized mint/read steps against the full-policy oracle, fork/join,
  continuation, mark-boundary retention, and recovery pass. On the repeated
  21,200-operation spine, both GCs remove all 6,000 deleted identity records;
  state GC is 32.1 ms and the snapshot is 80,965 bytes. The stronger
  60,000-operation scale check takes 88.7 ms and produces 223,195 bytes.
- Extend `benchmarks/run.mjs` into one reproducible entry point for the
  plain-text and Peritext suites. Run every job in an isolated process with
  fixed seeds. Support `--quick`, `--full`, and `--only`, record the machine,
  runtime, dependency versions, configuration, seed, and workload parameters,
  and exit nonzero when a correctness or convergence gate fails.
- Emit raw per-run JSON plus normalized plotting inputs:
  `results/raw/*.json`, `results/tables/*.csv`, `results/summary.json`, and a
  generated `results/summary.md`. Keep benchmark implementation and raw data
  in this repository. Keep paper-specific figure selection and prose in
  `Sal_paper`.
- Extend the existing cross-system plain-text suite over the four real editing
  traces, frequent sync, bulk sync, delete-heavy churn, delayed/offline peers,
  and empty-document convergence. Compare Sal EmbedRGA with Yjs, Automerge,
  Loro, and list-positions. Use Sal with both GCs as the headline and run the
  following ablations: no GC, commit-history GC only, state GC only, both GCs,
  and both GCs with delayed acknowledgements.
- Build the Peritext suite with real text traces plus formatting, concurrent
  text/mark editing, repeated mark add/remove, marked delete churn, offline
  catch-up, fully deleted documents, and long-running multi-epoch editing.
  Compare Sal Peritext with Yjs rich text and with Automerge/Loro rich text only
  where their observable semantics can be stated comparably. Run Sal
  ablations for no GC, text-state GC, text+mark-state GC, history GC, full GC,
  and delayed acknowledgements.
- Measure apply/format latency, sync latency and bytes, GC pause and amortized
  overhead, resident and durable bytes, commit count, retained tombstones/mark
  records/coordinate symbols, save/load time, late-bootstrap cost, and recovery
  cost. Gate every result on final text/render correctness and intra-system
  convergence; label semantically incomparable cells instead of coercing them
  into a ranking.
- Preserve `npm run bench:empty-gc` as the small GC sanity benchmark, and make
  the intended top-level interface:
  `npm run bench:quick`, `npm run bench:full`, and `npm run summarize`.

  **Plain-text harness increment completed 2026-08-15.** The schema-versioned
  result contract, isolated `plain-gc` worker, five production
  `DistributedReplica` GC configurations, normalized JSON/CSV, generated
  Markdown table, and npm entry points are implemented. The quick `freq`
  sweep passes every convergence/evidence gate. It also exposed and corrected
  an evaluation-order bug: prematurely running commit GC truncates causal
  ancestry used by the later state-GC certificate. The production both-GC
  configuration therefore compacts state at the settled cut before peers
  acknowledge and history is pruned. Current quick measurements retain 3,061
  commits with no GC, 52 with history GC, 3,062 with state GC, and one epoch
  base with both GCs; state GC reduces the durable state from 159,068 to
  59,172 bytes. The delayed-ack row records 3,062 commits while blocked and
  one after acknowledgement. Remaining work: migrate every legacy
  cross-system result to the raw schema, run the bulk/full sweep, and add the
  Peritext workloads and semantically compatible rich-text adapters.

  **Cross-system schema migration completed 2026-08-15.** Sequential trace,
  concurrent sync, and delete-churn workers for Sal, Yjs, Automerge, Loro, and
  list-positions now emit the same schema-v1 envelope while retaining their
  detailed legacy payload for audit. `npm run bench:quick` produces and
  validates 20 isolated raw records, a combined `results/summary.json`,
  `results/tables/results.csv`, the GC-only CSV, and the generated Markdown
  matrix. All semantic gates pass. The long bulk/four-trace `bench:full` run is
  now complete: 45 isolated schema-v1 records pass every semantic gate and the
  normalized artifacts cover all four traces, both concurrent presets, churn,
  and both Sal GC presets. The current full matrix runs each job once (while
  reporting within-job operation quantiles). Before freezing paper figures,
  add independent process repetitions and confidence intervals; do not present
  this single full sweep as a statistical distribution across runs.

  **Peritext workload design and Sal matrix completed 2026-08-15.**
  `benchmarks/PERITEXT_WORKLOADS.md` defines the complete-render observable,
  separates the cross-system stable-endpoint core from Peritext-specific
  gravity/rehoming semantics, specifies and implements seven deterministic
  workload families, six Sal ablations, metrics, and semantic gates. Directed
  Python-derived gravity and dead-anchor fixtures run before timing, and a
  differential digest gate requires every Sal GC ablation to produce the same
  render. All 42 quick-matrix rows pass. Full
  state GC reduces the sample from 604 shadow records / 293 deleted IDs / 498
  mark records / 38,625 coordinate symbols to 472 / 161 / 496 / 9,074 while
  preserving the render; full state plus history GC reduces 1,431 commits to
  one epoch base. The empty workload reaches a 9-byte state with no characters,
  anchors, deleted IDs, marks, or coordinate symbols under full state GC. The
  multi-epoch workload performs three real compactions and advances both
  acknowledged replicas together at epoch boundaries; pruning only one replica
  is intentionally invalid because subsequent deltas cease to be
  ancestor-closed. The full `freq` + `bulk` run is complete: all 84 rows pass
  convergence, snapshot, render-preservation, acknowledgement, and ablation
  gates. In the bulk trace, full GC reduces 26,753 commits to one and durable
  state from 59,118 to 34,831 bytes, but its roughly 1.1-second pause exposes
  the cost of traversing 38.8 million pre-compaction coordinate symbols. Bulk
  mark churn isolates the mark collector: history-only and text-only modes
  retain 4,000 mark records and 237,654 bytes, whereas mark-aware state GC
  retains zero mark records and 512 bytes. External rich-text comparisons are
  no longer a core paper requirement; the paper will use cross-system plain
  text and internal Peritext GC ablations.

  **Benchmark-table audit and implementation priorities (2026-08-15).** The
  current matrix is diagnostic, not yet the paper table. Complete these in
  order:

  1. Extend the shipped run-table binary format to concurrent replica
     snapshots, frontier/history metadata, Peritext text and marks, and wire
     deltas. JSON remains a debugging/reference encoding and must not be Sal's
     headline durable-size result.
  2. Profile and optimize run-table encoding and implement its matching binary
     decoder. Its measured 1.1--1.6 bytes per character is competitive, but
     current 0.2--2.0 second encoding times are not. Target a streaming linear
     traversal without repeated reconstruction or sorting.
  3. Replace in-memory string coordinates with packed, prefix-sharing, or
     run-based coordinates. Serialization alone does not address the bulk
     Peritext trace's 38.8 million coordinate symbols and roughly 1.1-second
     state-GC pause.
  4. Add a compact binary delta protocol using varints, run batching, shared
     agent identifiers, packed coordinates, and compact commit headers. The
     current concurrent payload is 5.9 KB/sync versus Yjs's 1.6 KB in the
     frequent preset, and 118.7 KB versus 15.1 KB in bulk.
  5. Audit why combined GC retains 1,207 commits after the bulk multi-epoch
     workload. Either add the missing final acknowledgement/prune transition or
     expose the causal reason as an explicit metric and paper limitation.
  6. After coordinate compression, evaluate incremental state GC to bound pause
     time rather than relying only on a large stop-the-world traversal.
  7. Rebuild the paper-facing evaluation: remove cross-system JS heap rankings;
     remove the obsolete binary estimate and duplicate Sal rows; group durable
     artifacts by whether they retain live state, tombstones, or full history;
     and either compare equivalent recovery artifacts or omit the cross-system
     load column. Do not rank an in-process Automerge merge against measured
     wire payloads.
  8. Replace the 84-row Peritext listing with plots for durable metadata,
     retained commits, GC pause versus coordinate symbols, mark reclamation,
     and the empty-document floor. Add independent process repetitions and
  confidence intervals before freezing any timing figure.

  **Packed-full-path experiment rejected 2026-08-15.** A dual packed-bit
  coordinate implementation passed 54 merge, compaction, epoch, serialization,
  Peritext, and property tests, but failed the performance gate: appending an
  insertion copied its entire packed path and made long typing traces
  quadratic (the 26k-operation trace exceeded one minute versus roughly 22 ms
  for the string/rope behavior). The experiment was removed. Item 3 must use a
  prefix-sharing node/run representation with a maintained traversal index;
  replacing strings by independently packed full paths is explicitly not an
  acceptable implementation strategy.

  **Prefix-sharing canary completed 2026-08-15.** The isolated
  `sharedEmbedRGA` stores one immutable `{parent, delta}` node per retained
  insertion and canonicalizes independently reconstructed prefixes at merge.
  Five directed/random differential tests match EmbedRGA, including deletion,
  concurrency, independent-prefix merge, and native snapshot round-trip. All
  four real traces pass. Representative results: `friendsforever_flat` applies
  26,078 operations in about 21 ms while retaining 21,806 shared nodes; the
  104,852-character `automerge-paper` result retains 123,537 nodes and its
  continuation-preserving snapshot encodes/decodes in roughly 71/44 ms. The
  initial node-table snapshot is 951,153 bytes (fast but not yet compact), so
  integrate run compression directly over the shared graph before promotion.
  Promotion is also gated on adapting certified compaction/epoch translation:
  post-compaction structural nodes cannot be naively identified only by their
  original insertion ids.

  **Shared-graph run compression completed 2026-08-15.** The encoder contracts
  maximal unique-child delta-1 chains directly over shared nodes and derives
  true insertion ids from `parent.id + delta`, so pre-compaction snapshots need
  no ID sidecar and remain continuation/merge capable after independent decode.
  Six differential tests pass, including future edits and a merge between two
  decoded snapshots. Across the four traces, encode/decode is tens of
  milliseconds rather than seconds. Sizes are 59,063 bytes for 21,362 visible
  characters and 249,972 bytes for 104,852 visible characters. These are larger
  than the old 1.1--1.6 B/character live-only serializer because this snapshot
  also retains the ancestor skeleton and continuation IDs. The remaining
  promotion gate is post-compaction identity: rank renumbering/spine fusion can
  make `parent.id + orderDelta` differ from the birth ID, so the compacted
  format needs an explicit sparse live-ID sidecar or native node-identity
  transport rather than reusing the pre-compaction derivation unsoundly.

  **Certified shared compaction increment completed 2026-08-15.** The shared
  datatype now projects to the existing certified absolute-coordinate
  compactor, rebuilds a prefix-shared result, and switches its run snapshot to
  an explicit gap-coded live-ID mode only when recoding breaks ID derivation.
  Ordinary `DistributedReplica` certified GC, no-GC read equality, peer sync,
  compacted snapshot recovery, and future local insertion pass. A new
  executable negative gate blocks premature promotion: a peer returning with a
  pre-compaction path currently triggers `path divergence` at the common live
  anchor. The representation must separate stable birth identity from the
  epoch-local order path; weakening the divergence check is not acceptable.

  **Birth/order separation completed 2026-08-15.** Live nodes now retain
  stable `(birthId, birthParentId)` provenance independently of their
  epoch-local structural parent/delta. Returning pre-compaction edits rebase by
  birth identity, while disagreement about birth parents remains a hard error.
  The directed test and a 40-trial cross-epoch twin PBT converge with the
  never-compacted control. This closes the earlier `path divergence` gate.
  However, the compatibility compactor is not production-ready: converting
  shared nodes to repeated absolute coordinates and back costs roughly 10.8 s
  on `automerge-paper`, and the naïve explicit post-GC provenance mode is
  662,814 bytes. Implement compaction directly over the shared node graph and
  compress birth provenance per run; do not promote the compatibility adapter
  or quote its timings as the intended design.

  **Direct shared-graph compaction completed 2026-08-15.** Settled-cut
  evidence, sibling rank renumbering, and eligible dead-spine fusion now run
  directly over retained shared nodes; the compatibility implementation
  remains the differential oracle.
  The direct result matches the oracle fingerprint on randomized branching
  state, is now the `DistributedReplica` hook, and passes ordinary certified
  GC plus the 40-trial returning-peer cross-epoch twin test. Real-trace GC drops
  from the compatibility path's roughly 10.8 s to about 102 ms on
  `automerge-paper` (123,537 to 106,400 retained nodes), and takes about 19 ms
  on `friendsforever_flat`. The remaining size issue is provenance encoding:
  the compacted `automerge-paper` continuation snapshot is 662,814 bytes
  because explicit `(birthId,birthParentId)` is currently emitted per live
  node. Compress this provenance by runs before considering promotion.

  **Run-level provenance compression completed 2026-08-15.** Post-compaction
  snapshots now pack four 2-bit provenance tags per byte, derive sequential
  birth IDs and parents implicitly, and emit varints only for exceptions. This
  retains exact birth-parent validation. The compacted `automerge-paper`
  continuation snapshot falls from 662,814 to 283,153 bytes while direct GC
  remains about 94--102 ms; `friendsforever_flat` is 60,847 bytes with roughly
  18 ms GC. All four trace canaries and 42 merge/serialization/GC/epoch tests
  pass. These continuation snapshots intentionally include retained skeleton
  and provenance, unlike the older 1.1--1.6 B/character live-read-only format.
  Next gate before default promotion: exercise the shared datatype in the full
  concurrent/offline/multi-epoch benchmark matrix.

  **Production-shaped shared GC canary completed 2026-08-15.** A reproducible
  `npm run bench:shared-gc` exercises concurrent editing, offline catch-up with
  mandatory pre-evidence refusal, and three real compaction/history-pruning
  epochs. Quick and full presets pass convergence, render preservation, and
  continuation-snapshot recovery. In the full preset, concurrent GC takes
  about 17 ms after 5,001 operations; offline GC takes about 8 ms after evidence
  arrives; the multi-epoch run performs three compactions, prunes 2,444 commit
  nodes, and finishes with converged 7,671-byte snapshots. Keep this as an
  experimental canary until the broader benchmark repetitions are complete;
  the default EmbedRGA is unchanged.

  **Direct guarded/Peritext integration completed 2026-08-15.** The native
  shared-graph compactor now consumes nonempty in-flight paths and frozen
  anchor coordinates without converting the state to absolute coordinates.
  It preserves guarded sibling deltas and blocks fusion at guarded nodes. A
  parameterized Peritext order kernel now exposes `compactibleSharedPeritext`,
  combining direct shared-coordinate GC with Peritext retention roots and A3
  pair-drop. Directed tests cover retained dead mark boundaries, frozen
  insert order, certified empty-document GC, and snapshot recovery; the full
  runtime suite passes 151/151. The implementation prerequisite is closed;
  repeated benchmark runs are now the next promotion gate.

  **Shared benchmark integration and full baseline completed 2026-08-15.**
  `sal-shared` is now a first-class sequential, concurrent, and churn system,
  and both plain-text and Peritext GC matrices sweep `absolute` and `shared`
  representations. Workers use each representation's native serializer,
  recovery path, and compactor; the generated tables label the shared artifact
  as a continuation-capable snapshot rather than comparing it silently with a
  live-read-only encoding. The quick matrix and full matrix pass, including
  all 168 Peritext representation/scenario/GC rows. `summary.json`, CSV tables,
  and `summary.md` were regenerated from the full run. Multi-process repeated
  trials remain the next statistical step; this run is the complete baseline.

  **Three-kernel rich-text matrix completed 2026-08-17.** The version-3
  Peritext harness replaces the obsolete absolute/shared labels with the
  production-facing `RGA`, `EmbedRGA`, and `SidedEmbedRGA` kernels and sweeps
  history-only, state-only, combined, and delayed-evidence GC. All 126 quick
  cells pass render, convergence, snapshot, refusal, and empty-floor gates.
  RGA now applies the same guarded A3 mark-pair collection as the embedded
  kernels. The paper-facing full-scale run should use informative mode samples,
  rather than repeat modes with identical post-evidence states, followed by
  independent repetitions.

  **Evaluation cleanup increment completed 2026-08-15.** Sal now saves and
  recovers from the real run-table binary in the sequential harness, uses it as
  the concurrent primary-save artifact, and measures the same encoding after
  compaction and during churn. JSON and the arithmetic binary estimate were
  removed from generated Sal comparison rows, duplicate shipped/projection
  rows were removed, and cross-system JS heap columns were replaced by an
  artifact-labelled recovery column with an explicit comparability warning.
  Regenerated results expose the next real bottleneck: excellent size
  (1.1--1.6 bytes/character; 9,191 bytes for the 1,804-character concurrent
  session) but slow encoding/recovery caused by reconstructing absolute string
  coordinates. Items 2--6 above remain implementation work.

  **Remaining EmbedRGA--Yjs engineering gaps (2026-08-15).** Preserve these as
  explicit benchmark tasks rather than treating the current baseline as the
  final comparison:

  1. Replace the benchmark/runtime position-to-ID array, whose splice is
     $O(\text{document length})$, with an indexed sequence structure. Report
     adapter cost separately from datatype `apply`; the latter is already
     approximately 0.49 microseconds on `automerge-paper`.
  2. Implement a streaming bulk decoder for both run-table and shared-run
     snapshots. Build HAMT nodes, shared paths, and traversal indexes in bulk
     rather than by repeated persistent updates and global sorting. Re-run the
     recovery comparison against Yjs after this change.
  3. Complete the compact binary sync format from item 4 above and use it for
     both absolute and shared EmbedRGA. The present 4--8x payload gap against
     Yjs measures JSON framing and repeated identifiers, not an established
     lower bound of the datatype.
  4. Profile shared-path sync independently of encoding. Remove avoidable HAMT
     lookups and repeated path/provenance traversal, then repeat the frequent
     and bulk sync experiments. Keep content-addressed commit construction as
     a separately reported runtime cost.
  5. Optimize save construction after the streaming traversal is in place.
     The durable run-table size already matches or beats Yjs update-v2, but its
     save time does not; do not present size parity as implementation parity.
  6. Preserve the artifact distinction in every table: the 1.1--1.6
     byte/character run-table save is a live-read-oriented artifact, whereas
     the 2.4--3.2 byte/character shared snapshot retains continuation
     provenance. Compare either against semantically equivalent artifacts or
     label the retained capabilities explicitly.

  **Binary sync framing and authenticated run batching completed 2026-08-15.** `runtime/src/wire.js`
  now provides a deterministic browser-safe codec with string interning,
  varints, raw content ids, and compact local commit references. Linear authored
  runs omit intermediate ids and parent links; the transmitted endpoint hash
  authenticates the reconstructed chain recursively. `syncPeers`
  crosses the encode/decode boundary before ingest, after which the existing
  state recomputation and content-address check still run. The full 152-test
  runtime suite passes, including a negative test that mutates an implicit
  intermediate commit and is rejected at the run endpoint. The benchmark now
  uses real content ids rather than the shared harness's short local ids.
  Payload falls from 5.9 to 1.0 KB/sync (`freq`) and from 118.7 to 16.0 KB/sync
  (`bulk`), versus Yjs at 1.6 and 15.1 KB. Item 3 is closed for the measured
  plain-text protocol; rich-text payload shapes and independent repetitions
  remain part of the broader evaluation work.

### 9. Finish Tree-RGA observational refinement

- **Paper-critical conditioning audit for RGA and Peritext.** Prove, through
  the public capstones rather than disconnected premises, the complete chain

  `local mint guard -> guarded distributed execution -> RGAHistoryOK/PtHistoryOK
  -> history-conditioned sequential refinement`.

  Check that applicability is evaluated at the issuer's materialized head,
  distributed execution supplies the mint provenance consumed by the
  generation contract, and the final RGA and Peritext refinement theorems use
  the history property derived by that chain rather than accepting an
  unrelated honesty premise. Audit the JavaScript minting API against the same
  guards, or state the implementation-refinement boundary explicitly. Until
  this closes, the paper may say that conditioning packages the missing
  provenance obligation, but must not claim that its end-to-end RGA/Peritext
  result derives sequential intent from local generation rules.

  **Audit finding (2026-08-19).** The desired implication is false for the
  current interface. `Step3.apply` requires a globally fresh timestamp, while
  `eSeqOK`/`sSeqOK` require each local timestamp to exceed every earlier
  insertion timestamp. `eApplicable`/`sApplicable` inspect only datatype
  state and do not enforce that Lamport maximum. The checked counterexample
  `applicable_mints_do_not_imply_eSeqOK` uses two sequential, guard-passing
  root inserts at timestamps 10 then 5. `LinearMintHistory` records the missing
  local-clock discipline; `eSeqOK_of_linearMintHistory` and
  `sSeqOK_of_linearMintHistory` prove that guard plus clock implies the exact
  sequential premises, and the two `*SequentialSound_of_linearMintHistory`
  theorems reach the naive sequence implementations. The JavaScript datatype
  kernels still accept caller-supplied identifiers through raw `commit`, but
  the production runtime now also exposes explicit-slot `generate`,
  `commitGenerated`, and batch variants with a persisted Lamport allocator.
  Remaining closure work is deployment-level collision-free slot allocation;
  name hashing or the browser demo's random salt is not accepted as a proof.
  Expose the local sequential bridge through the public certificate. Do not
  seek one `eSeqOK` list for a concurrent distributed execution: concurrent
  double-delete histories need not admit such a list.

- Generalize beyond root-only insertion.
- Strengthen causal consistency over evolving prefixes.
- Prove `visible_apply_merge` for multi-replica executions.

### 10. Develop a declarative replacement for the absorber clause

- Specify arbitration over surviving conflicts.
- Prove equivalence with `loOn` for conditional-commutativity instances.
- Investigate whether joint absorption requires a strictly more general
  specification.

### 11. Strengthen runtime certification

- Implement and test same-replica crash recovery. Persist the logical replica
  identity, mint counters, causal frontier, roster/evidence state, GC epoch and
  translation metadata, datatype state, and any pending synchronization state
  required by the protocol. After discarding the process, restore the same
  replica, mint collision-free operations, synchronize with a peer that knew
  the pre-crash replica, cross a GC epoch, and prove convergence. Keep the
  current load-and-render benchmark labelled as document-state recovery until
  this gate passes.
- Determine whether EmbedRGA's continuation certificate can be lifted to a
  complete DAG-level `StabilityVC`.
- Formalize divergent-epoch joins and certificate transport.

### 12. Complete repository validation

- Add CI gates for Lean builds, axiom audits, runtime tests, and benchmark
  schema validation.
- Publish stable theorem and benchmark manifests that the paper repository can
  consume without copying the mechanization.

## Dependency summary

- Priority 1 can begin immediately and should not wait for the emulation
  project.
- Priorities 3--5 are one proof project and should be executed in order.
- Priorities 6--10 can proceed independently once ownership is clear.
- Priority 12 follows the substantive Lean and runtime work.

## Completed foundation

The next active item is Priority 7A. The consolidation work underlying this backlog is recorded in
`Sal/ConditionedMRDTs/REFACTOR_ROADMAP.md`. Its checklist is complete. In
particular, the repository now has production `VerifiedMRDT` certificates,
EmbedRGA continuation-aware runtime recoding, a concrete heterogeneous
product, unified ledgers, representation lower bounds, and a retired Shesha
positive capstone whose premise was formally refuted.
