# Prioritized Remaining Work

This is the canonical development backlog for Sal. It owns Lean metatheory,
datatype proofs, runtime implementation, executable validation, benchmarks,
and repository CI. The sibling `Sal_paper` repository owns manuscript prose,
structure, figures, bibliography, paper builds, and paper-specific claim
audits. Paper plans may cite tasks here as evidence dependencies, but must not
duplicate them as paper-owned development tasks. Completed subsystem roadmaps
are historical evidence; this file determines what development comes next.

## Priority order

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
  7. Keep negative controls explicit: rehoming RGA must remain marked
     sequential-semantics-refuted, BudgetCart remains gated until its witness
     transfer is solved, and Shesha's refuted premise must not be promoted by
     the new packaging.
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
  sequence model independently of the refuted rehoming/Shesha line.

  MVR is now positive through `mvrApplicable`, `MVRMintHistory`,
  `mvrGeneration`, and `mvrUnified`. Tombstoned Peritext is positive through
  `ptApplicable`, `PtHistoryOK`, `ptSequentialSound`, and `ptUnified`; its
  folded state does not retain remove-operation timestamps, so the public
  guard claims target liveness but not freshness against earlier removes.
  EWFlag is positive through the doctrine-faithful `ewflagUnifiedF`, which
  consumes `JoinLemma3F` directly rather than assuming the Gate-G1 converse.
  The anchor/freshness/grave cluster in Shesha remains negative evidence
  because its Join/presplice premises are checked refutations.

  **Priority 7 completed 2026-08-14.** Every named positive production
  datatype is covered by a public checked package. Rehoming RGA remains
  sequential-semantics-refuted, BudgetCart remains gated on witness transfer,
  and Shesha remains premise-refuted; none is promoted by the ledger/checker.

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

### 8. Build the unified paper benchmark harness

- **Highest-priority runtime prerequisite: migrate the shipped sequence
  kernel from one-sided EmbedRGA to sided EmbedRGA under the plain Fugue
  generation policy.** Implement the L/R coordinate encoding and Fugue
  side-selection rule in both the absolute and prefix-shared JavaScript
  representations. Make Peritext use the same sided kernel. Preserve the
  one-sided implementation as an explicit benchmark ablation and differential
  oracle, not as the default. Before promotion, run the L1--L27 directed
  controls (especially L19), runtime convergence and offline/multi-epoch GC
  suites, Peritext render/marks-GC suites, snapshot recovery, and the full
  benchmark matrix. Report coordinate bytes, retained bytes, apply/sync/save/
  recovery time, and GC cost against the one-sided baseline to test the claim
  that reusing the framing bit adds no material end-to-end overhead. Do not
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

- Generalize beyond root-only insertion.
- Strengthen causal consistency over evolving prefixes.
- Prove `visible_apply_merge` for multi-replica executions.

### 10. Develop a declarative replacement for the absorber clause

- Specify arbitration over surviving conflicts.
- Prove equivalence with `loOn` for conditional-commutativity instances.
- Investigate whether joint absorption requires a strictly more general
  specification.

### 11. Strengthen runtime certification

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

The next active item is Priority 8. The consolidation work underlying this backlog is recorded in
`Sal/ConditionedMRDTs/REFACTOR_ROADMAP.md`. Its checklist is complete. In
particular, the repository now has production `VerifiedMRDT` certificates,
EmbedRGA continuation-aware runtime recoding, a concrete heterogeneous
product, unified ledgers, representation lower bounds, and a retired Shesha
positive capstone whose premise was formally refuted.
