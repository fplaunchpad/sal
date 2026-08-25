# Prioritized remaining work

This is the canonical development task list for Sal. This repository owns
Lean, JavaScript, executable validation, benchmark artifacts, and the two
anonymous long-form working papers under `docs/`.

## 0. Finish the plain-MRDT cutover

- [x] Create `refactor/plain-mrdt-framework` and preserve the previous tree on
  `archive/conditioned-mrdts-2026-08-21`.
- [x] Replace the conditioned signature with plain `MRDTSig`, implementer
  `Issuance`, sequential-specification, and `VerifiedMRDT` interfaces. Keep
  safety and datatype-state GC as separate optional certificates.
- [x] Port ordinary and canonical virtual-LCA semantics and adequacy without
  `LegacyBridge`.
- [x] Port the paper-facing RGA, EmbedRGA, SidedEmbedRGA/FugueMax, Peritext,
  queue, MVR, bounded-counter, counter, and grow-only proof packages.
- [x] Prove distributed commit-history GC and its direct ordinary/virtual
  refinement, without a global/STW intermediate semantics.
- [x] Move live RGA kernels into `Sal/MRDTs/Instances/RGAKernel`; remove the
  historical RGA experiment tree and standalone CRDT case-study artifacts.
- [x] Add a release gate covering the production Lean ledger, forbidden
  historical imports/files, `sorry`/`sorryAx`, and the complete runtime suite.
- [x] Package Sided Peritext state GC as a concrete `StateGCProtocol`, not only
  component lemmas. Its validity relation must cover text retention and
  LiveGap evidence, trimmed deletion evidence, guarded mark-pair removal,
  Lamport-fresh continuations, cross-epoch translation, ordinary merge, and
  virtual-LCA/head-only merge.
- [x] Audit the remaining tracked source/docs against the paper scope. Remove
  historical whiteboards and stale root notes after migrating any genuine open
  task here.
- [x] Run a clean-from-source Lean build, the runtime suite, repository checks,
  and benchmark schema validation. Publish a stable theorem manifest.
- [x] Fast-forward `main` to the verified refactor branch and push it.
- [x] Minimize the paper-facing distributed-GC state. Each replica now stores
  only `{head, commits}`; the fixed roster and partial immutable commit-author
  function are protocol parameters, and frontier evidence is derived.
- [x] Restore the framework and collaborative-editing working papers under
  `docs/`, update their core framework and GC descriptions after the refactor,
  and add an independent two-PDF build check.
- [x] Rewrite both working papers against the current `main` evidence rather
  than preserving the historical monolith. Make paper-level states,
  operational rules, execution diagrams, proof dependencies, and the two-GC
  simulation first-class; gate cited declarations with `PaperLedger.lean` and
  remove the retired shared source.
- [x] Adversarially rewrite the framework paper as the self-contained formal
  submission narrative. State the raw and certified semantics, all
  load-bearing Join/VC premises, the client-facing sequential theorem,
  canonical virtual-LCA rule, distributed history-GC protocol/refinement, and
  datatype-state-GC composition in typeset form. Keep the collaborative-
  editing paper as supporting material rather than a second submission.
- [x] Minimize `MRDTSig` to one ancestor-aware ternary operation named
  `merge`. Remove the independent binary field and compatibility obligation,
  derive the initial-base binary projection only for reused replay code, and
  synchronize Lean, both papers, and the release gate.
- [ ] Add the submission-facing bibliography and related-work comparison after
  the technical narrative stabilizes. Keep citations distinct from the
  machine-checked claim ledger.

## 1. Runtime and evaluation engineering

- [ ] Add same-replica crash recovery. Persist replica identity, Lamport mint
  state, causal frontier, roster evidence, epoch translations, datatype state,
  and pending synchronization state; test recovery across a GC epoch.
- [x] Replace benchmark position-to-ID array splices with a deterministic
  indexed-sequence adapter and report index, datatype, and rebuild costs
  separately while retaining overall wall time as the primary metric.
- [ ] Add streaming bulk decoders/builders for run-table and shared snapshots.
- [ ] Profile and optimize shared-path sync, save construction, and repeated
  HAMT/path traversal.
- [x] Keep EmbedRGA and SidedEmbedRGA as separate state-of-the-art baselines;
  report their storage/intent tradeoff rather than selecting one silently.
- [x] Complete statistically repeated benchmark runs and publish machine-readable
  raw results plus primary tabular summaries: the Sal-versus-external matrix,
  the three verified sequence kernels, and the focused Peritext/two-GC design.

## 2. Follow-on formal work

- [x] **HIGHEST PRIORITY — enforce the verified production boundary.** A raw
  `MRDTSig` remains available for theorem development, SPOTs, and
  countermodels, but no datatype may appear in the production registry unless
  it supplies a `VerifiedMRDT` for that exact signature.
  - [x] add a dependent `PackagedMRDT` type and a production ledger containing
    only such packages;
  - [x] move replay-only/refuted artifacts and interaction SPOTs to a separate
    negative-evidence ledger. Keep the queue/FIFO and MVR/single-register
    counterexamples visible without presenting either datatype as verified;
  - [x] implement a complete add-wins OR-set package with an honest observed
    remove issuance rule, convergence, an independent sequential machine,
    query refinement, and positive/negative issuance SPOTs;
  - [x] either give the FugueMax-specific `FMSig` a non-vacuous public
    sequential certificate or classify it as an internal proof signature and
    make the verified SidedEmbedRGA package the only production entry;
  - [x] require every production JavaScript datatype to have a machine-checked
    Lean package named in a runtime evidence manifest. Record correspondence
    separately as extracted, manually implemented and differentially tested,
    or unvalidated;
  - [x] make the release gate reject raw, replay-only, SPOT, or countermodel
    entries in the production ledger and reject runtime entries with missing
    Lean evidence;
  - [x] synchronize the theorem manifest, README, task status, both working
    papers, and generated PDFs. Remove the stale claim that AegisSheet is
    replay-only.

- [x] **HIGHEST PRIORITY — finish the public sequential-correctness cutover.**
  The replay-only `IsRALinearizable` result reconstructs implementation state;
  the public `IsSpecRALinearizable` result must additionally select an exact,
  `lo`-respecting history accepted by an independent sequential specification,
  relate both states, and agree on every query.
  - [x] replace the staging `Inv`/`Applicable`/`GuardBridge` API with the
    minimal public boundary: `Issuance.CanIssue` constrains origin operation
    creation, while `SequentialSpec.Legal` states acceptable abstract event
    histories without inspecting implementation state;
  - [x] remove arbitrary `GenerationContract.History`; convergence proofs now
    derive datatype-local history invariants directly from `MintHonest`;
  - [x] make `VerifiedMRDT` the strengthened public package and retain the old
    raw-fold result explicitly as internal `ReplayVerifiedMRDT`;
  - [x] remove duplicated ordinary proof fields: ordinary certified execution
    embeds in virtual-LCA execution, so convergence and optional safety store
    only their widened theorem and derive the ordinary theorem;
  - [x] state the strengthened per-version theorem with exact event-set
    membership, respect for `lo`, sequential legality and refinement, and
    explicit query agreement;
  - [x] factor one datatype-specific `SequentialCorrectnessCertificate` so ordinary and
    virtual-LCA executions reuse the same semantic proof;
  - [x] migrate the total grow-only set/map canary and the tombstone RGA;
    RGA's specification state is `List Nat`, deletion is physical and
    idempotent, and `listSpec.Legal` records timestamp/ID honesty plus earlier
    allocation of anchors and targets entirely over the abstract event list;
  - [x] resolve the checked mergeable-queue obstruction: two replicas can
    dequeue the same observed head, leaving the implementation's second
    element while a plain FIFO replay performs two pops. Either add an
    exactly-once dequeue protocol or mark the current queue as not FIFO
    RA-linearizable. The current package is now explicitly named
    `replayVerified`, and `duplicate_dequeue_not_fifo` is the checked negative;
  - [x] migrate the total counters/stores, TreeMove, and BoundedCounter to
    `VerifiedMRDT`. BoundedCounter uses a canonical increments-before-decrements
    witness and a client legality predicate that records the per-replica
    resource bound;
  - [x] classify the current MVR against its ordinary single-value register
    specification: two concurrent writes expose both values, so no state of
    that sequential machine can refine the merge. Keep the raw package named
    `replayVerified` and the obstruction in
    `concurrentState_no_sequential_register`;
  - [x] finish EmbedRGA and SidedEmbedRGA legalization. Their canonical merged
    histories are prefix-legal, including duplicate deletion, and respect the
    explicit semantic dependence policies supplied through `InteractionSpec`.
    The raw-state counterexample remains checked: universal
    `CRDTSig.commutes` over malformed list states is not a sound public
    dependence policy for these representations;
  - [x] migrate or classify every production datatype. EmbedRGA,
    SidedEmbedRGA, Peritext, the three-component Sided Peritext core, and its
    production rendered-query `RichCore` now have `VerifiedMRDT` packages.
    Queue and MVR remain replay-only with checked semantic counterexamples.
    AegisSheet now has a full package using causal-origin legality; the old
    whole-prefix predicate remains as the checked obstruction
    `concurrent_origins_not_guarded_chronological`;
  - [x] keep `SafetyCertificate.Safe` orthogonal to representation relations.
    Datatypes may reuse a proof-local reachable-state lemma when useful, but
    no coupling belongs in `VerifiedMRDT` and no production instance requires
    another public bridge;
  - [x] provide ordinary and virtual-LCA versions of the strengthened theorem;
  - [x] add positive and negative controls showing that origin issuance alone
    does not imply legality of an arbitrary merged witness.
  This is a gating issue for the framework and paper claims. Internal-state
  replay, convergence, or an add/tombstone representation theorem does not
  discharge it.

- [x] **High priority: replace the plain RGA event-store sequential certificate
  with observational refinement to an ordinary sequence.** Use an abstract
  `List` of uniquely identified elements (`List Nat` for the current Nat-only
  model, or `List (Id × Value)` for the generic interface). Its only updates
  are `insertAfter anchor freshId value` and `delete id`; deletion physically
  removes the entry, the distinguished root is not stored, and `read` returns
  the list of values. Keep timestamps, the insertion tree, and tombstones only
  in the RGA implementation and its representation relation. Make the total
  sequential step's invalid branches explicit, then use issuance and causal
  closure to prove the relevant branches unreachable: inserted IDs are fresh,
  insert anchors exist at their origin, and deletion targets were previously
  allocated. Repeated and concurrent deletion is legal and idempotent. Prove that
  every valid RGA execution has an RA-consistent sequential linearization whose
  ordinary-list observation equals the RGA traversal, including a concurrent
  insert whose anchor is deleted (linearize the insert before the concurrent
  delete). Replace the current `RGASeqState { adds, grave }` certificate; merely
  equating add/tombstone membership does not discharge this task.
  Completed by `RGASequential.rga_spec_linearizable` and
  `rga_spec_linearizableV`. The public client spec is `List Nat`; the selected
  witness contains the exact version event set, orders timestamp-sorted
  insertions before idempotent deletions, is prefix-legal, and has the same
  query result as the implementation.

- [ ] **High priority: verify AegisSheet against its published intent matrices.**
  Use Tables 3 and 4 of the PaPoC 2026 paper as the external oracle for all
  pairwise `EditCell`, row/column insert, remove, and move outcomes, both before
  and after local undo. Preserve each matrix cell as a named semantic fixture.
  Specify the range behavior shown in Figure 1 separately: anchored endpoints,
  border and interior deletion, crossing moves, overlap, and recreation. Build
  an independent sequential spreadsheet machine over stable row, column, cell,
  and range identities; then supply generation, convergence, safety, and
  sequential-refinement certificates for the compositional implementation.
  Audit whether purging can be a silent state-GC operation under an explicit
  stable-cut/authority precondition. The checked late-revival counterexample
  shows that the published behavior instead needs a semantic purge marker or a
  no-revival protocol: the Scala method exposes neither the paper's cutoff date
  nor its privileged-client premise. Audit the implementation against the
  paper before adopting it as the formal algorithm, including the custom
  `ReplicatedUniqueList` filter and undo closures. Formula evaluation is outside
  the published model; only stable formula-reference ranges are in scope. Use
  the resulting datatype-local algebraic obligations as the next SMT leaf-VC
  case study. Finally, implement a differential runtime and measure state GC
  after certified-stable row/column deletion.
  - [x] Encode all 16 merge and 16 selective-undo matrix entries as named
    external fixtures.
  - [x] Build the causally annotated stable-ID MRDT; prove ordinary and
    virtual-LCA convergence, guarded issuance, safety, and refinement to the
    independent incremental spreadsheet machine. Strict Lamport chronology
    makes the finite event set's sequential enumeration unique. The checked
    `concurrent_origins_not_guarded_chronological` example proves why it cannot
    be promoted with the old whole-prefix guard: two independent operations are
    valid at their empty origins, but whichever is second in a serialization
    did not observe the first;
  - [x] Define AegisSheet merged-history legality over each event's encoded
    causal origin view, extend the incremental materialization and observation
    theorems to that legality, and package the result as `VerifiedMRDT`.
    Every certified ordinary or virtual-LCA version has a deterministic
    timestamp-canonical witness. Each operation carries an applicable causal
    origin contained in its serialization prefix; the witness exactly
    materializes and observes the replicated state. Positive concurrent-origin
    and negative unavailable-origin controls prevent vacuous legalization;
  - [x] **High priority: audit and minimize the AegisSheet sequential
    specification.** The current incremental machine removes event-log replay,
    but its state still contains causal timestamps, observed-remove tokens,
    concurrent versions, and purge markers. Do not call this a conventional
    sequential spreadsheet without further evidence. Define the smallest
    plausible client-level state over ordered rows and columns, visible cells,
    anchored ranges, and explicit selective-undo information. For each current
    metadata field, search for two reachable states with the same client view
    and a legal continuation that distinguishes them. Preserve minimized
    distinguishing continuations as negative SPOTs; add positive controls for
    metadata that can be quotiented away. Either prove refinement to the
    reduced client ADT and replace the public `SequentialSpec`, or prove which
    hidden history is semantically necessary and state that boundary explicitly
    in the theorem and paper. Validate the chosen abstract operations against
    the published AegisSheet matrices rather than against the Lean
    materialization function alone. The audit refutes a `View`-only state with
    three reachable, causal-origin-legal same-view pairs. One common legal
    continuation distinguishes observed-remove axis tokens; two more
    distinguish active cell and range write identities. Thus these fields are
    semantic history required by persistent conflict and selective overwrite,
    not replay caches. Structural inspection classifies
    `knownRows`/`knownColumns` as finite-domain indexes and purge
    acknowledgements plus the covered-entry map as GC protocol evidence;
    obsolete position candidates remain a possible representation quotient.
    This audit establishes the semantic lower bound, not a globally minimal
    encoding. The public theorem therefore remains refinement to a causally aware
    incremental spreadsheet machine, not a conventional visible-sheet ADT.
    `AegisSheetAbstraction.no_view_only_step` records the boundary;
  - [x] Check the nontrivial merge, undo, and range scenarios with positive and
    negative SPOTs.
  - [x] Refute naive local purge as silent state GC with a kernel-checked late
    revival counterexample.
  - [x] Add an incremental in-place spreadsheet machine with observed-remove
    axis tokens, timestamped positions, active cell versions, and range
    versions; validate it on the directed matrix scenarios.
  - [x] Prove the general guarded-history refinement from the replicated model
    to that in-place machine, replacing the packaged event-list reference.
    The public relation now includes exact equality with a declarative cache
    materialization. Its inductive proof preserves metadata validity,
    timestamp uniqueness, and seen-frontier validity across every guarded
    minted step, including semantic purge markers.
  - [x] Prove guarded-history observational refinement:
    `Sequential.view (Sequential.run ops) = view ops.toFinset`. Exact cache
    materialization did not imply this equation by itself. The checked proof
    establishes row/column token, latest-position, active-cell/purge, and
    range-value correspondence, derives cell and purge provenance from every
    guarded history, and includes observation equality in the public state
    relation.
  - [x] Model an explicit semantic purge marker with an authority/required-roster
    guard and compact timestamp-to-coordinate entries; prove that collection
    preserves causal timestamps and is idempotent, and check late restoration,
    stale payload re-delivery, and fresh post-cutoff writes.
  - [x] Prove the general guarded-update/compatible-merge representation
    theorem and package the payload collector as a `StateGCCertificate`.
    Query preservation covers axes, positions, cells, and ranges; generic
    authored frontier evidence derives the purge marker's roster
    acknowledgements.
  - [x] Audit Bismuth commit `dd4c614` against the formal policy and paper.
    The executable regressions refute equivalence: numeric-index move undo
    violates Table 4 for move/insert and move/move; range undo restores the
    wrong stable endpoints after insertion; crossed ranges can leave a live
    range ID and make `listRanges()` throw. Merge-law and purge controls pass
    on the recorded scope. See `docs/aegissheet-scala-audit.md`.
  - [ ] Repair or replace the Scala runtime using stable-ID/anchor undo and
    axis-specific post-move range validation. Re-run the permanent regressions,
    then implement benchmarks only after the differential gate passes.
- [x] Add a canonical-replay MRDT model of the TPDS replicated tree move:
  finite move-event state, union merge, timestamp replay, generation guard,
  cycle safety, convergence, direct chronological tree refinement, and SPOTs.
- [x] Prove that timestamp-ordered undo/insert/redo refines the canonical tree
  renderer.
- [x] Instantiate TreeMove stable-prefix log GC and quiescent trash-subtree GC,
  package them as a `StateGCProtocol`, and compose that protocol with the
  framework's asynchronous distributed commit-history collector.
- [ ] Optimize TreeMove trash collection before the pending suffix becomes
  empty. This is not required for correctness: the current collector waits
  until the full local event log is stable before pruning the hidden subtree.
- [ ] Implement and benchmark a standalone JavaScript TreeMove runtime that
  mirrors the verified Lean model. Include canonical replay and incremental
  undo/redo, distributed commit-history GC, stable-prefix log GC, quiescent
  trash-subtree GC, crash recovery, differential tests against the Lean-facing
  semantic fixtures, and empty-tree metadata measurements.
- [ ] Build a verified structured-editor composition after the standalone
  TreeMove runtime is implemented and measured: use TreeMove with
  SidedEmbedRGA/FugueMax sibling positions to organize blocks, and a map from
  block IDs to Peritext documents for rich-text contents. Prove the
  cross-component generation policy, hierarchy and ordering safety,
  move/edit/delete concurrency behavior, sequential refinement to a mutable
  block editor, composition of commit and datatype-state GC, and constant
  metadata after a fully stable empty-document collection.
- [ ] Generalize the Tree-RGA observational refinement beyond root-only
  insertion and prove evolving-prefix/multi-replica visibility results.
- [x] **HIGH PRIORITY — consolidate arbitration and remove the
  `no_rc_chain` artifact from the MRDT interface.** `InteractionSpec` now
  supplies the public semantic conflict policy, while concrete-state
  commutation and `UpdateVCs.no_rc_chain` remain confined to one internal
  replay construction. `CRDTSig` no longer stores a resolver.
  - [x] Build minimal machine-checked LWW-register and add-wins OR-set SPOTs against
    independent sequential specifications. The LWW policy admits timestamp
    chains and the checked three-write instance refutes `no_rc_chain`. The
    OR-set SPOT distinguishes
    commuting representation effectors from conflicting abstract
    `add`/`remove` operations and recover add-wins by ordering a concurrent
    remove before the add.
  - [x] Validate and freeze a single implementer-facing interaction API,
    provisionally `independent | conflict concurrentOrder`, with a swap
    coherence law. Causal conflicts follow visibility; the supplied direction
    is used only for concurrent conflicts.
  - [x] Define the framework's set-relative ordering constraints from
    visibility and that interaction policy. State precisely how the new order
    relates to `loOn` and whether the absorber clause is derivable, retained as
    one internal proof technique, or eliminated.
  - [x] Do not add `no_rc_chain` or a blanket public acyclicity VC. Use the
    exact legalization witness to certify that client-facing constraints are
    satisfiable. Let each `ConvergenceCertificate` establish its internal
    replay order by an appropriate proof: a well-founded rank, the existing
    set-relative theorem, or a direct witness construction.
  - [x] Remove `rc` from the executable `CRDTSig`. If the existing absorber
    metatheory remains useful, parameterize it by an internal replay-order
    policy instead of storing that policy in every datatype signature.
  - [x] Migrate every production `VerifiedMRDT`, delete superseded compatibility
    definitions and vacuous `rc := Either` proofs, and run the clean Lean,
    theorem-ledger, repository, and runtime release gates.
  - [x] Update both working papers and theorem manifests. Present the broken
    Neem/global-arbitration route as motivation, distinguish representation
    convergence from sequential arbitration, and use LWW and OR-set as the
    small explanatory examples before the richer RGA/Peritext developments.
- [ ] Extend reusable state-GC certificates to other production datatypes where
  the state contains reclaimable metadata.

## 3. Repository automation

- [x] Add hosted CI for the release gate. Add benchmark schema checks to that
  workflow when the repeated-result publication format is frozen.
- [ ] Export stable theorem/runtime/benchmark manifests for downstream paper
  builds without duplicating development tasks.
