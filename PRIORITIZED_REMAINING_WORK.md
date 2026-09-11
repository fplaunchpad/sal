# Prioritized remaining work

This is the canonical development task list for Sal. This repository owns
Lean, JavaScript, executable validation, benchmark artifacts, and the two
anonymous long-form working papers under `docs/`.

## 0. Finish the plain-MRDT cutover

- [x] Create `refactor/plain-mrdt-framework` and preserve the previous tree on
  `archive/conditioned-mrdts-2026-08-21`.
- [x] Replace the conditioned signature with plain `MRDTSig`, implementer
  `Issuance`, sequential-specification, and `VerifiedMRDT` interfaces. Keep
  safety separate from the client-correctness package. Track datatype-state GC
  for every production entry in a separate typed coverage registry.
- [x] Port ordinary and canonical virtual-merge-base semantics and adequacy without
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
  virtual-merge-base/head-only merge.
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
  canonical virtual-merge-base rule, distributed history-GC protocol/refinement, and
  datatype-state-GC composition in typeset form. Keep the collaborative-
  editing paper as supporting material rather than a second submission.
- [x] Minimize `MRDTSig` to one ancestor-aware ternary operation named
  `merge`. Remove the independent binary field and compatibility obligation,
  keep the update/replay projection merge-free, isolate the initial-base
  binary slice behind an explicitly historical capability, and synchronize
  Lean, both papers, and the release gate.
- [x] Create a separate bottom-up **Formal Semantics and Theorem Reference**
  for the complete public framework theory, written in semantic dependency
  order rather than Lean file order.
  - [x] First milestone: typeset the primitive types, `UpdateSig`, `MRDTSig`,
    events, configurations, and the explicitly typed fork, apply, merge, and
    query rules as a self-contained operational-semantics chapter.
  - [x] Continue with replay contexts, `loOn`, canonical states,
    `CanonicalConfig`, Join and replay adequacy; then issuance, interaction
    ordering, `IsSpecLinearizable`, virtual merge bases, and the two GC refinements.
  - [x] Give every definition and principal theorem explicit types, its exact
    Lean declaration name, and a source link. Omit proof-local plumbing from
    the main line and isolate historical binary VCs and countermodels in an
    appendix.
  - [x] Add a Lean ledger and PDF build gate so the reference remains
    synchronized with the mechanized development.
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

- [ ] **HIGHEST PRIORITY — audit semantic-contract completeness across all
  RDTs.** The Queue review exposed a gap between distributed implementation
  replay plus sequential-only refinement and the intended concurrent client
  contract. Do not infer that other implementations are broken, or that a
  `VerifiedMRDT` inhabitant alone validates the chosen specification. Audit
  every production entry (currently 21), its relevant variants, and the
  replay-only/internal packages before declaring this class of gap closed.
  Use the formal-writing audit against theorem statements, not just names.
  - [x] Add an exact-public-certificate CI gate: independent component
    selections in `public-contracts.json`, full typed-registry equality,
    ordinary/virtual public conclusions, axiom audit, exact runtime mappings,
    and negative controls for partial packages and mismatched components.
    This checks proof connections, not human approval or completion of the
    semantic audit below.
  - [ ] For each datatype, record the independently stated client contract:
    ordinary sequential behavior, intended concurrent outcomes, observable
    operation results and queries, issuance, and the semantic `rc`. Distinguish
    element identity from value and origin visibility from replay position.
    The `SequentialSpec` itself may be the reviewed artifact, with issuance
    and `rc` supplying its concurrent interpretation; do not introduce a
    redundant specification layer. Review it before adapting it to the
    implementation's proofs.
  - [ ] Trace every promised property to a public theorem conclusion for all
    certified executions, ordinary and virtual where supported. Check for
    properties merely assumed as history honesty or legality, proved only
    for linear mint histories, or lost when stronger issuance facts are
    weakened for a replay proof. Separate implementation-state reconstruction
    from client correctness; separate per-version observations from claims
    about operation responses or whole execution histories.
  - [ ] Audit specification independence and non-vacuity: implementation-
    mirroring states or transitions, unjustified trivial legality, missing
    observations, incompatible proof policies, and separately valid results
    that lack a proved composition. Total legality is acceptable only when
    the rest of the contract actually enforces the intended behavior.
  - [ ] Add named positive and negative controls for each concurrency
    exception, plus mutation tests demonstrating that representative wrong
    implementations or weakened premises are rejected by the intended
    contract. Test reachable concurrent traces, not just selected folds;
    do not promote failure of particular replay orders to nonexistence of
    every allowed witness.
  - [x] **Queue first:** state FIFO independently of `qUpdate`, including
    head selection at the issuer's visible queue, timestamp resolution of
    concurrent enqueues, and permission for distinct dequeues to name the
    same element only when concurrent. Prove correct surviving contents,
    order, and relevant observations, and prove reduction to ordinary FIFO
    in sequential executions. Preserve the existing sequential `tail`
    theorem as a special case; arbitrary named deletion alone is not FIFO.
    Concurrent duplicate dequeues are intended, not a bug to suppress with
    an exactly-once protocol. State explicitly how unseen concurrent
    enqueues affect the FIFO obligation rather than silently assuming a
    globally visible queue.
    - [x] Prove same-target dequeues are visibility-incomparable, exact
      surviving identities for every certified version, and ordinary FIFO
      behavior of the candidate abstract machine on linear histories.
      Define head-only abstract dequeue with idempotent repeated targets;
      reject live non-head and never-enqueued targets. Check the grouped
      witness on 1,500 seeded and 6,561 exhaustive small fork/merge cases,
      including an extra-pop mutation control. See
      `docs/queue-contract-repair.md` for exact scope and residuals.
    - [x] Prove the general legal `loOn`-respecting grouped witness from
      issuance, connect it to the public sequential certificate, and pass
      the exact-contract production gate. `Queue.verified` is now registered;
      `queue_correct` combines legalization, exact surviving identities,
      timestamp order, and duplicate-target concurrency for the same ordinary
      or virtual execution. The gate requires this combined contract and
      `client_linear_fifo`; tests exercise the proved `legalize` construction.
      The abstract state is a list, with no retained tombstones. An unseen
      concurrent enqueue cannot invalidate a head selection at its issuer;
      surviving enqueues are timestamp ordered after integration.
  - [x] **MVR, after Queue:** replace the unsuitable single-value sequential
    target with the intended multi-value contract: concurrent writes survive
    together, a write supersedes exactly the writes it observed, and linear
    executions reduce to an ordinary register. Fix the observable API (the
    current signature exposes internal state), prove the connected public
    certificate, and add it to the exact-contract production gate. Preserve
    the existing single-value counterexample as evidence about the rejected
    specification, not about MVR correctness. Completed by `MVR.verified`,
    `mvr_correct`, and `linear_register`, with the maximal-write and ordinary
    query obligations explicitly enforced by the production gate. The same
    observed-supersession `rc` is used by replay and public correctness.
    See `docs/mvr-contract-repair.md` for proof and test scope. The subsequent
    live-state migration below removes the logs; no independent runtime is claimed.
  - [x] **Retire the tagged observed-remove set.** Remove its paper profile,
    Lean production and collection entries, public contract, and runtime
    release entry. Keep the efficient OR-set as the sole released set.
    Preserve the old Lean model only under `Metatheory/Countermodels` for
    regression controls, and classify its JavaScript module as comparison-only.
    Update registry counts and the paper/profile checks.
  - [x] **Replace grow-only MVR with live tagged values.** `MVRLive` implements
    observed-target removal, singleton issued writes, and ancestor-relative
    merge without a write log or tombstones in its state. The update, shared
    history merge, and chronological-fold representation lemmas are checked;
    the same sequential machine and `rc` are retained. `MVRLiveSPOT` is included
    in the refactor gate. `MVRLive.verified` now closes ordinary and virtual
    execution, including recursive merge bases; `mvr_correct` and
    `linear_register` discharge the required public obligations for that exact
    signature. The production registry, collection classification, and PDF
    now use the compact implementation. A gate mutation rejects substitution
    of the old certificate. See `docs/mvr-live-state.md`.
  - [x] **FugueMax:** complete the client-facing contract and public certificate
    for the actual FugueMax implementation and generation policy, connecting
    its existing replay and maximal-non-interleaving results. The registered
    `ProductionRGA.sided` certificate has a different signature and is not a
    substitute. Do not treat the prior classification of `FMSig` as internal
    as completion of FugueMax; register the exact completed package and its
    contract when the proof connection is established.
    - [x] Pin the issuance-state mismatch: two `MaxReach` histories have equal
      live coordinate states but different exact generated insertions. The
      weak `fApplicable` guard accepts a prepared operation that one history
      cannot generate at any client position. A state-only predicate cannot
      characterize both sets of allowed operations. See
      `FugueMaxContractSPOT.exact_issuance_not_state_predicate` and
      `docs/fuguemax-contract-repair.md`.
    - [x] Implement the approved birth/origin metadata repair: live coordinates
      plus a finite set of insertion records, without deletion-event history.
      `FugueMax.datatype` and `generation` use that state. Exact-generator
      issuance, storage-order independence, local update/fold refinement, and
      executable issuer-to-raw merge refinement are machine-checked. The
      deleted-child guard controls and 5,596 sampled/bounded forks pass.
    - [x] Prove general live-merge/replay refinement and maximal
      non-interleaving for the enriched signature, for ordinary and virtual
      certified execution. `FugueMax.join_of_mint` and
      `FugueMax.replay_noninterleaving` derive the generation invariants from
      framework issuance; callers do not supply a separate `MaxReach` proof.
    - [x] Connect that result to the public ordinary-list contract and exact
      production certificate. `FugueMax.verified` proves general legalization
      and list-fold refinement. `FugueMax.correct` combines them with maximal
      non-interleaving for one witness of the same certified execution.
      The production gate pins that whole conclusion. The abstract state is
      a plain identity/value list; birth metadata remains implementation-side.
      Datatype-state collection and an independent runtime remain absent.
      Do not turn the weak coordinate guard into a production claim about
      the exact FugueMax generator or assume `MaxReach` as an extra premise
      of the promised certified-execution theorem.
  - [ ] Assess whether the current public certificate can express every
    audited contract. `SequentialSpec.Legal` currently receives only a list,
    so visibility-dependent exceptions need an explicit proof connection.
    Reuse issuance, `rc`, replay, and execution semantics; if necessary,
    design the smallest general history-aware contract extension over
    abstract events/visibility/observations. Integrate the resulting theorem
    into the checked public package rather than leaving a required property
    as an optional, untracked side theorem. Do not add another event order.
  - [ ] Publish a per-datatype requirements-to-theorems matrix with exact
    scopes, missing obligations, and checked counterexamples. Reassess
    previously completed migration claims against this matrix, keeping
    runtime correspondence a separate evidence class. Gate completion and
    publication on the required contract proofs and controls, not merely
    successful compilation or declaration existence.

- [x] **Move the datatype catalogue after the generic collection framework.**
  In `docs/formal-reference/main.tex`, move current Section 9 after current
  Section 11 so collection definitions precede their datatype instances.
  Keep small motivating datatype examples early. Fold the separate
  per-datatype collection profiles into the corresponding full profiles:
  each should present `D`, `rc`, issuance, sequential specification, and
  datatype-state collection. For each supported collector, state the
  collected representation, collection operation, preconditions, and exact
  preservation theorem. Distinguish representation compression from actual
  reclamation; explicitly identify datatypes without a provided collector.
  Update cross-references, profile/order checks, and the claim ledger;
  rebuild and inspect the PDF for definitions before use and duplicated text.
  Generic certificates remain before collection (end of Section 8); the
  integrated catalogue is now Section 11, after history and state collection.

- [x] **Restore the TikZ merge diagrams beside their laws.** Keep detailed
  adapters in the appendix, but place each diagram with its redistribution law.

- [x] **Connect TreeMove issuance to its public sequential contract.** Preserve
  the API restrictions; require an issuable causal-origin witness in each
  replay prefix, prove it from certified execution, and gate the obligation.
  Positive and negative controls distinguish it from sorting-only legality.

- [x] **Define all datatype-profile sequential contracts explicitly.** Expand
  operation steps, legality, queries, initial states, and representation
  relations in all 15 profile blocks, including the nested SidedPeritext
  variants. Clarify absent-target, repeated-delete, missing-anchor, and
  total-step versus legality behavior. Record source correspondence in the
  formal-reference claim ledger and add mutation-tested per-profile component
  checks to the working-paper gate. This does not close human semantic review.

- [x] **High priority: resolve the formal-reference review findings.** Apply
  these in order: semantic scope and evidence corrections, proof
  consolidation, then presentation cleanup. Primary document:
  `docs/formal-reference/main.tex`. Preserve one public `rc` relation; do not
  reintroduce `Interaction*`, duplicate `rcOn`/`loOn`, or metadata-bearing
  public sequential states merely to simplify proofs.
  Completed review evidence is recorded in
  `docs/formal-reference/claim-ledger.md`, under “Completion of the
  presentation and order-proof review”. This closes the listed refactor and
  presentation findings, not the separate human semantic audit of contracts.
  - [x] **Whole-document correspondence corrections and RGA simplification.**
    RGA now stores `(identifier, anchor)` births and takes `addAfter(anchor)`;
    its timestamp supplies the identifier by construction. Rebuild ordinary
    and virtual public certificates and the lossless live/grave conversion.
    State size savings conditionally and retain growth/shrink controls.
    Correct the dead-anchor claim, canonicality/Join scope, historical-order
    support premise, binary countermodel scope, and production/GC counts.
    Resolve printed anchors automatically and mutation-test stale citations
    and counts. Align the plain JavaScript RGA guard; distinguish the
    PeritextRGA shadow contract. See `docs/formal-reference/claim-ledger.md`.
  - [x] **Clarify public `rc` versus sufficient concrete-update proof laws.**
    The subsequent design decision supersedes preserving `RcNonComm`:
    semantic `rc` specifies intended resolution, not concrete noncommutation.
    Generalize `ReplayLaws` to one-way `noncomm_covered` and a semantic
    absorber swap obligation, and state full `rc` acyclicity using `TransGen`.
    Expose the selected policy throughout the merge-law proof route. Prove
    `ReplayLaws.of_all_comm` for any acyclic policy and use LWW's single
    timestamp relation throughout replay, Join, and sequential correctness.
    Retain concrete positive/negative controls refuting the old biconditional.
    Keep the sufficient algebraic laws separate from the public certificate
    and preserve conflict-only visibility.
    Completed by `ReplayLaws.of_all_comm`, the generalized convergence proof,
    policy-parametric merge-law adapters, and `LWWRegister.replayLaws`,
    `join`, and `verified` under the same timestamp policy. Type-ascribed
    formal-reference ledger controls prevent fallback to the empty policy;
    `concrete_noncomm_iff_rc_refuted` pins the rejected equivalence.
  - [x] **Correct Queue's evidence status.** The former package supplied only
    replay adequacy plus refinement of linear mint histories; the completed
    public certificate now proves the intended concurrent contract. Present
    `Queue.ConditioningSPOT.duplicate_dequeue_not_fifo` with its actual scope:
    disagreement of particular folds with unconditional pops, not proof that
    every allowed replay fails or that concurrent duplicate dequeue is wrong.
    The intended semantics are now settled: concurrent duplicate dequeue is
    allowed; its contract and proofs are complete without an exactly-once
    protocol. The old coordinate-only FugueMax replay model remains internal;
    the enriched `FugueMax.datatype` now has its own public list certificate.
  - [x] **Resolve the resolver-reversal mismatch.** `ReplayPolicy` currently
    accepts an arbitrary three-valued function, while `rc` tests only
    `FstThenSnd` in the given argument order. The prose's claim that
    `SndThenFst` supplies the reverse edge needs an explicit reversal proof.
    Evaluate simplifying the mathematical interface to a binary relation,
    retaining three-valued resolvers only where executable code needs them;
    otherwise establish and cite reversal coherence. Do not silently assume
    it from the carrier type.
  - [x] **Replace the misleading certificate implication chain.** Remove
    `CanIssue => MintHonest => G => JoinAt => HasReplayWitness` as a literal
    theorem. State `JoinOn`, `IssuanceEstablishes`, and certified reachability
    as three premises at the same level, with the chosen `rc` explicit.
  - [x] **Consolidate order proofs before polishing their exposition.** Factor
    one order-only acyclicity and finite-enumeration development shared by
    `Framework/ReplayLaws.lean` and `Metatheory/Correctness.lean`; build fold
    convergence on it. Audit the proofs copied from
    `Metatheory/Join/SetRelativeReplay.lean` and make historical no-chain
    results instantiate the acyclicity-based core instead of maintaining
    parallel developments. Keep helper definitions proof-local where possible.
  - [x] **Separate definitions from sufficient proof obligations.** Introduce
    `rc` first, then `loOn` and the set-relative absorber clause, then the
    laws proving existence and fold uniqueness. Explain why the absorber
    matters before presenting `CondCommLift`; do not restore the long proof
    sketch.
  - [x] **Make parameter notation consistent.** Use infix notation for fixed
    binary relations such as `rc` and `vis`, and consistent ordinary argument
    notation for parameterized predicates. Stop switching `loOn` between
    infix and function application. Make varying policies visible in
    `ReplayLaws`, `Join`, and replay certificates, and normalize the raw and
    certified reachability notation without obscuring their different inputs.
  - [x] **Shorten the main merge-proof narrative.** Keep the semantic
    `JoinAt` contract and a short account of proof routes in the main text;
    move detailed merge-law adapters to an appendix. Reduce repetition between
    datatype profiles, the proof-route table, and declaration indexes while
    retaining precise Lean anchors.
  - [x] **Standardize per-datatype profiles.** Present the ordinary sequential
    specification, representation/query, issuance rule, formal `rc`, and exact
    theorem scope or remaining limitation together. Explain that issuance
    constrains event creation whereas `rc` constrains replay ordering, even
    when their conditions mention the same identifiers or dependencies.
  - [x] **Remove migration commentary from the mathematical exposition.** Move
    historical explanations such as “no second interaction order” to migration
    notes; let the current definitions establish the architecture directly.
  - [x] **Validate and synchronize the completed changes.** Check affected Lean
    declarations and claim ledgers, audit status claims across the reference,
    papers, README, and theorem manifest, rebuild affected PDFs, and inspect
    the resulting layout. Record completion by exact theorem scope rather
    than treating replay-only evidence as full sequential correctness.

- [x] **Efficient OR-set certificate (Neem).** Register the compact implementation
  with its own public certificate as `efficient-or-set`; preserve the existing
  tagged-set runtime's separate `or-set` contract.
  - [x] Implement finite `(replica,timestamp,element)` records, local replacement
    adds, tombstone-free removes, three-way survivor merge, and Neem's `rc`.
  - [x] Prove ordinary finite-set refinement of every replay list, acyclicity,
    and preservation of per-replica/per-element uniqueness by sequential folds.
  - [x] Pin add-wins, observed removal, replacement, and union-resurrection
    controls; test fork observations against an independent observed-remove model.
  - [x] Prove ordinary and virtual execution replay adequacy using compatible
    replica histories. The old all-state replay route is refuted for this `rc`;
    do not silently strengthen the public policy or substitute max updates.
  - [x] Construct `VerifiedMRDT`, register it in the production manifest/registry,
    run the certificate mutation gate, and update the PDF/status claims.
  See `docs/efficient-orset-port.md` for evidence and exact residual scope.
- [ ] Migrate the JavaScript OR-set runtime to the efficient representation,
  with new correspondence tests before changing its evidence-manifest certificate.

- [x] **HIGHEST PRIORITY — enforce the verified production boundary.** A raw
  `MRDTSig` remains available for theorem development, SPOTs, and
  countermodels, but no datatype may appear in the production registry unless
  it supplies a `VerifiedMRDT` for that exact signature.
  - [x] add a dependent `PackagedMRDT` type and a production ledger containing
    only such packages;
  - [x] keep replay-only artifacts in the non-production build gate and refuted
    artifacts in the negative-evidence ledger. Keep the queue/FIFO and
    MVR/single-register controls visible with their actual rejected-target
    scope; Queue and MVR now separately have complete public certificates;
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
  The replay-only `HasReplayWitness` result reconstructs implementation state;
  the public `IsSpecLinearizable` result must additionally select an exact,
  `lo`-respecting history accepted by an independent sequential specification,
  relate both states, and agree on every query.
  - [x] replace the staging `Inv`/`Applicable`/`GuardBridge` API with the
    minimal public boundary: `Issuance.CanIssue` constrains origin operation
    creation, while `SequentialSpec.Legal` states acceptable abstract event
    histories without inspecting implementation state;
  - [x] remove arbitrary `GenerationContract.History`; convergence proofs now
    derive datatype-local history invariants directly from `MintHonest`;
  - [x] make `VerifiedMRDT` the strengthened public package and retain the old
    raw-fold result explicitly as internal `ReplayAdequateMRDT`;
  - [x] remove duplicated ordinary proof fields: ordinary certified execution
    embeds in virtual-merge-base execution, so convergence and optional safety store
    only their widened theorem and derive the ordinary theorem;
  - [x] state the strengthened per-version theorem with exact event-set
    membership, respect for `lo`, sequential legality and refinement, and
    explicit query agreement;
  - [x] factor one datatype-specific `SequentialCorrectnessCertificate` so ordinary and
    virtual-merge-base executions reuse the same semantic proof;
  - [x] migrate the total grow-only set/map canary and the tombstone RGA;
    RGA's specification state is `List Nat`, deletion is physical and
    idempotent, and `listSpec.Legal` records timestamp/ID honesty plus earlier
    allocation of anchors and targets entirely over the abstract event list;
  - [x] resolve Queue's concurrent contract: two replicas may dequeue the same
    observed head without removing the second element. The old
    `duplicate_dequeue_not_fifo` compares selected folds, not every possible
    witness. `Queue.verified` now proves a legal head-only abstract replay
    allowing repeated absent targets; issuance excludes causally ordered
    duplicate targets. No exactly-once suppression protocol is required;
  - [x] migrate the total counters/stores, TreeMove, and BoundedCounter to
    `VerifiedMRDT`. BoundedCounter uses a canonical increments-before-decrements
    witness and a client legality predicate that records the per-replica
    resource bound;
  - [x] classify the current MVR against its ordinary single-value register
    specification: two concurrent writes expose both values, so no state of
    that sequential machine can refine the merge. Keep the raw package named
    `replayAdequate` and the obstruction in
    `concurrentState_no_sequential_register`;
  - [x] finish EmbedRGA and SidedEmbedRGA legalization. Their canonical merged
    histories are prefix-legal, including duplicate deletion, and respect the
    explicit semantic dependence encoded by their sole `rc` relations.
    The raw-state counterexample remains checked: universal
    `UpdateSig.commutes` over malformed list states is not a sound public
    dependence policy for these representations;
  - [x] migrate or classify every production datatype. EmbedRGA,
    SidedEmbedRGA, Peritext, the three-component Sided Peritext core, and its
    production rendered-query `RichCore` now have `VerifiedMRDT` packages.
    Queue and MVR now have complete public packages; MVR's counterexample to
    its unsuitable single-value specification remains checked.
    AegisSheet now has a full package using causal-origin legality; the old
    whole-prefix predicate remains as the checked obstruction
    `concurrent_origins_not_guarded_chronological`;
  - [x] keep `SafetyCertificate.Safe` orthogonal to representation relations.
    Datatypes may reuse a proof-local reachable-state lemma when useful, but
    no coupling belongs in `VerifiedMRDT` and no production instance requires
    another public bridge;
  - [x] provide ordinary and virtual-merge-base versions of the strengthened theorem;
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
  delete). The retained `BirthGraveState { adds, grave }` machine is only an
  internal proof intermediate; merely equating add/tombstone membership does
  not discharge this task.
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
    virtual-merge-base convergence, guarded issuance, safety, and refinement to the
    independent incremental spreadsheet machine. Strict Lamport chronology
    makes the finite event set's sequential enumeration unique. The checked
    `concurrent_origins_not_guarded_chronological` example proves why it cannot
    be promoted with the old whole-prefix guard: two independent operations are
    valid at their empty origins, but whichever is second in a serialization
    did not observe the first;
  - [x] Define AegisSheet merged-history legality over each event's encoded
    causal origin view, extend the incremental materialization and observation
    theorems to that legality, and package the result as `VerifiedMRDT`.
    Every certified ordinary or virtual-merge-base version has a deterministic
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
- [ ] **Explore a materialized three-way AegisSheet MRDT.** Treat this as a new
  datatype design, not as an optimization silently substituted for the
  released event-set/union model. Define a materialized state containing the
  semantically necessary observed-remove tokens, active timestamped cell and
  range versions, position candidates, and any retained anchor summary. Give a
  ternary merge whose ancestor argument supplies the causal information that
  the current events' `seen` sets reconstruct. State the candidate
  correspondence explicitly, for example
  `materialize (E₁ ∪ E₂) = mergeM (materialize (E₁ ∩ E₂))
  (materialize E₁) (materialize E₂)`, with a separate cross-component revival
  clause for update-wins row and column removal. Use randomized version-DAG
  property tests and minimized SPOTs against all published merge/undo matrix
  fixtures before attempting proofs. Then prove the appropriate `JoinAt`
  theorem, causal-origin sequential refinement, and a datatype-state GC
  protocol, and measure the metadata reduction against the event-set model.
  Preserve the known range-anchor and no-view-only-state counterexamples as
  design constraints.
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
  `no_rc_chain` artifact from the MRDT interface.** `VerifiedMRDT.rc` is now
  the sole public resolve-conflict relation. `rcOn` preserves visibility only
  for conflicting pairs and adds a directed edge only when `rc` selects it.
  Concrete-state commutation remains a separate proof fact, and the raw
  `UpdateSig` stores no resolver.
  - [x] Build minimal machine-checked LWW-register and add-wins OR-set SPOTs against
    independent sequential specifications. The LWW policy admits timestamp
    chains and the checked three-write instance refutes `no_rc_chain`. The
    OR-set SPOT distinguishes
    commuting representation effectors from conflicting abstract
    `add`/`remove` operations and recover add-wins by ordering a concurrent
    remove before the add.
  - [x] Port the full timestamped LWW register to the current interface. Its
    `max` update and merge use the default proof-local replay policy, while a
    timestamp-sorted witness proves the independent total overwrite-register
    specification and packages a production `VerifiedMRDT`.
  - [x] Remove the separate interaction datatype and policy. Use the Neem-style
    three-valued `rc` verdict directly; the biconditional noncommutation law
    says exactly that a conflicting pair is oriented in one of the two
    directions.
  - [x] Define the framework's set-relative order directly from visibility and
    `rc`. A visibility edge is retained only for a conflicting pair; `Either`
    contributes no edge. Retain the conflicting-absorber clause used by the
    set-relative replay proof.
  - [x] Replace `no_rc_chain` with acyclicity of the nonempty transitive closure
    `Relation.TransGen RcEdge`. This admits useful chains, including LWW's
    increasing timestamp chain, while rejecting cycles.
  - [x] Keep `rc` out of the raw datatype signature but store the one selected
    public relation in each `VerifiedMRDT`; proof-local convergence arguments
    may instantiate the same policy carrier independently.
  - [x] Migrate every production `VerifiedMRDT`, delete superseded compatibility
    interaction definitions, and run the clean Lean,
    theorem-ledger, repository, and runtime release gates.
  - [x] Update both working papers and theorem manifests. Present the broken
    Neem/global-arbitration route as motivation, distinguish representation
    convergence from sequential arbitration, and use LWW and OR-set as the
    small explanatory examples before the richer RGA/Peritext developments.
- [x] Add `Production.StateGC.registry` in production order and make it
  distinguish exact-state baselines, collecting certificates, operational
  protocols, and staged collectors. Document the compact representation,
  evidence, preservation result, and residual obligation for every released
  datatype in the formal reference.
- [ ] **Finish datatype-state collection coverage for every released
  datatype.** For each exact-state entry, either implement a genuinely smaller
  representation and its continuation-safe collector or prove that the
  released representation contains no reclaimable semantic metadata under its
  current operation and query interface. Do not count
  `StateGCCertificate.exactState` as reclamation.
  - [ ] Grow-only stores and flat grow-only stores: formalize the irreducibility
    claim for semantic members, or introduce a representation quotient with
    update, merge, query, and continuation preservation.
  - [ ] Flat counters and bounded counter: prove that the aggregate state is
    already minimal for the current interface, or specify replica retirement
    and coordinate normalization evidence and implement the corresponding
    operational collector.
  - [x] Tombstone RGA, current-policy quotient: package a compact interpreter
    storing `(id,parent)` facts and the live-ID set, prove update, ternary merge,
    list-read, and continuation refinement, and prove that its word-count model
    is strictly smaller when graves exist. Issuance now rejects insertion after
    an observed anchor deletion; retained dead identifiers are still needed to
    integrate insertions minted concurrently with that deletion.
  - [ ] Tombstone RGA, physical ID reclamation: introduce and justify an
    explicit anchor-retirement/translation policy, then prove that its frontier
    evidence excludes stale and future references before deleting the retained
    `(id,parent)` fact. Do not silently strengthen the current sequential spec.
  - [ ] OR-Set: reclaim dead add records and observed-tag tombstones with
    frontier or equivalent merge evidence, including stale-branch and
    no-resurrection controls.
  - [ ] EmbedRGA and Peritext EmbedRGA: determine which coordinate and anchor
    information remains continuation-relevant after deletion, then implement a
    stable-frontier summary and prove restricted-Join-compatible updates,
    merges, list/rich-text queries, and future insertions.
  - [ ] SidedEmbedRGA: extend that result to side-sensitive Fugue ordering and
    retain exactly the LiveGap/Fugue policy evidence needed by later inserts.
  - [ ] SidedPeritext core: either define an abstract query boundary under which
    text, deletion, and mark collection is observational, or prove that the raw
    component-store query prevents representation-changing GC. Relate the
    result explicitly to the existing rich-query protocol.
  - [ ] Rich SidedPeritext, TreeMove, and AegisSheet: promote the existing
    representation-changing certificates/protocols through the production
    runtime packaging, add stale-branch and crash-recovery scenarios where
    applicable, and publish before/after retained-state measurements.

## 3. Repository automation

- [x] Add hosted CI for the release gate. Add benchmark schema checks to that
  workflow when the repeated-result publication format is frozen.
- [ ] Export stable theorem/runtime/benchmark manifests for downstream paper
  builds without duplicating development tasks.
