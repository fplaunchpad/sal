# Prioritized remaining work

This is the canonical development task list for Sal. The sibling `Sal_paper`
repository owns manuscript prose, figures, bibliography, and paper builds.
This repository owns Lean, JavaScript, executable validation, and benchmark
artifacts.

## 0. Finish the plain-MRDT cutover

- [x] Create `refactor/plain-mrdt-framework` and preserve the previous tree on
  `archive/conditioned-mrdts-2026-08-21`.
- [x] Replace the conditioned signature with plain `MRDTSig`, implementer
  `GenerationContract`, `SafetyCertificate`, `SequentialRefinement`, and
  `VerifiedMRDT` interfaces.
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
- [ ] Keep EmbedRGA and SidedEmbedRGA as separate state-of-the-art baselines;
  report their storage/intent tradeoff rather than selecting one silently.
- [x] Complete statistically repeated benchmark runs and publish machine-readable
  raw results plus primary tabular summaries: the Sal-versus-external matrix,
  the three verified sequence kernels, and the focused Peritext/two-GC design.

## 2. Follow-on formal work

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
- [ ] Investigate a declarative arbitration replacement for the absorber
  clause and its relationship to `loOn`.
- [ ] Extend reusable state-GC certificates to other production datatypes where
  the state contains reclaimable metadata.

## 3. Repository automation

- [x] Add hosted CI for the release gate. Add benchmark schema checks to that
  workflow when the repeated-result publication format is frozen.
- [ ] Export stable theorem/runtime/benchmark manifests for the paper repository
  without duplicating development tasks there.
