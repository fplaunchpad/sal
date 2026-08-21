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
- [ ] Package Sided Peritext state GC as a concrete `StateGCProtocol`, not only
  component lemmas. Its validity relation must cover text retention and
  LiveGap evidence, trimmed deletion evidence, guarded mark-pair removal,
  Lamport-fresh continuations, cross-epoch translation, ordinary merge, and
  virtual-LCA/head-only merge.
- [x] Audit the remaining tracked source/docs against the paper scope. Remove
  historical whiteboards and stale root notes after migrating any genuine open
  task here.
- [ ] Run a clean-from-source Lean build, the runtime suite, repository checks,
  and benchmark schema validation. Publish a stable theorem manifest.
- [ ] Fast-forward `main` to the verified refactor branch and push it.

## 1. Runtime and evaluation engineering

- [ ] Add same-replica crash recovery. Persist replica identity, Lamport mint
  state, causal frontier, roster evidence, epoch translations, datatype state,
  and pending synchronization state; test recovery across a GC epoch.
- [ ] Replace benchmark position-to-ID array splices with an indexed sequence
  adapter and report adapter cost separately from datatype operations.
- [ ] Add streaming bulk decoders/builders for run-table and shared snapshots.
- [ ] Profile and optimize shared-path sync, save construction, and repeated
  HAMT/path traversal.
- [ ] Keep EmbedRGA and SidedEmbedRGA as separate state-of-the-art baselines;
  report their storage/intent tradeoff rather than selecting one silently.
- [ ] Complete statistically repeated benchmark runs and publish machine-readable
  raw results plus the primary tabular summaries consumed by `Sal_paper`.

## 2. Follow-on formal work

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
