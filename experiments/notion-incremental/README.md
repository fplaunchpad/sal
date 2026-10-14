# Indexed core research executable

`python3 experiments/notion-incremental/run.py --cases 100 --sizes 32,128,512 --repeats 5 --output experiments/notion-incremental/default-fold-observations.jsonl`

The runner fetches every module from `../notion-oracle/sources.json`, verifies its SHA-256, and stages unchanged source in a temporary directory. `structured.mjs` is a named standalone research adapter, not a patch to the downloaded source. There is no JavaScript extraction theorem or production Notion correspondence claim. The typed Lean model is the core formal reference; this executable is checked against the pinned JavaScript oracle on the recorded finite honest cases.

The adapter retains per-instance immutable origin rows, sorted descending origin-child indexes, delete-ID sets, marker-to-destination cuts, immutable create-origin links and sorted descending create-child indexes. It retains inactive title instances even when empty. Queries traverse origin indexes and assign every physical interval the owner of its preceding START/marker boundary. They do not inspect or replay transactions. Deleted rows remain in the tree as anchors. Direct merges union rows, deletes, cuts and create links, then union the retained archive; they do not run the transaction interpreter. Full payloads are currently retained for collision checks, reference comparison and honest client reissuance. Their memory cost is included.

The pinned `Replica.document()` reconstructs every time; `CrdtDocument` exposes no public incremental integration method (`#apply` is private). The baseline here eagerly reconstructs once after each unique received update, and once after each batch merge containing any new transaction, then uses that maintained document for queries. This baseline avoids repeated query-time replay. Each query in both engines renders the full ordered block-ID/text answer. This is an executable algorithm comparison, not a Lean runtime performance measurement. In particular, the pinned constructor also rebuilds mappings per transaction and checks its invariants. The independent adapter does not perform those extra checks on each receipt; differential checks run outside the timer.

Update measurements ingest already prepared, immutable honest transactions; local positional client preparation and workload generation are excluded. Merge measurements exclude constructing the two input states. Work counters are cumulative per retained state: `mergeStateWork` includes input construction, unlike merge timings. Query and post-merge query measurements are separate. Every recorded run uses seed 314159; correctness uses seeds 1 through 100. Warmup, allocation and garbage collection can affect individual timings: use the five recorded repeats and report medians. Memory is explicitly a proxy: archive JSON bytes plus counts of retained rows, deletion IDs, cuts, indexes, mappings and transaction references. It is not heap measurement, and the different per-entry object costs do not support a quantitative memory saving claim.

Workloads are generated through unchanged pinned `Replica` requests. Each participant has a distinct allocator session and receives whole other-participant versions periodically. Updates observed by the test adapter arrive as reversed participant-version batches, preserving each batch's received dependency prefixes while allowing concurrent lower source keys to arrive after higher keys. Every delivery prefix is compared with full reconstruction. Timed merge inputs are two whole-state honest forks of the completed common version, each with one fresh independent insertion; every timed merge adds a transaction. Both directions of each generated participant pairwise structural merge are compared with oracle union; a counter asserts merges do not interpret transactions. Duplicate deliveries and idempotent merges are tested. Modes are insertion-only and mixed create/insert/split/bounded nonempty deletion; formatting and block-editing merges are excluded.

PASS+FAIL controls have hand-derived answers: concurrent insertion into `ab` yields `aYXb`, not `aXYb`; concurrent split at one yields `a | empty | b`; erasing a newly inserted X yields `ab`, not `aXb`. A deliberately broken append-only create-splice interpreter applies concurrent split creates in arrival order and produces B-before-Z display, while canonical source replay and the structure produce Z-before-B. The output includes the literal split transactions for reproducibility.

The present indexes do eliminate transaction replay, but queries still scan physical rows including tombstones and markers, and merge scans the incoming retained structure plus archive. Array insertion into a long sibling list is linear. No balanced order-statistic index, compact memory layout, archive elimination or sublinear query claim is made.


Source footprint is measured separately with:

```sh
python3 experiments/notion-incremental/proof_metrics.py --output experiments/notion-incremental/proof-metrics.json
```

This reports new structural modules, intermediate cache/counterexample modules,
and the existing Notion dependencies separately. The reference baseline is the
Notion-specific transitive import closure of `NotionCoreProtocol`, not every
Notion file in the repository. Counts include unfinished source and are not
build evidence. Physical lines include definitions, comments and controls;
declaration counts are syntactic. Import closure is an upper bound on available
reused material, not an inventory of invoked lemmas. Until the end-to-end proof
is complete these numbers cannot support a proof-size reduction claim. They do
not measure researcher time or establish that a from-scratch structured proof
would be shorter.

## Checked creation-fold alignment

`python3 experiments/notion-incremental/run.py --cases 100 --sizes 32,128,512 --repeats 5 --display-fold-only --output experiments/notion-incremental/display-fold-observations.jsonl`

`Structured.query('fold')` uses the same maintained rows/deletes/cuts, then sorts immutable creation links by ascending creator source IDs and applies immediate-after insertion. It follows the checked Lean `StructuralDisplay.displayFacts` algorithm. The canonical bootstrap is an ordinary creator at A@1; it is not forced to the front before sorting, and no initial block is invented in bootstrap-absent versions. `query()` and `query('fold')` now use the creator fold by default; `query('tree')` is an explicitly selected comparison using descending create-child traversal. Both render full block-ID/text answers and avoid full transaction replay. This aligns the display algorithm only: JavaScript maintains row indexes, whereas the current Lean physical computation extracts and traverses finset rows. No extraction or identical runtime representation claim is made.

The supplemental corpus passed 200 cases and 12,400 oracle comparisons across tree and fold variants. `display-fold-summary.json` reports paired five-repeat query medians; at 512 mixed edits (179 blocks, 408 retained rows), tree took 0.077 ms and fold 0.167 ms. Updates and direct merges use the identical maintained structure and the original separate measurements; the supplemental file does not repeat those timings. `display-control-observations.jsonl` additionally records hand-derived PASS+FAIL lower-key pre-bootstrap creation and bootstrap-absent controls. The original `observations.jsonl` remains the earlier tree-default experiment, with 6,800 equality comparisons. The main benchmark now measures the default creator fold and labels its strategy in new records; earlier files retain their historical meanings. `default-fold-smoke.jsonl` records the default-switch check (20 cases and 1,240 comparisons). The explicit tree comparison remains in the supplemental display experiment.

## Bounded retained-heap experiment

`python3 experiments/notion-incremental/run.py --heap-comparison --sizes 512 --repeats 3 --output experiments/notion-incremental/heap-observations.jsonl`

Each engine/repeat runs in a separate Node process with `--expose-gc`. The fixed-seed honest workload is generated before the measurement and stays strongly retained equally in each engine's process. A small engine warmup is discarded, followed by three GC passes. The measured delta is `process.memoryUsage().heapUsed` after constructing the retained engine and three further GC passes, minus the prior heap use. Queries and oracle verification run after that measurement. The delta includes each engine's cloned archive and retained document/index; the shared prepared input payloads and generator retention are outside it. RSS is also recorded but is not used as retained-object memory. These are construction snapshots, not peak memory, and V8 allocation/GC noise remains.

The 12 records use Node v26.3.1 on Darwin arm64. Three-repeat median byte deltas for 512 insertion edits were 545,432 (full replay) and 478,496 (indexed structure); respective observed ranges were 410,344–545,432 and 478,464–478,496. For mixed edits they were 694,912 and 712,320, with ranges 693,184–695,896 and 685,152–715,328. The ranges overlap in both modes, and the direction changes between modes. This bounded measurement supports no general memory-saving claim. The earlier explicit proxies remain available to explain which archives, rows, cuts and indexes are retained. Summaries are in `heap-summary.json`.

## Native typed-core bridge

`python3 experiments/notion-incremental/run.py --native-fixtures-only --output experiments/notion-incremental/native-wire-fixtures.jsonl`

With the compiled JSON-lines driver available, pass its executable path through `--native-binary PATH`, with `--cases`, `--sizes` and `--repeats` as usual, and use a new output file. The runner stages unchanged hash-pinned source alongside the named `native-wire.mjs` codec and `native-harness.mjs` client. It preserves original pinned preparation and compares compiled-core outputs with pinned reconstruction. Native operation `elapsedNs` and complete JSON/IPC roundtrip milliseconds are recorded separately; source preparation, codec conversion, initial states and fixture warmup occur outside operation timings. No isolated native memory claim is made by this multi-replica process harness.

The six literal fixture groups include UTF-16 concurrent session ordering (emoji before private-use in source key order), separator/newline/emoji generated names, empty bootstrap, bootstrap-absent create, a lower-key pre-bootstrap create, and split/inherited-instance emoji insertion/deletion. Controls distinguish code-unit session encoding from string-iterator text atoms, pin iterator-based allocation width, and reject unsafe counters, noncanonical names and mismatched atomic split targets. Source/typed reservation maxima are compared. The codec is tested/trusted until its JSON/source-string boundary is proved; see `executable-contract.md` for the exact refinement obligations.

The first native full run is reproducible with:

`lake build notion_core_runtime`

`python3 experiments/notion-incremental/run.py --native-binary .lake/build/bin/notion_core_runtime --cases 100 --sizes 32,128,512 --repeats 5 --output experiments/notion-incremental/native-observations.jsonl`

That recorded run passed 200 cases and 10,008 query comparisons, with all six literal fixture groups and duplicate/late receipt/direct join checks. The native metadata control also passed: an unused local gap raises the source clock from 2 to 8, while a receipt merge and a fork cloned after that gap both keep the destination clock at 2. Audit caught and corrected an initial whole-engine clone that would have copied that gap; this is a native wrapper integration finding, not an additional Notion demo bug.

Five-repeat median native internal times at 512 insertion edits were update 4.072 ms, query 4.679 ms and merge 0.917 ms. At 512 mixed edits they were update 3.376 ms, query 73.741 ms and merge 0.931 ms; complete JSON/IPC roundtrip medians were 11.609 ms, 74.020 ms and 0.949 ms. These receipts/merges execute the proved core plus archive/allocator checks, with typed decoding and serialization outside the internal timer. The current compiled query recomputes physical/interval structure and is slower than both the earlier pinned maintained-document query (27.153 ms at 512 mixed) and the JavaScript indexed-fold query (0.167 ms). These are different-language implementation measurements, not a controlled compiler comparison or a claim that every operation improves. Direct structural receipt/merge removes full transaction replay; query indexing remains an explicit performance tail.

`native-summary.json` separates internal and IPC-inclusive medians. `native-build.json` records the measured binary's hash, toolchain/platform and reporting-time source/bridge hashes; Git HEAD alone does not capture local proof additions. The JSON/string codec and compiler remain explicit trust boundaries. Native process memory was not measured by this harness, and earlier JavaScript retained-heap results must not be relabeled as native memory results.

`python3 experiments/notion-incremental/run.py --native-binary .lake/build/bin/notion_core_runtime --native-controls-only --output experiments/notion-incremental/native-boundary-controls.jsonl`

The retained atomic-error controls deliberately cross the honest-input boundary. A receive batch first contributes a valid new create, then reuses the existing bootstrap ID with a different payload; the entire batch is rejected and the destination's query/archive/rows/blocks/clock stay unchanged. A merge from a state with a conflicting bootstrap identity is also rejected without changing the destination. These robustness tests validate native error handling, not an enlarged honest-protocol theorem. They run before the generated cases in the current native harness; the historical full corpus predates these extra checks.

Native receipt timings sum separate one-transaction requests across each prepared sequence; they do not measure one batched receive call. Merge avoids document-effect replay but still scans archived metadata and derives transaction reservation widths.
