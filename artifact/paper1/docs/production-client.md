# Reviewed experiments on extracted client editing code

These experiments execute editing functions from public production application
assets in fixture records, without an account, server or live page. They
establish behavior of the pinned functions under the harness's delivery and
specification choices. They do not establish a live-service bug, server
acceptance, or the correctness of the deployment protocol.

## Acquisition and reproducible checks

Requirements: Python 3, Node.js and npm. Node 26.3.1 was used for validation.
The first-party extractor pins Acorn 8.15.0 in its npm lockfile. The
[asset manifest](../experiments/notion-production-client/sources.json) pins 63
public assets from 2026-10-29, totaling 9,006,862 bytes. Those assets and the
4,335 extracted module bodies are **not distributed** in this artifact.

From the artifact root, acquire the manifest-listed assets outside the bundle:

```sh
python3 experiments/notion-production-client/download.py \
  --cache /tmp/public-editor-assets
python3 scripts/check-pbt.py --install --production-cache /tmp/public-editor-assets
```

Acquisition needs network access. Existing assets are checked by length and
SHA-256 and changed bytes are refused. The checked runner requires a complete
cache, installs only locked npm dependencies when `--install` is supplied,
and exports a new library into a temporary directory outside the bundle.
Later, with dependencies and assets already available:

```sh
python3 scripts/check-pbt.py --production-cache /tmp/public-editor-assets
```

This repeat is offline. The generated library's path is recorded in the
command logs under `results/pbt/`. Neither a browser nor user data is used.
The runner performs the following checks:

1. Verify the public assets, extract verbatim module slices, and run the 19
   original extraction/replay controls.
2. Verify the six exported files against the original pinned digests. The text
   verifier also checks all 63 assets and all 4,335 original source slices.
3. Run independent text and block specification tests, the declared fixture
   regressions, and the additional review controls.
4. Verify both library manifests again and check the artifact manifest after
   generated output and allowed npm installations have been created.

The exporter preserves `client.mjs`, `index.mjs`, `runtime.mjs`, `requests.mjs`
and the asset `sources.json` byte for byte. Together with `modules.json`
generated from the same public assets, they reproduce the **same six** pinned
library files. Anonymisation changes neither those wrapper bytes nor the
library digests. The source manifests are
[text pins](../ra-pbt/instances/notion-production-text/sources.json) and
[block pins](../ra-pbt/instances/notion-production-blocks/library.json).
Other first-party paths use the artifact's neutral project names.

For a reusable library, run the extractor yourself after installing its parser:

```sh
node experiments/notion-production-client/extract.mjs \
  /tmp/public-editor-assets /tmp/public-editor-library
export NOTION_PRODUCTION_CACHE=/tmp/public-editor-assets
export NOTION_PRODUCTION_LIBRARY=/tmp/public-editor-library
node ra-pbt/instances/notion-production-text/verify-sources.js
node ra-pbt/instances/notion-production-blocks/verify-sources.js
node --test experiments/notion-production-blocks/review-controls.mjs
```

The library destination must not already exist. Its bodies remain outside the
artifact; the instance verifiers reject a library located inside it.

## What the reviewed controls distinguish

The [review controls](../experiments/notion-production-blocks/review-controls.mjs)
make the following boundaries executable. Each has independently stated
expected results and a negative companion or changed-ingredient control.

| Observation | Supported interpretation |
| --- | --- |
| A label-addressed insertion, split or bold record is rejected despite its fixture causal predecessors being integrated | The shared interpreter rejects this input/state pair. A pending or rejected record is not evidence that two replicas integrated the same record set and diverged. |
| N-002/N-003 native editor-getter fixtures leave bold pending after full exchange while character inventories agree | Missing integration/formatting is distinguished from character loss in these particular fixtures. |
| Concurrent moves leave different documents with every fixture record integrated, no causal gaps and no pending work | Same-record-set divergence in the tested peer-delivery harness. Its applicability to deployment still depends on the real delivery/commit protocol. |
| `stale-merge` has no witness even after all causal dependencies are removed | A concrete mismatch with the supplied block specification, stronger than absence of a causal witness. It still uses fixture creation/removal and the shared interpreter. |
| `removed-anchor` and `order-mismatch` fail causal witness search but have a witness when all dependencies are removed | These examples alone do not refute the paper's implementation-dependent order criterion. |
| Fresh record-model clocks reuse a split marker; the original editor getter does not | A clock seam in the initial wrapper, not an editor duplicate-marker defect. |

The generic PBT witness search checks **full causal dependencies**. It has no
implementation `rc`/`lo_E` hook. The separate review's completely relaxed-order
check is a diagnostic for the listed finite histories, not a general
implementation of the paper's criterion.

The native editor control invokes the verbatim `970831.B` getter in a separate
runtime per client, with a fixture session and record accessors. The getter
chooses parser `266858.r` and clock holders `997076.W` itself. It neither
replaces the parser nor assigns a shared `W.overrides` map. The older block
campaign used a shared-runtime adapter; its additional isolation assumptions
are not silently promoted to whole-client correctness.

The original `ReplayReplica` comparison is a distinct fixture path. Its
full-exchange controls format the **actual** selected block, which contains
one character in these histories: N-002 rejects the received bold; N-003
converges to `[a] | bc`. The native editor-getter fixtures above reject in both
cases. Full exchange alone therefore does not explain both outcomes across
these different fixtures; clock/getter and request-selection choices must stay
explicit. Neither observation is a live-production result.

At the text layer, the specification distinguishes gap/left/both list readings,
anchored versus interval formatting, and insertion inheritance. The corrected
directed witness pruning preserves those readings; pruning controls and the
independent specification assertions are included. An admitted view under one
reading is not a guarantee under another. Historical campaign counts were not
regenerated by these directed regression checks.

## Client protocol remains outside the experiment

The initial wrapper calls shared interpreter `971340.N` for local operations
and explicit packet receipt. The actual optimistic path is `946729.y`, through
editor stores and the in-memory cache, with transaction handling in `323517`.
The editor's clock holders share a map **per text instance**, across block
trees; they are not a global server commit counter.

The pinned client also contains versioned record-value receipt through
`401033.e` and cache gate `11266.P`. `883194.J` handles save success, retryable,
untried and terminal failures. Its rollback path can install a returned
`rollbackRecordMap` or recover via `611569.U`, `549552.D`, `632228.X` and
`138635.B`; queue cleanup/backoff is in `79884`. These paths differ from the
fixture rule that a rejected packet remains pending.

This source evidence does not establish global server ordering, atomic receipt
across records, automatic positional-request rebasing, or the eventual outcome
of these particular label/move histories. A handler throw alone is not a live
bug report or proof of permanent data loss. Publication of deployment claims
must remain conditional on acceptance, ordering, rollback and recovery behavior.

## Recorded results and package scope

`recorded/pbt/notion-production-text/` and
`recorded/pbt/notion-production-blocks/` preserve historical aggregate evidence
and representative schedules. Host paths are neutralised. The large raw
failing-trial list from the out-of-order probe is omitted; its summary and
shrunk representatives remain. Campaign class names and old verdict labels
describe the original harness runs. Read them through the reviewed distinctions
above, especially pending integration versus same-record-set divergence.

The long prereview reports are not shipped. Production experiment READMEs point
here, while executable source, pins, regressions and review controls remain
available. This artifact contains no verification theorem for the extracted
production library, no claim about a user's live pages, and no GC result.
