# Production Notion editing-code extraction

The editing code shipped to Notion clients runs offline in this harness, with
independent records and explicitly controlled operation delivery. It executes
the original text-slice, slice-tree, annotation, serialisation, `RecordMap` and
record-operation functions. No Notion account or server is needed for these tests.

The snapshot contains 63 public application assets (9,006,862 bytes), pinned on
29 October 2026 in [sources.json](sources.json). Acorn extracts 4,335 module
definitions as verbatim source slices. The application bootstrap is not run.
Missing dependencies fail; editing functions have no replacement implementations.

## Reproduce and export

Tested with Node.js 26.3.1 and Python 3. From the repository root:

```sh
npm ci --prefix experiments/notion-production-client --ignore-scripts
python3 experiments/notion-production-client/download.py \
  --cache /tmp/notion-production-sources
NOTION_PRODUCTION_CACHE=/tmp/notion-production-sources \
  npm test --prefix experiments/notion-production-client
node experiments/notion-production-client/extract.mjs \
  /tmp/notion-production-sources /tmp/notion-production-library
```

The export directory must not already exist. It contains `index.mjs`, the small
runtime/record adapter, the extracted modules and the source manifest. After
export, the library needs only Node: neither Acorn nor the downloaded cache is
used at execution time. Downloaded bundles and generated exports are not tracked.

## Use two clients

```js
import { createClient } from '/tmp/notion-production-library/index.mjs';

const block = {
  table: 'block',
  id: '00000000-0000-4000-8000-000000000001',
  spaceId: '00000000-0000-4000-8000-000000000100',
};
const seed = createClient('seed');
seed.createBlock(block);
seed.apply(seed.prepareInsert(block, 0, 'ab'));
const a = createClient('A', seed.snapshot());
const b = createClient('B', seed.snapshot());
const ax = a.prepareInsert(block, 1, 'X'); a.apply(ax);
const by = b.prepareInsert(block, 1, 'Y'); b.apply(by);
a.apply(by); // Deliver B's operations to A now.
b.apply(ax); // Deliver A's operations to B now.
console.log(a.text(block), b.text(block)); // aYXb aYXb
```

`prepareInsert`, `prepareDelete`, `prepareBold` and `prepareSplit` call the
shipped operation builders. The adapter uses half-open ranges for deletion
and bold; the initial positional controls use ASCII text. Bold takes an explicit
add/remove choice, not a UI toggle. Apply a prepared local batch before preparing
another on that client. Deliver each batch once, after its causal predecessors;
transport deduplication is outside this library adapter.

`prepareMove` and `prepareMerge` assemble record-level commands around the
shipped split-for-merge builder and movement handlers. They do not reconstruct
the complete transactions issued by the Enter/Backspace UI. `createBlock` creates
a fixture record with the shipped empty-tree constructor and serialiser.

## Replay the five demo cases

[The saved comparison](results/replays.json) records ten analogous schedules:
the five reported cases under both orders of the replica-ID tie-break. None
reproduced a failure. All 50 local edits agreed with the independent positional
request specification, and both text-loss schedules retained their seed text
on both replicas. No schedule was rejected.

The original demo's critical intermediate layouts were not reached:

| Case | Demo layout before the failing request | Extracted-code layout at that step |
| --- | --- | --- |
| N-001 | empty · aX | X · a |
| N-002 | empty · ba | a · b |
| N-003 | ac · b | a · bc |
| N-004 | empty · abc | a · bc |
| N-005 | empty · empty · x | empty · x · empty |

These are analogous user-action schedules, not exact reproductions of the
demo's internal states. Formatting selects the whole actual target block;
it does not invent the two-character selection when that block has only one
character. N-004 retains `abc` and N-005 retains `x` on both replay replicas.

The production request builder moves following slice-tree siblings when
splitting and appends merges to the last target slice. Its shared
`moveTextSliceIntoBlock` handler also places the new block after the actual
holder of the moved text. These behaviours differ from the demo path.

The comparison freshly re-runs the unmodified, hash-pinned demo and reproduces
all five original failures plus its passing control:

```sh
python3 artifact/paper1/scripts/reproduce-notion.py \
  --download /tmp/notion-demo-sources
node experiments/notion-production-client/run-replays.mjs \
  /tmp/notion-production-sources /tmp/production-replays.json /tmp/notion-demo-sources
```

The output file must not already exist. It contains the operations, causal
dependencies, issue/delivery actions, intermediate displays and independent
expected local effects, as well as the original demo's failing traces.

`requests.mjs` executes the original split/merge request-builder module. It
adapts that module's transaction-output sink to collect operations and apply
the original shared record handlers. Fixture stores supply the current record
values. The full optimistic-client cache, server acceptance and live UI are
not exercised. Block creation/removal and packet delivery remain explicit
harness operations. This result does not establish that production Notion is
free of these or other bugs.

## Checked results

All 19 tests pass in [the extraction controls](test/extraction.test.mjs) and
[the replay controls](test/replays.test.mjs):

- Source slices match the pinned assets; a same-length modification is rejected.
- Missing editing dependencies fail, and constant/getter exports are preserved.
- Insertion, deletion, bold addition/removal and right-boundary inheritance work.
- Concurrent inserts agree in opposite delivery orders; the two states are independent.
- Splitting and moving preserve the complete suffix; merging appends before removal.
- An insertion still reaches its text instance after that suffix moves to another block.
- Formatting across instances and nonadjacent slices leaves other blocks unchanged.
- A standalone export executes and refuses to overwrite an existing export directory.

Behavioural controls include independently expected results and a rival result
that must not occur. In particular, the constructed `ac | b` case produces bold
`ac` with plain `b`. This is a handler-level control, not the original concurrent
demo trace or a live-production UI reproduction. No new production bug is claimed.

## Source and execution boundary

| Component | Original module | Pinned asset |
| --- | --- | --- |
| Text slice | `458789` | `79323.js` |
| Slice tree | `300957` | `79323.js` |
| Clock | `508649` | `79323.js` |
| Record operations | `971340` | `19658.js` |
| Record map | `412951` | `19658.js` |
| Original split/merge request builders | `701590` | `UISpacePermissionGroupToken.js` |

The manifest links each local asset name to its full public URL and SHA-256.
Extraction preserves original function text, including validation and ordering.
The runtime supplies bundler exports and standard platform APIs (URLs, encoding,
crypto, timing and DOM exceptions). Cache-expiry timers are unreferenced so they
do not keep the Node process alive. No network API or browser UI is supplied.

Fixtures and the record-command adapter are ours. The replay adapter replaces
the request builder's transaction sink (`955631.k`), not its editing algorithms.
Server acceptance, permissions,
network transport, full editor transactions and live deployment behaviour remain
outside the checked scope. The public demo and repaired Lean model are separate
implementations and are unchanged by this experiment.
