# Production Notion: clocks, optimistic edits, receipt and rejection

## Question and conclusion

Does the real client apply edits in a server total order, and what happens to
optimistic edits when a search-label lookup or move fails?

The pinned client contains optimistic local application, queued server commits,
versioned record-value receipt, and explicit rollback/refetch recovery. The
offline record-handler adapter does not execute that protocol. A handler
exception in a causally ordered fixture execution therefore does **not**
establish permanent divergence, text loss, or a live-service bug. Nor does this
source review establish that the server supplies one total order across clients
or records. Publication of deployment claims must remain conditional on those
unverified protocol premises.

There is also a concrete clock mismatch in the main extraction wrapper. Its
record-model parse uses fresh per-tree holders; the editor uses shared holders
keyed by text instance. A sequential control reproduces a duplicate marker
with the former and eliminates it with the latter. This is an adapter finding,
not evidence that the editor issues duplicate markers.

`SYNC` and `REJECTION` below name conceptual receipt/rejection paths. They are
not source enum names: neither literal identifier occurs in the inspected
snapshot.

## Evidence and scope

The evidence is the 63 public application assets pinned on 2026-10-29 by
[`sources.json`](../experiments/notion-production-client/sources.json), checked
through the unchanged extractor. The cache used for this review was
`/private/tmp/notion-client-analysis`. Extraction checks every asset length and
SHA-256 and yields 4,335 module bodies. It neither runs the application bootstrap
nor contacts an account or server.

I also read the separate worktree's `docs/notion-production-blocks.md`,
`docs/notion-production-text.md`, and corresponding adapters/regressions. Those
are experimental reports, not evidence of server acceptance. The block adapter
already distinguishes editor clocks from record-model clocks and its scope
section acknowledges the unexecuted optimistic-client path. Its stronger
statement that a sequencing server would show the same failure requires an
additional premise: the deployed server must accept and interpret these exact
fixture operations against the corresponding state. That premise has not been
established.

Module references below identify the original numeric module, minified
function/export, asset, and zero-based half-open **JavaScript string offsets**
of the module body in that asset. They are not line numbers or UTF-8 byte
offsets. The manifest supplies the full asset URL and digest.

| Module | Inspected entry point | Asset range |
| --- | --- | --- |
| `997076` | export `W`; holder `get`, `set`, `updateOverride`, `getOverrides` | `10130.js [8789,9349)` |
| `508649` | exports `g` (plain holder), `q` (clock); `reserveTicks`, `maybeUpdateClock` | `79323.js [18441,18992)` |
| `266858` | export `r`, parser function `i` | `79323.js [81398,81656)` |
| `174819` | deserializer function `d` | `79323.js [33684,34991)` |
| `500183` | record-model `getBlockTitleTextSliceTree` | `RecordModel.js [4019,33310)` |
| `970831` | export `B`; record-store `getBlockTitleTextSliceTree` | `RecordStore.js [29329,63253)` |
| `946729` | export `y` = `g`; local application `u`, move helper `s` | `3209.js [17787,27869)` |
| `323517` | `createAndCommit` = `W`, `createAndCommitAsync` = `V`; cancellation `O`, commit `U` | `97121.js [69,19195)` |
| `79884` | IndexedDB queue class `m`; `useSaveTransactionsApi`, `cleanupTasks` | `93335.js [48835,95471)` |
| `883194` | export `J` = async `b`; rollback helper `c` | `93335.js [22631,39082)` |
| `401033` | export `e` = async `T`; batched `performRequests` | `93335.js [717,5586)` |
| `11266` | export `P` = `n`; cache write and version gate | `93335.js [10629,13138)` |
| `56477` | export `o` = `a`; delete cached record | `93335.js [10094,10308)` |
| `138635` | export `B` = async `a`; force remote fetch | `93335.js [69,716)` |
| `611569` | export `U` = async `a`; task rollback dispatcher | `93335.js [45742,46041)` |
| `632228` | export `X` = async `s`; per-pointer refetch helper `n` | `93335.js [46042,47247)` |
| `549552` | export `D`; `recoverTask`, `attemptEntry`, retry loop | `93335.js [42766,45741)` |
| `210822` | `F8` gets lifecycle hooks; `P$` installs them | `93335.js [101630,102089)` |
| `971340` | export `N` = `B`; shared record-operation interpreter | `19658.js [433946,463476)` |
| `121141` | label/slice lookup helpers used by that interpreter | `19658.js [696291,701804)` |

## Clock ownership: per instance, across block trees

`508649.q` delegates to a value holder. `reserveTicks(n)` advances it and returns
the first reserved counter; `maybeUpdateClock(n)` advances only when necessary.
The plain holder `508649.g` stores one number.

`266858.r` enumerates the serialized tree's text instances and asks its caller
for one holder per instance. `174819.d` passes the corresponding holder to
each slice while rebuilding the tree. Thus multiple slices of an instance in
one parsed tree already share a holder. The distinction is what happens when
that instance spans **different block trees**:

| Path | Holder supplied to `266858.r` | Sharing boundary |
| --- | --- | --- |
| `500183.getBlockTitleTextSliceTree(session)` | new `508649.g(value)` | This parse of this block tree |
| `970831.getBlockTitleTextSliceTree()` | new `997076.W(value,textInstanceId)` | Module-static map keyed by text instance |
| Main `ProductionClient.tree` | Calls the record-model path | Fresh per-tree holders |
| Separate block harness's `liveTrees` | Calls the record-store-style parse | Per-client map, installed on `W` for the shared-runtime seam |

`997076.W.get()` consults the map before its own stored value. `set()` asserts
that the new value is nondecreasing and updates the map. This preserves the
largest observed/reserved counter across parsed trees of one instance in the
same runtime. It is not one global counter for all text instances, a server
commit index, or a proof of a global server order. `ReplayReplica.clock` is
separate harness packet metadata; it does not repair editor item allocation.

The main wrapper gives each `ProductionClient` its own VM/runtime, so using
the editor's original `W` directly would naturally isolate its map per client.
A harness that shares one runtime across simulated clients must additionally
isolate the maps. The other worktree's block adapter does that explicitly.
Because holders consult a static map when used, switching that map is a seam
assumption: a tree retained from one simulated client must not subsequently be
used while another client's map is installed. The published shared/isolated
controls cover selected schedules, not all possible object lifetimes.

### Independently reproduced control

One client creates `abc`, splits block 0 at 2, splits block 1 at 0, splits
block 0 at 1, then merges block 3 into its predecessor. Expected document:
`a | b | c`; the rival outcome is `ac | b | empty`.

- Main wrapper: the first three split markers are `A:4`, `A:5`, `A:5`;
  observed `ac | b | empty`.
- Editor-holder parse, changing only the clock seam: `A:4`, `A:5`, `A:6`;
  observed `a | b | c`.

This agrees with the block harness's declared `duplicate-marker` control.
The faithful next adapter is a separately named editor-clock variant, leaving
the pinned record-model wrapper and its published hashes intact. It should
retain the positive expected document, the negative rival document, and the
distinct-marker assertion. It does not by itself add the production protocol.

## Local application is optimistic, not peer receipt

The main [`RequestBuilder`](../experiments/notion-production-client/requests.mjs)
replaces transaction sink `955631.k` with collection followed by
`ProductionClient.apply`. That method calls shared interpreter `971340.N`.
Both local issuance and explicit packet receipt therefore use this shared
path in the fixture experiment.

The actual local path is `946729.y` → `u`. It captures initial record values
and inversion metadata in a transaction, obtains the current editor tree from
its store, applies text/split/annotation helpers, serializes the result, and
forces the new models into the in-memory cache through `11266.P`. Local moves
use helper `s`, which finds the source and target nodes in the current store
trees by instance/item identities and detaches/appends them. This is a different
entry path from resolving a received wire operation through shared-interpreter
label mappings. These differences matter even when the underlying slice
operations are shared.

`323517.createAndCommit` performs the local callback before waiting for server
commit. A local exception invokes cancellation `O`, which restores affected
records from `initialRecordMap` and invokes cancellation callbacks. Commit `U`
builds/enqueues a task, keeps a server-commit promise/callback, and marks the
transaction committed. Enqueue/local-validation errors also take cancellation
or error-hook paths. Local display and server acceptance are separate events.

The shared interpreter also increments record versions in paths where the
local helper serializes/caches an optimistic edit without that shared-handler
increment. A protocol adapter must preserve this distinction rather than use
fixture record versions as if they were server acknowledgments.

## Receipt and rejection paths

### Receipt of server record values

`401033.e` batches versioned record requests and calls
`syncRecordValuesMain` or the initial/fanout `syncRecordValuesSpace` API. It
collects response `recordMap` values. It does not hand another client's
unacknowledged operation list to `971340.N`.

`11266.P` installs an incoming model when forced, when its version is greater
than the cached version, or under its role-change conditions. Otherwise it can
leave the cached value unchanged. An isolated offline cache-seam control of
this original function observed: version 8 replaces 7; subsequent 6 is ignored;
forced 6 is accepted. This tests the cache rule, not an actual server response.
Per-record version comparison does not establish atomic receipt across blocks,
one total order across records, or preservation of every optimistic edit.

### Server commit success, retry and terminal failure

`883194.J` submits queued operations to `saveTransactions`,
`saveTransactionsMain`, or `saveTransactionsFanout`, depending on the cell path.
On success it reports saved tasks and invokes lifecycle hooks. On structured
failure it distinguishes saved transactions, retryable failures, untried
transactions and terminal failures. The client-side handling is richer than
the block fixture's rule “a thrown record remains unintegrated and pending.”

For terminal failures, rollback helper `883194.c` uses a returned
`rollbackRecordMap` when available: it deletes affected cached records using
`56477.o`, then installs supplied models through `11266.P`. Tasks whose
affected pointers are not covered can fall back to remote recovery. Without
the rollback map, recovery/refetch is also used. Some terminal HTTP/API failures
roll back the submitted tasks and invoke task-error hooks.

The recovery chain is `611569.U` → `549552.D.recoverTask` → `632228.X` →
`138635.B` → `401033.e`. The last fetch requests version `-1`; successful fetch
deletes the cached record before installing the returned model. Recovery can
retry failed fetches with backoff; `549552` tracks unresolved recovery entries.
These are source paths, not a measurement that every recovery eventually
succeeds.

`79884`'s IndexedDB queue `useSaveTransactionsApi` cleans up saved tasks and
terminally failed tasks, calls their callbacks, and retains retryable work with
backoff. The module has other queue implementations as well. Queue/session
management is not evidence of a global server sequencer.

No inspected branch proves an automatic rebase that regenerates the positional
request against fresh state or rewrites its search labels. The observed retry
path retains tasks; rollback replaces/refetches record state. Lifecycle hooks
are a further seam (`210822`), so this is not a whole-client proof that no
other code can reapply, transform, or recover an edit. Success callbacks alone
do not expose the server's accepted-order semantics.

### When a label lookup or move is rejected

The fixture's errors are real throws of the extracted shared interpreter:
`971340` uses `121141`'s label/slice lookup and contains checks such as missing
split results, missing annotation endpoints, and failed insertion backfill
lookup. They establish a concrete partiality/precondition boundary for that
interpreter under the supplied record state and operations.

They do not establish that the production server accepts such a transaction,
that a client receives it as an operation packet, or that its optimistic
state remains permanently visible. For a deployed claim, the next questions
are whether that input is accepted, retried, transformed, or rejected; what
record values follow; and what happens to dependent local tasks. The client
source explicitly provides paths for rejection and recovery. It does not
answer those questions for these particular label/move histories.

## What remains unknown, and the publication boundary

| Question | Evidence established here | Remaining premise |
| --- | --- | --- |
| Does the server maintain a total order? | Versioned records, batched commit APIs, queue acknowledgment/error handling | Server implementation/contract, scope of serialization and causal/atomic guarantees |
| Do clients receive identical operation orders? | The inspected fetch path receives record values | Full live update transport, ordering and interaction with outstanding local edits |
| Are optimistic edits replayed or rebased? | Local application, rollback, refetch and task retries exist | Full lifecycle hooks/native paths and behavior with multiple dependent pending transactions |
| Is a label/move rejection permanent data loss? | Shared interpreter can reject fixture inputs | Actual server verdict, subsequent snapshots, retry/recovery and final accepted history |
| Can per-tree clocks manufacture failures? | Yes: sequential duplicate-marker control above | Use editor-holder seam for editor claims; do not attribute this control to the editor |

The publishable result currently supported is an implementation/protocol
boundary finding: concurrent request builders plus a partial shared interpreter
can reject these fixture histories; a source-faithful editor clock removes a
separate harness artefact. This motivates a research question about the
protocol's **accepted** histories and its treatment of optimistic requests.
It is not yet a live bug report or a refutation of deployment correctness.
The PBT witness search's separate causal-order-versus-paper-order limitation
also continues to apply.

A useful next experiment needs an explicit client/server model with local
optimistic states, commit acknowledgments, rejection outcomes, versioned
snapshot receipt and dependent queued work. Its controls should include a
sequential accepted edit, a deliberately stale rejected edit followed by a
new authoritative snapshot, and two dependent optimistic edits across a
rejection. Such a model would test a stated protocol hypothesis; without a
production contract or observed accepted trace it would still be conditional.
No user's pages or live service were modified in this review.

## Reproduce the offline checks

The existing pinned extraction/replay suite was rerun unchanged:

```sh
NOTION_PRODUCTION_CACHE=/private/tmp/notion-client-analysis \
  npm test --prefix experiments/notion-production-client
```

The clock control uses only fixture records and an in-memory adapter seam:

```sh
node --input-type=module <<'NODE'
import assert from 'node:assert/strict';
import { extract } from './experiments/notion-production-client/extract.mjs';
import { ReplayReplica } from './experiments/notion-production-client/replay.mjs';
const extracted = extract('/private/tmp/notion-client-analysis');
for (const editorClocks of [false, true]) {
  const r = new ReplayReplica(extracted, 'A');
  if (editorClocks) {
    const c = r.client, W = c.module('997076').W;
    const parse = c.module('266858').r;
    c.tree = function (p) {
      return parse(this.recordMap.getValue(p).crdt_data.title,
        ({ value, textInstanceId }) => new W(value, textInstanceId), this.session);
    };
  }
  r.createBlock('abc');
  r.split(r.idAt(0), 2);
  r.split(r.idAt(1), 0);
  r.split(r.idAt(0), 1);
  r.merge(r.idAt(3));
  const ids = r.packets.flatMap(p => p.operations
    .filter(o => o.command === 'splitText').map(o => o.args.id));
  const shown = r.view().map(b => b.text);
  assert.deepEqual(ids.slice(0, 3), editorClocks
    ? [['A', 4], ['A', 5], ['A', 6]] : [['A', 4], ['A', 5], ['A', 5]]);
  assert.deepEqual(shown, editorClocks ? ['a', 'b', 'c'] : ['ac', 'b', '']);
  assert.notDeepEqual(shown, editorClocks ? ['ac', 'b', ''] : ['a', 'b', 'c']);
  console.log({ editorClocks, ids, shown });
}
NODE
```

These checks execute the public-source snapshot offline. Neither the main
wrapper nor its pinned exported-file hashes were changed.
