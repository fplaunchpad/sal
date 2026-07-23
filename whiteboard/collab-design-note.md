# Collaboration and deployment design sketch (#95 skin + #107 editor)

Status: RECONCILIATION + proposed deltas, not greenfield. Much of the #95 skin
is already built in `p2p-demo/` (verified below by reading the files); this note
records what exists and what #107/#95 still need. An earlier draft of section 0
wrongly listed the durable store / transport / hub / editor binding as unbuilt;
they exist. Grounded in `runtime/src/replica.js` and `p2p-demo/src/*`.

## 0. What already exists vs. what this note proposes

Runtime primitives (`runtime/src/replica.js`), all present:

- `commit(payload)` -> gid : one local op, one commit (see the #107 batching
  caveat in section 5).
- `read()` : render the head state (peritext: `[{id, char, marks}]`).
- `ancestryGids()` -> Set<gid> : the "have" summary (content ids in my
  reflexive ancestry).
- `delta(theirGids)` -> wireCommits[] : the commits the peer lacks, wire-shaped,
  parents-before-children; op commits carry the payload, merge commits carry
  parent refs, compaction commits carry inline decoded state.
- `ingest(wireCommits)` -> count : add remote commits, recomputing state by
  `apply`/`merge3` (compaction commits decoded inline), SHA content-address
  gated (`content-address mismatch` throws), auto-registers op authors.
- `mergeWithGid(gid)` -> headGid : verified three-way MRDT merge (fast-forwards
  when one side is an ancestor).
- `headGid`, `register(name)`, `compactStable(opts)`, `gc(headIds)`.
- `syncRound(a, b)` (module helper): one in-memory bidirectional round.

Deployment skin ALREADY built in `p2p-demo/` (this note's section 7 interfaces
are the generalized shapes of these, not new inventions):

- `gitstore.js` -- the durable store IS a real git repo (fenced hard against the
  sal repo): `persist(node, repoPath)` writes one SHA-addressed JSON record per
  commit under `commits/<sha>.json` (op payload / parent shas / inline compaction
  state, the SAME shas the wire uses) plus `heads.json` and a materialized
  `doc.txt` for `git log -p` readability, then `git add -A && git commit`.
  `load(repoPath)` topo-orders the records and replays them through `ingest`
  (content-address gated) + `mergeWithGid(head)`. This is the RefStore role
  (section 7.1) and it already realizes "the durable format is the wire format"
  (section 4).
- `relay.mjs` -- a star relay + static file server. Rooms = one per doc id (the
  rendezvous unit). IMPORTANT: it is a DUMB broadcast switch; it holds no state
  and never merges (never inspects the CRDT payload). So it is the transport hub,
  NOT the SyncServer-as-replica this note proposes (section 7.2). Membership:
  roster on join, leave on disconnect (the closed set the stability certificate
  quantifies over).
- `transport.js` -- WsTransport carrying have/req/delta framing.
- `node.js` -- a thin re-export of `DistributedReplica`.
- `editbind.js` -- a PLAIN-TEXT (embedRGA) editor binding, per-character
  `commit`, single author. No marks, no batching.

What is still MISSING (the #107/#95 delta this note is about):

- DONE: the PERITEXT (marks) editor binding (`peritextbind.js` +
  `web/richtext.js`, now a PROSEMIRROR view: PM owns the DOM, `read()` owns the
  truth via a post-transaction reconcile; presence renders as PM decorations;
  prosemirror ships as plain ESM through an import map, still no bundler).
  Browser-verified across two live tabs. The full mark surface is exposed:
  B/I/U, links (exclusive-end gravity, value-carrying), and comments (one
  mtype per comment so overlaps coexist; pinned at the datatype level).
- DONE: BATCHING via a group-op commit. `replica.commitBatch(ops)` seals a
  gesture as ONE commit through `applyBatch` (payload is the op array, folded
  into the content-id opaquely; `delta`/`ingest` unchanged; the two GC
  id-collectors generalized). `peritextbind.commitOps` uses it.
  `test/commitbatch.test.js`. On top, the editor DEBOUNCES by default: local
  ops buffer while the UI renders the speculative head+pending state
  (`peritextbind.specRead`), and a flush (~400ms idle / blur / pre-format /
  pre-merge / unload) seals the RUN as one commit + one announce. A typed
  sentence is 1-2 commits instead of ~50.
- DONE: PRESENCE (`presence.js` + `web/richtext.js`): ephemeral off-DAG cursors/
  selections over the same transport, never committed. `test/presence.test.js`.
- DONE: transport ROBUSTNESS found by driving the browser: (a) pull-on-have,
  so a lone typist's edits reach idle peers (`test/livepush.test.js`); (b)
  auto-reconnect after the browser drops a backgrounded tab's socket, with
  announce-on-up catching up both directions, plus relay ping/pong keepalive
  (`test/reconnect.test.js`).
- DONE: MANUAL MERGE mode (git-style explicit sync). `NetworkNode` fetches
  always (`ingest` = `git fetch`) and, in manual mode, defers `mergeWithGid`
  (= `git merge`) to `mergeStaged()`; editor toggle + `merge ⤵ N` button.
  Merge stays total (no conflict prompts); staged merges work OFFLINE.
  `test/manualmerge.test.js`.
- DONE: the certified GC is WIRED INTO the rich-text editor: it runs on
  `compactiblePeritext`, a metadata-cost panel (tombstones / mark records /
  coordinate symbols / state bytes / commits / wire summary / epoch / cut),
  and a GC button gated on the complete stability cut. Per-peer GC in turn is
  the manual barrier; converged peers fast-forward onto a compacted chain.
  Links are Cmd/Ctrl+Click openable (http(s) only).
- DONE: CLOUDFLARE deployment (`deploy/cloudflare/`): Worker + static assets +
  one Durable Object per room speaking the relay protocol (hibernation-ready).
  Verified locally under `wrangler dev`. The SyncServer promotion (below) now
  has a natural home: the same DO holding a headless replica + DO storage.
- Promoting the DUMB relay to an always-on MERGING HUB (a headless replica +
  gitstore) so peers collaborate ASYNCHRONOUSLY (today two peers must be online
  together to exchange; git persistence is per-peer, not a shared home).
- Invite links / a `doc-id -> head` ref abstraction over rooms.
- Authenticated identity (replica id is a string, not a key).

## 1. Doc identity and the ref

A commit's content id (gid) changes on every edit, so it cannot name the doc.
A doc needs a stable identity separate from its content:

```
doc-id  ->  head-gid      (the REF: mutable, "where this doc is now")
gid     ->  commit         (the OBJECTS: immutable, content-addressed Merkle DAG; exists)
```

The object line is the runtime's DAG. The ref line, plus discovery of
`doc-id -> where to sync`, is what this note adds. `doc-id` should be a public
key once identity lands (section 8), a UUID until then.

## 2. Topology: a star hub, mesh optional

Recommended default: a **star**. One durable SyncServer replica per doc is the
always-on home for that doc. Peers gossip to it; it holds the ref, persists the
objects, merges pushes, and re-serves. This is what buys ASYNCHRONOUS
collaboration: two peers never need to be online at the same time, because the
server holds and merges between them.

```
        peer A (browser)              peer C (offline, resyncs later)
             \                          /
              \      have/want         /
               v      gossip          v
            +-----------------------------+
            |  SyncServer (per doc):      |
            |   headless DistributedReplica  <- computes delta/ingest/merge
            |   + RefStore (durable)         <- persists objects + head
            +-----------------------------+
               ^                    ^
              /   optional direct    \
        peer B  <----WebRTC mesh----> (server is the always-on backstop)
```

Pure mesh is rejected as the default: no durable home, no rendezvous for a peer
that was offline, and discovery is hard. Direct WebRTC between co-present peers
is a latency optimization layered on top, with the server as backstop.

## 3. The sync protocol (have/want), on real primitives

Pull (fold remote changes into me):

1. send my `ancestryGids()` (the have),
2. peer/server returns `delta(myHave)` (the commits I lack),
3. `ingest(delta)` (content-address gated),
4. `mergeWithGid(remoteHead)` (verified three-way merge).

Push is the mirror: ask their have, send them my `delta(theirHave)`, they
`ingest` + `mergeWithGid(myHead)`. Convergence is order-independent (MRDT
merge), so pulling from several peers in any order lands in the same state. This
is git fetch/push in miniature over the runtime's own protocol; `syncRound` is
the two-party in-memory version.

## 4. Serialization: the durable format IS the wire format (already done)

`gitstore.js` already implements this; documented here because it is the load-
bearing choice. `snapshotBytes()` is only a byte-count probe, so there is no
in-runtime whole-replica serializer, and none is needed: the ancestor-closed
wire-commit records `delta()` emits and `ingest()` consumes ARE the on-disk
format. `gitstore.persist` writes one `commits/<sha>.json` per commit (op
payload / parent shas / inline compaction state) plus `heads.json`; `load`
topo-orders them and replays through `ingest` (content-address gated) +
`mergeWithGid(head)`. `ingest` rebuilds the DAG deterministically (`apply`/
`merge3` are pure) and re-checks every content address; GC'd logs still replay
because compaction commits carry inline decoded state. One content-addressed
object format serves wire, disk, and catch-up.

The one place this differs from a browser deployment: `gitstore` shells out to
`git` (node only). A browser peer needs the same records in IndexedDB instead of
a git dir; same format, different backend (section 7.1).

## 5. Batching (the #107 correction)

The editor must NOT commit per keystroke. A typing run, an IME composition, a
paste, and a multi-character format change each coalesce into an op list applied
through the datatype's `applyBatch` (one transient pass, proven equal to folding
`apply`, `test/applybatch.test.js`) and sealed as ONE commit. This rides the
batch-build fast path (pmap `begin()`/`freeze()`, the #111 apply fast path) and
keeps the commit DAG and the GC horizon from exploding under per-character
granularity.

Runtime dependency this exposes: a GROUP-OP COMMIT the replica does not yet have.
`commit(payload)` is one op per commit, and `applyBatch` is a proven primitive
not yet on the commit or `ingest` path. The batch path must be plumbed through
the local commit, the `delta` wire encoding, and `ingest` (a group-op commit
kind that replays via `applyBatch`). See the #107 goal in `runtime/README.md`.

## 6. The lifecycle, mapped to the interfaces below

- Find: `parseInvite(url)` gives `{docId, relay, cap}`; or `RefStore.listDocs()`
  for docs already held (the local directory).
- Open (have it): `openDoc(docId, store, ...)` = fresh replica + `ingest(log)` +
  fast-forward to stored head. Offline-ready immediately.
- Open (new): fresh replica, connect to relay, one pull (section 3) to catch up.
- Edit: coalesce a burst, `commitBatch(ops)` (section 5), append the fresh
  `delta` to the RefStore, advance the head.
- Push / merge: the have/want round of section 3 against the SyncServer.
- Close: drop the in-memory replica; the RefStore is the durable copy.
- Reopen later, continue: `openDoc` again, then resync. Works offline until a
  relay is reachable.

## 7. Concrete interfaces

These are the GENERALIZED shapes of code that already exists in `p2p-demo/`.
7.1 RefStore generalizes `gitstore.js` (git-dir backend) to a backend-agnostic
interface (adds an IndexedDB backend + the `doc-id -> head` ref). 7.2 SyncServer
is a PROPOSED UPGRADE of `relay.mjs`: today's relay is a dumb broadcast switch;
this makes the hub a headless replica that merges and persists, which is what
enables asynchronous collaboration. 7.3 invite links are new (rooms exist in the
relay; the capability/identity part does not).

### 7.1 RefStore (durable: refs + content-addressed object log)

Why two backends. `gitstore.js` shells out to `git` (node `child_process`), so
it cannot run in a browser tab, which is where the #107 editor lives. A browser
peer needs an origin-local durable store to survive tab close/reload and to
open/edit offline. IndexedDB is that store: async and transactional (persisting
on every commit does not block typing, unlike synchronous `localStorage`), large
quota (`localStorage` caps at a few MB), stores binary records keyed by gid
directly, and runs in a Web Worker. It maps onto this interface verbatim: an
`objects` store keyed by gid, a `refs` store keyed by docId. It is LOCAL-ONLY
(not sync; the relay/hub still moves bytes) and evictable unless
`navigator.storage.persist()` is called. So: git repo = server/desktop durable
home (inspectable, cloneable); IndexedDB = a browser peer's local cache. (OPFS
is the alternative if blob size or sync-worker access dominates; for a gid-keyed
object log IndexedDB's keyed store is the closer fit.)

```js
// Generalizes gitstore.js. Backends: git dir (exists, node), IndexedDB
// (exists, browser: src/idbstore.js), LevelDB / fs. Objects keyed by gid.
// wireCommits are exactly replica.delta()'s output / replica.ingest()'s input.
interface RefStore {
  // refs (mutable)
  getHead(docId): Promise<gid | null>
  setHead(docId, gid): Promise<void>            // advance the ref (CAS on prevGid if concurrent writers)
  listDocs(): Promise<DocMeta[]>                // local directory: {docId, head, title, lastOpened}

  // objects (immutable, content-addressed, append-only)
  putObjects(docId, wireCommits): Promise<void> // ancestor-closed; idempotent by gid
  getLog(docId, sinceGids?): Promise<wireCommits[]>  // whole ancestor-closed log, or the suffix beyond sinceGids

  drop(docId): Promise<void>
}
```

Reopen and persist-on-edit glue:

```js
async function openDoc(docId, store, datatype, myId) {
  const r = new DistributedReplica(datatype, myId);
  const log = await store.getLog(docId);
  if (log.length) r.ingest(log);                    // rebuild DAG, content-address gated
  const head = await store.getHead(docId);
  if (head && head !== r.headGid) r.mergeWithGid(head);
  return r;
}

async function localEdit(r, store, docId, ops) {    // ops = one coalesced burst
  const before = r.ancestryGids();
  const gid = r.commitBatch(ops);                   // group-op commit (section 5 dependency)
  await store.putObjects(docId, r.delta(before));   // just the new commit(s), wire-shaped
  await store.setHead(docId, r.headGid);
  return gid;
}
```

### 7.2 SyncServer (the star hub)

```js
// One process, many docs. Per doc: a headless DistributedReplica (computes
// delta/ingest/merge) + a RefStore (durable). On restart, rebuild each replica
// via openDoc(). Transport-agnostic; wrap over WebSocket / HTTP / WebRTC relay.
interface SyncServer {
  // have/want, section 3
  onHave(docId, peerHave):   Promise<{ delta: wireCommits[], serverHead: gid }>
  onPush(docId, wireCommits, peerHead):
                             Promise<{ accepted: bool, serverHead: gid }>
     // replica.ingest(wireCommits) (gated) -> mergeWithGid(peerHead)
     // -> RefStore.putObjects + setHead -> fan out to subscribers

  // liveness
  onSubscribe(docId, peerId): () => void             // returns unsubscribe; pushes new commits live
  onPresence(docId, peerId, ephemeral): void         // off-DAG cursors/selection; RELAYED, never committed

  // admin
  createDoc(docId, datatypeName, acl): Promise<InviteLink>
  gc(docId): Promise<void>   // compactStable + gc; keep-set MUST include every subscriber's last-known head (section 8A)
}
```

Presence is ephemeral: it rides the same channel but is never ingested or
persisted, matching the peritext datatype's off-DAG presence note.

### 7.3 Invite link (discovery + capability)

```
sal://doc/<doc-id>?relay=<wss-url>&k=<key>&t=<r|rw>
```

- `doc-id`: stable doc identity (a public key once identity lands; a UUID until
  then).
- `relay`: the SyncServer to rendezvous at.
- `k`, `t`: the capability. Read-cap = a decryption key for op payloads;
  write-cap = signing authority (a bearer token the server checks, until real
  identity).

```js
interface InviteLink { docId, relay, cap: { read?: Key, write?: Signer } }
mintInvite(docId, relay, cap): string     // -> sal:// URL
parseInvite(url): InviteLink

// open from a link: parse -> connect(relay) -> onHave(docId, emptySet) to
// fast-forward -> openDoc persists locally -> now offline-capable.
```

Auth caveat (section 8D): until `doc-id` is a real public key, a write-cap is
only a bearer token the relay trusts. The SHA content-address gate bounds WHAT a
commit says, not WHO authored it.

## 8. Sharp edges (open problems, not hand-waves)

A. **GC horizon vs. offline peers.** The commit GC prunes interior commits to a
keep-set (MCAs of current heads + descendant cone). If a peer edits offline long
enough that the server GCs past that peer's branch point, the MCA is gone and
`mergeWithGid` has no common ancestor. Requirement: `SyncServer.gc` must retain
the MCAs of every KNOWN peer head, including offline peers (track last-known
heads per subscriber), or bound how long a peer may stay dark. This is the one
place "close it and come back in a month" can fail.

B. **Multi-MCA merge: RESOLVED (#90 landed).** The metatheory closed the
question (sal-mrdts.tex 14: `Step3V`, `mca_events_cover`,
`virtualLCAState_canonical`, kernel-clean; single-MCA picks machine-refuted),
and `DistributedReplica` now transliterates the recursive rule: the LCA slot
of a criss-crossed pair gets the virtual base folded over the MCA antichain
(content-id sorted; result canonical hence order-insensitive for join-lemma
datatypes), and the commit-GC keep set widened to the MCA closure
(`keepSetV`). Pinned in `runtime/test/virtual-lca.test.js` (directed
countermodel with hand-derived resurrection FAILs + a randomized mesh that
previously gated). N-way concurrent editing no longer defers on
criss-crosses; the transport defer path remains for cross-epoch only (C).

C. **Concurrent divergent compaction is deferred (#97).** `ingest` throws
`cross-epoch merge` when two sides compacted at different cuts; the runtime
linearizes epochs with a settled barrier. A single SyncServer can act as that
barrier (compact centrally, one epoch line), which is why the star topology also
side-steps this for now. Lifting it (peers compacting independently) is the #97
multi-epoch `CompatChain`.

D. **Identity and access.** Replica id is a string. A real deployment needs
`doc-id` = a public key, ops signed (write access), and op payloads encrypted
under a read-cap so an untrusted relay cannot read content. Content-addressing
gives integrity, not authorization.

## 8.5 Decision (2026-07-23): git integration is FROZEN at one-way

Git cannot be a source of truth for this system, only a mirror: hand edits
to `doc.txt` have no ops to become, hand edits to `commits/*.json` are
rejected by the content-address gate, and git-level merges are not the
verified `merge3`. A two-way integration would advertise a collaboration
surface that is read-only in disguise. The frozen posture:

- `.saldoc.json` BUNDLES are the interchange primitive: the editor's
  `download .saldoc` / `open .saldoc` buttons save and restore whole-history
  files anywhere, no git involved (durable == wire == bundle format,
  SHA-gated on import).
- Git is an ARCHIVAL SINK only: `bundle2git` / `doc2git` mint a snapshot
  repo (readable `git log -p`, open format, pushable) when wanted.
- NOT built, deliberately: browser-native git (isomorphic-git + CORS proxy
  + tokens in the page), git-as-sync-transport, workspace repo layouts.
  The steelman (git remote as a serverless async transport with
  per-replica ref files) is coherent but competes with the DO SyncServer,
  which is native and planned; revisit only if "no custom server" becomes
  a hard requirement.

## 9. Suggested build order

Already built (reuse, do not rewrite): `gitstore.js` (RefStore, git backend),
`idbstore.js` (RefStore over IndexedDB + the `doc-id -> head` ref, shared record
round-trip with gitstore, `listDocs` directory; `test/idbstore.test.js`),
`relay.mjs` (dumb transport hub), `transport.js`, `editbind.js` (plain-text
binding), and `peritextbind.js` + `web/richtext.js` (the rich-text editor:
marks-aware op layer + browser view; `test/peritextbind.test.js`). The remaining
#107/#95 work, roughly in order:

1. DONE: group-op commit. `replica.commitBatch(ops)` applies a gesture's op list
   in one `applyBatch` pass and seals ONE commit; the op-array payload folds into
   the content-id opaquely so `delta`/`ingest` and the hash are unchanged (the
   two certified-GC id-collectors were generalized to array payloads).
   `peritextbind.commitOps` uses it. `test/commitbatch.test.js`; relieves edge A
   (fewer commits per keystroke -> a shallower GC horizon).
2. DONE: peritext editor binding (`peritextbind.js` + `web/richtext.js`) and
   PRESENCE (`presence.js`, ephemeral off-DAG cursors/selections painted into
   the rendered doc). `test/peritextbind.test.js`, `test/presence.test.js`.
3. DONE: `idbstore.js` wired into the rich-text editor: load-before-connect
   keyed by room (top-level await), re-persist on every head change
   (gid-guarded), reopen-under-a-new-name via `rebuildNode` opts, and the
   record shape split into the browser-safe `src/records.js` (gitstore was
   Node-only and un-importable in a tab). Browser-verified across two
   reload cycles with the relay stateless. Remaining offline polish: a
   service worker for the app shell (the DATA is durable; the PAGE still
   needs the network to load).
4. DONE: the SYNC HUB (`src/hub.js`): a transport-agnostic headless replica
   per room, run by BOTH the node relay and the Cloudflare Durable Object
   (DO storage adapter), persisting via the RefStore. Invisible to rosters
   and GC. Availability + durability + peritext round-trip pinned in
   `test/hub.test.js`; live-verified on the deployed DO (push, leave, a
   later peer converges from the hub alone).
4b. DONE: EPOCH-BASE PRUNING (the "O(history) is scary" answer). The
   runtime's `pruneToEpochBase()` drops history below the newest compact
   commit once the compaction has SETTLED (cut complete + every author's
   evidence at the epoch); the compact commit becomes a parent-free epoch
   base whose content id still verifies (hash covers the parent gid string
   + state fingerprint), `delta` ships it to unheard peers, `ingest` gates
   it by recomputation, and a pristine replica adopts the head, so fresh
   peers bootstrap at O(document). The hub prunes on persist and mirrors
   its store (`pruneStored`); the editor prunes on its slow tick and drops
   the same records from IndexedDB. This also RELIEVES edge A for readers:
   only authors pin the horizon now (their evidence gates the prune), and
   an author's returning chain descends from its evidence, hence from the
   base. `runtime/test/epochbase.test.js` + the pruning test in
   `test/hub.test.js` (pruned store survives a relay restart).
5. Invite links + local directory (`listDocs`, exists) for discovery (rooms
   exist too).
6. Keypair identity, signatures, payload encryption (edge D).
7. Then the harder runtime tasks: #90 recursive/multi-MCA merge, #97 concurrent
   divergent compaction, and the keep-set-vs-offline retention policy (edge A).
