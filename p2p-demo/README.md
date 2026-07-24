# sal p2p-demo (task #95)

A peer-to-peer collaborative text editor built **on top of** the verified sal
runtime (`../runtime`). It shows the runtime's kernel-clean pieces -- commit-DAG
merge, the criss-cross gate, delta gossip, the certified stability cut, and the
state GC -- doing real work: several replicas edit one document over a real
network transport and converge, a replica's whole history is savable in a **git
repository** (point at the repo, get the doc), and certified GC fires *while the
session is live*.

This package **imports** the runtime. As of task #108 the p2p replica itself is
a first-class runtime object (`DistributedReplica` in `../runtime/src/replica.js`:
one SHA-addressed store with both wire sync and the certified GCs); the demo's
`Node` is a thin re-export of it, and the SHA content hash lives in the core
(`../runtime/src/hash.js`), shared by wire and disk. The only new machinery
**here** is the deployment skin: a git codec, a WebSocket transport, and a
browser UI.

```
npm install          # once (pulls `ws` for the relay + prosemirror-* for the rich-text editor)
npm test             # 46 headless tests: node, git, IndexedDB, transport, live push, reconnect, manual merge, auto-GC, forget, text + rich-text bindings, presence
npm run demo         # scripted multi-node scenario, prints a transcript
npm run relay        # serves the browser editor + the sync relay on one port
```

## What it demonstrates, and what is verified underneath

| Demo shows | Verified-underneath (see `../runtime/README.md`) | Demo glue (here) |
| --- | --- | --- |
| replicas converge to one doc | `DistributedReplica` delta gossip, LCA + criss-cross gate, delta/ingest content-address gate, the SHA content id | the wire framing over WebSocket |
| GC fires mid-session, reads unchanged | `compactStable` = the evidence-frontier stability cut + `settledAt_of_allHeard`; `compactEliasDelta` re-coding | the settled **barrier** that linearizes epochs across peers |
| "point at a git repo, get the doc" | the run-table serializer (`serialize.js`), the coordinate representation | the git directory codec + fencing |
| a new peer clones and catches up | the same delta gossip that converges in-process | reconnect + fold over the transport |

The runtime's theorems are about the CRDT semantics (convergence up to `≈`, the
GC preserving reads under a certified cut). This demo does not re-prove them; it
exercises the JS runtime that mirrors them and asserts the observable
consequences (equal reads, reads unchanged by GC, git round-trip).
`../whiteboard/verification-distance.md` is the layer-by-layer accounting of
how far the deployed editor sits from the proofs, what keeps each testing
bridge honest, and what would shrink the distance.

## Architecture

```
 browser tab            browser tab                 node process
 ┌──────────┐           ┌──────────┐                ┌──────────┐
 │ app.js   │           │ app.js   │                │ demo.mjs │
 │  Node    │           │  Node    │                │  Node×N  │
 │  (store) │           │  (store) │                │ (stores) │
 └────┬─────┘           └────┬─────┘                └────┬─────┘
      │ WsTransport (have/req/delta over WebSocket)      │
      └───────────────┬───────────────┬─────────────────┘
                      ▼               ▼
                 ┌─────────────────────────┐
                 │  relay.mjs (star relay)  │  broadcasts per room;
                 │  + static file server    │  serves the UI; never
                 └─────────────────────────┘  inspects the CRDT payload
```

- **`src/node.js` -- the p2p replica, a thin adapter.** `Node` is now just
  `DistributedReplica` (`../runtime/src/replica.js`) with the demo's historical
  defaults (the embed RGA, name `n0`). The runtime's first-class object is the
  fold that used to live here: ONE content-addressed store that has BOTH the
  delta gossip (`ancestryGids`/`delta`/`ingest`/`mergeWithGid`) sync.js's `Peer`
  had and the certified state GC (`compactStable`) runtime.js's `Replica` had,
  plus the keep-set commit GC, datatype-parametric. `test/node.test.js` pins the
  demo surface (SHA re-export, wire convergence, compaction refuse/fire); the
  parametric core coverage (embed **and** orset) is in
  `../runtime/test/replica.test.js`.

- **SHA content addressing (`src/hash.js` -> `../runtime/src/hash.js`).** #108
  moved the content hash into the core and unified it. `DistributedReplica`
  (hence `Node`) names every commit by the SHA-256 of its canonical content, a
  Merkle DAG (a commit's id folds in its parents'):
  `root = sha({root:true})`, `authored = sha({p,replica,seq,payload})`,
  `merge = sha({p: sorted parents})`, `compaction = sha({compact,p,fp})`. The
  same id names the same commit on **every** peer and **on disk**, so the wire
  dedups and git persistence content-addresses with **one** hash -- the FNV/SHA
  seam is gone (`sync.js`'s `Peer` uses the same core hash now). The demo's
  `src/hash.js` is a thin re-export of the core; the pure-JS SHA-256 is checked
  bit-for-bit against `node:crypto` (NIST vectors + random) in the runtime.

- **Download `.saldoc.json` -- the doc as one JSON file.** The editor's
  `download .saldoc` button exports the replica's WHOLE commit DAG (records
  + heads, wire SHAs) as plain JSON; `scripts/bundle2git.mjs <file> --repo
  <path>` turns it into the git repo below. Works against ANY relay
  (including the deployed one): the export is built client-side from the
  tab's own replica. Full history rides along: deleted text and authorship
  are recoverable from a bundle, so share it as you would share history,
  not as you would share a rendered document.

- **`scripts/doc2git.mjs` -- push YOUR live doc to a git repo.** A headless
  peer joins the room, pulls the document from whoever is online (your open
  browser tab; the relay is stateless), and persists it via `gitstore.js`:
  `node scripts/doc2git.mjs --room <room> --repo <path>` (add `--plain` for
  plain-text rooms, `--relay wss://...` for a deployed relay). The target
  repo is then plain git: add a remote and push. The script authors nothing,
  so the roster hygiene drops it on disconnect (it never blocks certified
  GC).

- **`src/gitstore.js` -- git persistence.** `persist(node, repoPath)` writes
  `commits/<sha>.json` (one per commit) + `heads.json` + a materialized
  `doc.txt`, then `git add && git commit` **in that repo**. `load(repoPath)`
  replays the commits into a fresh `Node` whose reads equal the original and
  which re-enters the live wire with identical shas. `git clone` of the repo
  therefore yields a self-contained, loadable document; because `doc.txt`
  changes when the doc changes, plain `git log -p` reads as sensible edit
  history.

- **`src/idbstore.js` -- the browser sibling of git persistence, WIRED IN.**
  `gitstore.js` shells out to `git` and cannot run in a browser tab, so the
  shared record shape + rebuild now live in the browser-safe `src/records.js`
  (the durable format IS the wire format; gitstore re-exports for compat).
  `RefStore` persists those records into IndexedDB over a tiny async KV
  (`MemoryKV` for headless tests, `openIdbKV()` in the browser); same
  content-address gate: a tampered stored record is rejected on load. The
  RICH-TEXT EDITOR uses it (local-first): load-before-connect keyed by room
  (top-level await, so the doc is on screen before any peer answers),
  re-persist on every head change (gid-guarded, idempotent puts), a
  `local store: restored N` chip, and reopening under a new session name
  keeps history + roster while starting a fresh authoring seq
  (`rebuildNode` opts). Browser-verified: edit, reload, doc restored from
  IndexedDB alone (the relay is stateless); edit again, reload, both edits
  restored. See `whiteboard/collab-design-note.md` section 7.1.

- **`src/transport.js` -- the wire.** `WsTransport` carries the gossip over a
  WebSocket (browser and Node both use the global `WebSocket`). `NetworkNode`
  binds a `Node` to a transport and speaks `have`/`req`/`delta`. A `pull` is an
  awaited request/reply, giving the headless test a deterministic,
  criss-cross-free **linear fold** (`converge`). `barrierCompact` reaches a
  common compaction epoch across peers (below). In active mode a `have`
  advertising a head outside my ancestry triggers a `req` back at the
  announcer (pull-on-have), so a lone typist's edits reach idle peers; passive
  mode stays pure-pull so `converge` remains deterministic
  (`test/livepush.test.js` pins both).

- **`src/hub.js` -- the SYNC HUB (design-note step 4): docs survive
  disconnects.** One headless replica per room, living with the relay,
  speaking the SAME have/req/delta protocol as any peer and persisting
  through a RefStore (MemoryKV locally, Durable Object storage in the cloud;
  debounced, content-addressed). A peer pushes and leaves; a later peer
  joins an empty room and catches up from the hub alone -- previously
  impossible (the stateless-relay FAIL shape is pinned). INVISIBLE by
  construction: never sends `join`, never authors, never broadcasts
  presence, so clients never roster it and it cannot block the certified
  GC or compete for auto-GC leadership. The datatype label rides the join
  message (`dt`); a restored hub trusts its STORED label (a hibernated
  Durable Object can wake on any message). `test/hub.test.js`:
  availability, the hubless FAIL companion, store-outlives-process
  durability, peritext marks; verified LIVE against the deployed Durable
  Object (author pushes, disconnects; a later reader converges).

  (Epoch-base HISTORY PRUNING on the hub is temporarily DEFERRED: it was
  built on the old integer-epoch model and needs a re-port onto the #112
  cut-keyed epoch DAG. The hub's persist path keeps the guarded call site.)

- **`src/relay.mjs` -- the server.** A `ws` relay that broadcasts within a room
  (or routes a `to:`-addressed message) and also serves the sal tree
  statically, so the browser editor imports the runtime ESM directly and the
  demo is one command.

- **`web/` -- the editors.** `web/app.js` is the plain-text editor: a textarea
  bound to an embed-RGA `Node` (`src/editbind.js` turns each edit into ins/del
  ops; `test/editbind.test.js` proves 400 random contiguous edits reproduce the
  target text). Panels show live convergence, the roster, the commit DAG, the
  certified stable cut, and a GC button.

- **`web/richtext.js` -- the RICH-TEXT editor (task #107).** A PROSEMIRROR view
  over the verified Peritext datatype: one directly-edited surface (typing,
  Enter, paste; Bold/Italic/Underline, links, comments via toolbar or
  Cmd/Ctrl+B/I/U/K), no preview pane. ProseMirror owns the DOM (caret, IME,
  block structure); the datatype owns the truth: every transaction is diffed
  into ops by `src/peritextbind.js` (a text edit -> ins/del; a format gesture
  -> one addMark/removeMark; toggling off emits the LWW-winning removeMark),
  the marks analog of `editbind.js`, headless-tested in
  `test/peritextbind.test.js` (including Ex7 end-side growth and mark survival
  across a delete). After each local transaction the PM doc is reconciled
  against `read()`: on mark-boundary questions (does a char typed at a span
  edge inherit bold?) the verified semantics win. The full mark surface:
  bold/italic/underline are growing boolean marks; a LINK is a value mark with
  the exclusive (never-growing) end gravity (Ex8); a COMMENT is one mtype per
  comment (`comment:<id>`, note in `value`), so OVERLAPPING comments coexist
  under the per-(char,mtype) LWW (pinned in the runtime's
  `test/peritext.test.js` comments block; PM side uses a `comment` mark with
  `excludes:''`). The doc model is flat (chars + `\n`); PM paragraphs are
  presentation (`flatToPm`/`pmToFlat`). ProseMirror loads as plain ESM via an
  import map into `node_modules` -- still no bundler. Commit granularity is a
  TYPING RUN, not a keystroke: local ops buffer in a DEBOUNCED queue while the
  editor renders the speculative state (`specRead`: head + pending, one
  transient `applyBatch` pass), and a flush (300ms idle OR a 1s max-latency
  deadline so a continuous typist still syncs, blur, tab-hide -- browsers
  freeze hidden tabs' timers -- before a format gesture or a manual merge, on
  unload) seals the buffer as ONE group-op commit (`node.commitBatch`) and
  announces once. Pending ops are
  self-contained CRDT ops, so a remote merge landing mid-buffer is harmless.
  A paste is likewise one commit. Pinned in `test/peritextbind.test.js`
  (buffered run == per-keystroke twin, one commit vs five) and runtime
  `test/commitbatch.test.js`. The header names WHICH doc (the room id, a
  large title) and WHO is editing (the display name), and a DOC SWITCHER
  makes the "docs are rooms" model visible: a picker of the docs saved in
  this browser (`RefStore.listDocs`) and a `+ New doc` field that slugifies
  a name and opens it. There is no rename of a DOC (a doc is identified by
  its name); switching or creating navigates, carrying the display name.
  TWO-LEVEL IDENTITY: the human DISPLAY name (editable, remembered in
  `localStorage`, kept out of shared URLs via `replaceState`) is separate
  from the REPLICA id, which is `display~<session>` and UNIQUE PER SESSION.
  Two tabs (or devices) that share a display name are therefore distinct
  CRDT replicas -- a shared replica id would mean colliding `seq`/event keys
  and a corrupt frontier. The roster shows the display name and
  disambiguates duplicates with the session tag (`kc-laptop·b6e9`).

- **`src/presence.js` -- PRESENCE (task #107).** Ephemeral, OFF-DAG peer
  awareness: live cursors/selections + identity, broadcast as plain `presence`
  room messages over the same transport, never committed, merged, or persisted.
  A pure registry (ttl prune, stable per-peer color) tested in
  `test/presence.test.js`; `web/richtext.js` renders peers as ProseMirror
  DECORATIONS (inline highlights for selections, caret widgets with name
  flags).

- **Reconnect (zombie-tab fix).** Browsers close the sockets of tabs that sit
  in the background; before, the page kept saying "connected" while every send
  was silently dropped. `WsTransport` now detects the drop (`down`), rejoins
  with backoff (`up`), and `NetworkNode` re-announces on `up`, which catches up
  BOTH directions (peers top me up; my advertised head triggers their
  pull-on-have). The relay pings clients and terminates the unresponsive
  (broadcasting their `leave`). Pinned in `test/reconnect.test.js`, including
  edits made on both sides DURING the outage.

- **CERTIFIED GC IN THE RICH-TEXT EDITOR.** The editor runs on
  `compactiblePeritext` (the marks-layer GC of #110, with a `symbolCount`
  probe over the embed shadow), shows a METADATA-COST panel (visible chars vs
  tombstones, mark records, coordinate symbols, encoded-state bytes, commits,
  wire-summary size, epoch, stable-cut status), and has a `run certified GC`
  button: enabled only when the stability cut is complete (evidence from
  every registered peer), it fires `compactStable`, preserves reads, and
  advances the epoch. Epochs are linearized: each peer GCs in turn (a
  peer that converged before compacting fast-forwards onto the compacted
  chain). CONVERGENCE GATE: every compaction path (the button, auto-GC, and
  the forget-triggered reclaim) refuses unless this peer is CONVERGED with
  every peer it tracks (`convergedWithPeers`: all known heads equal mine, or
  solo). Compacting while diverged would open a new epoch on a divergent
  branch, and a cross-epoch merge is refused (the runtime linearizes epochs),
  so the two peers could never reconcile -- the "why is the text different"
  failure. Gated on convergence, the leader compacts and everyone else
  fast-forwards onto the identical compact commit (converged peers even
  compute the same compact SHA, so simultaneous firing dedups instead of
  splitting). ROSTER HYGIENE: a peer that leaves WITHOUT ever authoring a commit
  is dropped from the roster (`replica.unregister`, wired to the transport's
  `leave`), else a drive-by visitor would block the stability cut forever; a
  departed WRITER stays registered conservatively (the GC-horizon vs
  offline-peers edge, design note 8A). `test/roster.test.js` pins both plus
  the full block -> leave -> barrier-compact cycle. Browser-measured on a 57-char doc with 22 tombstones: 49231→1803
  coordinate symbols, 50719→2830 state bytes, tombstones to 0, the bold's
  mark record retained.

- **LIVENESS-AWARE ROSTER + FORGET (the departed-writer stall).** A departed
  writer stays registered (above), so its frontier evidence PINS the GC
  horizon at its last-synced position: nothing typed since can be reclaimed.
  The roster line marks each peer live (green) or DARK (grey, absent from
  presence), and a dark peer carries a `✕ forget`. Forgetting calls
  `replica.forget` (drops it from BOTH the roster and the authors set, unlike
  the conservative `unregister`), which releases the horizon so the cut rises
  and GC advances. SOUNDNESS is the operator's to grant: a forgotten peer that
  returns must re-sync fresh (forfeiting un-shared offline edits), not merge a
  stale-head delta. Runtime-pinned in `runtime/test/forget.test.js` ("forget
  lifts a departed author": the cut is capped while the dark author is
  rostered, then GC fires after the forget, reads preserved).

- Links render as real anchors and OPEN with Cmd/Ctrl+Click (plain clicks
  keep editing; contentEditable swallows them). Only http(s) hrefs are
  emitted (no script-scheme vectors); bare `example.org` input is normalized
  to `https://`.

- **MANUAL MERGE (git-style explicit sync).** `NetworkNode` has two merge
  policies. Auto (default): every received delta merges immediately (live
  co-editing). Manual: deltas are still FETCHED eagerly (`ingest`:
  content-addressed, head untouched -- `git fetch`) but `mergeWithGid`
  (`git merge`) waits for `mergeStaged()`; the editor's `merge: auto/manual`
  toggle and `merge ⤵ N` button drive it. Because `merge3` is total there is
  never a conflict prompt; manual is a consent/review policy, not a safety
  one. The staged merge needs no network (the commits are already local), so
  review-then-merge works OFFLINE; an awaited `pull()` is an explicit sync and
  always merges. Pinned in `test/manualmerge.test.js`.

- **Cloudflare deployment (`../deploy/cloudflare/`).** One Worker serves the
  static tree and routes WebSocket upgrades to a DURABLE OBJECT per room, the
  serverless twin of `relay.mjs` (same protocol; hibernation-friendly, so idle
  rooms cost nothing on the free plan). `WsTransport` sends `?room=` on the
  upgrade URL so the Worker can pick the DO before any message arrives, and
  speaks `wss://` under https. `./build.sh && npx wrangler deploy`.

## Certified GC across peers: the barrier

The runtime's `compactStable` re-codes coordinates and opens an **epoch**.
Cross-epoch merge is now the certificate-determined JOIN (#112 phase 3, the
mechanized epoch diamond): two heads at different cuts merge by lifting to a
common frame, so a peer compacting alone no longer strands the others. `barrierCompact`
keeps them together: after `converge`, every peer holds the same DAG but a
*different* certified cut (each excludes itself from the frontier meet). One
no-op **checkpoint** round fixes that -- once every peer has published a commit
that absorbed the whole converged history, each peer's frontier meet equals the
full pre-checkpoint history, identical across peers, so every peer's
`compactStable` computes the **identical** re-coding (same SHA) and the final
`converge` dedups them. That is the demo's honest "GC under live sync": the
certificate is the runtime's; the barrier is the demo linearizing epochs.

## Epoch-base pruning: history is not forever (DEFERRED)

Epoch-base history pruning -- dropping commits below a settled compaction and
turning it into a parent-free base so a fresh peer bootstraps at O(document) --
was implemented on the OLD integer-epoch model. The #112 merge replaced that
model with the cut-keyed epoch DAG, whose content-addressing does not (yet)
support the parent-less-compact base trick the pruning relied on. Pruning is
therefore temporarily REMOVED pending a re-port onto the new model (coordinated
with the epoch-DAG owner). The guarded call sites remain (hub persist, editor
tick), so it re-enables cleanly once `pruneToEpochBase` returns.

## Running each stage

**Stage 1 (git, headless):**
```
node --test test/gitstore.test.js
```
builds a doc, persists to a fresh repo, `git clone`s it, loads the clone (reads
equal), edits + persists, and asserts `git log`/`git show` report `doc.txt`
changing. The fencing test asserts the sal repo is refused.

**Stage 2 (transport, headless -- the headline):**
```
node --test test/integration.test.js
```
starts the relay, spins up 3 nodes over real WebSockets, applies concurrent
random edits and gossips to convergence, fires certified GC under sync, then
persists one node, `git clone`s + loads it as a 4th node, reconnects it, and
asserts it catches up. See the exact assertions at the bottom.

**Stage 3 (browser):**
```
npm run relay          # prints http://127.0.0.1:8787/
```
open that URL in two or more tabs/windows (add `?room=NAME` to pick a room).
Type in one; the others converge. The GC button runs a certified
`compactStable` on that tab (state size drops, reads preserved) with an honest
note that other tabs stay at their epoch until they also GC.

**Stage 4:**
```
npm run demo
```
the scripted scenario below.

## Sample `npm run demo` transcript

```
==== 3. CONCURRENT edits: bob appends, carol inserts at the front ======
   before sync: bob="Hello, world"  carol=">> Hello"
   alice  reads: ">> Hello, world"
   bob    reads: ">> Hello, world"
   carol  reads: ">> Hello, world"
   -> all 3 peers converged to one document.
==== 4. certified GC UNDER LIVE SYNC (compactStable at a settled barrier)
   live coordinate symbols per peer (state size): [105, 105, 105]
   alice  compact: true  symbols 105 -> 93  (epoch 1)
   ...
   reads unchanged by GC: true  (certified, reads preserved)
   all peers on the identical compacted head SHA: true
==== 6. git CLONE -> load a NEW peer -> reconnect -> catch up ==========
   cloned + loaded 'dave' from git: reads ">> Hello, world"  (== live doc: true)
   dave reconnected and caught up: ">> Hello, world!"  (converged: true)
```

## Honest limits (what a production p2p would still need)

- **Relay, not mesh.** Every message hops through `relay.mjs`. It gives reliable
  ordered delivery and trivial NAT traversal (what a demo needs), but it is a
  star, not peer-to-peer at the network layer. The `Transport` interface is
  shaped so a WebRTC data-channel mesh could implement the same
  `send`/`sendTo`/`on` shape and drop in under `NetworkNode` unchanged. Signaling,
  ICE, and reconnection/backoff are out of scope.
- **No auth.** The relay trusts whoever connects and whatever name they claim.
  A real deployment needs authenticated identities (the replica id must be a
  key, not a string), and the content-address SHA gate bounds *tampering with a
  commit's content* but not *who is allowed to author*.
- **Open membership is cooperative.** The roster is the room's join set, which
  is the closed replica set the stability certificate quantifies over. Eviction,
  Byzantine members, and members who never settle (blocking GC forever) are not
  handled; a real system needs a membership protocol and a liveness policy.
- **Cross-epoch merge is the certificate-determined JOIN (#112 phase 3).**
  Two peers compacting different cuts and then merging across epochs no longer
  throws: the mechanized epoch diamond (`runtime/src/epoch.js`,
  `Sal/.../EmbedRGA_EpochDiamond.lean`) lifts both heads to a common frame and
  merges there. The editor still prefers to compact only when converged (a
  policy, not a necessity now).
- **Criss-cross merges are RESOLVED (virtual LCAs, #90 landed).**
  `DistributedReplica` now computes the virtual base for a criss-crossed
  pair by the mechanized recursive rule (runtime README; pinned in
  `../runtime/test/virtual-lca.test.js`), so opportunistic browser merges
  no longer defer on criss-crosses (the transport's defer path remains for
  cross-epoch merges only). The deterministic linear fold (`converge`)
  still stays inside the criss-cross-free regime by construction.
- **`embedRGA` is an unverified transliteration** of the verified embed kernel
  (see `../runtime/README.md`); the demo inherits that caveat.

## Files

```
src/hash.js        re-export of the core content hash (../runtime/src/hash.js)
src/node.js        thin adapter: Node = DistributedReplica with the demo defaults
src/gitstore.js    persist()/load() a Node to/from a git repo; git fencing
src/records.js     the persistence record shape + rebuild (browser-safe; wire == durable)
src/idbstore.js    RefStore over IndexedDB (browser durable store, wired into the editor)
src/transport.js   WsTransport, NetworkNode, converge(), barrierCompact()
src/relay.mjs      ws relay + static server (npm run relay)
src/editbind.js    textarea-edit -> ins/del ops (browser-safe, tested)
src/peritextbind.js rich-text gestures -> ins/del/addMark/removeMark, batched (tested, #107)
src/presence.js    ephemeral off-DAG peer cursors/selections registry (tested, #107)
web/index.html     the plain-text editor shell + panels
web/app.js         the plain-text browser editor logic
web/richtext.html  the rich-text editor shell (toolbar + import map for prosemirror ESM)
web/richtext.js    the ProseMirror <-> Peritext binding (#107)
scripts/demo.mjs   the scripted scenario (npm run demo)
test/*.test.js     node, gitstore, idbstore, integration, livepush, reconnect, manualmerge, autogc, hub, editbind, peritextbind, presence (46 tests)
data/              (gitignored) any demo repos created here are SEPARATE git repos
```
