# sal p2p-demo (task #95)

A peer-to-peer collaborative text editor built **on top of** the verified sal
runtime (`../runtime`). It shows the runtime's kernel-clean pieces -- commit-DAG
merge, the criss-cross gate, delta gossip, the certified stability cut, and the
state GC -- doing real work: several replicas edit one document over a real
network transport and converge, a replica's whole history is savable in a **git
repository** (point at the repo, get the doc), and certified GC fires *while the
session is live*.

Nothing in `../runtime/src` was modified; this package **imports** it. The only
new machinery here is glue: a SHA content-address, a git codec, a WebSocket
transport, and a browser UI.

```
npm install          # once (pulls `ws`, the relay's only dependency)
npm test             # 10 headless tests: node, git, transport, editor binding
npm run demo         # scripted multi-node scenario, prints a transcript
npm run relay        # serves the browser editor + the sync relay on one port
```

## What it demonstrates, and what is verified underneath

| Demo shows | Verified-underneath (see `../runtime/README.md`) | Demo glue (here) |
| --- | --- | --- |
| replicas converge to one doc | commit-DAG merge, LCA + criss-cross gate, delta/ingest content-address gate | the SHA id, the wire framing over WebSocket |
| GC fires mid-session, reads unchanged | `compactStable` = the evidence-frontier stability cut + `settledAt_of_allHeard`; `compactEliasDelta` re-coding | the settled **barrier** that linearizes epochs across peers |
| "point at a git repo, get the doc" | the run-table serializer (`serialize.js`), the coordinate representation | the git directory codec + fencing |
| a new peer clones and catches up | the same delta gossip that converges in-process | reconnect + fold over the transport |

The runtime's theorems are about the CRDT semantics (convergence up to `≈`, the
GC preserving reads under a certified cut). This demo does not re-prove them; it
exercises the JS runtime that mirrors them and asserts the observable
consequences (equal reads, reads unchanged by GC, git round-trip).

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

- **`src/node.js` -- the p2p replica.** A separate commit store (imported
  `Dag`) that unifies two things the runtime keeps apart: `sync.js`'s
  `Peer` (delta gossip: `ancestryGids`/`delta`/`ingest`/`mergeWithGid`) and
  `runtime.js`'s `Replica.compactStable` (certified state GC), which the
  separate-store `Peer` does not have. Every load-bearing primitive is imported
  (`lca`, `frontierOf`/`stableCut`/`insertIds`, `compactEliasDelta`,
  `serialize`). `test/node.test.js` cross-checks a `Node` against the reference
  `Peer` on the same op stream (identical reads + convergence), so this
  combination is pinned to the runtime, not merely plausible.

- **SHA content addressing (`src/hash.js`).** #95 asks the demo to swap the
  sync layer's model FNV hash for a real SHA. `Node` names every commit by the
  SHA-256 of its canonical content, a Merkle DAG (a commit's id folds in its
  parents'):
  `root = sha({root:true})`, `authored = sha({p,replica,seq,payload})`,
  `merge = sha({p: sorted parents})`, `compaction = sha({compact,p,fp})`. The
  same id names the same commit on **every** peer and **on disk**, so the wire
  dedups and git persistence content-addresses with one hash. The pure-JS
  SHA-256 is checked bit-for-bit against `node:crypto` (NIST vectors + random).

- **`src/gitstore.js` -- git persistence.** `persist(node, repoPath)` writes
  `commits/<sha>.json` (one per commit) + `heads.json` + a materialized
  `doc.txt`, then `git add && git commit` **in that repo**. `load(repoPath)`
  replays the commits into a fresh `Node` whose reads equal the original and
  which re-enters the live wire with identical shas. `git clone` of the repo
  therefore yields a self-contained, loadable document; because `doc.txt`
  changes when the doc changes, plain `git log -p` reads as sensible edit
  history.

- **`src/transport.js` -- the wire.** `WsTransport` carries the gossip over a
  WebSocket (browser and Node both use the global `WebSocket`). `NetworkNode`
  binds a `Node` to a transport and speaks `have`/`req`/`delta`. A `pull` is an
  awaited request/reply, giving the headless test a deterministic,
  criss-cross-free **linear fold** (`converge`). `barrierCompact` reaches a
  common compaction epoch across peers (below).

- **`src/relay.mjs` -- the server.** A `ws` relay that broadcasts within a room
  (or routes a `to:`-addressed message) and also serves the sal tree
  statically, so the browser editor imports the runtime ESM directly and the
  demo is one command.

- **`web/` -- the editor.** A textarea bound to an embed-RGA `Node`
  (`src/editbind.js` turns each edit into ins/del ops; `test/editbind.test.js`
  proves 400 random contiguous edits reproduce the target text). Panels show
  live convergence, the roster, the commit DAG, the certified stable cut, and a
  GC button.

## Certified GC across peers: the barrier

The runtime's `compactStable` re-codes coordinates and opens an **epoch**; a
cross-epoch merge is undefined in v1 (the runtime linearizes epochs; concurrent
divergent compaction is its deferred protocol half). In a p2p setting a single
peer compacting alone would diverge in epoch from the others. `barrierCompact`
keeps them together: after `converge`, every peer holds the same DAG but a
*different* certified cut (each excludes itself from the frontier meet). One
no-op **checkpoint** round fixes that -- once every peer has published a commit
that absorbed the whole converged history, each peer's frontier meet equals the
full pre-checkpoint history, identical across peers, so every peer's
`compactStable` computes the **identical** re-coding (same SHA) and the final
`converge` dedups them. That is the demo's honest "GC under live sync": the
certificate is the runtime's; the barrier is the demo linearizing epochs.

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
- **Compaction is linearized (the barrier).** Truly concurrent divergent
  compaction -- two peers compacting different cuts without a barrier, then
  merging across epochs -- is the runtime's own deferred protocol half. `Node`
  refuses a cross-epoch merge rather than guess.
- **Criss-cross merges are gated, not resolved.** Virtual-LCA (recursive merge
  of the maximal common ancestors, git-style) is runtime task #90. The
  deterministic linear fold (`converge`) stays inside the criss-cross-free
  regime; opportunistic browser merges catch a criss-cross and defer it.
- **Two hashes are consistent but not one.** The demo uses SHA everywhere; the
  reference `sync.js` still uses its FNV model hash. Unifying them means editing
  `runtime/src` (making the runtime gid = SHA), which #95 forbids. `Node` is the
  SHA-based version cross-checked against the FNV reference.
- **`embedRGA` is an unverified transliteration** of the verified embed kernel
  (see `../runtime/README.md`); the demo inherits that caveat.

## Files

```
src/hash.js        pure-JS SHA-256 + canonical content id  (checked vs node:crypto)
src/node.js        the p2p replica: SHA-addressed store + gossip + certified GC
src/gitstore.js    persist()/load() a Node to/from a git repo; git fencing
src/transport.js   WsTransport, NetworkNode, converge(), barrierCompact()
src/relay.mjs      ws relay + static server (npm run relay)
src/editbind.js    textarea-edit -> ins/del ops (browser-safe, tested)
web/index.html     the editor shell + panels
web/app.js         the browser editor logic
scripts/demo.mjs   the scripted scenario (npm run demo)
test/*.test.js     node, gitstore, integration, editbind (10 tests)
data/              (gitignored) any demo repos created here are SEPARATE git repos
```
