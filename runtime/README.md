# sal-runtime

A git-like commit-DAG MRDT runtime: pluggable
datatypes over a shared commit store, three-way merges through the DAG's
LCA, and the keep-set commit GC from the verified design. Pure
dependency-free ESM; runs in the browser and in Node unchanged (no
Node-only APIs in `src/`).

## API

```js
import { Runtime } from './src/runtime.js';
import { embedRGA } from './src/datatypes/embedRGA.js';

const rt = new Runtime(embedRGA);      // root commit holds datatype.init()
const a = rt.replica('A');
const b = rt.replica('B');

a.commit({ type: 'ins', id: 1, el: 'x', anchorId: null }); // op on OWN head
b.sync(a);                              // join the two CURRENT heads
a.read();                               // datatype read of a's head state
rt.gc();                                // keep-set commit GC -> { kept, dropped }
a.compactStable();                      // certified state GC (needs a compactible
                                        // datatype); { compacted, ... } or
                                        // { compacted: false, missing } if the
                                        // evidence certificate is absent
```

```js
// Separate stores over the wire (src/sync.js):
import { Peer, syncPeers } from './src/sync.js';
const p = new Peer(embedRGA, 'A'), q = new Peer(embedRGA, 'B');
p.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
syncPeers(p, q);                        // exchange deltas + converge; reports payload bytes
```

```js
// The first-class distributed replica (src/replica.js): one SHA-addressed store
// with BOTH wire sync and the certified GCs, datatype-parametric.
import { DistributedReplica, syncReplicas } from './src/replica.js';
const a = new DistributedReplica(embedRGA, 'A');  // datatype defaults to compactibleEmbedRGA
const b = new DistributedReplica(embedRGA, 'B');
a.register('B'); b.register('A');
a.commit({ type: 'ins', id: 1, el: 'x', anchorId: null });
syncReplicas(a, b);                     // delta gossip + converge (SHA content-ids)
a.compactStable();                      // certified state GC (compactible datatypes)
a.gc();                                 // keep-set commit GC over its own DAG
```

- `src/dag.js` -- commit store. A commit is
  `{ id, parents: [ids], op, state }`, `op = { replica, seq, payload }` or
  `null` for merge commits (and the root). Ancestry defines the event set
  implicitly: `dag.events(id)` returns the ops along the reflexive ancestor
  closure `dag.ancestorSet(id)`; `dag.isAncestor(a, b)` is the subsumption
  check (upward BFS, early exit).
- `src/lca.js` -- `mcas(dag, a, b)` returns ALL maximal common ancestors;
  `lca(dag, a, b)` returns the unique one or throws (see the criss-cross
  gate below).
- `src/runtime.js` -- replicas enforcing head-sync by construction: the
  only mutators are `commit(payload)` (on your own head) and `sync(other)`
  (join of the two current heads: fast-forward when one head subsumes the
  other, else a merge commit whose state is
  `datatype.merge3(lcaState, aState, bState)`). After `sync` BOTH replicas
  point at the join. Replica heads are private fields; there is no API to
  point a replica at an arbitrary commit.
- `src/gc.js` -- `keepSet` / `runGc`: seeds = all pairwise MCAs of the
  current heads (i = j included, so every head is a seed); Keep = the
  reflexive upward (descendant) closure of the seeds; everything else is
  dropped. Surviving commits may then reference pruned parents; DAG
  traversals skip them (ancestry truncated at the GC horizon).
- `src/frontier.js` -- THE ONE FRONTIER. `frontierOf(dag, head)`
  gives, per replica, its latest absorbed commit (its *evidence commit*);
  `stableCut(dag, head, registered, self)` intersects those event sets into
  the largest cut this head can certify. Its direct no-GC refinement is proved
  in `Sal/MRDTs/GC/Refinement.lean`.
- `src/sync.js` -- the delta/op WIRE protocol: content-
  addressed `Peer`s over SEPARATE stores exchange head frontiers and ship the
  ancestor-set difference as a delta, converging by merge (see below).
- `src/hash.js` -- THE CONTENT HASH. A pure-JS SHA-256 (checked
  bit-for-bit against `node:crypto`) and `commitContentId`, the single
  Merkle-DAG derivation every content-addressed store mints commit ids through
  (`hash` argument pluggable, default the SHA), so WIRE and DISK name the same
  commit the same way.
- `src/replica.js` -- THE FIRST-CLASS DISTRIBUTED REPLICA:
  `DistributedReplica`, ONE content-addressed store with BOTH wire sync AND the
  certified state GC (plus the keep-set commit GC), datatype-parametric (see
  below). It unifies the two-store split (`Replica` = GC-but-no-wire, `Peer` =
  wire-but-no-GC) into one object; the p2p demo's `Node` is a thin
  re-export of it.
- `src/pmap.js` -- THE STATE CONTAINER. `PMap`/`PSet`, a
  dependency-free browser-safe persistent HAMT: `set`/`delete` return a new
  map in O(log n) by path copy with structural sharing, avoiding the
  O(live-set)-copy-per-op that a `new Map(state)`-per-keystroke container
  would pay. Public iteration (`entries`/`keys`/`values`/iterator) is
  DETERMINISTIC (sorted by key), so no consumer can depend on hash order;
  `forEachRaw` is the hash-order escape hatch for order-insensitive bulk
  scans only. Transients (`begin()`/`freeze()`) give the batch-build fast
  path; each datatype exposes `applyBatch(state, ops)` over one transient
  pass, proven equal to folding `apply` (`test/applybatch.test.js`).
  Observables (reads, fingerprints, SHA content ids, serialized bytes) are
  byte-identical to the Map-backed representation. `test/pmap.test.js` is
  the randomized Map-equivalence / structural-sharing / collision suite.

A datatype is `{ init, apply(state, op), merge3(l, a, b), read(state) }`,
all pure (`apply`/`merge3` return fresh states: commits keep old states;
"fresh" is O(log n) structural sharing over `src/pmap.js`,
and `merge3` on persistent states is a delta merge from one parent).
The bundled datatypes also expose an optional `fingerprint(state)` used by
the twin tests, and `embedRGA` adds `readIds`/`readEntries`/`symbolCount`,
`orset` adds `observe` (helpers for honest op construction and cost probes).
THREE datatypes ship: `embedRGA` (a sequence), `orset` (a set), and
`peritext` (rich text = the verified document-order mark model over
`embedRGA`, see its own section below).

## Peritext: verified document-order rich text over embedRGA

`src/datatypes/peritext.js` is the THIRD datatype: rich text, built as the
Lean-verified DOCUMENT-ORDER mark read model layered on the sequence datatype.
It plugs into `DistributedReplica` over the same `{init, apply, merge3, read}`
contract as `embedRGA`/`orset`, so rich text gets delta gossip + SHA content
addressing + commit GC with NO Peritext-specific runtime code: the whole
datatype is the only new piece (the parametricity payoff, proven directly in
`test/peritext.test.js`).

- STATE `= { text: { shadow, deleted }, marks }`. `text.shadow` is an
  insert-only `embedRGA` state holding every character (birth order + reading
  order, reused verbatim: insert, reading order, and merge all delegate to
  `embedRGA`); `text.deleted` is a grow-only set of logically deleted ids;
  `marks` is a map (`PMap`) `mid → { mtype, value, startId, endId, startSide, endSide,
  ts, removed }`. This is `DocD` from the verified spec: a delete is LOGICAL
  (the birth is kept), because the resolver rehomes a dead boundary anchor to
  its nearest surviving neighbour *in reading order*, which needs the dead
  anchor's birth position. `live = birth order minus deleted` (the embed
  capstone's P3).
- OPS: character `{type:'ins'|'del'}` (delegated to `embedRGA` on the shadow /
  the deleted set); mark `{type:'addMark'|'removeMark', mid, mtype, value,
  startId, endId, startSide, endSide, ts}`. A `removeMark` is a first-class
  negative mark (`removed:true`); per `(char, mtype)` last-writer-wins by `mid`
  resolves add-vs-remove at READ time.
- `merge3`: text births by `embedRGA.merge3` (union of insert-only shadows),
  deletes by union (delete-wins), marks by union on `mid` (a grow-only G-map;
  `mid` is globally unique). `read` = `renderMarksDoc`: characters in reading
  order each paired with their active mark set; a dead boundary anchor rehomes
  to the nearest survivor on its gravity side, GROWTH IS END-SIDE ONLY (an
  `endSide=after` end grows right over the newer-than-mark run; a `before` start
  is stable).
- MATCHES THE VERIFIED MODEL in
  `Sal/MRDTs/Instances/PeritextRender.lean`
  (`doc_no_backward_leak`, `doc_delete_can_respan`, the Ex1–8 renderings).
  `test/peritext.test.js` pins the Ex1–8 paper examples, the directed
  no-backward-leak (delete a bold start anchor; the boundary rehomes forward,
  earlier text stays plain, never a backward tree-ancestry leak),
  the gravity contrast (bold grows at its end, a link does not), the honest
  atomicity re-span (`doc_delete_can_respan`), and mark-permutation convergence,
  each PASS with a `≠` FAIL companion. Expected values are reviewed fixtures,
  never read back from the JS implementation.
- STATE COMPACTION FIRES for `compactiblePeritext`: the marks-layer GC of
  `src/compact-peritext.js`, whose obligations are mechanized in
  `Sal/MRDTs/Instances/PeritextRenderGC.lean` and
  `Sal/MRDTs/Instances/PeritextMarkPairGC.lean`. The keep-set is live ids ∪
  mark boundary anchor ids ∪ declared in-flight anchors: retained dead anchors
  survive as re-coded dead records (still listed in `deleted`), so rehoming
  never loses a birth position; every other settled-dead record drops exactly
  as for plain `embedRGA` (same `compactEliasDelta` machinery, same certified
  cut and skipped-group guard, with the peritext refinement that a record is
  freed only once its DELETE is settled, not just its insert). On top, the A3
  guarded pair-drop removes an (add, remove) pair with equal boundary tuples
  and frees its retention roots under three guards (removal settled; no other
  same-mtype mark below the remove's mid, declared in-flight marks included;
  no id inside the growth window). Blind pruning demonstrably flips reads (the
  `noRetention`/`unguardedPairDrop` negative
  controls); the plain hookless `peritext` object refuses.
  `test/peritext-gc.test.js` carries the directed PASS+FAIL family and a
  multi-epoch twin PBT against a never-compacted control; cost measured there:
  retained dead records ≤ 2 per mark record (structural bound, met with max
  2.000). `encodeState`/`decodeState` give the lossless snapshot round-trip
  (also carrying compaction commits over the wire).

WHAT THE EDITOR STILL NEEDS on top of this datatype: an
EDITOR-WIDGET BINDING (a ProseMirror/CodeMirror-style view that maps
`read()`'s `[{id, char, marks}]` to rendered spans and maps user
keystrokes/formatting gestures back to `ins`/`del`/`addMark`/`removeMark` ops
on a `DistributedReplica`), and PRESENCE (live cursors/selections and peer
identity, ephemeral off-DAG state carried alongside the document, not a CRDT
op). Everything below the widget (convergence, persistence, catch-up) is the
runtime the datatype already rides on.

## The delta code is pluggable; the default is the verified Elias-delta

`embedRGA` coordinates are chains of codewords of an order-preserving
prefix-free DELTA code, and the datatype is parametric in it:
`makeEmbedRGA(code)` takes `{ name, enc(delta) -> bit-string }`. Two codes
ship:

- `eliasDeltaCode` (the DEFAULT, used by the exported `embedRGA`): the
  flipped Elias-delta code transliterated from the verified Lean instance
  by `Sal/MRDTs/Instances/RGAKernel/BinaryCode.lean`
  (`dEnc d = binEnc (size d) ++ (d minus its leading bit)`, header `binEnc`
  from `Embed_Code_Binary.lean`); codeword cost `log2 d + O(log log d)`.
  The kernel-checked example values from that file are pinned in
  `test/code.test.js` (Lean `List Bool` mapped `false -> '0'`,
  `true -> '1'`, MSB first; the comparator's `'2'` sentinel is not part of
  any codeword).
- `unaryCode` (`enc(d) = '1'^d '0'`), retained for readability in examples
  and for the invariance tests. Its cost is linear in the delta, and
  cross-replica Lamport deltas grow with the GLOBAL op count, so unary
  coordinates grow linearly with history: fine for semantics, not the
  design's measured cost point.

Reads are code-invariant (the Lean theorems are parametric in the
`OrderedPrefixCode` structure); `test/code.test.js` checks this executably
(all directed fixtures plus 100 randomized head-sync runs under both
codes) and measures the cost gap on a growing-delta workload (200
interleaved root-anchored ops: unary 20300 vs eliasDelta 2283 total
coordinate symbols, ~8.9x).

## State GC: compactEliasDelta

`src/compact.js` implements the state-level GC of the embed RGA as a pure
function `compactEliasDelta(state, cut, opts) -> { state', translate,
stats }` over the stable coordinate tree: dead ranges below the cut with
no live descendants and no known in-flight coordinates through them
vanish; every settled sibling group with no known in-flight children
rank-renumbers its deltas to ordinals `1..k` (order preserved, re-encoded
with `eliasDeltaCode`); groups with known in-flight children are SKIPPED
for the epoch (dense renumbering against a frozen in-flight delta can
flip an order; the negative-control test demonstrates the flip via the
`unguardedRenumber` knob, which must never be set in production). The
returned `translate` is the lazy stable-prefix map
`rho-hat(c) = rho(stab c) ++ rest c`.

SPINE FUSION (opt-in via `opts.fuseSpines`). A fusible spine is a
maximal chain of dead below-cut nodes, each with exactly one child branch
counting every known coordinate INCLUDING declared in-flight prefixes,
and no in-flight op anchored at any spine node; it collapses to ONE level
at the spine head's group codeword, so a typing-run-then-delete chain of
depth k costs one codeword instead of k. One `translate` covers
renumbering and fusion together. Order survives by the three-class H2
argument (within-block prefix replaced wholesale; block-vs-sibling
decided at the head's level, whose codeword fusion keeps; no key ends at
a fused-away level since spine nodes are dead). THE GUARD is
conservative: any known in-flight branch or anchor at a spine node blocks
that node from every spine (`stats.spinesSkippedInflight`); through
traffic below the spine still fuses, the frozen tail translated verbatim.
`test/fusion.test.js` pins each H2 class directed, the guard, ingest
translation through a fused spine, and a 120-trial twin PBT (fusion on,
per-step reads vs an uncompacted control; a run reports ~129 spines
fused, ~182 levels removed, 0 guard skips under settled cuts).

Measured on the josephg editing traces
(`benchmarks/models/embed_compact_measure.py`, which mirrors the fusion
map and re-checks history-independence three ways plus display order on
the fused coordinates), bits per live char, before / renumber-only /
renumber+fusion: automerge-paper 2304 / 2076 / 1279 (1.8x), seph-blog1
2975 / 2310 / 917 (3.2x), friendsforever 1623 / 906 / 856 (1.9x),
clownschool 2489 / 1472 / 1471 (1.7x). HONEST VERDICT: the fused column
does land on the code cost of the live tree shape (the surviving DEAD
levels cost only 3-76 bits/char), but that live-shape cost is NOT "a few
bits/char": 97-99.8% of the remaining bits are LIVE ancestor levels
(mean live depth 835-1468 levels/coordinate), the intrinsic cost of
immutable chain coordinates over deep live anchoring runs, which no
dead-level GC can touch. The next lever is re-coding LIVE runs (a
representation change, not an epoch map).

The runtime hook is `replica.compact(cut)` (needs a datatype with
`compact` + `remapState`; `compactibleEmbedRGA` in `src/compact.js`
provides both). Each compaction opens an EPOCH; merges lift the
lower-epoch side and the LCA payload into the newer epoch record by
record, so replicas that never compact keep merging and their records are
translated on ingest. SETTLED-CUT CONTRACT: sound only when the cut is
settled at the compacting replica (all concurrency delivered:
heard-from-everyone-since-the-cut); the caller asserts it, and evidence certificates are a
follow-on. This shared-store `Runtime` still linearizes epochs; the
first-class `DistributedReplica` (below) instead merges divergent epochs
via the certificate-determined join (THE EPOCH DIAMOND).

## Save/load: the run-table serializer

`src/serialize.js` is the SHIPPED lossless serializer. `encode(state) -> Uint8Array`,
`decode(bytes) -> state`. It builds the canonical RUN TABLE of the state
(the run-table projection measured by `benchmarks/models/run_table_measure.py`): decode every
live record's coordinate into a shared kept tree, cut it
into maximal FUSIBLE chains (a node's unique kept child at delta 1 and equal
liveness, side vacuously R), and address each record as `(run-id, offset)`.
The buffer is a varint count, a mode byte, bit-packed per-entry headers
(liveness, parent ref, Elias-delta head delta, Elias-delta length), then the
elements (one byte/char for single-code-point elements). The run-id, offset
and parent-offset are NOT stored: records sit positionally in their run and
the parent-offset is the tail by the tail-attachment lemma.

Lossless: coordinates reconstruct exactly, so `decode(encode(s))` reads
identically to `s` (ids are the (ts,agent) tie-break the representation does
not encode; decode assigns fresh ids and coordinates are injective).
`accountingBits(state)` reproduces `run_table_measure.py`'s bit accounting
BIT-FOR-BIT (the projection), and the shipped metadata bit count equals that
total minus the recoverable positional fields it drops -- an identity the
tests assert. `tableWalk(table)` reproduces the display without materializing
chains. Compose it AFTER `compactEliasDelta` for the smallest output: on the
josephg traces it lands at 1.1-1.3 bytes/char (an order of magnitude below
the packed absolute-chain estimate, at production save size). Tests:
`test/serialize.test.js` (directed accounting vs the Python model, size
ratios, coalesce/tail-attachment, and a 120-trial merge/delete round-trip
PBT). Measured in `benchmarks/` (`tools/run_table_shipped.mjs`, column 3 of
the save-size matrix).

## The delta/op sync wire

`src/sync.js` is an Automerge-repo-style gossip protocol between `Peer`s that
hold SEPARATE commit stores (unlike the shared-DAG `Runtime`, which merges
in-process). Two peers exchange their DAG frontier (head content-ids), each
computes which commits the other lacks (an ancestor-set difference), and ships
those as a DELTA: per commit only the op payload + parent refs + author
replica-id, never the whole state. A whole-state snapshot (`src/serialize.js`)
is used only for a genuine bulk catch-up (`deltaOrSnapshot` picks it when the
delta would be larger, e.g. a brand-new or very-far-behind peer).

- CONTENT ADDRESSING (the ONE hash). Separate stores assign
  different local ids to the same commit, so the wire speaks global content-ids
  minted by `commitContentId` (`src/hash.js`): a SHA-256 Merkle DAG folding in
  parent ids -- authored commits hash `{parents, replica, seq, payload}`, a
  merge commit hashes its SORTED parent ids (so `merge(a,b)` and `merge(b,a)`
  are the SAME commit and never diverge into a spurious criss-cross), the root
  hashes `{root:true}`. Peers dedup on the global id and RECOMPUTE each ingested
  commit's state (`apply` for authored, `merge3` for merges) -- a transmitted
  state is never trusted; the recomputed id must match the wire id (a
  content-address gate). This is the SAME id git persistence uses on disk, so
  wire and disk agree.
  The `hash` constructor argument is pluggable (default: the SHA content id).
- CONVERGENCE. `syncPeers(a, b)` runs one bidirectional round: both compute the
  other's delta from the pre-merge frontiers, both ingest, both merge their
  head with the other's advertised head. After the round both stores hold every
  commit and (content-addressing the shared merge) their heads carry equal
  reads. `test/sync.test.js` gossips N peers to convergence (a criss-cross-free
  linear fold), pins per-round read equality, and measures the payload: the
  per-round delta is a function of that round's ops, CONSTANT across rounds,
  while a whole-state resync grows with the document, so in steady state the
  delta is well under half the whole-state baseline. `src/wire.js` supplies the
  deterministic binary framing: repeated strings are interned, safe integers
  use varints, content ids use raw bytes, and local commit references use
  numeric varints. Linear authored runs omit intermediate ids and parent links;
  their explicit endpoint hash recursively authenticates the reconstructed
  chain. The decoder is exercised before ingest; ingest still
  recomputes state and the content id, so the codec does not enlarge the trust
  boundary. JSON sizing remains available only as a diagnostic control.
- HEAD-SYNC PRESERVED. A peer only ever merges its current head with the
  current head another peer just advertised, never a stale interior commit --
  the hypothesis `gc_safety` consumes. Merges go through the same `lca()`
  criss-cross gate as the shared-store runtime.

The concurrent benchmark (`benchmarks/`) reports the sync
payload column with `sharedDelta`: the bidirectional wire delta a sync would
ship, measured on the shared-store pair before the merge (comparable to
Yjs/Automerge's update-bytes column).

## Certified state GC: the evidence producer

`replica.compactStable(opts)` uses a CHECKED certificate built from the frontier
(`src/frontier.js`) in place of `replica.compact`'s ASSERTED settledness. The
correspondence to `Sal/MRDTs/GC/Protocol.lean` and
`Sal/MRDTs/GC/Refinement.lean`:

| runtime                                   | formal target                       |
| ----------------------------------------- | ----------------------------------- |
| the frontier (per-replica evidence commit `c_j`) | `AllHeardSince C v S`        |
| `stableCut` = meet of `E(c_j)`            | the maximal such `S`                |
| certificate present (`complete`)          | the hypothesis `hAll`               |
| reads preserved by the compaction         | `settledAt_of_allHeard` -> StabilityVC |

The certificate is CHECKED: if any registered replica has not been heard from
since the cut (its evidence commit is absent from this head's ancestry),
compaction is REFUSED (a no-op returning `{ compacted: false, missing }`). That
is the runtime witness of `settledAt_of_allHeard`'s not-heard breaker (the
`createReplica` case, EvidenceDischarge section 3): absence of evidence is
refusal, never assumption. `test/sync.test.js` pins this directed at
runtime level with the discriminating-remove countermodel
(`stability-vc-note.md` section 2): a concurrent op held by a lagging replica
makes `compactStable` refuse, then fire once that replica is heard from, reads
identical to a never-compacted control throughout -- with a FAIL companion
showing the OLD asserted compaction at the same point DIVERGES (a frozen-delta
order flip), so the certificate's refusal is load-bearing, not pessimism.

THE IN-FLIGHT DISCHARGE. `compact.js`
takes a `cut.inflight` argument: an in-flight op concurrent with the cut whose
frozen delta a dense renumber could flip. Under a CERTIFIED cut no such op
exists: every op concurrent with the cut is already delivered (SettledAt
condition 2), so it is an at-rest member that compact.js's own per-group
stability gate refuses to renumber; every UNdelivered op is Lamport-fresh
future work that sorts past the compacted block and translates verbatim. So
`compactStable` passes `inflight: []` and it is PROVED sufficient, not asserted.

ONE FRONTIER, TWO CONSUMERS (`runtime-gc-note.md` section 6). The commit GC
(`rt.gc()`) reads the current-heads frontier from ABOVE (retain the upward
closure of the pairwise head meets); this stability producer reads the same
frontier from BELOW (what is settled). `rt.registeredNames()` is the closed
replica set both quantify over (the open-membership caveat). Note that
aggressive commit GC truncates ancestry at the keep horizon, which can hide the
very evidence commits `compactStable` needs -- interleaving the two is the
deferred historical-payload interaction (`stability-vc-note.md` section 8); the
tests exercise each consumer against its own frontier, not both at once.

## The first-class distributed replica

`src/replica.js`'s `DistributedReplica` folds the runtime's TWO-STORE SPLIT into
one object. The two halves otherwise sit apart:

| object              | store   | wire sync | certified GC | commit GC | hash |
| ------------------- | ------- | --------- | ------------ | --------- | ---- |
| `runtime.js` Replica| shared  | no        | yes          | yes       | n/a  |
| `sync.js` Peer      | separate| yes       | no           | no        | FNV  |
| **`DistributedReplica`** | **separate** | **yes** | **yes** | **yes** | **SHA** |

It is ONE content-addressed store that has BOTH capabilities: local ops
(`commit`), delta gossip (`ancestryGids`/`delta`/`ingest`/`mergeWithGid`, the
content-address re-computation gate), the certified stability GC (`stableCut` ->
`compactStable`, the evidence frontier adapted to the single store), and the
keep-set commit GC (`gc()`, `src/gc.js` over its own DAG, defaulting the head
set to this head plus the frontier's per-replica evidence commits), all under
SHA content addressing (`commitContentId`). `syncReplicas(a, b)` runs one
bidirectional round.

`DistributedReplica.gc()` is evidence-gated: if any other registered member
has no frontier entry, it returns `{refused:true, missing:[...]}` and changes
nothing. Absence of evidence is never treated as a smaller head set. On
success, GC deletes payloads outside the keep set and removes every parent
reference crossing its boundary; retained seeds become parent-free bases, so
the old root and dangling historical skeleton are not retained. The Lean
counterpart is `Metatheory/GC_CompressedDAG.lean` plus
`Metatheory/Distributed_GC.lean`.

Epoch-base history pruning also accepts a fetch-aligned acknowledgement from a
quiescent peer. `syncReplicas(a, b)` records each peer's advertised current
head and epoch after a successful bidirectional fetch/head-sync round. The
receiver accepts the receipt only if its local content-addressed DAG contains
that exact head and recomputes the same epoch key. The receipt does not create
a datatype operation or enter the causal frontier. Before every registered
peer acknowledges the cut, `pruneToEpochBase()` continues to refuse. The Lean
counterpart is `Metatheory/Distributed_GC_Acknowledgements.lean`; it proves
that arbitrary finite fetch/ack/GC executions refine the no-GC semantics after
receipt steps are erased, and that complete receipts provide
datatype-independent pruning evidence. Receipts are soft state and are not
persisted; after restart, a replica safely waits for another fetch round.

Run `npm run bench:empty-gc` to measure the empty-document steady state. The
2026-08-15 reference run grew histories to 22, 202, and 2,002 commits. After
state GC, a quiet-peer fetch acknowledgement, and history pruning, every case
retained one epoch-base commit, 9 datatype bytes, zero coordinate symbols, and
zero visible characters. Treat timings as machine-specific measurements; the
constant retained counts are also asserted by the harness.

DATATYPE-PARAMETRIC. Everything except state compaction is datatype-agnostic
(`init`/`apply`/`merge3`/`read`). A datatype that also provides `{compact,
remapState, encodeState, decodeState}` additionally gets `compactStable` (the
last two (de)serialize a compaction commit's inline state on the wire and on
disk); one that does not -- e.g. `orset` -- gets everything else and
`compactStable` returns `{ compacted: false, reason: 'does not support state
compaction' }`. A datatype may additionally provide `cutFromMeet(meet)` to
shape its own cut from the certified meet (`compactiblePeritext` extracts
settled deletes and settled mark mids this way; in-flight fields stay empty,
discharged by the certificate). `test/replica.test.js` runs convergence, the
SHA round-trip / tamper gate, and commit GC over BOTH `embedRGA` and `orset`,
and the certified state GC over `embedRGA` (refuse-then-fire) with `orset`
refusing; `test/peritext-gc.test.js` does the same refuse-then-fire for
`compactiblePeritext`.

THE EPOCH DIAMOND (concurrent divergent compaction). Epoch
identity in `DistributedReplica` is the SETTLED CUT plus its certificate, held in
a CUT-INDEXED DAG (`src/epoch.js`) whose nodes are cuts and whose edges are
compaction refinements and JOINS (`W = U ∪ V`), NOT a per-replica integer. A
cross-epoch merge does not THROW: it is the certificate-determined join,
validated by the runtime tests and mechanized in the MRDT state-GC modules. Two heads at
INCOMPARABLE cuts merge by lifting both DOWN to their common base frame through
the per-epoch INVERSE maps (`buildInverseTranslate`) and `merge3`-ing there; the
merged read equals the never-compacted twin, with no coordination (both replicas
lift deterministically to the same frame). Coordinate translation, not op-replay,
is the sound realization -- it rewrites dead-ancestor prefixes a re-application
cannot reconstruct; a forward MAP lift of a divergently-compacted peer's head is
unsound (a concurrently-minted record it never saw would be squeezed into a wrong
ordinal). The frame stays coordination-free because a compaction frame is minted
ONLY by the shipped, content-addressed `compactStable` (keyed by the commit's
content id, so two frames that freeze stragglers differently stay distinct),
never re-derived at merge. Translation maps are GC'd per the A3 DOUBLE
certificate (`dropEpochMap`: everyone advanced past `e` AND every pre-advance
mint heard everywhere); the ack-only shortcut is unsound and refused.
`test/epoch.test.js` pins the c1 diamond (s1, bit-identical), the c4 flip
(translation necessary), the aliasing negative, the A3 map-drop, and a 600-trial
twin PBT of incomparable-cut merges vs the never-compacted twin. Same-epoch merges are
byte-identical; only cross-epoch merges translate rather than throw.

## The head-sync discipline, and why

The GC is sound ONLY if every merge is between two CURRENT heads. This is
exactly the hypothesis of the `gc_safety` theorem on the Lean side; the
runtime makes it structural rather than advisory.

Old-commit-pull countermodel (sketch): let replicas A and B sync to a merge
`m` and run `gc()`, which prunes everything below the keep-set horizon.
If some agent could now merge against an OLD commit `s` (a stale head from
before the sync), the LCA of `s` and `m` lies strictly below the horizon
and is gone; the merge would run with a wrong (too-high or missing) LCA
state. Concretely, an element inserted below the horizon and deleted in
both branches is no longer witnessed as deleted by the substitute LCA, and
the live-set rule `(A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)` resurrects it. Under
head-sync the pairwise MCAs of the current heads are precisely what Keep
retains, so every future LCA query lands inside the kept region.

The GC-safety PBT (`test/gc-pbt.test.js`) is the empirical twin of the
theorem: identical random head-sync runs on two runtimes, GC invoked
aggressively on one, reads and states asserted identical throughout.

## The criss-cross gate

Criss-cross merges genuinely arise under honest head-sync (two disjoint
replica pairs merge the same diverged heads `x`,`y` into rival merge
commits; any later sync across them finds MCAs `{x, y}`). Virtual LCAs
(recursive merging of the MCAs, git style) are not in the in-process
verified model, so `lca()` throws `CrissCrossError`: an explicit gate,
never a silent pick. Consequence: a criss-crossed replica pair using `lca()`
cannot sync; the PBT skips gated syncs (and asserts both twins return
the SAME verdict: a GC-induced verdict flip would itself be a safety
violation). `gc()` uses `mcas()` directly (keeping every MCA is sound
without uniqueness), so GC never throws this.

VIRTUAL LCAs IN `DistributedReplica`. The distributed replica
RESOLVES criss-crosses rather than gating them: its merge base is the
`#baseState` fold of the MCA antichain (sorted by content id, recursively
resolved sub-bases), which feeds the epoch join exactly as a single LCA
would (`#baseFor` also returns the base's epoch key). A criss-cross whose
antichain also SPANS epochs (incomparable cuts AND a criss-cross) is the
doubly-hard case the virtual-LCA and epoch-diamond constructions do not
claim; it throws `CrissCrossError` so consumers defer it. Pinned in
`test/virtual-lca.test.js`. The in-process `runtime.js`/`sync.js` use
`lca()` (the gate above).

ROSTER HYGIENE + FORGET. `DistributedReplica` tracks `authors` (replicas that
have authored a commit here) alongside `registered`; `unregister(name)` drops
a name IFF it never authored (a lurker), keeping writers conservatively, and
`forget(name)` drops it unconditionally (the operator-directed lever to
release the GC horizon a departed author pins). Pinned in `test/forget.test.js`.

EPOCH-BASE HISTORY PRUNING (`pruneToEpochBase`). After a SETTLED compaction,
history below it is dropped and the compaction becomes a parent-free EPOCH
BASE whose content id still verifies (the hash covers the wire parent gid
STRING + the state fingerprint, so `ingest` gates it parent-free); a fresh
peer bootstraps from the base at O(document). The gate is the certified
condition for forgetting: the stability cut is complete AND every registered
replica's evidence has ADVANCED PAST the compaction's cut (`epochDag.subcut`),
so no registered peer holds a below-base head. Soundness is the
model-independent "a settled cut licenses forgetting" (the stability VC),
which applies to the cut-keyed epochs: pruning removes only history
below the base, and every future merge lifts down to at most the base. Pinned
in `test/pruning.test.js` (bootstrap + post-bootstrap authoring, tamper gate,
under-evidenced refusal, records round-trip) and the hub pruning test in
`../p2p-demo/test/hub.test.js`.

## Open-membership caveat

The keep-set is computed against the CURRENT registered replica set. A
replica registered after a GC, or an unregistered peer, may need pruned
history; membership must be closed at GC time. Operationally the runtime
refuses `rt.replica(...)` once the root commit has been pruned. The separate
store additionally refuses `DistributedReplica.gc()` until every existing
roster member has frontier evidence.

## Running the tests

```
cd runtime && npm test        # or: node --test test/*.test.js
```

(Node v26. `node --test test/` with a bare directory is not accepted as a
`--test` positional; the glob form above is equivalent.)

Suites: `test/hash.test.js` (the content hash: SHA-256 vs `node:crypto`,
key-order-invariant stable stringify, `commitContentId`'s Merkle DAG),
`test/replica.test.js` (the first-class `DistributedReplica`: convergence via
gossip, the SHA round-trip / tamper gate, certified state GC refuse-then-fire,
commit GC, and the cross-epoch-merge join -- reads == the never-compacted twin,
run over BOTH `embedRGA` and `orset` where applicable), `test/epoch.test.js` (the
epoch diamond: the cut-indexed DAG units, the inverse-map
round-trip, the c1 diamond at s1, the aliasing negative, the c4 no-translation
flip, the A3 double-certificate map-drop, and a 600-trial twin PBT of
incomparable-cut merges vs the never-compacted twin -- each PASS with a FAIL
companion), `test/dag.test.js` (DAG/LCA units, criss-cross
construction), `test/embed.test.js` (litmus fixtures, below), `test/code.test.js`
(Lean-pinned codewords, code-invariance, the cost gap), `test/gc.test.js`
(GC genuinely prunes; post-GC merges match a no-GC control; the membership
gate), `test/gc-pbt.test.js` (the GC-safety PBT: 220 embedRGA + 120 orset
twin trials, 3-5 replicas, 25-50 steps, sync/del/gc probabilities
.35/.30/.35, plus a per-replica LIVE oracle against the implicit event
set), `test/compact.test.js` (compactEliasDelta: directed delete-heavy
compaction with pinned symbol counts, the in-flight negative control and
its guarded companion, lazy translation on ingest, dead-range keeping,
future mints past the compacted block, the v1 epoch guards, and a
140-trial twin PBT compacting at explicitly-settled points against a
never-compacting control), `test/sync.test.js` (the sync/gossip layer: N-peer
delta-sync convergence with the bounded-payload assertion; the wire-vs-snapshot
chooser; the directed refuse-then-fire evidence test plus its divergence FAIL
companion; and a 160-trial twin PBT of certified GC vs a no-compaction control,
per-step read equality, both certificate branches exercised -- 746 fires /
1060 refuses on this machine), `test/peritext.test.js` (the rich-text datatype:
the Ex1-8 paper renderings, `doc_no_backward_leak`, the gravity contrast,
`doc_delete_can_respan`, and mark-permutation convergence -- each with a `≠`
FAIL companion, all expected values extracted from the validated
`peritext_read_model.py`; plus the parametricity payoff running Peritext through
`DistributedReplica` to convergence with wire clone/catch-up and a snapshot
round-trip), `test/peritext-gc.test.js` (the marks-layer state GC:
retention roots + A3 guarded pair-drop, hand-derived directed cases D6/D1/D3/D7
each PASS with its FAIL companion -- the no-retention read flip, the alpha
undeclared-straggler flip, the beta growth-window flip, the unguarded-renumber
order flip -- plus refuse-then-fire under the certificate, the settled-delete
gate, an empty-document audit proving that durable datatype metadata returns
to the fresh-empty representation while quiescent-peer epoch history safely
remains gated, and a 150-trial multi-epoch twin PBT with declared stragglers against a
never-compacted control, cost bound retained ≤ 2 per mark record asserted),
`test/pmap.test.js` (the persistent HAMT: randomized Map
equivalence over mixed set/delete batches for number and string keys,
structural-sharing sanity, transient freeze correctness, real birthday-found
32-bit hash collisions, deterministic sorted iteration),
`test/applybatch.test.js` (`applyBatch` == fold of `apply` for all three
datatypes, including honesty preconditions and intra-batch anchoring).

## What the p2p demo still needs on top of this

The demo's core replica object IS `DistributedReplica` above
(one content-addressed store, wire sync + both GCs, SHA throughout); the demo's
`Node` is a thin re-export, and `src/hash.js` is the one
hash for wire and disk. What the demo adds on top is the deployment
skin, not runtime machinery:

- a TRANSPORT binding -- carry the `{ t: 'delta', c: [...] }` / snapshot
  messages over a real channel (WebSocket / WebRTC / a sync server), with the
  have/want negotiation driven by `DistributedReplica.ancestryGids()` +
  `.delta(...)`;
- GIT-STYLE PERSISTENCE -- durable per-peer stores keyed by the SHA content id
  (commits + heads to disk / IndexedDB so a peer survives restart);
- AUTHENTICATED IDENTITY -- the SHA content-address gate bounds tampering with a
  commit's content, but not *who* may author; a real deployment needs the
  replica id to be a key, not a string;
- open-membership handling on the wire (registration/eviction), the same closed
  set the certificate and commit GC quantify over;
- CONCURRENT DIVERGENT COMPACTION -- the certificate-determined epoch join in
  the core `DistributedReplica` (`src/epoch.js`);
  the demo's checkpoint barrier is not required for correctness, though it
  is still the cheapest path when replicas can coordinate.

## Datatype ports are UNVERIFIED transliterations

`embedRGA` implements the embedded-chain RGA proved in
`Sal/MRDTs/Instances/ProductionRGA.lean`; `orset`
is a standard observed-remove set. Neither JS file is verified; they are
pinned to the verified semantics by reviewed fixtures: L1
delete-reorder and the two sibling-splice fooling-pair worlds, which pin
exactly the dead-ancestor coordinate-prefix behavior. A 300-scenario
randomized differential run against the Python model was also performed
(scratch harness, not committed). If port and fixture ever
disagree, the port is wrong, never the fixture.

Deviations from the Python file (all equivalence-preserving, pinned by the
fixtures):

1. Representation: the model stores parent-relative `Fraction` intervals
   and refolds on delete/merge (isometric fold). By the model's own P3 the
   absolute coordinate is a birth constant, so the port stores it directly:
   each record carries its immutable chain coordinate
   `coord(anchor) ++ enc(ts - anchorTs)` as a bit-string. Delete becomes
   pure removal, merge carries coordinates unchanged, display is descending
   lexicographic key order (anchor above its descendants via a `'2'`
   sentinel). The remaining deviation on the STORAGE axis is deliberate:
   absolute per-record chains repeat shared anchor prefixes, where a
   factored (prefix-sharing / tree or trie) store would share them; that
   storage axis does not affect semantics.
2. The delta code layer: pluggable, default flipped Elias-delta matching
   the verified Lean instance (see the code section above); `dEnc` is also
   cross-checked against the Python model's
   `EmbedTreeCodeD.C` on 69 deltas (scratch harness, not committed). Any
   order-preserving prefix-free code yields identical reads, checked by the
   code-invariance tests.
3. Insert under a dead anchor: undefined behavior in the Python model (the
   record becomes unreachable; merge KeyErrors). The port makes the
   honesty/applicability precondition explicit and throws.
4. The merge live-set is written `(A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)` (the task's
   form) vs the model's `(L ∩ A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)`; these are equal
   since `(A ∩ B) ∖ L ⊆ A ∖ L`.

## Experimental prefix-sharing representation

`src/datatypes/sharedEmbedRGA.js` factors repeated coordinate prefixes into
immutable shared nodes and keeps stable birth provenance separate from
epoch-local order paths. `src/shared-compact.js` performs settled-cut rank
renumbering and dead-spine fusion directly over that graph; the original
absolute-coordinate compactor remains its differential oracle. Nonempty
in-flight paths and frozen anchors are handled directly and conservatively:
affected sibling groups are not renumbered and guarded spines are not fused.
`compactibleSharedPeritext` runs the same graph beneath Peritext's retention
roots and A3 mark-pair collection. This representation is a promotion canary,
not yet the default datatype.

Run `npm run bench:shared-gc` for the full concurrent, offline-evidence, and
three-epoch convergence/snapshot canary. The tests in
`test/shared-embed-rga.test.js` include future editing after recovery,
independently decoded merge, certified GC, returning pre-compaction peers, and
a 40-trial cross-epoch twin comparison with a never-compacted control.
`test/peritext-gc.test.js` additionally checks dead mark-boundary retention,
frozen in-flight insertion order, certified empty-document collection, and
shared snapshot recovery.
