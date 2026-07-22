# sal-runtime

A git-like commit-DAG MRDT runtime (task #94, engineering half): pluggable
datatypes over a shared commit store, three-way merges through the DAG's
LCA, and the keep-set commit GC from the verified design. Pure
dependency-free ESM; runs in the browser and in Node unchanged (no
Node-only APIs in `src/`).

This runtime is a TESTED MIRROR of the Lean proofs, not an extraction:
`../whiteboard/verification-distance.md` records, layer by layer, how each
piece connects to the proved artifacts, which layers have no Lean counterpart
(the replica/wire machinery), and what would shrink the distance.

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
- `src/frontier.js` -- THE ONE FRONTIER (task #106). `frontierOf(dag, head)`
  gives, per replica, its latest absorbed commit (its *evidence commit*);
  `stableCut(dag, head, registered, self)` intersects those event sets into
  the largest cut this head can CERTIFY. This is exactly `AllHeardSince` /
  `settledAt_of_allHeard` of
  `Sal/ConditionedMRDTs/Metatheory/EvidenceDischarge.lean` (see below).
- `src/sync.js` -- the delta/op WIRE protocol (task #104 item 3): content-
  addressed `Peer`s over SEPARATE stores exchange head frontiers and ship the
  ancestor-set difference as a delta, converging by merge (see below).
- `src/hash.js` -- THE CONTENT HASH (task #108). A pure-JS SHA-256 (checked
  bit-for-bit against `node:crypto`) and `commitContentId`, the single
  Merkle-DAG derivation every content-addressed store mints commit ids through
  (`hash` argument pluggable, default the SHA). Replaces the FNV model hash the
  `Peer` used to carry, so WIRE and DISK name the same commit the same way.
- `src/replica.js` -- THE FIRST-CLASS DISTRIBUTED REPLICA (task #108):
  `DistributedReplica`, ONE content-addressed store with BOTH wire sync AND the
  certified state GC (plus the keep-set commit GC), datatype-parametric (see
  below). This is the two-store split (`Replica` = GC-but-no-wire, `Peer` =
  wire-but-no-GC) resolved into one object; the p2p demo's `Node` is now a thin
  re-export of it.
- `src/pmap.js` -- THE STATE CONTAINER (task #111). `PMap`/`PSet`, a
  dependency-free browser-safe persistent HAMT: `set`/`delete` return a new
  map in O(log n) by path copy with structural sharing, killing the
  O(live-set)-copy-per-op the datatypes previously paid (`new Map(state)`
  per keystroke). Public iteration (`entries`/`keys`/`values`/iterator) is
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
since task #111 "fresh" is O(log n) structural sharing over `src/pmap.js`,
and `merge3` on persistent states is a delta merge from one parent).
The bundled datatypes also expose an optional `fingerprint(state)` used by
the twin tests, and `embedRGA` adds `readIds`/`readEntries`/`symbolCount`,
`orset` adds `observe` (helpers for honest op construction and cost probes).
THREE datatypes ship: `embedRGA` (a sequence), `orset` (a set), and
`peritext` (rich text = the verified document-order mark model over
`embedRGA`, see its own section below).

## Peritext: verified document-order rich text over embedRGA (task #55 → #107)

`src/datatypes/peritext.js` is the THIRD datatype: rich text, built as the
Lean-verified DOCUMENT-ORDER mark read model layered on the sequence datatype.
It plugs into `DistributedReplica` over the same `{init, apply, merge3, read}`
contract as `embedRGA`/`orset`, so rich text gets delta gossip + SHA content
addressing + commit GC with NO Peritext-specific runtime code — the whole
datatype is the only new piece (the parametricity payoff, proven directly in
`test/peritext.test.js`).

- STATE `= { text: { shadow, deleted }, marks }`. `text.shadow` is an
  insert-only `embedRGA` state holding every character (birth order + reading
  order, reused verbatim: insert, reading order, and merge all delegate to
  `embedRGA`); `text.deleted` is a grow-only set of logically deleted ids;
  `marks` is a map (`PMap`) `mid → { mtype, value, startId, endId, startSide, endSide,
  ts, removed }`. This is `DocD` from the verified spec — a delete is LOGICAL
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
- MATCHES THE VERIFIED MODEL exactly:
  `whiteboard/litmus/peritext_read_model.py` (the executable
  `DocumentOrderResolver`) and
  `Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Embed/PeritextEmbed_MarkIntent.lean`
  (`doc_no_backward_leak`, `doc_delete_can_respan`, the Ex1–8 renderings).
  `test/peritext.test.js` pins the Ex1–8 paper examples, the directed
  no-backward-leak (delete a bold start anchor; the boundary rehomes forward,
  earlier text stays plain — never the retracted backward tree-ancestry leak),
  the gravity contrast (bold grows at its end, a link does not), the honest
  atomicity re-span (`doc_delete_can_respan`), and mark-permutation convergence
  — each PASS with a `≠` FAIL companion. Expected values are EXTRACTED by
  running the Python reference (invocation cited in the test header), never read
  back from the JS implementation.
- STATE COMPACTION now FIRES (task #110): the old refusal is replaced by the
  VALIDATED marks-layer GC of `src/compact-peritext.js` (`compactiblePeritext`;
  design + machine verdicts in `whiteboard/marks-gc-note.md`, reference
  semantics `whiteboard/litmus/marks_gc_check.py`). The keep-set is live ids ∪
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
  note's D6; kept executable as the `noRetention`/`unguardedPairDrop` negative
  controls); the plain hookless `peritext` object still refuses.
  `test/peritext-gc.test.js` carries the directed PASS+FAIL family and a
  multi-epoch twin PBT against a never-compacted control; cost measured there:
  retained dead records ≤ 2 per mark record (structural bound, met with max
  2.000). `encodeState`/`decodeState` give the lossless snapshot round-trip
  (also carrying compaction commits over the wire). `compactiblePeritext` also
  carries the `symbolCount` cost probe (its text shadow IS an embedRGA state),
  and the #107 editor runs on it: a metadata-cost panel plus a certified-GC
  button gated on the complete stability cut (see `p2p-demo/README.md`).

WHAT #107 (THE EDITOR) IS. A working editor exists in the #95 demo skin over
this datatype: a PROSEMIRROR view (`p2p-demo/web/richtext.js`, browser-verified
across two live tabs) whose transactions are diffed into ops by
`p2p-demo/src/peritextbind.js` (the op layer: a text edit -> `ins`/`del`, a
format gesture over a selection -> one `addMark`/`removeMark`, a toggle-off ->
the LWW-winning `removeMark`). ProseMirror owns the DOM; `read()` owns the
truth: after each local transaction the PM doc is reconciled against it, so on
mark-boundary questions (does a char typed at a span edge inherit bold?) the
verified semantics win. Presence renders as PM decorations. The editor exposes
the datatype's full mark surface: bold/italic/underline (growing boolean
marks), links (a value mark with the exclusive, never-growing end gravity of
Ex8), and comments (one mtype per comment, `comment:<id>` with the note in
`value`, so overlapping comments COEXIST under the per-(char,mtype) LWW --
pinned in `test/peritext.test.js`'s comments block, including the FAIL
companion showing the naive same-mtype encoding collapses). Headless-tested in
`test/peritextbind.test.js` against the datatype (Ex7 end-side growth, Ex8
exclusive-end links, overlapping comments, mark survival across a delete) and
a real replica. It generalizes the plain-text precursor `editbind.js`.

BATCHING is done. The replica now has a GROUP-OP COMMIT: `commitBatch(ops)`
(`replica.js`) seals a gesture's op list as ONE commit, applied via `applyBatch`
(one transient pass, proven equal to folding `apply`). The commit's payload is
the op ARRAY; the content-id folds it in opaquely, so `delta` ships it verbatim
and `ingest` replays it via `applyBatch` with no wire or hash change (the two
certified-GC id-collectors, `frontier.insertIds` and
`compact-peritext.peritextCutFromMeet`, were generalized to iterate array
payloads). `test/commitbatch.test.js` pins batch==fold-as-one-commit, the wire
round-trip under the content-address gate, convergence with mixed batch/single
commits, peritext batches, and the cut collecting a batch's ids.
`peritextbind.commitOps` uses it, and the editor buffers local ops in a
DEBOUNCED queue (rendering the speculative head+pending state via
`peritextbind.specRead`; flush on ~400ms idle / blur / pre-format / pre-merge /
unload), so a typing RUN, a paste, or a multi-char format lands as a single
commit, not one per character. The buffered run is proven equal to the
per-keystroke fold (`p2p-demo/test/peritextbind.test.js`).

PRESENCE is done. `p2p-demo/src/presence.js` is the ephemeral, OFF-DAG peer-
awareness registry (live cursors/selections + identity), carried as plain
`presence` room broadcasts over the same transport, never ingested, merged, or
persisted; `web/richtext.js` renders remote carets and selections as
ProseMirror decorations inside the one editing surface.
`test/presence.test.js` covers the registry (ttl prune, departure, span
normalization, stable per-peer color). Everything below the widget:
convergence, persistence, catch-up: is the runtime the datatype rides on.
Remaining #107 polish: collaborative undo (inverting my own ops rather than PM
history, which a replace-from-read() model bypasses) and block-level structure
beyond paragraphs (headings, lists) as mark-like metadata.

## The delta code is pluggable; the default is the verified Elias-delta

`embedRGA` coordinates are chains of codewords of an order-preserving
prefix-free DELTA code, and the datatype is parametric in it:
`makeEmbedRGA(code)` takes `{ name, enc(delta) -> bit-string }`. Two codes
ship:

- `eliasDeltaCode` (the DEFAULT, used by the exported `embedRGA`): the
  flipped Elias-delta code transliterated from the verified Lean instance
  `eliasDeltaCode` in `Sal/MRDTs/RGA_Embed/Embed_Code_EliasDelta.lean`
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

## State GC: compactEliasDelta (task #97, practical tail)

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

SPINE FUSION (iteration two, opt-in via `opts.fuseSpines`; design:
`whiteboard/embed-recoding-note.md` Addendum 2). A fusible spine is a
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
(`whiteboard/litmus/embed_compact_measure.py`, which mirrors the fusion
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
heard-from-everyone-since-the-cut, `whiteboard/stability-vc-note.md`
section 2); the caller asserts it, and evidence certificates are a
follow-on. Epochs are also linearized per runtime (concurrent divergent
compactions are the deferred protocol half,
`whiteboard/embed-recoding-note.md` section 6).

## Save/load: the run-table serializer (task #104)

`src/serialize.js` is the SHIPPED lossless serializer, the successor to the
JSON/binary absolute-chain saves. `encode(state) -> Uint8Array`,
`decode(bytes) -> state`. It builds the canonical RUN TABLE of the state
(the run-table PROJECTION of `whiteboard/run-table-note.md` / task #73, made
real): decode every live record's coordinate into a shared kept tree, cut it
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

## The delta/op sync wire (task #104, item 3)

`src/sync.js` is an Automerge-repo-style gossip protocol between `Peer`s that
hold SEPARATE commit stores (unlike the shared-DAG `Runtime`, which merges
in-process). Two peers exchange their DAG frontier (head content-ids), each
computes which commits the other lacks (an ancestor-set difference), and ships
those as a DELTA: per commit only the op payload + parent refs + author
replica-id, never the whole state. A whole-state snapshot (`src/serialize.js`)
is used only for a genuine bulk catch-up (`deltaOrSnapshot` picks it when the
delta would be larger, e.g. a brand-new or very-far-behind peer).

- CONTENT ADDRESSING (task #108: the ONE hash). Separate stores assign
  different local ids to the same commit, so the wire speaks global content-ids
  minted by `commitContentId` (`src/hash.js`): a SHA-256 Merkle DAG folding in
  parent ids -- authored commits hash `{parents, replica, seq, payload}`, a
  merge commit hashes its SORTED parent ids (so `merge(a,b)` and `merge(b,a)`
  are the SAME commit and never diverge into a spurious criss-cross), the root
  hashes `{root:true}`. Peers dedup on the global id and RECOMPUTE each ingested
  commit's state (`apply` for authored, `merge3` for merges) -- a transmitted
  state is never trusted; the recomputed id must match the wire id (a
  content-address gate). This is the SAME id git persistence uses on disk, so
  wire and disk agree; it replaces the FNV model hash a `Peer` used to carry.
  The `hash` constructor argument is pluggable (default: the SHA content id).
- CONVERGENCE. `syncPeers(a, b)` runs one bidirectional round: both compute the
  other's delta from the pre-merge frontiers, both ingest, both merge their
  head with the other's advertised head. After the round both stores hold every
  commit and (content-addressing the shared merge) their heads carry equal
  reads. `test/sync.test.js` gossips N peers to convergence (a criss-cross-free
  linear fold), pins per-round read equality, and measures the payload: the
  per-round delta is a function of that round's ops, CONSTANT across rounds,
  while a whole-state resync grows with the document, so in steady state the
  delta is well under half the whole-state baseline. (The delta is JSON
  op-encoding; a binary framing would shrink it further, the same
  representation gap the save-size story documents.)
- HEAD-SYNC PRESERVED. A peer only ever merges its current head with the
  current head another peer just advertised, never a stale interior commit --
  the hypothesis `gc_safety` consumes. Merges go through the same `lca()`
  criss-cross gate as the shared-store runtime.

The concurrent benchmark (`benchmarks/`) fills its previously-`n/a` sync
payload column with `sharedDelta`: the bidirectional wire delta a sync would
ship, measured on the shared-store pair before the merge (comparable to
Yjs/Automerge's update-bytes column).

## Certified state GC: the evidence producer (task #106)

`replica.compactStable(opts)` replaces `replica.compact`'s ASSERTED settledness
with a CHECKED certificate built from the frontier (`src/frontier.js`). The
exact correspondence to `Sal/ConditionedMRDTs/Metatheory/EvidenceDischarge.lean`:

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

THE IN-FLIGHT DISCHARGE (the point of #106 over `compact.js`'s v1). `compact.js`
carried a `cut.inflight` crutch: an in-flight op concurrent with the cut whose
frozen delta a dense renumber could flip. Under a CERTIFIED cut no such op
exists -- every op concurrent with the cut is already delivered (SettledAt
condition 2), so it is an at-rest member that compact.js's own per-group
stability gate refuses to renumber; every UNdelivered op is Lamport-fresh
future work that sorts past the compacted block and translates verbatim. So
`compactStable` passes `inflight: []` and it is PROVED sufficient, not asserted
-- delivering the "computing evidence certificates is a follow-on" of
`stability-vc-note.md` section 2.

ONE FRONTIER, TWO CONSUMERS (`runtime-gc-note.md` section 6). The commit GC
(`rt.gc()`) reads the current-heads frontier from ABOVE (retain the upward
closure of the pairwise head meets); this stability producer reads the same
frontier from BELOW (what is settled). `rt.registeredNames()` is the closed
replica set both quantify over (the open-membership caveat). Note that
aggressive commit GC truncates ancestry at the keep horizon, which can hide the
very evidence commits `compactStable` needs -- interleaving the two is the
deferred historical-payload interaction (`stability-vc-note.md` section 8); the
tests exercise each consumer against its own frontier, not both at once.

## The first-class distributed replica (task #108)

`src/replica.js`'s `DistributedReplica` folds the runtime's TWO-STORE SPLIT into
one object. Before #108 the two halves were kept apart:

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

THE EPOCH BARRIER (concurrent divergent compaction is NOT claimed).
`compactStable` opens a new epoch, and a cross-epoch merge THROWS: the runtime
LINEARIZES compaction epochs. Two replicas compacting different cuts and then
merging across epochs is the deferred protocol half -- the #97 multi-epoch
`CompatChain` not yet discharged for cross-replica different cuts
(`stability-vc-note.md` section 8, `embed-recoding-note.md` section 6). A
deployment reaches a common epoch with a coordinated CHECKPOINT barrier (every
replica absorbs the converged history, then all compact the identical cut to the
identical re-coding / same SHA); `test/replica.test.js` pins that a peer which
has not itself reached the new epoch is refused a cross-epoch merge, rather than
guessing.

## The head-sync discipline, and why

The GC is sound ONLY if every merge is between two CURRENT heads. This is
exactly the hypothesis of the `gc_safety` theorem being proved concurrently
on the Lean side; the runtime makes it structural rather than advisory.

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

## The criss-cross gate (task #90)

Criss-cross merges genuinely arise under honest head-sync (two disjoint
replica pairs merge the same diverged heads `x`,`y` into rival merge
commits; any later sync across them finds MCAs `{x, y}`). Virtual LCAs
(recursive merging of the MCAs, git style) are task #90 and not yet in the
verified model, so `lca()` throws `CrissCrossError` -- an explicit gate,
never a silent pick. Consequence: a criss-crossed replica pair cannot sync
until #90 lands; the PBT skips gated syncs (and asserts both twins return
the SAME verdict: a GC-induced verdict flip would itself be a safety
violation). `gc()` uses `mcas()` directly (keeping every MCA is sound
without uniqueness), so GC never throws this.

## Open-membership caveat

The keep-set is computed against the CURRENT registered replica set. A
replica registered after a GC, or an unregistered peer, may need pruned
history; membership must be closed at GC time. Operationally the runtime
refuses `rt.replica(...)` once the root commit has been pruned.

## Running the tests

```
cd runtime && npm test        # or: node --test test/*.test.js
```

(Node v26. Deviation from the original spec's `node --test test/`: Node
v26 no longer accepts a bare directory as a `--test` positional; the glob
form is equivalent.)

Suites: `test/hash.test.js` (the content hash: SHA-256 vs `node:crypto`,
key-order-invariant stable stringify, `commitContentId`'s Merkle DAG),
`test/replica.test.js` (the first-class `DistributedReplica`: convergence via
gossip, the SHA round-trip / tamper gate, certified state GC refuse-then-fire,
commit GC, and the cross-epoch-merge refusal -- run over BOTH `embedRGA` and
`orset` where applicable), `test/dag.test.js` (DAG/LCA units, criss-cross
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
round-trip), `test/peritext-gc.test.js` (the marks-layer state GC #110:
retention roots + A3 guarded pair-drop, hand-derived directed cases D6/D1/D3/D7
each PASS with its FAIL companion -- the no-retention read flip, the alpha
undeclared-straggler flip, the beta growth-window flip, the unguarded-renumber
order flip -- plus refuse-then-fire under the certificate, the settled-delete
gate, and a 150-trial multi-epoch twin PBT with declared stragglers against a
never-compacted control, cost bound retained ≤ 2 per mark record asserted),
`test/pmap.test.js` (the persistent HAMT: randomized Map
equivalence over mixed set/delete batches for number and string keys,
structural-sharing sanity, transient freeze correctness, real birthday-found
32-bit hash collisions, deterministic sorted iteration),
`test/applybatch.test.js` (`applyBatch` == fold of `apply` for all three
datatypes, including honesty preconditions and intra-batch anchoring).

## What #95 (the p2p demo) still needs on top of this

As of task #108 the demo's core replica object IS `DistributedReplica` above
(one content-addressed store, wire sync + both GCs, SHA throughout); the demo's
`Node` is a thin re-export. The FNV/SHA seam is gone (`src/hash.js` is the one
hash for wire and disk). What the #95 demo still adds on top is the deployment
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
- CONCURRENT DIVERGENT COMPACTION -- the demo uses a coordinated checkpoint
  barrier to keep epochs linearized; lifting that (cross-replica different cuts)
  is the runtime's own deferred protocol half (the #97 multi-epoch
  `CompatChain`).

Much of this skin is already built in `p2p-demo/`: `gitstore.js` (durable store
= a fenced real git repo of SHA-addressed commit records + `doc.txt`; `load()`
replays them through `ingest` + `mergeWithGid`), `relay.mjs` (a dumb star relay,
rooms = doc ids), `transport.js` (WsTransport have/req/delta), and
`editbind.js` (a plain-text embedRGA binding). `whiteboard/collab-design-note.md`
reconciles those against the remaining #107/#95 work: the peritext (marks)
editor binding, batching, promoting the dumb relay to an always-on merging hub
for asynchronous collaboration, and identity/auth.

## Datatype ports are UNVERIFIED transliterations

`embedRGA` ports the embedded-chain RGA from the Python model
`whiteboard/litmus/embed_tree.py` (`EmbedTree`/`EmbedTreeCode`); `orset`
is a standard observed-remove set. Neither JS file is verified; they are
pinned to the verified semantics by fixtures extracted by RUNNING the
Python model (invocations recorded in `test/embed.test.js`): L1
delete-reorder and the two sibling-splice fooling-pair worlds, which pin
exactly the dead-ancestor coordinate-prefix behavior. A 300-scenario
randomized differential run against the Python model was also performed at
port time (scratch harness, not committed). If port and fixture ever
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
   storage half is queued as task #97 and does not affect semantics.
2. The delta code layer: pluggable, default flipped Elias-delta matching
   the verified Lean instance (see the code section above); `dEnc` was also
   cross-checked at port time against the Python model's
   `EmbedTreeCodeD.C` on 69 deltas (scratch harness, not committed). Any
   order-preserving prefix-free code yields identical reads, checked by the
   code-invariance tests.
3. Insert under a dead anchor: undefined behavior in the Python model (the
   record becomes unreachable; merge KeyErrors). The port makes the
   honesty/applicability precondition explicit and throws.
4. The merge live-set is written `(A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)` (the task's
   form) vs the model's `(L ∩ A ∩ B) ∪ (A ∖ L) ∪ (B ∖ L)`; these are equal
   since `(A ∩ B) ∖ L ⊆ A ∖ L`.
