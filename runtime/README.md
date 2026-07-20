# sal-runtime

A git-like commit-DAG MRDT runtime (task #94, engineering half): pluggable
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
rt.gc();                                // keep-set GC -> { kept, dropped }
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

A datatype is `{ init, apply(state, op), merge3(l, a, b), read(state) }`,
all pure (`apply`/`merge3` return fresh states: commits keep old states).
The bundled datatypes also expose an optional `fingerprint(state)` used by
the twin tests, and `embedRGA` adds `readIds`/`readEntries`/`symbolCount`,
`orset` adds `observe` (helpers for honest op construction and cost probes).

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

Suites: `test/dag.test.js` (DAG/LCA units, criss-cross construction),
`test/embed.test.js` (litmus fixtures, below), `test/code.test.js`
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
never-compacting control).

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
