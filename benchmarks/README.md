# benchmarks/: verified Sal sequence kernels vs production CRDT libraries

Cross-system comparison of the JavaScript implementations corresponding to
the verified RGA, EmbedRGA, and SidedEmbedRGA designs against four production
sequence-CRDT implementations. Every matrix cell comes from a run on this
machine; no cell is quoted from literature. EmbedRGA and SidedEmbedRGA are both
paper-facing choices: the former targets lower retained metadata, while the
latter retains policy state for stronger non-interleaving semantics.

## Systems

| key | system | what is measured |
| --- | --- | --- |
| `rga` | Sal RGA | verified explicit-tombstone baseline |
| `embed-rga` | Sal EmbedRGA | verified shared-coordinate design with lower retained metadata |
| `sided-embed-rga` | Sal SidedEmbedRGA | verified sided policy with stronger non-interleaving behavior |
| `yjs` | Yjs 13.6.31 | `Y.Text` |
| `automerge` | @automerge/automerge 3.3.2 (wasm) | text field, one `Automerge.change` per char (the automerge-perf convention) |
| `loro` | loro-crdt 1.13.7 (wasm) | `LoroText` |
| `listpositions` | list-positions 2.0.0 | `Text` (chars at CRDT positions). NOT a full CRDT library: it ships positions and a local structure, op delivery is left to the app; its sync row uses an op-log integration (see below) |

All external systems installed cleanly from npm; none was dropped.

## Reproduction

```
cd benchmarks
npm install          # once (package-lock.json is checked in)
node run.mjs         # full matrix, ~25 min wall (regenerates results/*.json + results/summary.md)
node run.mjs --quick # smallest trace + freq preset + churn only, ~1 min
node run.mjs --only seq:sal        # substring filter on job ids
node run.mjs --skip-projection    # skip the python run-table projection
```

The npm interface is `npm run bench:quick`, `npm run bench:full`, and
`npm run summarize`. The GC-ablation workers write schema-versioned records to
`results/raw/`; `tools/normalize.mjs` validates their required fields and emits
`results/summary.json` plus plot-ready `results/tables/results.csv` and the
GC-specific `results/tables/plain-gc.csv`. The schema is
`schema/result.schema.json`. Every sequential, concurrent, and churn worker
embeds its detailed legacy result under `detail`, so normalization does not
discard methodology-specific measurements.

The plain-text Sal GC sweep runs both the absolute and shared representations
through the production `DistributedReplica` and five
configurations: `none`, `history`, `state`, `both`, and `both-delayed`. In the
both-GC configurations, state compaction consumes the settled causal ancestry
before commit history is pruned to the acknowledged epoch base. Reversing this
order weakens the state-GC certificate and is not labeled as the production
configuration.

## Peritext suite

`PERITEXT_WORKLOADS.md` is the semantic contract for rich-text measurements.
The unified runner implements all seven workload families for both Peritext
text representations and six Sal GC
configurations and writes `results/tables/peritext.csv`. It gates the run with
directed gravity and dead-anchor fixtures whose expected values come from the
independently validated Python model, complete-render convergence, snapshot
round-trip, pre-evidence refusal, post-acknowledgement pruning, and equal render
digests across all ablations. `empty-rich` additionally checks that full state
GC reaches the 9-byte fresh-empty representation, and `multi-epoch-rich`
requires three actual settled-cut compactions. External rich-text adapters remain staged until
their interval, removal, and gravity behavior passes the declared comparison
boundary.

Each job runs in a fresh `node --expose-gc` child process (heap and wasm
isolation), sequentially, never in parallel. Raw per-job results are
checked in under `results/*.json`; `results/summary.md` is the generated
matrix (embedded below).

## Workloads

* **(a) Sequential trace replay, per-char apply.** The real editing traces
  of the josephg corpus in `benchmarks/traces/`
  (`friendsforever_flat`, `clownschool_flat`, `seph-blog1`,
  `automerge-paper`), flattened to single-character events exactly as
  `benchmarks/models/entropy_measure.py` applies them (for each patch
  `[pos, ndel, content]`: `ndel` single-char deletes at `pos`, then the
  content chars one at a time). Gate: the final text must equal the
  trace's `endContent`. All trace characters are BMP code points, so
  UTF-16 code-unit and code-point indexing agree across all five systems.
* **(b) Concurrent two-replica session** (deterministic, mulberry32 seed
  42). Per round each replica applies a burst locally (80% insert of a
  random char at a uniform position of its own doc, 20% delete), then one
  bidirectional sync. Presets: `freq` = 60 rounds x 25 ops/replica,
  `bulk` = 6 rounds x 500 ops/replica. The rng stream is consumed in a
  fixed order and lengths evolve identically, so every system sees the
  byte-identical op sequence. Gate: replicas converge (equal texts) after
  the final sync. Cross-system merge ORDER may legitimately differ; only
  intra-system convergence is gated.
* **(c) Delete-heavy churn** (seed 7, single writer): 5 cycles of
  { insert 2000 chars at random positions, delete 1800 at random
  positions }, then a final 200-char insert; every native save variant is
  measured after every phase. This is the storage-growth-on-delete axis
  and reproduces the anomaly-matrix cell: Automerge's save GROWS across a
  delete phase.

## Metrics and methodology (explicit, papers vary)

1. **Per-char apply time**: `process.hrtime.bigint()` around each
   single-char op; median and p95 over all ops after excluding the first
   1000 as warmup (JIT, wasm lazy init). Totals include warmup. Timer
   overhead is roughly 30-60 ns per op on this machine and is NOT
   subtracted; sub-microsecond medians (Yjs, Loro, list-positions) carry
   that additive bias. For `sal` the op includes the adapter's
   position-to-id bookkeeping (an id-array splice) plus the datatype
   `apply` (an O(log n) persistent-HAMT path copy; a copied-Map container
   would instead copy the whole live-set Map per op and dominate every
   trace, the pre-HAMT interface cost reported below).
2. **Save size**: bytes of each library's NATIVE serialization, measured
   (`Buffer.byteLength` on strings, `.length` on Uint8Array). What each
   save CONTAINS differs and is stated per row: Automerge `save` is the
   full change history (no state-only mode exists); Loro `snapshot`
   carries full history while `shallow-snapshot` drops history at the
   current frontiers; Yjs `encodeStateAsUpdate` drops deleted content but
   cannot drop tombstone id structure (v2 = run-length compressed
   encoding); list-positions saves live chars plus position metadata
   (JSON); ours saves live state only (delete = pure removal). Our three
   fair-play columns are described in the next section.
3. **Load time**: from the primary native save into a fresh document,
   median of 5 runs in one process; includes materializing the text once
   (render parity). For `sal` this includes re-deriving the display order
   (the full coordinate sort).
4. **Merge/sync time**: workload (b), the bidirectional exchange timed
   per round, median/p95 over rounds. System-native mechanisms: Yjs =
   state-vector diff updates both ways; Loro = version-vector delta
   export/import both ways; Automerge = `Automerge.merge` both ways
   (in-process, no wire format); ours = `Replica.sync` (unique-LCA
   `merge3` under the shipped head-sync Runtime; commit-GC runs after
   each sync OUTSIDE the timed window and is reported separately);
   list-positions = applying the other side's op log (its documented
   integration pattern), payload = JSON bytes of those ops.
5. **Peak JS heap**: `process.memoryUsage().heapUsed` sampled every 500
   ops without forced GC, so it includes garbage; retained = heapUsed
   after two forced GCs at the end of the apply loop minus a
   two-forced-GC baseline taken before it (in workload (a), measured
   BEFORE saves/loads/compaction so transient save artifacts do not
   pollute it). Caveat: wasm-backed libraries (Automerge, Loro) keep
   document state in wasm linear memory, visible in `external` /
   `arrayBuffers` deltas (recorded in the JSON), NOT in heapUsed; heap
   numbers are not comparable across the wasm boundary and are flagged.

## Sal durable artifact

Our shipped runtime stores ABSOLUTE chain coordinates: a record's
coordinate is the full root-to-record delta chain under the flipped
Elias-delta code, kept as a `'0'/'1'` JS string (1 byte per bit, and JS
strings are 2-byte-capable; the in-heap cost is higher still). This is a
KNOWN representation gap with a designed successor (the run table),
shipped as a serializer (`runtime/src/serialize.js`).
The paper-facing matrix reports the shipped run-table binary as Sal's durable
artifact. JSON and the former packed-bits arithmetic estimate are retained only
as historical diagnostics and are not cross-system ranking columns. The
run-table encoding is lossless for reads and composes with settled-cut
compaction.

Historical development notes for the superseded diagnostic columns follow:

1. **runtime-as-shipped (measured)**: `json-shipped` = the datatype's own
   JSON serialization (coord bit-strings verbatim), plus
   `binary-estimate` = a defined packed encoding computed from the same
   state (per record, sorted by id: varint(id delta) + varint(coord bit
   length) + packed coord bits + UTF-8 element; plus varint(count)).
   The estimate is computed arithmetic, no encoder is shipped; it is the
   honest "if we packed the bits we already have" number.
2. **runtime + compaction (measured, shipped code)**: the state after
   `compactEliasDelta` (rank-renumber + spine fusion, `fuseSpines: true`)
   over a settled cut, re-serialized both ways. Legitimate wherever the
   workload permits a settled cut: trace replay and churn are single
   writer (everything settled), and the concurrent session is fully
   synced at the end. Compaction wall time and the order-preservation
   gate (re-read equals the expected text) are reported.
3. **run-table serialized, SHIPPED (measured, shipped code)**:
   `run-table-serialized` = the state re-encoded by the run-table
   serializer (`runtime/src/serialize.js`), over the as-shipped state and
   over the settled-cut compacted state. It builds the canonical run table
   (maximal fusible chains, records addressed (run-id, offset)) and emits
   bit-packed entry headers + positional records + packed text. Lossless:
   `decode(encode(state))` reads identically, gated on every trace and by a
   120-trial merge/delete PBT (`runtime/test/serialize.test.js`). These are
   REAL bytes, the successor to columns 1-2. On the compacted state it lands
   at 1.1-1.3 bytes/char, an order of magnitude below `binary-estimate` and
   at production save size (below Yjs update-v2, on par with Loro
   shallow-snapshot).
4. **run-table PROJECTION (measured-in-model)**: the exact bit accounting
   of `benchmarks/models/run_table_measure.py` executed on the
   same trace via `tools/run_table_projection.py`;
   `projected bytes = ceil(order-metadata bits / 8) + UTF-8 text bytes`.
   The model charges per-record run-id + offset and per-entry headers; it
   does NOT charge the (ts, agent) tie-break (our binary-estimate does
   charge ids) nor any framing. `accountingBits(state)` in the shipped
   serializer reproduces this column's bits BIT-FOR-BIT (raw 472745,
   474128, 1476002, 2491316; composed 476343, 478753, 1314975, 2507561 --
   asserted by `tools/run_table_shipped.mjs`). The shipped column 3 lands
   BELOW this projection because the model deliberately charges the
   recoverable positional fields (per-record run-id and offset, and the
   parent-offset the tail-attachment lemma makes derivable) that a real
   encoder stores positionally and drops (whiteboard/run-table-note.md
   section 9.1). Reconciliation, not a bug in either: the shipped metadata
   bit count == model total minus (rec_id + rec_off + hdr_poff), an
   identity asserted in the tests.

Anchoring the projection to the shipped code: the model's chain
accounting reproduces the shipped state bit-for-bit on the same trace
(`chain_before` = `compact.js` `symbolsBefore` = 34,660,055 bits on
`friendsforever_flat`, and `chain_fused` = `symbolsAfter` = 18,296,270
bits, exactly). Same id stream (dense Lamport ticks, deletes tick too),
same code, same deltas.

Symmetrically, per-library save content is stated in every save-size
table (history vs state), and history-carrying saves (Automerge always,
Loro snapshot) are never compared against state-only saves without the
label saying so.

## The honest headline

### The persistent-HAMT state container

The shipped `apply` uses a persistent HAMT (`runtime/src/pmap.js`, O(log n)
path copy, structural sharing) with byte-identical observables (same
reads, fingerprints, SHA content ids, serialized bytes; both suites and
all gates pass). A copied-`Map` container instead returns a fresh `Map`
per op, an O(live-set) copy per keystroke that is ~100% of the measured
apply cost; the matrix below reports both, as the PRE-HAMT INTERFACE
COST against the HAMT numbers.

| trace | apply median pre-HAMT | apply median HAMT | speedup | total pre-HAMT | total HAMT |
| --- | --- | --- | --- | --- | --- |
| friendsforever_flat (26k ops) | 363.54 us | 0.50 us | 727x | 9.49 s | 0.02 s |
| clownschool_flat (24k ops) | 347.13 us | 0.38 us | 913x | 8.56 s | 0.02 s |
| seph-blog1 (368k ops) | 1.66 ms | 3.96 us | 418x | 546.92 s | 1.74 s |
| automerge-paper (260k ops) | 3.16 ms | 4.08 us | 775x | 713.28 s | 1.94 s |

Concurrent sessions (same seed): local op mean 25.65 -> 2.44 us (freq),
62.80 -> 16.41 us (bulk); sync median 73.46 -> 107.4 us (freq), 730.92 ->
753.5 us (bulk) -- merge3 is a structural-sharing delta merge from
one parent, but per-id lookups are O(log n) HAMT walks instead of O(1)
Map hits, and the remaining sync time is dominated by DAG bookkeeping
(LCA + frontier ancestry walks), not the datatype. Save bytes are
byte-identical in every variant, every workload.

Where we lose, as shipped:

* **Per-char apply.** With the copied-Map container, `apply` copies the
  live-set Map on every op, so cost grows linearly with document size
  (median 347-364 us on ~21k-char docs, 1.66 ms at 57k chars, 3.16 ms at
  105k chars; ~15-120x slower than Automerge and 3 to 4
  orders of magnitude slower than Yjs / Loro / list-positions; 713 s
  whole-trace replay on automerge-paper). The persistent HAMT closes this
  (table above): 0.38-4.08 us medians, within ~6x of Yjs/Loro (0.5-1.7 us, with
  ~30-60 ns of the gap being timer overhead) and faster than Automerge
  (24-27 us) on every trace; whole-trace replay 1.9 s on automerge-paper
  vs 0.2 s (Loro), 0.67 s (Yjs), 7.1 s (Automerge). The residue at 100k+
  chars (4 us median vs 0.5 us on small docs) is the O(log n) trie depth
  plus the adapter's O(n) id-array splice, not a live-set copy.
* **Save size, absolute-chain representation.** 1637-2991 bytes/char as
  JSON (243 MB for the 105k-char doc) vs 0.6-10 bytes/char for every
  production save. Packing the same bits (binary-estimate) still leaves
  207-376 B/char; the shipped compaction (measured, rank-renumber + spine
  fusion) cuts the coordinate bits by 1.9-3.2x, leaving 112-188 B/char.
  Two orders of magnitude worse than production; this is the known
  absolute-chain-coordinate gap -- CLOSED by the run-table serializer below.
* **Load.** 39-289 ms (JSON parse + HAMT build + coordinate sort), vs
  Loro 0.2-0.3 ms and Yjs 2-9 ms. Automerge's full-history load is in our
  range (29-446 ms); on automerge-paper ours loads in 289 ms vs
  Automerge's 319 ms.

Where we are competitive or win, as shipped:

* **Merge/sync.** Unique-LCA `merge3` under the head-sync Runtime: 107 us
  median (freq preset), 754 us (bulk), Yjs-level (90 us / 1.13 ms) and
  17-24x faster than Automerge (1.8 / 18.3 ms) and Loro (6.3 / 17.1 ms)
  in these sessions. Only list-positions' raw op-log apply is comparable
  (34 / 626 us). Caveat: small docs (1.8k / 3.6k chars); the
  merge is a structural-sharing delta from one parent (it touches the ids
  the other side added or deleted, plus two O(n log n) membership scans),
  so large-doc syncs do not pay a full live-set rebuild; the scans
  still keep it short of O(delta).
* **Storage on delete.** Our save never grows on delete, it shrinks by
  construction (delete = pure record removal): measured 20-46 KB shrink
  per 1800-char delete phase (binary-estimate). See the churn table for
  the production comparison.
* **Resident memory.** Retained heap after full replay is 4-22 MB: the
  absolute coordinates share prefixes structurally (V8 cons strings along
  the anchor chain), so the in-heap state is compact and the bit cost
  only materializes at serialization. The persistent HAMT keeps allocation
  churn ~3x lower than the copied-Map container (sampled peak heap 132 MB on
  the automerge-paper replay vs 433 MB; GC-noise caveat applies) at the price
  of a few MB of retained trie nodes (12 -> 22 MB on that trace).

The Automerge-grows-on-delete cell (reproduced): across the five delete
phases Automerge's save grew by +3383, +3327, +3383, +3370, +3430 bytes
(monotone growth to 60,742 B for a 1200-char final doc). Loro's `snapshot`
also grows on every delete phase; Loro's `shallow-snapshot` and Yjs do
not grow, but Yjs cannot shed tombstone structure (165.4 KB v1 / 45.9 KB
v2 for the same 1200 live chars, vs our compacted binary-estimate 7.9 KB;
Loro shallow-snapshot 3.9 KB is the smallest).

Where we win with the run-table serializer:

* **Save size, run-table serialized (SHIPPED).** The
  run table is a real encoder/decoder (`runtime/src/serialize.js`).
  Over the settled-cut compacted state it lands at **1.1-1.3 bytes/char**
  (24,126 / 22,438 / 72,848 / 120,276 B on the four traces), and 1.2-1.6
  B/char over the raw as-shipped state. That is an order of magnitude below
  our own `binary-estimate` (112-188 B/char compacted), BELOW Yjs update-v2
  (1.5-2.4 B/char) and Automerge's compressed full history (1.2-3.6
  B/char), on par with Loro shallow-snapshot (0.6-1.1 B/char, still the
  smallest), and it never grows on delete. Lossless: `decode(encode(s))`
  reproduces the read on every trace and across a 120-trial merge/delete
  PBT. This closes the absolute-chain save-size gap: the metadata is
  ~1 bit/char (few long fusible runs after fusion) plus 1 byte/char text.

The run-table PROJECTION column (22.3-23.9
bits/char of order metadata, 3.8-4.0 B/char with text) is a shipped
measurement: `accountingBits(state)` reproduces `run_table_measure.py`'s
totals bit-for-bit on every trace (raw and composed). The SHIPPED bytes sit
BELOW the projection because the model charges recoverable positional
fields (per-record run-id + offset, derivable parent-offset) that the real
encoder drops. Neither number is wrong:
shipped_metadata_bits == projection_total - rec_id - rec_off - hdr_poff, an
identity the tests assert.

## The matrix

The tables below are `results/summary.md`, regenerated by every
`node run.mjs` (this copy matches the checked-in results/*.json).

Environment: node v26.3.1, darwin arm64, Apple M4 Pro, 24 GB RAM.
Every cell below was produced by a run in this repo (results/*.json); nothing from literature.

## Sequential replay: automerge-paper (259778 per-char ops, final 104852 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 4.08 us | 21.63 us | 1.94 s | 288.9 ms (json-shipped) | 131.9 MB | 21.9 MB | text OK |
| Yjs | 1.38 us | 10.88 us | 0.67 s | 5.5 ms (update-v1) | 113.0 MB | 3.5 MB | text OK |
| Automerge | 26.83 us | 32.96 us | 7.09 s | 319.3 ms (save-full-history) | 105.2 MB | 0.8 MB | text OK |
| Loro | 0.46 us | 1.42 us | 0.20 s | 0.3 ms (snapshot) | 83.8 MB | 0.3 MB | text OK |
| list-positions | 0.67 us | 1.13 us | 0.19 s | 3.0 ms (json-text+order) | 105.8 MB | 2.1 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, automerge-paper (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 243276637 | 2320.2 | 285.8 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 30668998 | 292.5 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | run-table-serialized | 130300 | 1.2 | 1718.6 ms | live state only; SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read |
| ours (embed RGA, as shipped) | json-shipped+compacted | 135792070 | 1295.1 | 137.6 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 17233096 | 164.4 | -- | packed-bits estimate of the compacted state |
| ours (embed RGA, as shipped) | run-table-serialized+compacted | 120276 | 1.1 | 1129.7 ms | SHIPPED run-table binary over the compacted state (lossless) |
| ours (run-table serialized, SHIPPED) | run-table-serialized | 130300 | 1.2 | -- | live state only; SHIPPED serializer over the as-shipped state; lossless (decode reads = read); real bytes, not the projection |
| ours (run-table serialized, SHIPPED) | run-table-serialized+compacted | 120276 | 1.1 | -- | SHIPPED serializer over the settled-cut compacted state; lossless; realizes the projection at 1.1 B/char (< the model's 4.0 B/char: the model charges the recoverable positional run-id/offset/parent-offset the encoder drops) |
| ours (PROJECTION, run table) | run-table composed (model) | 418298 | 4.0 | -- | measured-in-model (run-table accounting, gates_ok=true); order metadata 23.9 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 311038 | 3.0 | 5.2 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 159929 | 1.5 | 2.7 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 129126 | 1.2 | 19.1 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 251015 | 2.4 | 12.2 ms | state + full op history |
| Loro | shallow-snapshot | 65066 | 0.6 | 3.2 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 492935 | 4.7 | 2.4 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: clownschool_flat (24326 per-char ops, final 21148 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 0.38 us | 1.88 us | 0.02 s | 52.0 ms (json-shipped) | 20.3 MB | 4.3 MB | text OK |
| Yjs | 1.67 us | 2.38 us | 0.05 s | 2.8 ms (update-v1) | 21.6 MB | 1.7 MB | text OK |
| Automerge | 26.25 us | 32.96 us | 0.66 s | 28.6 ms (save-full-history) | 18.8 MB | 0.8 MB | text OK |
| Loro | 0.75 us | 1.71 us | 0.03 s | 0.3 ms (snapshot) | 12.9 MB | 0.2 MB | text OK |
| list-positions | 0.67 us | 2.83 us | 0.02 s | 0.4 ms (json-text+order) | 19.1 MB | 0.6 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, clownschool_flat (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 52938278 | 2503.2 | 53.6 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 6672560 | 315.5 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | run-table-serialized | 32782 | 1.6 | 456.2 ms | live state only; SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read |
| ours (embed RGA, as shipped) | json-shipped+compacted | 31415483 | 1485.5 | 27.7 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 3982162 | 188.3 | -- | packed-bits estimate of the compacted state |
| ours (embed RGA, as shipped) | run-table-serialized+compacted | 22438 | 1.1 | 402.7 ms | SHIPPED run-table binary over the compacted state (lossless) |
| ours (run-table serialized, SHIPPED) | run-table-serialized | 32782 | 1.6 | -- | live state only; SHIPPED serializer over the as-shipped state; lossless (decode reads = read); real bytes, not the projection |
| ours (run-table serialized, SHIPPED) | run-table-serialized+compacted | 22438 | 1.1 | -- | SHIPPED serializer over the settled-cut compacted state; lossless; realizes the projection at 1.1 B/char (< the model's 3.8 B/char: the model charges the recoverable positional run-id/offset/parent-offset the encoder drops) |
| ours (PROJECTION, run table) | run-table composed (model) | 80993 | 3.8 | -- | measured-in-model (run-table accounting, gates_ok=true); order metadata 22.6 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 93322 | 4.4 | 1.9 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 42997 | 2.0 | 1.9 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 25724 | 1.2 | 4.8 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 65553 | 3.1 | 7.0 ms | state + full op history |
| Loro | shallow-snapshot | 22732 | 1.1 | 2.7 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 61026 | 2.9 | 0.5 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: friendsforever_flat (26078 per-char ops, final 21362 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 0.50 us | 1.58 us | 0.02 s | 38.5 ms (json-shipped) | 27.0 MB | 4.3 MB | text OK |
| Yjs | 1.54 us | 2.42 us | 0.05 s | 2.2 ms (update-v1) | 20.4 MB | 1.4 MB | text OK |
| Automerge | 24.33 us | 31.79 us | 0.67 s | 30.4 ms (save-full-history) | 20.3 MB | 0.8 MB | text OK |
| Loro | 0.63 us | 1.67 us | 0.03 s | 0.2 ms (snapshot) | 13.7 MB | 0.2 MB | text OK |
| list-positions | 0.63 us | 1.54 us | 0.02 s | 0.8 ms (json-text+order) | 20.0 MB | 0.7 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, friendsforever_flat (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 34971320 | 1637.1 | 39.1 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 4427040 | 207.2 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | run-table-serialized | 31457 | 1.5 | 275.3 ms | live state only; SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read |
| ours (embed RGA, as shipped) | json-shipped+compacted | 18607535 | 871.1 | 19.7 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 2381219 | 111.5 | -- | packed-bits estimate of the compacted state |
| ours (embed RGA, as shipped) | run-table-serialized+compacted | 24126 | 1.1 | 219.4 ms | SHIPPED run-table binary over the compacted state (lossless) |
| ours (run-table serialized, SHIPPED) | run-table-serialized | 31457 | 1.5 | -- | live state only; SHIPPED serializer over the as-shipped state; lossless (decode reads = read); real bytes, not the projection |
| ours (run-table serialized, SHIPPED) | run-table-serialized+compacted | 24126 | 1.1 | -- | SHIPPED serializer over the settled-cut compacted state; lossless; realizes the projection at 1.1 B/char (< the model's 3.8 B/char: the model charges the recoverable positional run-id/offset/parent-offset the encoder drops) |
| ours (PROJECTION, run table) | run-table composed (model) | 80905 | 3.8 | -- | measured-in-model (run-table accounting, gates_ok=true); order metadata 22.3 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 81480 | 3.8 | 1.8 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 40889 | 1.9 | 1.6 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 27423 | 1.3 | 4.3 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 61707 | 2.9 | 6.2 ms | state + full op history |
| Loro | shallow-snapshot | 21646 | 1.0 | 2.7 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 100337 | 4.7 | 0.7 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: seph-blog1 (368209 per-char ops, final 56769 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 3.96 us | 12.25 us | 1.74 s | 165.0 ms (json-shipped) | 99.6 MB | 12.7 MB | text OK |
| Yjs | 1.42 us | 5.29 us | 0.74 s | 9.1 ms (update-v1) | 91.1 MB | 4.6 MB | text OK |
| Automerge | 26.71 us | 31.71 us | 9.91 s | 446.2 ms (save-full-history) | 84.5 MB | 0.9 MB | text OK |
| Loro | 0.58 us | 1.33 us | 0.30 s | 0.2 ms (snapshot) | 67.6 MB | 0.3 MB | text OK |
| list-positions | 0.96 us | 3.67 us | 0.48 s | 3.6 ms (json-text+order) | 85.8 MB | 2.4 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, seph-blog1 (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 169774875 | 2990.6 | 183.2 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 21362422 | 376.3 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | run-table-serialized | 88120 | 1.6 | 1059.6 ms | live state only; SHIPPED run-table binary (entry headers + positional records + packed text); lossless, decodes to the same read |
| ours (embed RGA, as shipped) | json-shipped+compacted | 52956992 | 932.9 | 55.0 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 6759513 | 119.1 | -- | packed-bits estimate of the compacted state |
| ours (embed RGA, as shipped) | run-table-serialized+compacted | 72848 | 1.3 | 448.2 ms | SHIPPED run-table binary over the compacted state (lossless) |
| ours (run-table serialized, SHIPPED) | run-table-serialized | 88120 | 1.6 | -- | live state only; SHIPPED serializer over the as-shipped state; lossless (decode reads = read); real bytes, not the projection |
| ours (run-table serialized, SHIPPED) | run-table-serialized+compacted | 72848 | 1.3 | -- | SHIPPED serializer over the settled-cut compacted state; lossless; realizes the projection at 1.3 B/char (< the model's 3.9 B/char: the model charges the recoverable positional run-id/offset/parent-offset the encoder drops) |
| ours (PROJECTION, run table) | run-table composed (model) | 221141 | 3.9 | -- | measured-in-model (run-table accounting, gates_ok=true); order metadata 23.2 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 338289 | 6.0 | 4.8 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 135225 | 2.4 | 2.8 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 205250 | 3.6 | 25.7 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 336808 | 5.9 | 14.8 ms | state + full op history |
| Loro | shallow-snapshot | 52683 | 0.9 | 3.0 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 572686 | 10.1 | 3.2 ms | live chars + position-order metadata (library-native JSON) |

## Concurrent 2-replica session, preset freq (60 rounds x 25 ops/replica/round, seed 42, final 1804 chars)

| system | sync median | sync p95 | sync total | payload/sync | local op mean | primary save | converged |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 107.42 us | 162.17 us | 6.7 ms | 5.9 KB | 2.44 us | 170693 B (json-shipped) | yes |
| Yjs | 89.54 us | 307.08 us | 7.1 ms | 1.6 KB | 3.98 us | 39782 B (update-v1) | yes |
| Automerge | 1.82 ms | 2.19 ms | 117.2 ms | n/a (in-process) | 35.48 us | 12698 B (save-full-history) | yes |
| Loro | 6.29 ms | 11.40 ms | 381.4 ms | 0.4 KB | 3.04 us | 19642 B (snapshot) | yes |
| list-positions | 33.50 us | 160.50 us | 2.8 ms | 6.4 KB | 2.34 us | 196682 B (json-text+order) | yes |

ours, post-session settled-cut compaction: 3.8 ms, json-shipped+compacted = 58788 B, binary-estimate+compacted = 10448 B; runtime commit-GC total 2.7 ms (outside sync timing).

## Concurrent 2-replica session, preset bulk (6 rounds x 500 ops/replica/round, seed 42, final 3604 chars)

| system | sync median | sync p95 | sync total | payload/sync | local op mean | primary save | converged |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 753.46 us | 810.50 us | 4.4 ms | 118.7 KB | 16.41 us | 386110 B (json-shipped) | yes |
| Yjs | 1.13 ms | 3.67 ms | 8.0 ms | 15.1 KB | 3.20 us | 80667 B (update-v1) | yes |
| Automerge | 18.32 ms | 19.21 ms | 108.0 ms | n/a (in-process) | 30.87 us | 24774 B (save-full-history) | yes |
| Loro | 17.12 ms | 22.04 ms | 98.8 ms | 4.6 KB | 2.30 us | 39130 B (snapshot) | yes |
| list-positions | 626.33 us | 1.01 ms | 4.0 ms | 123.6 KB | 2.02 us | 353262 B (json-text+order) | yes |

ours, post-session settled-cut compaction: 7.2 ms, json-shipped+compacted = 129449 B, binary-estimate+compacted = 22324 B; runtime commit-GC total 5.2 ms (outside sync timing).

## Delete-heavy churn (5 cycles of +2000/-1800 chars, then +200; final 1200 chars)

Save bytes after selected phases; growth-on-delete = does the save GROW across a delete phase.

| system | variant | cycle1-ins | cycle1-del | cycle5-ins | cycle5-del | final-ins | grows on delete? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 150121 | 14666 | 525107 | 188008 | 229695 | NEVER |
| ours (embed RGA, as shipped) | binary-estimate | 22278 | 2191 | 72322 | 25891 | 31596 | NEVER |
| ours (embed RGA, as shipped) | run-table-serialized | 8759 | 1657 | 19059 | 11111 | 12098 | NEVER |
| ours (embed RGA, as shipped) | json-shipped+compacted | 64529 | 5899 | 115753 | 39481 | 47848 | NEVER |
| ours (embed RGA, as shipped) | binary-estimate+compacted | 11576 | 1090 | 18884 | 6524 | 7882 | NEVER |
| Yjs | update-v1 | 32931 | 31671 | 163331 | 161995 | 165395 | NEVER |
| Yjs | update-v2 | 9539 | 8812 | 45776 | 44841 | 45856 | NEVER |
| Automerge | save-full-history | 8004 | 11387 | 56294 | 59724 | 60742 | ALWAYS |
| Loro | snapshot | 13349 | 15337 | 76144 | 78290 | 79679 | ALWAYS |
| Loro | shallow-snapshot | 6170 | 878 | 8677 | 3296 | 3882 | NEVER |
| list-positions | json-text+order | 121933 | 94172 | 454518 | 428465 | 436314 | NEVER |

## Caveats and known limits

* Automerge is driven one `Automerge.change` per char (the automerge-perf
  convention); batching chars into one change would lower its per-op cost
  and history size.
* list-positions is a positions library, not a full CRDT; its sync row is
  the documented op-log integration and its payload is unoptimized JSON.
* Loro sync timing includes commit + delta export + import in both
  directions through the wasm boundary.
* For `sal`, each timed op includes the adapter's position-to-id
  bookkeeping (id-array splice) on top of the datatype `apply`; deletes
  tick the Lamport clock (dense logical time, matching the litmus model
  and hence the projection's id stream).
* Cross-system merged ORDER may differ on concurrent insertions; only
  intra-system convergence is gated.
* Heap columns are not comparable across the wasm boundary (Automerge,
  Loro keep state in wasm linear memory); see the memory methodology.

## Owed / follow-ons

* The run-table serializer is shipped as column 3 above
  (`runtime/src/serialize.js`, `tools/run_table_shipped.mjs`), turning the
  projection into measurement and landing at 1.1-1.3 B/char compacted, at
  production save size. Two related items remain out of scope here: (a) a
  BATCHED-APPLY path (the mutable/transient fast path below),
  and (b) a WIRE FORMAT: the serializer is a save/load (whole-state)
  encoder, while sync uses the deterministic binary delta codec in
  `runtime/src/wire.js`. The concurrent payload column applies that codec to
  `sharedDelta` using real content ids. Linear authored runs elide intermediate
  ids and parent references; the explicit endpoint hash authenticates the
  reconstructed chain.
* The mutable/batched apply follow-on is done. The O(live-set)
  Map copy per op comes from the state container, not the order
  machinery; the persistent HAMT (`runtime/src/pmap.js`) moves per-char
  apply into the microsecond class (0.4-4.1 us medians, table above)
  without touching the semantics, and observables are byte-identical. Each
  datatype also provides `applyBatch(state, ops)` (one transient pass,
  proven equal to folding `apply` in `runtime/test/applybatch.test.js`);
  the DAG granularity is one op per commit.
* Concurrent sessions at realistic document sizes (the merge numbers here
  are small-doc), plus repeated trials of the authenticated run-batched binary
  sync format on plain text and Peritext payloads.

## Files

The canonical paper-facing reports are:

- `results/summary.md`: verified Sal kernels versus external systems;
- `results/kernel-comparison-repeated.md`: repeated RGA, EmbedRGA, and
  SidedEmbedRGA comparison;
- `results/peritext-paper-repeated.md`: repeated rich-text and two-GC
  evaluation, including the isolated ancestor-spine experiment.

Other JSON files are source measurements or aggregates, not competing prose
reports.

* `run.mjs`: one-command orchestrator.
* `workloads/seq.mjs|concurrent.mjs|churn.mjs`: the three workloads, one
  child process per (system, workload, trace/preset).
* `lib/adapters/*.mjs`: uniform adapter per system; `lib/adapters/sal.mjs`
  documents the position-to-id bookkeeping, the settled-cut usage, and
  wires the SHIPPED run-table serializer (`saveRunTable`, column 3).
* `lib/traces.mjs`, `lib/bench.mjs`: trace loading/flattening, timing and
  heap helpers.
* `../runtime/src/pmap.js`: the persistent HAMT state container
  behind the `sal` apply/merge numbers; unit-tested by
  `../runtime/test/pmap.test.js`.
* `../runtime/src/serialize.js`: the SHIPPED run-table serializer:
  `encode`/`decode`, `buildRunTable`, `accountingBits` (the
  run-table accounting, bit-for-bit), `tableWalk`. Tested by
  `../runtime/test/serialize.test.js`.
* `tools/run_table_projection.py`: runs the run-table accounting on the
  same traces, writes `results/projection.json`.
* `tools/run_table_shipped.mjs`: runs the SHIPPED serializer on the same
  traces' final states (fast mutable replay; byte-identical to seq.mjs),
  gates round-trip losslessness and cross-checks `accountingBits` against
  `projection.json`, writes `results/run_table_shipped.json`.
* `tools/summarize.mjs`: regenerates `results/summary.md` from
  `results/*.json` (including the shipped run-table rows).
* `results/*.json`: raw per-job results (checked in).
