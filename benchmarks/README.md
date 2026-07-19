# benchmarks/ : embed RGA runtime vs production CRDT libraries (task #98)

Cross-system performance comparison of our shipped embed RGA runtime
(`runtime/`, the unverified ESM transliteration of the Lean-verified embed
kernel) against four production sequence-CRDT implementations, on the
metrics CRDT papers use. Every cell in the matrix comes from a run of the
scripts in this directory on this machine; no cell is quoted from
literature.

## Systems

| key | system | what is measured |
| --- | --- | --- |
| `sal` | ours: `runtime/src/datatypes/embedRGA.js` (flipped Elias-delta code, the verified default) + `runtime/src/compact.js` + `runtime/src/runtime.js` (head-sync Runtime for the concurrent workload) | the AS-SHIPPED persistent datatype: `apply` returns a fresh Map (an O(live-set) copy per op), records carry absolute chain coordinates as `'0'/'1'` bit-strings |
| `yjs` | Yjs 13.6.31 | `Y.Text` |
| `automerge` | @automerge/automerge 3.3.2 (wasm) | text field, one `Automerge.change` per char (the automerge-perf convention) |
| `loro` | loro-crdt 1.13.7 (wasm) | `LoroText` |
| `listpositions` | list-positions 2.0.0 | `Text` (chars at CRDT positions). NOT a full CRDT library: it ships positions and a local structure, op delivery is left to the app; its sync row uses an op-log integration (see below) |

All five installed cleanly from npm; none dropped.

## Reproduction

```
cd benchmarks
npm install          # once (package-lock.json is checked in)
node run.mjs         # full matrix, ~25 min wall (regenerates results/*.json + results/summary.md)
node run.mjs --quick # smallest trace + freq preset + churn only, ~1 min
node run.mjs --only seq:sal        # substring filter on job ids
node run.mjs --skip-projection    # skip the python run-table projection
```

Each job runs in a fresh `node --expose-gc` child process (heap and wasm
isolation), sequentially, never in parallel. Raw per-job results are
checked in under `results/*.json`; `results/summary.md` is the generated
matrix (embedded below).

## Workloads

* **(a) Sequential trace replay, per-char apply.** The real editing traces
  of the josephg corpus as checked into `whiteboard/litmus/traces/`
  (`friendsforever_flat`, `clownschool_flat`, `seph-blog1`,
  `automerge-paper`), flattened to single-character events exactly as
  `whiteboard/litmus/entropy_measure.py` applies them (for each patch
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
   `apply`; the Map copy inside the shipped `apply` dominates.
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

## Fair play: our three columns

Our shipped runtime stores ABSOLUTE chain coordinates: a record's
coordinate is the full root-to-record delta chain under the flipped
Elias-delta code, kept as a `'0'/'1'` JS string (1 byte per bit, and JS
strings are 2-byte-capable; the in-heap cost is higher still). This is a
KNOWN representation gap with a designed successor (the run table, task
#73). The matrix therefore reports three clearly-labeled columns for us:

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
3. **run-table PROJECTION (measured-in-model, NOT shipped)**: the exact
   bit accounting of `whiteboard/litmus/run_table_measure.py` (task #73)
   executed on the same trace via `tools/run_table_projection.py`;
   `projected bytes = ceil(order-metadata bits / 8) + UTF-8 text bytes`.
   The model charges per-record run-id + offset and per-entry headers; it
   does NOT charge the (ts, agent) tie-break (our binary-estimate does
   charge ids) nor any framing. Never read this column as a shipped
   number.

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

Where we lose, as shipped:

* **Per-char apply.** Median 347-364 us on ~21k-char docs, 1.66 ms at 57k
  chars, 3.16 ms at 105k chars: the persistent `apply` copies the live-set
  Map on every op, so cost grows linearly with document size. That is
  ~15-120x slower than Automerge (24-27 us, flat) and 3 to 4 orders of
  magnitude slower than Yjs / Loro / list-positions (0.5-1.7 us, flat).
  Whole-trace replay: 713 s on automerge-paper vs 0.2 s (Loro), 0.67 s
  (Yjs), 7.1 s (Automerge).
* **Save size, as shipped.** 1637-2991 bytes/char as JSON (243 MB for the
  105k-char doc) vs 0.6-10 bytes/char for every production save. Packing
  the same bits (binary-estimate) still leaves 207-376 B/char; the shipped
  compaction (measured, rank-renumber + spine fusion) cuts the coordinate
  bits by 1.9-3.2x, leaving 112-188 B/char. Two orders of magnitude worse
  than production; this is the known absolute-chain-coordinate gap.
* **Load.** 31-253 ms (JSON parse + coordinate sort), vs Loro 0.2-0.3 ms
  and Yjs 2-9 ms. Automerge's full-history load is in our range (29-446
  ms); on automerge-paper ours loads in 253 ms vs Automerge's 319 ms.

Where we are competitive or win, as shipped:

* **Merge/sync.** Unique-LCA `merge3` under the head-sync Runtime: 73 us
  median (freq preset), 731 us (bulk), Yjs-level (90 us / 1.13 ms) and
  20-25x faster than Automerge (1.8 / 18.3 ms) and Loro (6.3 / 17.1 ms)
  in these sessions. Only list-positions' raw op-log apply is comparable
  (34 / 626 us). Caveat: small docs (1.8k / 3.6k chars); our merge is
  O(live set), so this does not extrapolate to 100k-char documents.
* **Storage on delete.** Our save never grows on delete, it shrinks by
  construction (delete = pure record removal): measured 20-46 KB shrink
  per 1800-char delete phase (binary-estimate). See the churn table for
  the production comparison.
* **Resident memory.** Retained heap after full replay is 2-12 MB: the
  absolute coordinates share prefixes structurally (V8 cons strings along
  the anchor chain), so the in-heap state is compact and the bit cost
  only materializes at serialization. The price is allocation churn
  instead: sampled peak heap up to 433 MB during the automerge-paper
  replay (GC-noise caveat applies).

The Automerge-grows-on-delete cell (reproduced): across the five delete
phases Automerge's save grew by +3383, +3327, +3383, +3370, +3430 bytes
(monotone growth to 60,742 B for a 1200-char final doc). Loro's `snapshot`
also grows on every delete phase; Loro's `shallow-snapshot` and Yjs do
not grow, but Yjs cannot shed tombstone structure (165.4 KB v1 / 45.9 KB
v2 for the same 1200 live chars, vs our compacted binary-estimate 7.9 KB;
Loro shallow-snapshot 3.9 KB is the smallest).

Projection, measured-in-model and NOT shipped: recoding the same final
states as the task #73 run table costs 22.3-23.9 bits/char of order
metadata, i.e. 3.8-4.0 bytes/char including the text. That is the same
order of magnitude as production saves, within 1.4x of Yjs update-v1 on
every trace (80,905 vs 81,480 B on friendsforever_flat), but still 3-6x
above the smallest production state serializations (Loro shallow-snapshot,
Yjs v2) and above Automerge's compressed full history on the low-churn
traces. The projection closes the representation gap to rough parity with
Yjs v1; it does not win save size outright.

## The matrix

The tables below are `results/summary.md`, regenerated by every
`node run.mjs` (this copy matches the checked-in results/*.json).

Environment: node v26.3.1, darwin arm64, Apple M4 Pro, 24 GB RAM.
Every cell below was produced by a run in this repo (results/*.json); nothing from literature.

## Sequential replay: automerge-paper (259778 per-char ops, final 104852 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 3.16 ms | 4.37 ms | 713.28 s | 253.3 ms (json-shipped) | 432.5 MB | 12.0 MB | text OK |
| Yjs | 1.38 us | 10.88 us | 0.67 s | 5.5 ms (update-v1) | 113.0 MB | 3.5 MB | text OK |
| Automerge | 26.83 us | 32.96 us | 7.09 s | 319.3 ms (save-full-history) | 105.2 MB | 0.8 MB | text OK |
| Loro | 0.46 us | 1.42 us | 0.20 s | 0.3 ms (snapshot) | 83.8 MB | 0.3 MB | text OK |
| list-positions | 0.67 us | 1.13 us | 0.19 s | 3.0 ms (json-text+order) | 105.8 MB | 2.1 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, automerge-paper (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 243276637 | 2320.2 | 229.4 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 30668998 | 292.5 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | json-shipped+compacted | 135792070 | 1295.1 | 135.4 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 17233096 | 164.4 | -- | packed-bits estimate of the compacted state |
| ours (PROJECTION, run table) | run-table composed (model) | 418298 | 4.0 | -- | measured-in-model (task #73 accounting, gates_ok=true); order metadata 23.9 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 311038 | 3.0 | 5.2 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 159929 | 1.5 | 2.7 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 129126 | 1.2 | 19.1 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 251015 | 2.4 | 12.2 ms | state + full op history |
| Loro | shallow-snapshot | 65066 | 0.6 | 3.2 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 492935 | 4.7 | 2.4 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: clownschool_flat (24326 per-char ops, final 21148 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 347.13 us | 723.25 us | 8.56 s | 43.7 ms (json-shipped) | 126.1 MB | 2.1 MB | text OK |
| Yjs | 1.67 us | 2.38 us | 0.05 s | 2.8 ms (update-v1) | 21.6 MB | 1.7 MB | text OK |
| Automerge | 26.25 us | 32.96 us | 0.66 s | 28.6 ms (save-full-history) | 18.8 MB | 0.8 MB | text OK |
| Loro | 0.75 us | 1.71 us | 0.03 s | 0.3 ms (snapshot) | 12.9 MB | 0.2 MB | text OK |
| list-positions | 0.67 us | 2.83 us | 0.02 s | 0.4 ms (json-text+order) | 19.1 MB | 0.6 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, clownschool_flat (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 52938278 | 2503.2 | 47.1 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 6672560 | 315.5 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | json-shipped+compacted | 31415483 | 1485.5 | 22.6 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 3982162 | 188.3 | -- | packed-bits estimate of the compacted state |
| ours (PROJECTION, run table) | run-table composed (model) | 80993 | 3.8 | -- | measured-in-model (task #73 accounting, gates_ok=true); order metadata 22.6 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 93322 | 4.4 | 1.9 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 42997 | 2.0 | 1.9 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 25724 | 1.2 | 4.8 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 65553 | 3.1 | 7.0 ms | state + full op history |
| Loro | shallow-snapshot | 22732 | 1.1 | 2.7 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 61026 | 2.9 | 0.5 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: friendsforever_flat (26078 per-char ops, final 21362 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 363.54 us | 715.75 us | 9.49 s | 31.2 ms (json-shipped) | 101.0 MB | 2.2 MB | text OK |
| Yjs | 1.54 us | 2.42 us | 0.05 s | 2.2 ms (update-v1) | 20.4 MB | 1.4 MB | text OK |
| Automerge | 24.33 us | 31.79 us | 0.67 s | 30.4 ms (save-full-history) | 20.3 MB | 0.8 MB | text OK |
| Loro | 0.63 us | 1.67 us | 0.03 s | 0.2 ms (snapshot) | 13.7 MB | 0.2 MB | text OK |
| list-positions | 0.63 us | 1.54 us | 0.02 s | 0.8 ms (json-text+order) | 20.0 MB | 0.7 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, friendsforever_flat (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 34971320 | 1637.1 | 31.2 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 4427040 | 207.2 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | json-shipped+compacted | 18607535 | 871.1 | 12.8 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 2381219 | 111.5 | -- | packed-bits estimate of the compacted state |
| ours (PROJECTION, run table) | run-table composed (model) | 80905 | 3.8 | -- | measured-in-model (task #73 accounting, gates_ok=true); order metadata 22.3 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 81480 | 3.8 | 1.8 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 40889 | 1.9 | 1.6 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 27423 | 1.3 | 4.3 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 61707 | 2.9 | 6.2 ms | state + full op history |
| Loro | shallow-snapshot | 21646 | 1.0 | 2.7 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 100337 | 4.7 | 0.7 ms | live chars + position-order metadata (library-native JSON) |

## Sequential replay: seph-blog1 (368209 per-char ops, final 56769 chars)

| system | apply median | apply p95 | total | load (median of 5) | peak heap* | retained heap | gates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 1.66 ms | 2.20 ms | 546.92 s | 166.0 ms (json-shipped) | 318.7 MB | 7.0 MB | text OK |
| Yjs | 1.42 us | 5.29 us | 0.74 s | 9.1 ms (update-v1) | 91.1 MB | 4.6 MB | text OK |
| Automerge | 26.71 us | 31.71 us | 9.91 s | 446.2 ms (save-full-history) | 84.5 MB | 0.9 MB | text OK |
| Loro | 0.58 us | 1.33 us | 0.30 s | 0.2 ms (snapshot) | 67.6 MB | 0.3 MB | text OK |
| list-positions | 0.96 us | 3.67 us | 0.48 s | 3.6 ms (json-text+order) | 85.8 MB | 2.4 MB | text OK |

*peak = JS heapUsed sampled every 500 ops, no forced GC (includes garbage); wasm state (Automerge, Loro) lives outside heapUsed.

### Save size, seph-blog1 (bytes; what each save contains differs -- see notes)

| system | variant | bytes | bytes/char | save time | contains |
| --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 169774875 | 2990.6 | 172.3 ms | live state only; coord bit-strings at 1 byte/bit (shipped) |
| ours (embed RGA, as shipped) | binary-estimate (est.) | 21362422 | 376.3 | -- | live state only; packed coord bits + varint ids (computed estimate, no shipped encoder) |
| ours (embed RGA, as shipped) | json-shipped+compacted | 52956992 | 932.9 | 42.5 ms | live state after settled-cut compaction (measured, shipped code) |
| ours (embed RGA, as shipped) | binary-estimate+compacted (est.) | 6759513 | 119.1 | -- | packed-bits estimate of the compacted state |
| ours (PROJECTION, run table) | run-table composed (model) | 221141 | 3.9 | -- | measured-in-model (task #73 accounting, gates_ok=true); order metadata 23.2 bits/char + UTF-8 text; excludes (ts,agent) ids; NOT a shipped serializer |
| Yjs | update-v1 | 338289 | 6.0 | 4.8 ms | state incl. tombstone structure, deleted content dropped; cannot drop tombstone ids |
| Yjs | update-v2 | 135225 | 2.4 | 2.8 ms | same content as v1, run-length compressed encoding |
| Automerge | save-full-history | 205250 | 3.6 | 25.7 ms | FULL change history (compressed); no state-only save exists |
| Loro | snapshot | 336808 | 5.9 | 14.8 ms | state + full op history |
| Loro | shallow-snapshot | 52683 | 0.9 | 3.0 ms | state, history dropped at current frontiers |
| list-positions | json-text+order | 572686 | 10.1 | 3.2 ms | live chars + position-order metadata (library-native JSON) |

## Concurrent 2-replica session, preset freq (60 rounds x 25 ops/replica/round, seed 42, final 1804 chars)

| system | sync median | sync p95 | sync total | payload/sync | local op mean | primary save | converged |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 73.46 us | 168.75 us | 5.2 ms | n/a (in-process) | 25.65 us | 170693 B (json-shipped) | yes |
| Yjs | 89.54 us | 307.08 us | 7.1 ms | 1.6 KB | 3.98 us | 39782 B (update-v1) | yes |
| Automerge | 1.82 ms | 2.19 ms | 117.2 ms | n/a (in-process) | 35.48 us | 12698 B (save-full-history) | yes |
| Loro | 6.29 ms | 11.40 ms | 381.4 ms | 0.4 KB | 3.04 us | 19642 B (snapshot) | yes |
| list-positions | 33.50 us | 160.50 us | 2.8 ms | 6.4 KB | 2.34 us | 196682 B (json-text+order) | yes |

ours, post-session settled-cut compaction: 3.8 ms, json-shipped+compacted = 58788 B, binary-estimate+compacted = 10448 B; runtime commit-GC total 2.6 ms (outside sync timing).

## Concurrent 2-replica session, preset bulk (6 rounds x 500 ops/replica/round, seed 42, final 3604 chars)

| system | sync median | sync p95 | sync total | payload/sync | local op mean | primary save | converged |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | 730.92 us | 1.12 ms | 4.7 ms | n/a (in-process) | 62.80 us | 386110 B (json-shipped) | yes |
| Yjs | 1.13 ms | 3.67 ms | 8.0 ms | 15.1 KB | 3.20 us | 80667 B (update-v1) | yes |
| Automerge | 18.32 ms | 19.21 ms | 108.0 ms | n/a (in-process) | 30.87 us | 24774 B (save-full-history) | yes |
| Loro | 17.12 ms | 22.04 ms | 98.8 ms | 4.6 KB | 2.30 us | 39130 B (snapshot) | yes |
| list-positions | 626.33 us | 1.01 ms | 4.0 ms | 123.6 KB | 2.02 us | 353262 B (json-text+order) | yes |

ours, post-session settled-cut compaction: 5.9 ms, json-shipped+compacted = 129449 B, binary-estimate+compacted = 22324 B; runtime commit-GC total 8.1 ms (outside sync timing).

## Delete-heavy churn (5 cycles of +2000/-1800 chars, then +200; final 1200 chars)

Save bytes after selected phases; growth-on-delete = does the save GROW across a delete phase.

| system | variant | cycle1-ins | cycle1-del | cycle5-ins | cycle5-del | final-ins | grows on delete? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ours (embed RGA, as shipped) | json-shipped | 150121 | 14666 | 525107 | 188008 | 229695 | NEVER |
| ours (embed RGA, as shipped) | binary-estimate | 22278 | 2191 | 72322 | 25891 | 31596 | NEVER |
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

* A shipped run-table serializer (turn column iii from projection into
  measurement; the model and its gates already exist in task #73).
* A mutable or batched apply path: the O(live-set) Map copy per op is
  inherited from the persistent datatype interface, not from the order
  machinery; a transient-state fast path would move per-char apply toward
  the microsecond class without touching the verified semantics.
* Concurrent sessions at realistic document sizes (the merge numbers here
  are small-doc), and a wire format for our sync (payload column is n/a).

## Files

* `run.mjs`: one-command orchestrator.
* `workloads/seq.mjs|concurrent.mjs|churn.mjs`: the three workloads, one
  child process per (system, workload, trace/preset).
* `lib/adapters/*.mjs`: uniform adapter per system; `lib/adapters/sal.mjs`
  documents the position-to-id bookkeeping and the settled-cut usage.
* `lib/traces.mjs`, `lib/bench.mjs`: trace loading/flattening, timing and
  heap helpers.
* `tools/run_table_projection.py`: runs the task #73 accounting on the
  same traces, writes `results/projection.json`.
* `tools/summarize.mjs`: regenerates `results/summary.md` from
  `results/*.json`.
* `results/*.json`: raw per-job results (checked in).
