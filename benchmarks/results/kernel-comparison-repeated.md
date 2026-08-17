# Repeated sequence-kernel comparison

This report summarizes three isolated repetitions from
`kernel-comparison-repeated.json`. All three kernels use packed continuation
snapshots. The codecs are implementation-specific, so byte ratios measure the
current implementations rather than a representation lower bound.

## Real sequential traces

Values are medians across three runs.

| Trace | Operations | Kernel | Apply (ms) | Snapshot (bytes) | Load (ms) |
|---|---:|---|---:|---:|---:|
| friendsforever | 35,200 | RGA | 32.0 | 145,183 | 17.4 |
|  |  | EmbedRGA | 20.5 | 59,064 | 13.4 |
|  |  | SidedEmbedRGA | 34.6 | 63,113 | 17.9 |
| clownschool | 43,500 | RGA | 19.1 | 138,358 | 16.8 |
|  |  | EmbedRGA | 16.3 | 62,412 | 12.1 |
|  |  | SidedEmbedRGA | 25.8 | 62,912 | 16.0 |
| seph-blog1 | 368,209 | RGA | 1,892.5 | 1,440,927 | 348.0 |
|  |  | EmbedRGA | 1,795.1 | 161,046 | 47.4 |
|  |  | SidedEmbedRGA | 1,924.0 | 210,153 | 84.3 |
| automerge-paper | 260,978 | RGA | 2,031.9 | 1,182,880 | 267.8 |
|  |  | EmbedRGA | 1,927.2 | 249,973 | 88.6 |
|  |  | SidedEmbedRGA | 2,083.2 | 323,888 | 138.6 |

Plain RGA is 4.7 times larger than EmbedRGA on `automerge-paper` and 8.9
times larger on `seph-blog1`. SidedEmbedRGA costs 1--30% more snapshot space
than EmbedRGA across these traces. On the two large traces, its total apply
time is 7--8% higher than EmbedRGA.

## Concurrent synchronization

| Workload | Kernel | Median sync (us) | Snapshot (bytes) |
|---|---|---:|---:|
| frequent sync | RGA | 134 | 16,886 |
|  | EmbedRGA | 231 | 15,511 |
|  | SidedEmbedRGA | 371 | 9,648 |
| bulk sync | RGA | 918 | 34,165 |
|  | EmbedRGA | 1,181 | 31,796 |
|  | SidedEmbedRGA | 4,119 | 20,247 |

The sided codec is smallest in these concurrent fixtures, but its merge cost
is higher, especially for bulk synchronization. This result does not establish
a general space advantage because the reachable structures and codecs differ.

## Peritext ancestor-spine GC

The full canary performs 21,200 semantic text operations in 90 commit batches.

| Kernel | GC | State bytes | Identity records | Path nodes | Deleted IDs | State GC |
|---|---|---:|---:|---:|---:|---:|
| PeritextRGA | none | 150,563 | 15,200 | 15,200 | 6,001 | -- |
| PeritextRGA | both | 150,561 | 15,200 | 15,200 | 6,000 | 19.5 ms |
| PeritextEmbedRGA | none | 104,954 | 15,200 | 15,200 | 6,001 | -- |
| PeritextEmbedRGA | both | 46,072 | 9,200 | 15,200 | 0 | 32.7 ms |
| PeritextSidedEmbedRGA | none | 135,360 | 15,200 | 15,200 | 6,001 | -- |
| PeritextSidedEmbedRGA | both | 80,965 | 9,200 | 15,200 | 0 | 32.1 ms |

History GC reduces both histories to one commit. Per-state RGA GC cannot
remove deleted nodes on the retained ancestor spine. EmbedRGA removes all
6,000 deleted identifiers and their tombstone records, and produces a state
3.3 times smaller than the collected RGA state. It retains anonymous shared
path nodes on which live coordinates depend; `Path nodes` therefore remains
15,200. Thus EmbedRGA removes per-deletion identity metadata rather than the
ancestor geometry itself, and remains useful even with both GCs.

`PeritextSidedEmbedRGA` implements the machine-checked `LiveGap` observation:
the root and each retained anchor keep one `hasR` bit and at most one successor
id and chain. Shared chain nodes carry no character identity. GC therefore
removes the same 6,000 identity records as EmbedRGA while retaining the path
geometry required by the live spine. Its 80,965-byte state is 76% larger than
one-sided EmbedRGA because sided coordinates and mint-policy summaries provide
the additional evidence for the L19 non-interleaving guarantee; it is 46%
smaller than the collected plain RGA state.

Native prefix-graph depth accounting, inverse translation, and content
fingerprinting reduced median shared EmbedRGA collection time from 8.36
seconds to 32.8 milliseconds (32.4--33.1 ms), over 250 times faster. A larger
60,000-operation stress run, stronger than the configuration that previously
exhausted a 4 GB heap, completes with both GCs in 87.6 ms and leaves a 125,078
byte snapshot. Treat the stress number as a scale check, not a repeated paper
measurement.

The corresponding 60,000-operation sided stress run completes state GC in
88.7 ms, removes all 17,500 deleted identity records, and produces a 223,195
byte snapshot.

## Reproduction

Run `node benchmarks/tools/run-kernel-comparison.mjs 3` from the repository
root. The driver exits on any failed semantic or convergence gate and writes
the raw repetitions and aggregate JSON to `benchmarks/results/`.
