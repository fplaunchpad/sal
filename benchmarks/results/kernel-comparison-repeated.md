# Repeated sequence-kernel comparison

This report summarizes three isolated repetitions from
`kernel-comparison-repeated.json`. All three kernels use packed continuation
snapshots. The codecs are implementation-specific, so byte ratios measure the
current implementations rather than a representation lower bound.

## Real sequential traces

Values are medians across three runs.

| Trace | Operations | Kernel | Apply (ms) | Snapshot (bytes) | Load (ms) |
|---|---:|---|---:|---:|---:|
| friendsforever | 35,200 | RGA | 30.7 | 145,183 | 17.5 |
|  |  | EmbedRGA | 21.2 | 59,064 | 15.0 |
|  |  | SidedEmbedRGA | 35.1 | 63,113 | 17.3 |
| clownschool | 43,500 | RGA | 18.1 | 138,358 | 17.5 |
|  |  | EmbedRGA | 16.4 | 62,412 | 13.1 |
|  |  | SidedEmbedRGA | 26.5 | 62,912 | 16.9 |
| seph-blog1 | 368,209 | RGA | 2,000.2 | 1,440,927 | 355.0 |
|  |  | EmbedRGA | 1,906.0 | 161,046 | 52.4 |
|  |  | SidedEmbedRGA | 2,063.6 | 210,153 | 87.9 |
| automerge-paper | 260,978 | RGA | 2,184.8 | 1,182,880 | 269.8 |
|  |  | EmbedRGA | 2,081.8 | 249,973 | 90.4 |
|  |  | SidedEmbedRGA | 2,237.9 | 323,888 | 140.5 |

Plain RGA is 4.7 times larger than EmbedRGA on `automerge-paper` and 8.9
times larger on `seph-blog1`. SidedEmbedRGA costs 1--30% more snapshot space
than EmbedRGA across these traces. On the two large traces, its total apply
time is 7--8% higher than EmbedRGA.

## Concurrent synchronization

| Workload | Kernel | Median sync (us) | Snapshot (bytes) |
|---|---|---:|---:|
| frequent sync | RGA | 131 | 16,886 |
|  | EmbedRGA | 247 | 15,511 |
|  | SidedEmbedRGA | 376 | 9,648 |
| bulk sync | RGA | 915 | 34,165 |
|  | EmbedRGA | 1,205 | 31,796 |
|  | SidedEmbedRGA | 4,264 | 20,247 |

The sided codec is smallest in these concurrent fixtures, but its merge cost
is higher, especially for bulk synchronization. This result does not establish
a general space advantage because the reachable structures and codecs differ.

## Peritext ancestor-spine GC

The full canary performs 21,200 semantic text operations in 90 commit batches.

| Kernel | GC | State bytes | Records | Deleted IDs | State GC |
|---|---|---:|---:|---:|---:|
| PeritextRGA | none | 150,563 | 15,200 | 6,001 | -- |
| PeritextRGA | both | 150,561 | 15,200 | 6,000 | 20.7 ms |
| PeritextEmbedRGA | none | 104,954 | 15,200 | 6,001 | -- |
| PeritextEmbedRGA | both | 46,072 | 9,200 | 0 | 8,358 ms |

History GC reduces both histories to one commit. Per-state RGA GC cannot
remove deleted nodes on the retained ancestor spine. EmbedRGA removes all
6,000 deleted identifiers and produces a state 3.3 times smaller than the
collected RGA state. Thus EmbedRGA remains useful even with both GCs.

The current shared EmbedRGA compactor is not production-ready at this scale:
its median collection time is 8.36 seconds. The original 57,500-operation
configuration also exhausted a 4 GB heap. These are measured implementation
limits and the next optimization target, not excluded benchmark results.

## Reproduction

Run `node benchmarks/tools/run-kernel-comparison.mjs 3` from the repository
root. The driver exits on any failed semantic or convergence gate and writes
the raw repetitions and aggregate JSON to `benchmarks/results/`.
