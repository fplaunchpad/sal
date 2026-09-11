# Repeated sequence-kernel comparison

This report summarizes three isolated repetitions from
`kernel-comparison-repeated.json`. All three kernels use packed continuation
snapshots. The codecs are implementation-specific, so byte ratios measure the
current implementations rather than a representation lower bound.

## Real sequential traces

Values are medians across three runs.

Recovery loads the kernel's continuation snapshot into a fresh state and
materializes the visible sequence. The table reports the median load time.

| Trace | Operations | Kernel | Apply (ms) | Snapshot (bytes) | Recovery (ms) |
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

## Reproduction

Run `node benchmarks/tools/run-kernel-comparison.mjs 3` from the repository
root. The driver exits on any failed semantic or convergence gate and writes
the raw repetitions and aggregate JSON to `benchmarks/results/`.
