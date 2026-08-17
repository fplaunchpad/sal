# Peritext text-kernel GC canary

This canary compares `PeritextRGA` with `PeritextEmbedRGA` on the same
single-writer text churn. It generates 7,501 commits, retains 3,300 visible
characters, and uses two anchor topologies:

- `spine`: each insertion anchors on the previous character;
- `leaves`: every insertion anchors at the root.

The workload contains no marks. This isolates the text kernel and avoids
charging either row for a different marks-pair collector. Each number below is
one isolated quick run on 2026-08-17. Treat timings as canaries, not final paper
statistics.

| Kernel | Topology | GC | State bytes | Commits | State-GC time |
|---|---|---:|---:|---:|---:|
| RGA | spine | none | 52,663 | 7,502 | -- |
| RGA | spine | history | 52,663 | 2 | -- |
| RGA | spine | state | 52,661 | 7,503 | 775 ms |
| RGA | spine | both | 52,661 | 1 | 788 ms |
| EmbedRGA | spine | none | 23,850 | 7,502 | -- |
| EmbedRGA | spine | history | 23,850 | 2 | -- |
| EmbedRGA | spine | state | 8,864 | 7,503 | 471 ms |
| EmbedRGA | spine | both | 8,864 | 1 | 539 ms |
| RGA | leaves | none | 53,770 | 7,502 | -- |
| RGA | leaves | history | 53,770 | 2 | -- |
| RGA | leaves | state | 26,473 | 7,503 | 10.7 ms |
| RGA | leaves | both | 26,473 | 1 | 10.9 ms |
| EmbedRGA | leaves | none | 54,149 | 7,502 | -- |
| EmbedRGA | leaves | history | 54,149 | 2 | -- |
| EmbedRGA | leaves | state | 25,736 | 7,503 | 15.0 ms |
| EmbedRGA | leaves | both | 25,736 | 1 | 14.9 ms |

## Finding

Commit-history GC and per-state GC solve different problems. History GC reduces
both kernels to one or two commits but leaves document metadata unchanged.
Plain RGA can collect a settled dead leaf, but it must retain a dead ancestor
of a live character. EmbedRGA removes all 2,100 deleted identifiers in both
topologies. With both GCs, the packed artifacts differ by only about 3% for
independent leaves, but EmbedRGA is 5.9 times smaller for the spine. EmbedRGA
therefore remains useful for structural tombstones, not for every topology.

The byte comparison includes each implementation's optimized continuation
snapshot. `PeritextEmbedRGA` uses the run-table codec. `PeritextRGA` uses
delta-coded ids, parent distances, length-prefixed UTF-8 elements, and a
delta-coded tombstone list. These are different codecs, so do not present the
ratio as a representation lower bound. The retained-record counts establish
the topology-dependent collection result independently of byte encoding.
