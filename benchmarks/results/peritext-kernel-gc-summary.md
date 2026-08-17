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
| RGA | spine | none | 93,651 | 7,502 | -- |
| RGA | spine | history | 93,651 | 2 | -- |
| RGA | spine | state | 93,649 | 7,503 | 814 ms |
| RGA | spine | both | 93,649 | 1 | 781 ms |
| EmbedRGA | spine | none | 23,850 | 7,502 | -- |
| EmbedRGA | spine | history | 23,850 | 2 | -- |
| EmbedRGA | spine | state | 8,864 | 7,503 | 471 ms |
| EmbedRGA | spine | both | 8,864 | 1 | 539 ms |
| RGA | leaves | none | 95,865 | 7,502 | -- |
| RGA | leaves | history | 95,865 | 2 | -- |
| RGA | leaves | state | 51,764 | 7,503 | 9.9 ms |
| RGA | leaves | both | 51,764 | 1 | 9.8 ms |
| EmbedRGA | leaves | none | 54,149 | 7,502 | -- |
| EmbedRGA | leaves | history | 54,149 | 2 | -- |
| EmbedRGA | leaves | state | 25,736 | 7,503 | 15.0 ms |
| EmbedRGA | leaves | both | 25,736 | 1 | 14.9 ms |

## Finding

Commit-history GC and per-state GC solve different problems. History GC reduces
both kernels to one or two commits but leaves document metadata unchanged.
Plain RGA can collect a settled dead leaf, but it must retain a dead ancestor
of a live character. EmbedRGA removes all 2,100 deleted identifiers in both
topologies. This makes EmbedRGA useful even when both GCs are available.

The byte comparison includes each implementation's current continuation
snapshot. `PeritextEmbedRGA` uses the optimized run-table codec.
`PeritextRGA` uses deterministic id/anchor/element tuples and a tombstone list.
Do not present the byte ratio as a representation lower bound until RGA also
has a packed binary codec. The topology-dependent retention result does not
depend on this codec difference.
