# Repeated Peritext bulk evaluation

This report summarizes `peritext-paper-repeated.json` (three fresh-process
repetitions per cell, 162 trials). Every trial passed its render, convergence,
snapshot, evidence-refusal, and scenario-specific GC gates. Values are medians.

The design uses all four informative modes (`none`, `history`, `full-state`,
and `both`) for the concurrent and format traces. It uses smaller mode subsets
for mark churn, empty documents, delayed offline evidence, and repeated epochs,
where the omitted modes would repeat the same claim.

## Combined-GC result

| workload | kernel | elapsed (s) | durable state | commits before -> after | identity records | marks |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| concurrent rich | RGA | 13.56 | 205,426 B | 4,108 -> 1 | 1,608 | 1,426 |
| concurrent rich | EmbedRGA | 13.07 | 95,438 B | 4,108 -> 1 | 1,502 | 1,426 |
| concurrent rich | SidedEmbedRGA | 14.53 | 212,685 B | 4,108 -> 1 | 1,502 | 1,426 |
| format trace | RGA | 35.98 | 204,936 B | 26,753 -> 1 | 22,313 | 173 |
| format trace | EmbedRGA | 36.18 | 72,182 B | 26,753 -> 1 | 21,869 | 173 |
| format trace | SidedEmbedRGA | 36.63 | 203,219 B | 26,753 -> 1 | 21,869 | 173 |
| mark churn | RGA | 41.80 | 4,069 B | 4,543 -> 1 | 500 | 0 |
| mark churn | EmbedRGA | 42.21 | 1,014 B | 4,543 -> 1 | 500 | 0 |
| mark churn | SidedEmbedRGA | 42.40 | 3,764 B | 4,543 -> 1 | 500 | 0 |
| empty document | RGA | 0.32 | 65 B | 1,203 -> 1 | 0 | 0 |
| empty document | EmbedRGA | 0.32 | 9 B | 1,203 -> 1 | 0 | 0 |
| empty document | SidedEmbedRGA | 0.32 | 61 B | 1,203 -> 1 | 0 | 0 |
| offline, delayed evidence | RGA | 4.12 | 105,530 B | 2,502 -> 1 | 1,266 | 707 |
| offline, delayed evidence | EmbedRGA | 4.23 | 50,019 B | 2,502 -> 1 | 1,121 | 707 |
| offline, delayed evidence | SidedEmbedRGA | 4.49 | 108,034 B | 2,502 -> 1 | 1,121 | 707 |

## Interpretation

The two collectors remove different metadata. Per-state GC reduces tombstones,
obsolete coordinates, and closed mark pairs; history GC reduces the commit DAG.
Using both reaches the small empty-document floors above and reduces every
single-epoch history shown here to one commit.

EmbedRGA retains roughly half the bytes of RGA and SidedEmbedRGA on the
concurrent and offline workloads, and about one third on format and mark churn.
SidedEmbedRGA has no clear throughput penalty on the trace workloads: their
median elapsed times differ by less than two percent. Its visible cost in this
implementation is durable ordering metadata, paid for the stronger interleaving
policy. The paper should present that semantic/space tradeoff explicitly.

The multi-epoch workload is included in the JSON artifact but omitted from the
commit column above: it collects at three intermediate cuts, and the generic
`commitsBeforeFinalGc` field describes only the final epoch rather than total
history removed. Its scenario-specific gates and `intermediatePruned` metric are
the appropriate evidence.
