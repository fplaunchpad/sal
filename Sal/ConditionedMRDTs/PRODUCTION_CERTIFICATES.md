# Production certificate pattern

A `VerifiedMRDT` instance supplies four independent pieces:

1. a configuration-level honesty predicate;
2. the initial state invariant;
3. a Join proof through `JoinKitAt`;
4. an independent sequential machine and a history-conditioned refinement.

The fourth field is deliberately history-conditioned. For EmbedRGA,
SidedRGA, and MergeableQueue, the issuer contract includes freshness and
applicability at every prefix. Those facts cannot in general be reconstructed
from the current visible state after deletion.

The three reference packages live in
`MRDT_Instances/VerifiedCertificates.lean`:

| Certificate | Join honesty | Sequential discipline | Intent state |
|---|---|---|---|
| `embedVerified` | `EHonestCore` | `eSeqOK` | naive text buffer |
| `sidedVerified` | `SHonestCore` | `sSeqOK` | two-sided sentinel buffer |
| `queueVerified` | `QHonestCore` | `qOK` | FIFO value list |

Products use `HistorySequentialRefinement.prod`: a mixed history is projected
with `projList₁` and `projList₂`, each component discipline is checked on
its projection, and `applySeq_prod` plus `SequentialSpec.run_prod` assemble the
result.

`embedVerifiedRuntime` extends the EmbedRGA package with the concrete
continuation-aware recoding contract. A `StablePrefixMap` transforms both the
stored state and lagging operations; its domain and future-mint premises are
the explicit `RuntimeRecoding.Admissible` obligation. The theorem
`embedVerifiedRuntime_multiEpoch` packages a compatible map chain through
`chainSPM`. This interface is intentionally distinct from
`StabilityEpochFamily`, whose worlds require complete DAG-level `StabilityVC`
bundles.

`embedQueueVerified` is the concrete heterogeneous product demonstration: an
EmbedRGA document and a mergeable FIFO consume one interleaved sum history,
with convergence and both projected intent disciplines checked compositionally.

Validation uses `Metatheory/ProductionCertificateLedger.lean`, which now also
imports the general refactor ledger. The old namespace collision was removed by
renaming Shesha's callback to `sheshaUpdate`; SidedRGA retains `sUpdate`.
