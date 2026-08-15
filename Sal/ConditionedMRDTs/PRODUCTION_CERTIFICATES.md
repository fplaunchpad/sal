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

## Public generation and safety contracts

`Metatheory/GenerationContract.lean` layers the actual client policy over raw
`Step3`. `GuardedStep3` checks an apply against the issuing head state, while
`MintCertifiedReach3` retains the existential causal-fold witness that a later
configuration cannot reconstruct after the head advances. This distinction is
load-bearing for the queue: requiring its head guard at every permutation of a
causal past is too strong.

The production guard catalogue is
`MRDT_Instances/ProductionGenerationContracts.lean`:

| Public contract | Local guard | History consequence |
|---|---|---|
| `boundedCounterGeneration` | `bcApplicable` | `BCHonest` (existential-to-universal is proved from count permutation invariance) |
| `queueGeneration` | `qApplicable` | `QHonest` |
| `embedGeneration` | `eApplicable` | `EHonest` |
| `sidedGeneration` | `sApplicable` | `SHonest` |
| `peritextEmbedGeneration` | `eApplicable` at `PeritextElt` | canonical Embed Peritext honesty |

`UnifiedVerifiedMRDT` packages an established `VerifiedMRDT`, its generation
contract, the history-to-Join bridge, and a safety certificate whose invariant
is separate from structural `Configuration` well-formedness. Its product
constructor reuses `VerifiedMRDT.prod`; product client policy and safety laws
remain explicit arguments because they are not consequences of the merge
algorithms.

The bounded-counter public capstone `boundedCounter_flagship` connects its
real guard, RA-linearizability, `BCInv` at every registered version, and
`bc_value_nonneg`. `boundedCounterUnified` packages its Join theorem,
generation contract, independent sequential machine, and global safety proof
in the common interface. `boundedCounterCertificate` also exposes a
counter-specific view of the independent per-replica balance machine
`boundedCounterSequentialRefinement` and the history/global
`boundedCounterSafety` proof. The latter is essential: `BCInv` is not
preserved by an arbitrary ternary merge of three invariant states; it is
preserved for causally related versions by `bc_version_inv`.

Run `sh scripts/check-conditioning-contracts.sh` to ensure every known
nontrivial guard/bridge chain remains represented in the public catalogue and
that gated/refuted designs are not promoted there.

## Audited flat and gated datatypes

The flat production wrappers in `MRDT_Instances/FlatUnifiedCertificates.lean`
use the explicit `True` generation contract only where both the existing Join
capstone and an independent sequential theorem are already present. This
includes ORSet/ORSetE, LWW/FWW registers, GOSet/GOMap, Counter/IOC/PN,
and AWPQ. In particular, FWW's experimental `fwwApplicable` predicate
is not promoted: its own development records that the proposed exclusivity
check is not stable under concurrent extension.

The tombstoned RGA is no longer gated. `RGA_Intent.lean` supplies
`rgaApplicable` (anchor closure, timestamp/id freshness, grave exclusion, and
live-remove checks), `RGAHistoryOK`, the independent `rgaSequentialSpec`,
`rgaSequentialSound`, and the complete `rgaUnified` package. This is separate
from the refuted rehoming/Shesha line.

MVR is also conditioned rather than flattened: `mvrApplicable` requires a
fresh stamp and the exact visible overwrite-tag set, `MVRMintHistory` retains
existential mint provenance, and `mvrUnified` packages its existing `mvrOK`
last-write sequential refinement.

Tombstoned Peritext now supplies `ptApplicable`, `PtHistoryOK`,
`ptSequentialSound`, and `ptUnified`. Its state records character and mark IDs
plus character tombstones, but does **not** retain the timestamp of a remove
operation. Consequently `ptApplicable` checks that the removal target is live;
it cannot reject reuse of a timestamp that appeared only on an earlier remove.
`PtHistoryOK` sequences exactly these state-checkable guards and does not claim
to reconstruct discarded removal timestamps.

EWFlag is packaged without assuming the open Gate-G1 converse. The sibling
`UnifiedVerifiedMRDTF` consumes `EWFlag_joinLemma3F` directly through the
full-closure adequacy theorem; `ewflagUnifiedF` includes its independent
sequential refinement and trivial generation/safety policies.

Shesha's separate anchor/grave machinery still has checked Join and presplice
refutations and remains negative evidence; it is not used by `rgaUnified`.
