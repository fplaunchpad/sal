# Verification companion: consolidation layer

This companion records the reusable interfaces extracted from the full proofs
in `sal-mrdts.tex`. Its build target detects interface drift.

## Correctness stack

1. **Causal history → canonical MRDT state**
   - `CanonicalizationDoctrine`, `JoinKitAt`
   - `VerifiedMRDT.ra_linearizable`
2. **MRDT update fold → independent sequential machine**
   - `SequentialSpec`, `HistorySequentialRefinement`
   - history disciplines remain explicit; unconditional local simulations
     embed through `SequentialRefinement.toHistory`
3. **Canonical state → compacted/runtime representation**
   - `WorldCompaction`, `StabilityEpochFamily`
   - `StabilityEpochFamily.multiEpoch_reads`
4. **Negative representation results**
   - `ContinuationEquivalent`, `ContinuationRepresentation`
   - `ContinuationFoolingPair.lowerBound`

## Compatibility guarantees

- `JoinKitAt` is definitionally equivalent to `JoinLemma3At` under the plain
  doctrine and to `JoinLemma3AtW` under the witness doctrine.
- `AbstractJoinAt` gives exact adapters for core, witness-restricted, and
  explicit-arbitration joins over a generic ambient visibility structure.
- The stronger routes intentionally remain separate:
  `ObservationalJoinDoctrine` keeps invariant, full-closure, honest-universe,
  and timestamp-uniqueness premises explicit; `CoherentWitnessJoinDoctrine`
  returns a named witness coherent with both branches. Their adapters preserve
  `EqJoinLemma3C_H` and `JoinLemma3AtWC`, respectively.
- `HonestReach` and `HonestReachV` retain their public names while sharing
  `ContractReach`.
- Widened reachability maintains `GoodConfig3 × StoreInv` in one fold.
- Existing counterexamples remain load-bearing: Shesha still refutes the
  witness-only doctrine, while sibling splice now proves a generic retention
  lower bound.
- Unsafe late-mark compaction is a second retention lower bound. The rehoming
  result uses the same interface but remains explicitly a semantic separation
  from the naive buffer, rather than a physical-state retention claim.
- Pairwise continuation distinguishability makes every correct encoding
  injective. For finite families, `card_history_le_repr` gives the literal
  representation-state lower bound and `card_history_le_two_pow_bits` proves
  that a `Bits`-boolean encoding distinguishes at most `2^Bits` classes.

## Production certificates

`MRDT_Instances/VerifiedCertificates.lean` packages three complete examples:

- `embedVerified`: embedded-chain RGA against the naive text buffer;
- `sidedVerified`: two-sided RGA against the sentinel-based buffer;
- `queueVerified`: mergeable queue against a plain FIFO.
- `embedVerifiedRuntime`: EmbedRGA plus state-and-operation recoding under the
  stable-prefix-map domain contract.
- `embedQueueVerified`: a concrete EmbedRGA × FIFO product certificate.

The migration exposed why sequential honesty belongs at history scope:
Lamport freshness and issuer applicability depend on the full prefix and are
not recoverable from an arbitrary visible state. Product certificates project
both the history and its discipline to each component.

The runtime package is continuation-aware: compaction alone is not the proved
operation, because lagging operations must be translated through the same map.
Compatible epoch chains become one certified world via `chainSPM`.

## Canary migrations

- Positive: embedded-chain RGA, `e_join_kit_at`.
- Negative: Shesha, `shesha_join_kit_at_eff_refuted`.
- Provenance: EmbedRGA, SidedRGA, and MergeableQueue consume the axiom-free
  `GenHonest.exists_causalFold` theorem.

## Validation

The remaining historical placeholders and their corrected/refuted routes are
catalogued in [LEGACY_SORRY_AUDIT.md](LEGACY_SORRY_AUDIT.md).

```sh
lake build Sal.ConditionedMRDTs.Metatheory.RefactorLedger
lake build Sal.ConditionedMRDTs.Metatheory.ProductionCertificateLedger
cd Sal/ConditionedMRDTs
tectonic --keep-logs --keep-intermediates sal-mrdts.tex
```
