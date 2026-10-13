# Distinct operations in rc-non-comm

**Result:** the distinct-application-operation equation holds for efficient
OR-set, but it cannot replace the existing replay laws by itself. Equal-operation
concurrent pairs still need a concrete swap argument. Production laws,
implementations, specifications and issuers are unchanged.

The [full soundness follow-up](rc-non-comm-full-soundness.md) tests the complete
five-VC contracts, rather than the replay-law implication in isolation.

## The proposed equation

For eligible concurrent events `a = (ta, ra, oa)` and `b = (tb, rb, ob)`:

```text
oa ≠ ob  implies
  (not Commutes_Inv(a,b) iff rc(oa,ob) or rc(ob,oa))

Commutes_Inv(a,b) := for every s satisfying Inv,
  update(update(s,a),b) = update(update(s,b),a)
```

`rc` takes application operations. Concrete commutation takes complete events.
The operation inequality exempts equal payloads from this equation; it does not
make their effectors commute. On a supported concurrent event pair with distinct
payloads, timestamp and replica inequality follow from execution facts. The
new scoped adapters prove this implication explicitly.

## Why the exemption needs another argument

Take a datatype with one application operation and concrete update
`update(s, (t,r,op)) = t`. Let `a = (1,0,op)` and `b = (2,1,op)` be concurrent.
Use empty `rc`, empty visibility, and invariant `True`.

The proposed exactness equation holds vacuously; no-rc-chain and conditional
commutation also hold. Both `[a,b]` and `[b,a]` are complete, legal,
order-respecting replays, but their results are respectively **2 and 1**.
This is a kernel-checked failure of replay uniqueness under the proposed laws.
It is **not** a counterexample satisfying all five merge VCs and every
additional representation obligation. That stronger claim is not established.

The affected proof step is `GuardedConvergence.lean`'s use of
`noncomm_exact` to obtain an `rc` direction for a noncommuting pair being
exchanged. Operation inequality is not available there. The five merge VCs
derive representation closure under Join; `ConcreteVCExecution.lean` still
separately invokes replay uniqueness when constructing its correctness
certificate. The counterexample targets that separate replay implication.

Two checked ways to close the gap are:

- **Raw replay:** require equal-payload, timestamp-distinct, different-replica
  events to commute concretely. Combined with the proposed laws, this recovers
  the existing guarded replay theorem. This convenient global condition is
  stronger than the minimum local swap obligation.
- **Certified replay:** retain the existing diamond for every eligible,
  concurrently ready, unordered pair at a represented prefix, including equal
  payloads. The policy equation can then use operation inequality. Existing
  supported scoped certificates adapt without changing that diamond.

The certified diamond is a separate obligation, not a consequence proved here
from the five merge equations. Its necessity is checked by the countermodel:
it satisfies the new policy equation but cannot supply the diamond.

## Efficient OR-set

Different application operations satisfy the proposed equation even without
timestamp or replica inequalities. For repeated `add(x)` at one replica,
executing timestamps 1 then 2 retains tag 2; reversing them retains tag 1.
These equal operations still fail concrete commutation. Their causal edge
preserves the needed order, even though `rc(add(x), add(x))` is false.

Equal `add(x)` events from different replicas commute, so the efficient set
satisfies the raw repair above. Equal-operation causal successors can also
serve as absorbers: the checked local-add example absorbs a differing prefix,
whereas a remote add does not. Therefore concrete commutation must remain in
both the causal and absorber clauses of the ordering definition.

## Changes needed in the paper

Locations refer to the locally inspected manuscript `0450d48` (8 October 2026),
not a newly fetched Overleaf revision.

1. **`ralin.tex`, Notations and the rc-non-comm display (lines 35 and 140):**
   distinguish complete events from their operation projections. State the
   equation above with its eligible-event, concurrency and state-domain scope.
   Do not define concrete commutation to hold automatically for equal payloads.
2. **Replay-law assumptions and the Uniqueness proof (`lem:unique`):** the step
   “they do not commute, so rc-non-comm applies” needs a case split on operation
   equality. Supply the extra equal-operation swap condition, or state the
   certified theorem over legal causal replays with its independently proved
   diamond. Scoped uniqueness does not imply arbitrary public-order uniqueness.
3. **The order definition and conditional commutation:** retain actual concrete
   noncommutation for causal edges and absorbers. No change to no-rc-chain is
   justified by this experiment.

The bare replacement was refuted, so it has not been applied to production
certificates. The scoped alternatives are proved as explicit adapters rather
than silently weakening the existing contracts.

## Checked sources

- [Counterexample](../Sal/MRDTs/Paper1/DistinctOperationCounterexample.lean)
- [Raw repaired replay theorem](../Sal/MRDTs/Paper1/DistinctOperationReplay.lean)
- [Certified and invariant-scoped adapters](../Sal/MRDTs/Paper1/DistinctOperationPolicy.lean)
- [Efficient OR-set equation and controls](../Sal/MRDTs/Paper1/EfficientORSetDistinctOperation.lean)
- [Combined positive and negative controls](../Sal/MRDTs/Paper1/DistinctOperationControls.lean)

Validation: the Paper1 ledger imports the combined controls; the new printed
axiom closures contain only Lean's standard logical axioms. Both
`sh scripts/check-paper1.sh` and `sh scripts/check-mrdt-refactor.sh` pass
(187 runtime tests, 569 benchmark-result validations). The production automation
audit passes for all 23 named cases and 95 existing theorem roots. No datatype
implementation, independent sequential specification or issuance contract was
changed by this investigation.
