# Automating Sal’s five merge VCs

**All five merge VCs are proved for both exact and efficient OR-set.**
The new proofs use the existing implementations and VC statements. Lean checks
both complete proofs, without reusing their previous VC or Join proofs or
supplying extra datatype state/history invariants.

## How much is automated?

We manually developed an induction that reduces histories of arbitrary length
to finite equations. After unfolding the datatype definitions and preparing
those equations, **Lean’s built-in `simp` and `grind` tactics solve them**.
They produce proofs checked by Lean’s kernel; no external solver is needed.

The induction and its coverage argument are also proved in Lean, but were
written manually. Automatically discovering this expansion remains future work.

The checked metatheory connects the expanded obligations to Sal’s original
five merge VCs, which feed into the existing Join theorem. Obtaining
RA-linearizability also requires the separate sequential-specification bridge.

## Solver comparison

We tested three approaches on 30 local-redistribution, freshness and causal-delta
equations across the two OR-sets, using the same preparation for each approach.

| Approach | Lean-checked proofs | Solver successes without checked proofs | Unsolved |
|---|---:|---:|---:|
| Lean’s built-in automation (`simp` / `grind`) | **30/30** | 0 | 0 |
| lean-smt with cvc5 | 24/30 | 0 | 6 |
| Lean-auto with Z3 | 4/30 | 26/30 | 0 |

Lean-auto’s four checked proofs came from its internal simplification. Its Z3
successes did not produce kernel-checked proofs. lean-smt returned incomplete
responses for six equations.

These 30 equations are a benchmark, not the five VCs themselves or a minimal
list of proof obligations. Some exploratory equations are unused by the final
proof. The complete five-VC proofs were checked separately.

## Check the result

The two complete proofs are in [ExpandedVCs.lean](ExpandedVCs.lean).
The local and causal induction bridges are in
[LocalAssembly.lean](LocalAssembly.lean) and
[CausalCoverage.lean](CausalCoverage.lean).

From the repository root, with the production Lean dependencies built, run:

```sh
python3 experiments/vc-automation/verify_expansion.py
```

This rebuilds all 15 experiment modules and audits both proofs. The
[audit](results/expansion-audit.json) confirms standard Lean axioms only and no
reuse of previous datatype invariant, VC or Join proofs. Benchmark results are
recorded in [local trials](results/local-campaign.json) and
[causal trials](results/causal-campaign.json).

## What remains

These proofs are experimental; the production proof bundles still use their
existing proofs. The next extension is to other RDTs. Issuance-certified RDTs
also need the expansion to preserve their issuance and reachability evidence.
Automation of the separate sequential-specification bridge is outside this
experiment.
