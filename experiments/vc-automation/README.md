# Automating Sal’s five merge VCs

The experiment proves Sal’s **five unchanged merge VCs** from finite equations
and checked history-expansion arguments. Implementations, issuers, policies and
representations stay unchanged. No previous datatype VC/Join proof or additional
datatype state/history invariant is supplied.

## Coverage

| RDTs | New expansion route |
|---|---|
| Ordinary and efficient OR-set | All five VCs checked |
| Eight simple set/counter/map registry entries | All five VCs checked |
| Bounded Counter, TreeMove and AegisSheet | All five VCs checked |
| MVR | All five VCs checked |
| LWW, using its existing empty-policy port | All five VCs checked |
| Native, Embedded and Sided RGA | All five VCs checked |
| Peritext, Sided Core and RichCore | All five VCs checked |
| Queue (anchored enqueue) | All five VCs checked |
| FugueMax | All five VCs checked; sequential bridge still obstructed |

The certified audit covers **23/23 current named instances**, including aliases. A five-VC
proof is not by itself an RA-linearizability certificate: the separate sequential
bridge is still required. In particular, Fugue has a known specification
obstruction. Queue here means the current anchored-enqueue implementation. The earlier
unanchored queue is retained only as a historical note in the task list.
Core/RichCore retain their existing native-insert-only premise.

## How much is automated?

We manually developed an induction that reduces histories of arbitrary length
to finite equations. After unfolding the datatype definitions and preparing
those equations, **Lean’s built-in tactics (`simp`, `grind`, `tauto`, and arithmetic automation)
solve them**.
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

## Certified histories

The certified extension derives record provenance, freshness and deletion
coverage from the existing representation and issuance evidence. A generic
fold proof works for any supported, duplicate-free, causally ordered replay;
it does not reissue operations in reordered states. Finite membership equations
then prove the merge VCs. List ordering and product-store adapters are checked
separately. MVR derives overwrite coverage from the existing issuer; Bounded
Counter, TreeMove and AegisSheet use the commuting specialization. These
evidence adapters required manual proof development.

## Reproduce

From the repository root, with production Lean dependencies built, run:

```sh
python3 experiments/vc-automation/verify_expansion.py --all
```

This rebuilds the experiment modules and audits every named five-VC instance.
The [combined audit](results/all-audit.json) records source hashes,
standard Lean axioms and transitive proof dependencies. See the
[scope inventory](transfer-inventory.json) for individual theorem names.
Benchmark details are in [local trials](results/local-campaign.json) and
[causal trials](results/causal-campaign.json).

The production proof bundles
still use their existing proofs. Sequential-specification bridge automation
is outside this experiment.
