# Automating Sal’s five merge VCs

The experiment proves Sal’s **five unchanged merge VCs** from finite equations
and checked history-expansion arguments. Implementations, issuers, policies and
representations stay unchanged. No previous datatype VC/Join proof or additional
datatype state/history invariant is supplied.

**All 23 current named instances have kernel-checked five-VC proofs.** The finite
VC templates are discharged with Lean’s built-in tactics; no external SMT
solver is needed for the final proofs. Some instances also require the
RDT-specific adapter proofs listed below.

## What does the RDT author currently write?

Shared induction templates, coverage proofs and VC-to-Join soundness theorems
are **framework work**, not work to repeat for each RDT. The relevant remaining
cost is instantiating those templates and connecting an RDT’s definitions and
existing certification premises to them.

The table estimates **additional proof-body lines in the current experiment**,
with shared datatype proofs charged once. It excludes RDT descriptions and
generic framework proofs. Small counts include routine unfolding, extensionality,
case splits and calls to `simp`, `grind`, `tauto` or `omega`. Larger counts also
include explicit intermediate arguments and datatype-specific inductions.

| Instance | Approx. additional proof lines | Current datatype-specific work |
|---|---:|---|
| Grow-only set | 10 | Instantiate commuting template; set extensionality and simplification. |
| Add-store | 1 | Reuse the same generic Add-store proof as grow-only set. |
| Finite add-store | 10 | Finite-set extensionality and simplification. |
| Counter | 5 | Generic additive-counter equations, unfolding and `omega`. |
| Increment-only counter | 1 | Specialize the additive-counter proof. |
| PN-counter | 1 | Specialize the same proof to signed increments. |
| Flat grow-only set | 5 | Pointwise Boolean equations and simplification. |
| Flat grow-only map | 1 | Specialize the Boolean-store proof to key/value pairs. |
| Bounded Counter | 20 | Component decomposition, operation cases and `omega`; no new history proof. |
| LWW register | 5 | Maximum algebra, using its existing empty-policy port. |
| Native RGA | 20 | Component decomposition and finite membership equations; no new history induction. |
| TreeMove | 10 | Commuting template, insertion/union unfolding and simplification. |
| AegisSheet | 10 | Commuting template, insertion/union unfolding and simplification. |
| Ordinary OR-set | 230 | Finite equations and policy facts; connect replay and ordering to generic coverage. |
| Efficient OR-set | 300 | Finite equations; update/order certificates and semantic-representation-to-replay adapter. |
| MVR | 85 | One-step membership; issuer overwrite equality to visible-birth evidence; freshness and coverage. Uses generic provenance induction. |
| Embedded RGA | 260 | Generic membership/provenance instantiation; freshness/deletion evidence; list-to-set correspondence and sortedness induction. |
| Sided Embedded RGA | 260 | Corresponding evidence, list normalization and sortedness proofs for sided records. |
| Peritext Embedded RGA | 1 | Specialize the Embedded RGA proof to its payload type. |
| Queue (anchored enqueue) | 1 | Specialize the Embedded RGA proof to its carrier. |
| Sided Peritext Core | 160 | Reuse Sided RGA; text projection, store membership, component normalization and update/merge correspondence. |
| Sided Peritext RichCore | 10 | Reuse Core and adapt context fields. |
| FugueMax | 450 | Birth-store and list adapters, generator branch lemmas, and timestamp induction deriving insertion-chain evidence from issuance. |

These are estimates of the **present marginal proof code**, not lower bounds
on user effort or a prediction for a new RDT from scratch. Reuse rows assume
the named parent proof already exists. Counts also assume the existing library
of raw datatype/collection helper lemmas; they do not include developing those
helpers, existing policy/issuance certification, or sequential bridges.

For example, MVR’s visible-birth argument uses a generic history induction:
its remaining code connects the one-step update and issuer definitions to that
induction. Further templates could remove such per-RDT proof work. We have not
established that any listed adapter must remain user-written.

Counting method: nonblank, noncomment lines in reachable datatype-specific
**theorem bodies**, including tactic setup and assembly. Theorem statements,
definitions, shared framework proofs and unused experimental lemmas are
excluded. Counts are rounded; one-line aliases count as one line. The
[source-count inventory](results/proof-effort.json) records declarations,
source locations, hashes and unrounded dependency totals. Shared totals must
not be added together. Core’s generic store-fold induction is framework work;
its datatype-specific instantiations are counted.

## Scope of the result

The 23 cases include aliases and specializations. Core/RichCore retain their
existing native-insert-only premise. Queue means anchored enqueue; the earlier
unanchored queue is historical and excluded from this count.

The checked metatheory connects the expanded obligations to the five merge VCs
and the existing Join theorem. Full RA-linearizability additionally requires
the sequential-specification bridge. Fugue’s five-VC proof does not resolve its
known sequential-specification obstruction. Sequential-bridge automation is
outside this experiment, and production bundles still use their existing proofs.

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
