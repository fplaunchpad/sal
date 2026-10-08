# Automating Sal’s five merge VCs

**All 23 current named instances have kernel-checked five-VC proofs.** The
finite equations close with Lean tactics (`simp`, `grind`, `tauto`, `omega`,
`aesop`); the final proofs require no external SMT solver. Implementations,
issuers, representations, policies and VC statements are unchanged.

## What does the RDT author supply?

Shared induction templates and soundness proofs are framework work. The author
supplies datatype mappings, finite-law instantiations and any required helper
lemmas. The table reports the current local proof/annotation code, charging
shared families once. Counts include statements and annotations, not just tactic
bodies; they exclude RDT implementation definitions and generic framework code.

| Instance | Approx. local code lines | Current author work |
|---|---:|---|
| Grow-only set | 10 | Commuting template, set extensionality and simplification. |
| Add-store | 1 | Reuse the same Add-store proof as grow-only set. |
| Finite add-store | 10 | Finite-set extensionality and simplification. |
| Counter | 5 | Additive-counter equations and `omega`. |
| Increment-only counter | 1 | Specialize the additive-counter proof. |
| PN-counter | 1 | Specialize it to signed increments. |
| Flat grow-only set | 7 | Pointwise Boolean equations. |
| Flat grow-only map | 1 | Specialize the Boolean-store proof. |
| Bounded Counter | 21 | Component decomposition, operation cases and `omega`. |
| LWW register | 6 | Maximum algebra, using its existing empty-policy port. |
| Native RGA | 21 | Component decomposition and finite membership equations. |
| TreeMove | 10 | Commuting template and insertion/union simplification. |
| AegisSheet | 10 | Commuting template and insertion/union simplification. |
| Ordinary OR-set | 108 | Raw-definition annotations, operation cases and finite policy equations; the template converts its replay witness. |
| Efficient OR-set | 218 | The same finite equation template, plus mask mappings and projections of its existing live/dead representation. |
| MVR | 15 | Four record mappings, six finite laws and template instantiation. |
| Embedded RGA | 113 | Ordered-record mappings, finite laws, helper references and existing honesty projections. |
| Sided Embedded RGA | 112 | The corresponding sided-record mappings and finite laws. |
| Peritext Embedded RGA | 3 | Specialize the Embedded RGA theorem. |
| Queue (anchored enqueue) | 4 | Specialize the Embedded RGA theorem. |
| Sided Peritext Core | 209 | Text projection, store membership and component normalization; reuses the earlier Sided RGA adapter. |
| Sided Peritext RichCore | 11 | Reuse Core and adapt context fields. |
| FugueMax | 548 | Record/list adapters, generator lemmas and an issuance timestamp induction. |

These are current code-size estimates, not unavoidable human effort. One-line
reuse rows assume the parent proof exists. The
[declaration inventory](results/proof-effort.json) records source locations,
hashes and dependency totals; shared dependency totals must not be summed.
Core and Fugue retain their existing expansion routes.

Both OR-sets, MVR and both RGAs use shared templates; their instance files
contain no history induction. Queue and Peritext reuse the Embedded RGA template. Lean selects
registered RGA membership, ordering and equality helpers automatically. For both
OR-sets, a shared tactic unfolds registered raw definitions, converts equation
assumptions to membership formulas, and solves the finite cases with `simp` and
`grind`. Operation cases and frozen-state choices remain explicit.

The local-code counts exclude existing helper-library proofs: Embedded RGA
uses another **135 lines**, and Sided RGA **143 lines**. Each registers five
helper names; eight lines of identifier reasoning and 14 lines of registry/tactic
declarations are shared. If the helpers are unavailable, the RDT author must supply them.
Neither OR-set route uses an existing datatype theorem helper. Their shared
finite registry/tactic adds **11 declaration lines**; policy assembly adds **49**,
and the efficient representation’s mask template adds **64**. These framework
costs are separate from the per-instance rows and reuse the generic coverage
library. The [helper inventory](results/template-effort.json) records these costs.

Mappings, finite-case setup and projections of existing certification evidence
remain explicit. The templates do not automatically establish issuer honesty
for a new RDT. The audit excludes the old datatype history adapters from these
seven template-based proofs.

## Scope and reproduction

The 23 cases include aliases and specializations. Core/RichCore retain their
native-insert-only premise. Queue means anchored enqueue; the earlier unanchored
queue is historical and excluded. Five VCs feed the checked Join theorem, but
full RA-linearizability additionally needs the sequential bridge. Fugue’s
sequential-specification obstruction remains open. Sequential-bridge automation
is deferred; production bundles still use their existing proofs.

From the repository root, with production dependencies built:

```sh
python3 experiments/vc-automation/verify_expansion.py --automated
python3 experiments/vc-automation/measure_template_effort.py
```

This rebuilds all 23 cases, selecting the reusable templates for both OR-sets, MVR,
Embedded RGA, Sided RGA, Queue and Peritext. The [combined audit](results/automated-audit.json)
records source hashes, standard Lean axioms and transitive dependencies. The
[scope inventory](transfer-inventory.json) identifies each theorem.
