# Join-interface inventory

This inventory records the convergence hooks that accumulated as the
conditioned MRDT development learned which information a datatype actually
needs at a merge. It is a refactoring map, not a deprecation notice.

| Interface | Canonical witness | Equality | Extra discipline | Configuration scope |
|---|---|---|---|---|
| `JoinLemma3At` | arbitrary `loOn` witness | state equality | weak noncommuting closure | one core configuration |
| `JoinLemma3AtW` | witness satisfying `W` | state equality | `W` on all three inputs and output | one core configuration |
| `JoinLemma3AtWC` | named `W` witnesses | state equality | coherence relation between the named witnesses | one core configuration |
| `EqJoinLemma3C` | raw fold witness | observational `≈` | invariant, full closure, generation discipline | abstract visibility universe |
| `EqJoinLemma3C_NF` | born-applicable/raw witness | observational `≈` | no separate generation-supply premise | abstract visibility universe |
| `EqJoinLemma3C_H` | witness satisfying `H` | observational `≈` | honest join context and timestamp uniqueness | abstract visibility universe |
| `JoinLemma3AtArb` / `EqJoinLemma3C_ArbH` | corresponding witness family | equality / `≈` | explicit arbitration family | configuration / abstract universe |

## Shared core

All interfaces express the same ternary history equation:

```text
Canon(E₁ ∩ E₂, s₀)  Canon(E₁, s₁)  Canon(E₂, s₂)
-------------------------------------------------
Canon(E₁ ∪ E₂, mergeL s₀ s₁ s₂)
```

They differ along four independent axes:

1. the witness predicate;
2. equality versus observational equivalence;
3. closure and generation/honesty premises;
4. the arbitration relation respected by a witness.

`Metatheory/JoinKit.lean` factors the shared event-set geometry for the first
two state-equality interfaces and supplies definitional adapters.
`Metatheory/AbstractJoin.lean` then abstracts the ambient visibility universe
and supplies definitional adapters for core, witness, and arbitration
canonicity. Observational equality and named-witness coherence remain separate:
their extra premises are semantically load-bearing, not merely alternate
choices of `Canon`. `Metatheory/SeparateJoinDoctrines.lean` formalizes that
policy. `ObservationalJoinDoctrine` exposes invariant, universe, and closure
premises as fields and adapts exactly to `EqJoinLemma3C_H`;
`CoherentWitnessJoinDoctrine` returns a named output witness together with its
two branch-coherence obligations and adapts definitionally to
`JoinLemma3AtWC`.

## Refactoring constraints

- Preserve the counterexamples: a generic interface must not weaken `W` or
  witness coherence merely to obtain a uniform theorem.
- Keep feasibility/honesty premises explicit. They are semantic restrictions,
  not proof noise.
- Prefer adapters into the common interface before changing existing imports.
- Require each adapter to be definitionally equal or proved by a small
  equivalence theorem.
