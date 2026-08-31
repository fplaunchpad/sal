# Historical 24 VCs versus the ternary Join lemma

## Claim

The historical ternary verification conditions imply the corrected,
set-relative ternary Join lemma:

```text
HistoricalVCs24 D P → JoinWithPolicy D P
```

Status: **refuted**.

Formal oracle: `HistoricalVCs24_not_imply_JoinWithPolicy` in
`Sal/MRDTs/Metatheory/Join/HistoricalVCs.lean`.

Verification command:

```sh
lake env lean Sal/MRDTs/Metatheory/Join/HistoricalVCs.lean
```

The command succeeds without `sorry`, `admit`, or new axioms.

## Checked counterexample

`HistoricalGap` has four states: `initial`, `add`, `rem`, and `conflict`.
An update records whether the operation is `add` or `rem`. Its symmetric
three-way merge returns the changed branch when the other branch equals the
LCA, and returns `conflict` for two distinct changes.

The replay policy returns `Either` for two operations of the same kind and
`Snd_then_fst` for two operations of different kinds. It never returns
`Fst_then_snd`. Consequently:

- `rc_non_comm` holds: `Either` is equivalent to commutativity.
- Every historical interaction VC guarded by `Fst_then_snd` is vacuous.
- The remaining base and induction equations hold by exhaustive case analysis.

`HistoricalGap_historicalVCs24` checks all 24 fields.

Take two concurrent events at different replicas and with distinct timestamps:

```text
e₁ = (0, 0, add)       E₁ = {e₁}       state(E₁) = add
e₂ = (1, 1, rem)       E₂ = {e₂}       state(E₂) = rem
E₁ ∩ E₂ = ∅                              state(∅) = initial
```

Each input state is canonical. The ternary merge is
`merge initial add rem = conflict`. No sequential fold of `{e₁, e₂}` can
produce `conflict`: the last update always leaves `add` or `rem`.
`HistoricalGap_not_joinWithPolicy` checks this failure for every replay
policy, including the policy that satisfies the 24 VCs.

## Controls

Positive control: `HistoricalUnit_historicalVCs24` and
`HistoricalUnit_join` show that the transcription and Join harness admit
a datatype for which both sides hold.

Negative control: `HistoricalFlag_not_historicalVCs24` shows that the
historical LCA-induction VC rejects the earlier last-writer Boolean
countermodel. The new counterexample is therefore not just reusing a model
that the old induction bundle already excludes.

PBT gate: not used. The countermodel has a finite state and application-op
space, and the Lean proofs exhaust those cases directly. Timestamps and
replica identifiers do not affect its update or merge functions.

## Missing constraint

The historical `rc_non_comm` field constrains only the `Either` result. It does
not require a noncommuting pair to produce `Fst_then_snd` in one direction.
The counterexample exploits exactly this gap by producing `Snd_then_fst` in
both directions.

The later `rc_non_comm_directional` condition rejects this model because it
requires every distinct noncommuting pair to be `Fst_then_snd` in at least one
direction. This result establishes that such directional coverage is
necessary for this proof route. It does not establish that adding this one
condition to the historical bundle is sufficient for `Join`.

## Definition audit

The current framework declaration elaborates as:

```text
Join : MRDTSig → Prop
```

It does not retain the section-local `ReplayPolicy` parameter, even though
canonicality depends on replay order. `JoinWithPolicy` makes that
dictionary explicit so the premise and conclusion use the same policy.
`HistoricalVCs24_not_imply_join` also checks that the implication fails
against the current policy-erased declaration.

## Sources and trust boundary

The 24 statements were transcribed from the archived ternary artifact at git
commit `8c22e47dc85a98991b2f77b8f5d010d852637dac`, especially
`CaseStudies/Fstar_like_implementations/MRDTs/SAL/OR_Set_MRDT.lean`.
The OOPSLA paper's generic BottomUp table provides the corresponding published
presentation.

Trusted definitions: the transcription of the historical statements, the
current definitions of `IsCanonicalState` and ternary merge, and the intended
meaning of `ReplayPolicy`. Lean checks consequences of these definitions; it
does not validate that the transcription or the framework semantics match the
historical implementation.

Residual questions:

- Repair `Join` so its replay-policy dependency is explicit throughout
  the framework.
- Test a strengthened bundle containing `rc_non_comm_directional` against
  `JoinWithPolicy`.
- Determine whether the other later additions (`cond_comm_lift`, `merge_init`,
  `commuting_peel`, and the corrected shared-event peel law) are independently
  necessary.
