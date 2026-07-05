# Rehoming-aware Faith step — no reorder, no DepComp

*2026-07-05. Replaces the deps-first-reorder Faith step of the simultaneous induction, which was
refuted (`DepComp` false: tombstone-free rehoming makes `loOnA` non-transitive,
`RGA_DepComp_Gate.lean`). The architecture (strong induction on `|S|`, `Conv ∧ Faith` together,
maximal-peel) is unchanged and sound; only the Faith step's mechanism changes.*

## Why the old Faith step needed DepComp, and why the new one doesn't

Old: to seat `GenDisc2`'s accuracy base (stated at `o`'s dependency prefix `d`), it reordered the
prefix `ρ ≈ d ++ c` — deps *contiguous* first, concurrents after. Making `d ++ c` `loOnA`-respecting
requires the cross-component `∀ a∈d, b∈c, ¬ lo b a`, i.e. `lo b a → lo a o → lo b o` = **`DepComp`**
(transitivity). Rehoming defeats it (a delete severs `b`'s relevance to `o`).

New: **do not reorder.** Thread the invariant along the *actual* `ρ` in place. The only order fact
used is that **every prefix of a `loOnA`-respecting `ρ` is dependency-closed** — which holds *without
transitivity* (a prefix of a respecting list contains every predecessor of each of its elements,
because predecessors come earlier and are in `ρ`). That is the whole point: prefix-closure is free;
contiguous-reorder is not.

## The Faith step, rehoming-aware

Goal (inside the `|S|`-induction step, `S` dep-closed, IH = `Conv T`, `Faith T` for all dep-closed
`T ⊊ S`): for `o ∈ S` and a `loOnA`-respecting enumeration `ρ ++ [o]` of `S` (so `ρ` enumerates
`S \ {o}`, `o` last), prove `Faithful o (applySeqR init_st ρ)`.

Thread `ChainFaithful (recList o)` along `ρ = [x₁, …, xₖ]` **in place** (recList o is fixed event
data; the invariant is well-defined at every fold state):

- **Base:** `ChainFaithful (recList o) init_st` — vacuous, `chainFaithful_init` (nothing live at
  `init`).
- **Step `xᵢ`:** from `ChainFaithful (recList o) (fold [x₁..xᵢ₋₁])` derive it at `fold [x₁..xᵢ]`,
  by cases on `xᵢ` (a `GoodStep` for `recList o`):
  - `xᵢ` a fresh `Ins`, id `∉ recList o` (concurrent): `chainFaithful_incompFold` / `chainFaithful_doIns`.
  - `xᵢ` a fresh `Ins`, id `∈ recList o` (an ancestor entry of `o` being inserted):
    `chainFaithful_doIns_ancestor` — needs `AncInsLink xᵢ` (`xᵢ`'s recorded anchor is the correct next
    entry). **Supplied by IH-Faith**, see below.
  - `xᵢ` a `Del` (staled or not, **including a delete of `o`'s target/an ancestor** — the rehoming
    case): `chainFaithful_doDel_faithful` — needs `Faithful xᵢ (fold [x₁..xᵢ₋₁])`, and relates the
    deleted node to **nothing** in `recList o`, so it tolerates rehoming. **`Faithful xᵢ` supplied by
    IH-Faith.**
- **Project:** `ChainFaithful (recList o) (fold ρ) → Faithful o (fold ρ)` via
  `climbFaithful_of_chain` / `faithful_of_recPathFaithful`.

## The key move: `xᵢ`'s own faithfulness from IH-Faith on the prefix-set

Both non-trivial step cases need `xᵢ`'s own faithfulness at `fold [x₁..xᵢ₋₁]` (the `AncInsLink` for an
ancestor `Ins`, or `Faithful xᵢ` for a `Del`). Get it from the **induction hypothesis**, applied to
the prefix-set `Tᵢ := {x₁, …, xᵢ}`:

1. `Tᵢ ⊆ S \ {o} ⊊ S`, so `|Tᵢ| < |S|` — IH applies.
2. `Tᵢ` is **dependency-closed**: for `xⱼ ∈ Tᵢ`, every `loOnA`-predecessor `z` of `xⱼ` in `S` lies in
   `Tᵢ`. Proof: `z` is a predecessor, `ρ` respects `loOnA`, so `z` precedes `xⱼ` in `ρ` (hence in
   `[x₁..xⱼ] ⊆ Tᵢ`); and `z ≠ o` (`o` is last, not a predecessor of anything in `ρ`), so `z ∈ ρ`.
   **No transitivity used — only that a respecting prefix contains predecessors.**
3. `[x₁..xᵢ]` is a `loOnA`-respecting enumeration of `Tᵢ` with `xᵢ` last (it is a prefix of the
   respecting `ρ`).
4. Therefore `Faith Tᵢ` (IH, `|Tᵢ| < |S|`) gives `Faithful xᵢ (applySeqR init_st [x₁..xᵢ₋₁])`.
   The `AncInsLink` for the ancestor-`Ins` case follows from `Faithful xᵢ` (recList-consistency of
   `xᵢ` = its recorded anchor resolves correctly = the next-entry link `chainFaithful_doIns_ancestor`
   needs).

That is the whole fix: **each event certifies its own step from IH-Faith at a strictly smaller
dependency-closed set, reached as an in-place prefix of `ρ` — never reordering, never needing
`DepComp`.**

## Conv step (unchanged, and DepComp-free — confirm)

`Conv S`: reorder `π₁, π₂` to put the peeled maximal `m` last via **adjacent transpositions of
`loOnA`-incomparable pairs** (`eqSwap_of_bothFaithful`, Faithfuls from the just-proved `Faith S`).
Swapping *adjacent incomparable* elements preserves `respects` **without transitivity** (only the two
swapped elements' relation matters). Then `Conv (S\{m})` (IH) + `do_eq_congr`. So Conv never needed
`DepComp`; only the old Faith reorder did.

## Why this is not another circular/rebundle move

- No new hypothesis. `DepComp` is **removed**, not replaced. Residuals stay `GenDisc2` + `ReachInv`
  (both honest: the per-event generation discipline and the routine fold invariants).
- Not convergence-circular: `xᵢ`'s faithfulness comes from IH at `|Tᵢ| < |S|` (strict decrease), and
  `Faith S` is proved before `Conv S` within the step (Conv S uses Faith S; both use only IH at
  `⊊ S`). Same measure/ordering as the existing induction.
- Rehoming is handled head-on: the `Del`-of-`o`'s-ancestor case is `chainFaithful_doDel_faithful`,
  which is agnostic to `recList o` — the exact lemma the refutation's counterexample (`d` deleting
  node 1 under node 2) exercises.

## Target

Rebuild the Faith step of `RGA_SimulInduction` (or a sibling file) with the in-place thread + IH-Faith-
on-prefix-set, **deleting the `DepComp` premise**. Output: `RGA_update_convergence` conditional on
`GenDisc2` + `ReachInv` + enumeration hyps only — no `DepComp`, no per-prefix Faithful. This also
supplies the merge side's `FoldBirthChain` (same fold-faithfulness). Then the `≈`-quotient assembles
the metatheorem.

## Residual risk

The one place to watch: `chainFaithful_doIns_ancestor`'s exact hypotheses vs. what `Faithful xᵢ`
provides (the `AncInsLink` shape). If `Faithful xᵢ` is weaker than the `AncInsLink`
`chainFaithful_doIns_ancestor` wants, may need `RecPathFaithful xᵢ` instead — also obtainable from IH
if `Faith` is strengthened to carry `RecPathFaithful` (add it as a third conjunct of the combined
invariant `P`). Flag, don't force.
