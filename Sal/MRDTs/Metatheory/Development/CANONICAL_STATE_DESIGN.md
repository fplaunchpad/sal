# Update convergence via direct canonical-state characterization

*2026-07-05. The pivot after two machine-checked refutations of swap-based convergence
(`RGA_DepComp_Gate`, `RGA_SimulInduction2`). Both failed because rehoming makes an event's recorded
chain "time-relative" — correct at generation, wrong at reordered intermediate states. This approach
never asks about a not-yet-applied event's faithfulness; it characterizes the fold state directly as a
function of the applied event SET. It is the UPDATE analog of the merge bridge (`eq_merge_single`,
BranchInv, per-id extensional match) — which WORKED.*

## The idea

Two `loOnA`-respecting folds of `E` converge because each equals a canonical state that is a pure
function of `E`. No swaps, no intermediate faithfulness.

Define, for a finite applied-event set `F` (and the ambient recorded data):
- `survivors F` := `{k : k inserted in F} \ {k : k deleted in F}` — a pure function of `F`.
- `canonAnc F k` := climb `recList k` to the nearest id in `survivors F` (or 0) — pure function of `F`.
- `CanonMatch F s` := `∀ k, contains s k = (k ∈ survivors F) ∧ (k ∈ survivors F → anc s k = canonAnc F k ∧ payload s k = recorded k)`.

`CanonMatch F s` says `s` is observationally the canonical state of the set `F`. Note `CanonMatch` is
`eq`-respecting: `CanonMatch F s ∧ s ≈ s' → CanonMatch F s'`.

## The main lemma (by induction on the fold, per-id extensional)

> **`canon_fold`:** for a `loOnA`-respecting enumeration `π` of a dep-closed reachable `E`,
> `CanonMatch (π.toFinset) (applySeqR init_st π)`.

Induction on `π` (prefix by prefix); `F` = the applied set so far. **Crucially the invariant is over
the APPLIED set, not full `E`** — so `canonAnc F` only ever mentions events already folded, and the
"chain ahead of state" failure of the swap approach cannot arise (verified on the refuting trace:
`3` under `2` at `{w1,w2,wc}` = `canonAnc({..wc},3)`; `3` under `1` after `wd` = `canonAnc({..wd},3)`
— matches at every prefix).

- **Base:** `CanonMatch ∅ init_st` — trivial (no survivors).
- **Step `x = Ins k` (fresh `k`):** `F' = F ∪ {k}`. `do_ (fold F) (Ins k)` sets `k`'s anchor by
  resolving `recList k` against `fold F ≈ canonState F`. Since `π` is `loOnA`-respecting, `k`'s
  ancestor-inserts are already in `F`, so `recList k`'s entries are exactly `k`'s genuine ancestors in
  `F`; resolving lands at the nearest survivor = `canonAnc F' k`. Other nodes' anchors/domain
  unchanged, and `survivors F' = survivors F ∪ {k}`. So `CanonMatch F' (do_ …)`. Uses
  `subchain_resolve` / the merge-side climb algebra at the applied-set level.
- **Step `x = Del k`:** `F' = F ∪ {Del k}`. `do_ (fold F) (Del k)` removes `k` and rehomes each child
  of `k` to `k`'s nearest surviving ancestor. `survivors F' = survivors F \ {k}`; each affected node's
  new anchor = climb over the reduced survivor set = `canonAnc F' ·`. This is exactly `branchInv_doDel`
  / the `climb_remove_*` algebra (merge side), reused. So `CanonMatch F' (do_ …)`.

## Convergence — immediate

> **`canon_convergence`:** two `loOnA`-respecting enumerations `π₁, π₂` of `E` satisfy
> `applySeqR init_st π₁ ≈ applySeqR init_st π₂`.

Both `π₁.toFinset = π₂.toFinset = E` (they enumerate the same set). By `canon_fold`,
`CanonMatch E (fold π₁)` and `CanonMatch E (fold π₂)`. Two states with `CanonMatch E` are `eq` (same
domain, same per-id anchor+payload — the definition of `eq`/observational equivalence). Done.

## Why this succeeds where swap failed

- **No unapplied event's faithfulness.** The swap approach needed `Faithful o` (o NOT applied) at
  reordered prefixes — false under rehoming. Here every claim is about APPLIED events matching
  `canonAnc` of the APPLIED set. `canonAnc F` grows with `F`; it never anticipates a future delete.
- **No `DepComp` / no transitivity.** The induction is straight along `π`; the only order fact used is
  that a respecting prefix has each insert's ancestors already applied (prefix-closure — free, as
  established in `prefix_depClosed`).
- **Reuses the WORKING merge machinery.** `subchain_resolve`, `branchInv_doDel`, `climb_remove_*`,
  `resolve_climb_start`, the per-id extensional `eq` characterization (`eq_merge2_of_branchInv2`
  pattern) all transfer — this is the same per-id-extensional style that closed the merge bridge.

## Residuals

- Still conditional on the honest generation discipline: each insert `accurate`+`fresh` at its own
  application (so `recList k` resolves to genuine ancestors) — the `GenDisc2`-style per-event input,
  now used only at each event's OWN application point (where it is true by construction), NOT at
  arbitrary reordered prefixes. This is strictly weaker/cleaner than before.
- `wf`/`id_mono`/`contains 0=false` fold invariants (`ReachInv`, routine).
- The Ins-step "resolve lands at nearest survivor" needs `recList k` = genuine ancestor chain in `F` —
  from the per-event accuracy at `k`'s application (its ancestors are in `F` by respecting-prefix).

## Target

`RGA_update_convergence_canon`: two `loOnA`-respecting enumerations of a backward-closed reachable `E`
fold to `eq`-equal states, conditional only on the per-event generation discipline (+ ReachInv). No
swap oracle, no per-prefix Faithful, no DepComp. Then this + the merge bridge both feed the ≈-quotient.

## Risk

Moderate but well-supported. The per-id-extensional style is proven to work (merge bridge). The main
new work is the Del-step rehoming match at the applied-set level (`branchInv_doDel` analog for the
single-sided fold) and the Ins-step anchor match. Both are single-sided versions of already-proved
two-sided merge lemmas — should be EASIER than the merge bridge, not harder. If a step needs a
merge-side lemma that's only stated two-sided, specialize it. Flag any genuine gap; do not force.
