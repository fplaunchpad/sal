# WALL 1 (the merge residual) — pen-and-paper, and how the re-base helps

*The sole remaining gap to the end-to-end RGA `≈`-linearizability: `EqJoinLemma3C_NF` for the RGA =
`RgaEqJoinResidual_NF` = the merge=delta-fold branch assembly.*

## The reduction chain (all already mechanized, kernel-clean)

To prove `EqJoinLemma3C_NF` it suffices (via `RGA_EqJoin_NF.rga_eqJoin_of_mergeFoldResidual_NF` +
`isCanonicalStateEqNF_union_of_fold`) to produce, for the LCA enum `ρ₀` and a delta enum `π₀`:

    hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) (mergeL s₀ s₁ s₂)          (†)

And `RGA_MergeConvergenceCanon.merge_fold_indep_canon` shows: if (†) holds for ONE delta enum `π₀`
(the reference `href`), it holds for ANY `loOnEq`-respecting delta enum — by canonical-state
convergence, NO swap oracle. So the residual is: produce ONE `href : eq (merge l a b) (applySeqR l π₀)`.

`RGA_MergeFoldChain.eq_merge_two_sided_final` produces `href` from SIX pieces (l := `s₀`, a := `s₁`,
b := `s₂`):

| piece | content | status |
|-------|---------|--------|
| `hMSR` | swap facts (`Faithful`/`NoFreshClash`/distinct/wf/…) for `vis`-pending pairs | **born-applicable** — `ConditionedExecutionModel.conditioned_premises` emits exactly this for `noopFeasible` prefixes |
| `hcm`  | `CanonMatch F (applySeqR l π₀)` | `canon_fold` on the delta fold |
| `hbridge` | `CanonBirthBridge l F (birthAnc l a b k) rc` — PURE event-set/LCA identity | reduces (`canonBirthBridge_via_branchCanon` → `hin_of_survFilterEq`) to `hFiltEq`: `rcSuf.filter(survB F) = cw.filter(survB F)` (the birth anchor's surviving recorded ancestors = its surviving LCA-forest ancestors) — discharged by path **accuracy** |
| `hD`   | `survivors l a b k = contains (applySeqR l π₀) k` (OR-set = live-set of the delta fold) | not yet mechanized |
| `hB`   | `BranchInv l (applySeqR l π₀)` (per-`Del`, needs `π₀` pinned to branch `Ins`/`Del`) | not yet mechanized |
| `hBE`  | branch-new element = `birthEl l a b k` | not yet mechanized |

## The GAP-1 obstruction and the re-base's resolution

`branchInv2_of_pieces`'s branch-`LiveChain` inputs (`hlive`/`hsurv`/`hsplit`) require the branch
states `s₁`, `s₂` to be the **LITERAL** canonical folds of their enumerations, with the specific
recorded inserts. `IsCanonicalStateEq` supplies them only up to `≈`, and the survivor/anchor
projections needed are NOT `≈`-invariant in the combined-forest form. That is the wall.

**Resolution (the born-applicable re-base).** `GoodConfig3NF`'s `IsCanonicalStateEqNF` carries a
`noopFeasible` delivery `ρ_i` whose RAW fold `σ_i' := applySeqR init_st ρ_i` is a **literal** concrete
state, with `σ_i' ≈ s_i`. Run the entire six-piece merge machinery on the LITERAL folds
`σ₀' , σ₁' , σ₂'` (where the branch `LiveChain` structure genuinely exists — `σ_i'` IS the branch
fold), obtaining

    eq (merge σ₀' σ₁' σ₂') (applySeqR σ₀' π₀)                                 (‡)

then TRANSPORT (‡) to the `≈`-classes `s₀ s₁ s₂` via `mergeL_congr` (the RGA's `≈`-congruence of
`merge`, `rgaCongVC'.mergeL_congr`):

    merge σ₀' σ₁' σ₂'  ≈  merge s₀ s₁ s₂  =  mergeL s₀ s₁ s₂                   (mergeL_congr)

giving (†) by `eq`-transitivity.  The `≈`-vs-literal tension is thereby CONFINED to the transport
step, which `mergeL_congr` discharges — and the six pieces are proved for LITERAL states, where they
are honest facts about the branch folds, not `≈`-classes.

**Reconciliation of the unknown:** the tension was an artifact of stating the merge machinery over the
`≈`-only `IsCanonicalStateEq` witness. The born-applicable delivery gives a *literal* witness fold; the
merge machinery runs there; `mergeL_congr` bridges back. NO strengthening of the merge machinery is
needed — only the born-applicable literal fold + one congruence step.

## Plan

1. **`mergeFold_transport`** (this file's Lean deliverable) — the reconciliation core: from (‡) + the
   three `σ_i' ≈ s_i` + `Inv`s, derive (†) by `mergeL_congr` + `eq`-transitivity. Confines the
   `≈`-vs-literal to one congruence.
2. **`RgaEqJoinResidualLit`** — restate the residual over the LITERAL folds (produce `π₀` with (‡)),
   and `rga_eqJoin_of_residualLit_NF : RgaEqJoinResidualLit → EqJoinLemma3C_NF` via
   `mergeFold_transport` + `isCanonicalStateEqNF_union_of_fold`. Extracts `ρ₁`, `ρ₂` (branch
   deliveries) from the two `IsCanonicalStateEqNF` inputs and `ρ₀` from the LCA.
3. **The six pieces for the literal folds** (`hD`/`hB`/`hBE`/`hbridge`/`hcm`/`hMSR`) — the remaining
   mechanization, now UNBLOCKED (no `≈`-vs-literal): `hMSR` from `conditioned_premises`, `hcm` from
   `canon_fold`, `hbridge` from `hFiltEq` (accuracy), and the OR-set/branch-inv facts (`hD`/`hB`/`hBE`)
   as honest inductions on the literal branch folds.
