import Sal.ConditionedMRDTs.Development.RGA_BirthBridge

/-!
# #39, corrected — the per-survivor `hbridge` bundle, case-A-safe

*Additive; modifies no existing file; 0 `sorry`.*

Skeleton-first, and a CORRECTION. Careful pen-and-paper (see `RGA_BIRTHBRIDGE_DISCHARGE.md`) surfaced
that routing every survivor through `RGAHinFilterEq.canonBirthBridge_of_branchChain` (my earlier
`RGA_BirthBridge.canonBirthBridge_per_survivor`) is WRONG for the off-forest case: it forces
`hlive : IsAncPath σ₀' bw (liveSub σ₀' rcSuf)` UNCONDITIONALLY, but when `bw = birthAnc ∉ σ₀'` is a
branch-new node whose recorded anchor is an LCA node `c ∈ σ₀'`, then `rcSuf = c :: …`,
`liveSub σ₀' rcSuf = c :: …` and `IsAncPath σ₀' bw (c :: …)` demands `anc σ₀' bw = c` while `bw ∉ σ₀'`
gives `anc σ₀' bw = 0` — false.

The fix: route through `RGABranchCanon.canonBirthBridge_via_branchCanon`, whose in-forest obligation
`hin` is CONDITIONAL on `contains σ₀' bw = true`. Off-forest (`bw ∉ σ₀'`) it is supplied VACUOUSLY;
the off-forest bridge itself is discharged internally by `branchCanon_hout` (`hcm`/`hD`). The `bw = 0`
root case is separate (`canonAnc F rc = 0` directly). So the per-survivor residual is exactly
`hRc` = `∃ rcPre rcSuf, split ∧ dead-prefix ∧ (in-forest ⟹ chain reconciliation)`, with the
reconciliation naturally guarded — the branch `LiveChain`/`BranchInv` content lands ONLY in the
`contains σ₀' bw` case, which is where it is provable.

`canonBirthBridge_bundle` produces the FULL `hbridge` shape that `RGA_MergeCanon.canonMatch_merge_of_inputs`
consumes, from that residual. This precisely (re)types the #39 sub-residual, case-A included.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGABirthBridgeBundle

open Sal.Emulation
open RGACanonConvergence (survP CanonMatch canonAnc)
open RGAMergeFoldChain (CanonBirthBridge)
open RGABranchCanon (canonBirthBridge_via_branchCanon)

/-- **#39, corrected bundle.**  For every survivor `t` of `F` (recorded `Ins`, `survP F t`), the
per-survivor `hbridge` obligation of `canonMatch_merge_of_inputs`:

    CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' t) (a :: p)
      ∧ (birthAnc σ₀' σ₁' σ₂' t = 0 ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true)

from the forest invariants (`hlwf`/`hawf`/`hbwf`), the domain identity `hD`, the union-fold
`CanonMatch` `hcm`, `h0`, and the per-survivor residuals: the recorded-chain reconstruction `hRc`
(split + dead-prefix + the *in-forest-guarded* chain reconciliation — the ONLY carrier of branch
`LiveChain`/`BranchInv` content), the root-anchor collapse `hRoot` (for `bw = 0`), the survivor domain
fact `hSurv`, and the birth-anchor 0-or-survivor `hBwSurv`. The `bw ≠ 0` case goes through
`canonBirthBridge_via_branchCanon` (so off-forest is handled without a false `hlive`); the `bw = 0`
case collapses to `canonAnc F (a :: p) = 0`. -/
theorem canonBirthBridge_bundle
    (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t) (fold : concrete_st)
    (hlwf : ∀ t, contains σ₀' t = true → (anc σ₀' t = 0 ∨ contains σ₀' (anc σ₀' t) = true))
    (hawf : ∀ t, contains σ₁' t = true → (anc σ₁' t = 0 ∨ contains σ₁' (anc σ₁' t) = true))
    (hbwf : ∀ t, contains σ₂' t = true → (anc σ₂' t = 0 ∨ contains σ₂' (anc σ₂' t) = true))
    (hD : ∀ j, survivors σ₀' σ₁' σ₂' j = contains fold j)
    (hcm : CanonMatch F fold)
    (h0 : contains σ₀' 0 = false)
    (hSurv : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t → survivors σ₀' σ₁' σ₂' t = true)
    (hRc : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t → birthAnc σ₀' σ₁' σ₂' t ≠ 0 →
        ∃ rcPre rcSuf : List ℕ,
          (a :: p) = rcPre ++ birthAnc σ₀' σ₁' σ₂' t :: rcSuf
          ∧ (∀ c ∈ rcPre, ¬ survP F c)
          ∧ (contains σ₀' (birthAnc σ₀' σ₁' σ₂' t) = true →
              ∃ cw, IsAncPath σ₀' (birthAnc σ₀' σ₁' σ₂' t) cw
                ∧ canonAnc F cw = canonAnc F rcSuf))
    (hRoot : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t → birthAnc σ₀' σ₁' σ₂' t = 0 →
        canonAnc F (a :: p) = 0)
    (hBwSurv : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t →
        birthAnc σ₀' σ₁' σ₂' t = 0 ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true) :
    ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ F → survP F t →
        CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' t) (a :: p)
        ∧ (birthAnc σ₀' σ₁' σ₂' t = 0 ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true) := by
  intro t r e a p hins hsv
  refine ⟨?_, hBwSurv t r e a p hins hsv⟩
  by_cases hbw0 : birthAnc σ₀' σ₁' σ₂' t = 0
  · -- root-anchored survivor: `bw = 0` off-forest, non-surviving; collapse to `canonAnc F rc = 0`.
    rw [hbw0]
    exact ⟨fun hc => absurd hc (by rw [h0]; decide), fun _ => hRoot t r e a p hins hsv hbw0⟩
  · -- `bw ≠ 0`: the branch-canonical bridge, off-forest handled inside (no false `hlive`).
    obtain ⟨rcPre, rcSuf, hsplit, hpreDead, hin⟩ := hRc t r e a p hins hsv hbw0
    exact canonBirthBridge_via_branchCanon σ₀' σ₁' σ₂' F fold t (a :: p) rcPre rcSuf
      hlwf hawf hbwf hD hcm (hSurv t r e a p hins hsv) hbw0 hsplit hpreDead hin

#print axioms canonBirthBridge_bundle

end Sal.ConditionedMRDTs.RGABirthBridgeBundle
