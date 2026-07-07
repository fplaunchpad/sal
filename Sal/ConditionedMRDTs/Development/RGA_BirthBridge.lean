import Sal.ConditionedMRDTs.Development.RGA_HinFilterEq

/-!
# #39 skeleton — `CanonBirthBridge` per survivor, reduced to the four carriers

*Additive; modifies no existing file; 0 `sorry`.*

Skeleton-first (see `RGA_BIRTHBRIDGE_DISCHARGE.md`). `canonBirthBridge_per_survivor` lifts the built
`RGAHinFilterEq.canonBirthBridge_of_branchChain` to ALL survivors, taking the four branch-chain
carriers (`hsplit`/`hpreDead`/`hlive`/`hsurv`) as a per-survivor ∃-bundle `hcarriers`. That bundle is
the ENTIRE residual of #39: by the pen-and-paper it comes from the branch `LiveChain` (`CanonInv ρᵢ σᵢ'`,
#37) + `BranchInv σ₀' σ₁'`/`σ₀' σ₂'` I4 (the sole genuine sub-residual, case (ii)) + `survP`/`deletedIn`
set-algebra. This lemma is exactly the `CanonBirthBridge` part of `hMergeInputs`, so discharging
`hcarriers` closes #39.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGABirthBridge

open Sal.Emulation
open RGACanonConvergence (survP CanonMatch)
open RGAHinFilterEq (canonBirthBridge_of_branchChain)
open RGAMergeFoldChain (CanonBirthBridge)

/-- **#39, reduced to the carriers.**  For every survivor `k` (recorded insert in `F`, `survP F k`,
`birthAnc ≠ 0`), `CanonBirthBridge σ₀' F (birthAnc k) (a::p)` — given the forest invariants, the
domain identity `hD`, the union-fold `CanonMatch` `hcm`, and the per-survivor carrier bundle
`hcarriers` (`hsplit`/`hpreDead`/`hlive`/`hsurv`). The carriers are #39's residual. -/
theorem canonBirthBridge_per_survivor
    (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t) (fold : concrete_st)
    (hlwf : ∀ t, contains σ₀' t = true → (anc σ₀' t = 0 ∨ contains σ₀' (anc σ₀' t) = true))
    (hawf : ∀ t, contains σ₁' t = true → (anc σ₁' t = 0 ∨ contains σ₁' (anc σ₁' t) = true))
    (hbwf : ∀ t, contains σ₂' t = true → (anc σ₂' t = 0 ∨ contains σ₂' (anc σ₂' t) = true))
    (hD : ∀ j, survivors σ₀' σ₁' σ₂' j = contains fold j)
    (hcm : CanonMatch F fold)
    (hcarriers : ∀ (k r e a : ℕ) (p : List ℕ), (k, r, .Ins e p a) ∈ F → survP F k →
        birthAnc σ₀' σ₁' σ₂' k ≠ 0 →
        ∃ rcPre rcSuf : List ℕ, (a :: p) = rcPre ++ birthAnc σ₀' σ₁' σ₂' k :: rcSuf
          ∧ (∀ c ∈ rcPre, ¬ survP F c)
          ∧ IsAncPath σ₀' (birthAnc σ₀' σ₁' σ₂' k) (liveSub σ₀' rcSuf)
          ∧ (∀ c ∈ rcSuf, survP F c → contains σ₀' c = true)) :
    ∀ (k r e a : ℕ) (p : List ℕ), (k, r, .Ins e p a) ∈ F → survP F k →
        birthAnc σ₀' σ₁' σ₂' k ≠ 0 →
        CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' k) (a :: p) := by
  intro k r e a p hins hsv hbwne
  obtain ⟨rcPre, rcSuf, hsplit, hpreDead, hlive, hsurv⟩ := hcarriers k r e a p hins hsv hbwne
  have hsurvk : survivors σ₀' σ₁' σ₂' k = true := by
    rw [hD k]; exact (hcm.1 k).mpr hsv
  exact canonBirthBridge_of_branchChain σ₀' σ₁' σ₂' F fold k (a :: p) rcPre rcSuf
    hlwf hawf hbwf hD hcm hsurvk hbwne hsplit hpreDead hlive hsurv

#print axioms canonBirthBridge_per_survivor

end Sal.ConditionedMRDTs.RGABirthBridge
