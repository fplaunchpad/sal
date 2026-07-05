import Sal.MRDTs.Metatheory.Development.RGA_EqQuotient
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant

/-!
# The `l`-argument merge `≈`-congruence, CONDITIONED on the RGA `Inv` (M5)

`RGA_EqQuotient` proved the two *branch*-argument merge `≈`-congruences
(`merge_eq_congr_a`, `merge_eq_congr_b`) unconditionally, and proved the
**`l`-argument congruence FALSE on the full type** (`merge_eq_congr_l_fails`):
two `≈`-equal empty-domain LCAs drive the climb of a surviving *branch-new* node
(whose branch anchor is dead, so `wf a` fails) to different anchors, because the
climb reads `anc l` at an off-`domain l` node where `≈` is silent.

This file proves the `l`-argument congruence **on the reachable subfamily** —
where every input is a `wf` forest — and composes it with the two branch
congruences into the full ternary `≈`-congruence matching the framework's
`GenericEqQuotient.CongVC.mergeL_congr` shape.

## The climb-congruence crux

`anc (merge l a b) k = climb (anc l) (survivors l a b) (birthAnc l a b k)`.  With
`eq l l'`, the survivor set (`domain`-only) and the birth-anchor (read on live
`l` where `≈` fixes it) coincide, so the two merges' anchors differ only through
`anc l` vs `anc l'`.  These agree on every **live-in-`l`** node (`eq l l'`), and —
this is where `wf l` is load-bearing — the climb, started at a birth-anchor that
`betaf_start` places in `{0} ∪ survivors ∪ (live l)` (needs `wf a`, `wf b`), only
ever walks `anc l` through live-in-`l` nodes (`wf l` keeps `anc l` inside the live
forest).  So the two climbs march in lockstep and coincide.  `id_mono l` — the
fuel-sufficiency discipline that `Inv_merge` needs — is **not** required here:
matched fuel makes the two climbs halt together regardless of sufficiency.
-/

set_option maxHeartbeats 1000000

open Sal.Metatheory.RGAConditionedConvergence
open Sal.Metatheory.RGAEqQuotient

namespace RGAMergeCong

/-! ## §1  Climb congruence in the anchor function

If two anchor functions `anc l`, `anc l'` agree on every live-in-`l` node
(`Hag`), and `l`'s forest keeps `anc l` inside the live domain (`Hstay = wf l`),
then their `climb`s coincide on any start in `{0} ∪ I ∪ (live l)`.  The walk visits
only nodes where `Hag` applies, so the two climbs are pointwise identical.  No
id-monotonicity is used: the fuel is the *same* start id on both sides, so they
run out together. -/
theorem climb_aux_anc_congr (l l' : concrete_st) (I : set ℕ)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (Hag : ∀ y, contains l y = true → anc l y = anc l' y) :
    ∀ (fuel x : ℕ), (x = 0 ∨ I x = true ∨ contains l x = true) →
      climb_aux (fun y => anc l y) I fuel x
        = climb_aux (fun y => anc l' y) I fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x _; rfl
  | succ f ih =>
    intro x hs
    by_cases hx0 : x = 0
    · subst hx0; simp [climb_aux]
    · by_cases hIx : I x = true
      · simp [climb_aux, hIx]
      · have hIxf : I x = false := by
          cases hI : I x with
          | true => exact absurd hI hIx
          | false => rfl
        have hlx : contains l x = true := by
          rcases hs with h | h | h
          · exact absurd h hx0
          · simp [h] at hIxf
          · exact h
        have hcondF : (decide (x = 0) || I x) = false := by simp [hx0, hIxf]
        have hstepL : climb_aux (fun y => anc l y) I (f + 1) x
                    = climb_aux (fun y => anc l y) I f (anc l x) := by
          simp only [climb_aux]; rw [if_neg (by rw [hcondF]; simp)]
        have hstepR : climb_aux (fun y => anc l' y) I (f + 1) x
                    = climb_aux (fun y => anc l' y) I f (anc l' x) := by
          simp only [climb_aux]; rw [if_neg (by rw [hcondF]; simp)]
        rw [hstepL, hstepR, ← Hag x hlx]
        exact ih (anc l x) (by
          rcases Hstay x hlx with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))

/-- `climb`-level congruence in the anchor function (fuel matched at the start). -/
theorem climb_anc_congr (l l' : concrete_st) (I : set ℕ)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (Hag : ∀ y, contains l y = true → anc l y = anc l' y) (x : ℕ)
    (hs : x = 0 ∨ I x = true ∨ contains l x = true) :
    climb (fun y => anc l y) I x = climb (fun y => anc l' y) I x := by
  simp only [climb]
  exact climb_aux_anc_congr l l' I Hstay Hag x x hs

/-! ## §2  The `l`-argument merge `≈`-congruence on the `Inv`-subfamily

FALSE on the full type (`merge_eq_congr_l_fails`); here `wf l`, `wf a`, `wf b`
make it hold.  `id_mono l` / `contains l 0 = false` are **not** needed for the
congruence (only for `wf`-preservation, `Inv_merge`): a genuinely weaker
conditioning than the merge state-invariant. -/
theorem merge_eq_congr_l_inv (l l' a b : concrete_st)
    (hlwf : wf l) (hawf : wf a) (hbwf : wf b) (h : eq l l') :
    eq (merge l a b) (merge l' a b) := by
  simp only [wf] at hlwf hawf hbwf
  have hdomll : domain l = domain l' := funext (fun k => (h k).1)
  have hsurv : survivors l a b = survivors l' a b := by
    simp only [survivors, hdomll]
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_merge, contains_merge, hsurv]
  · intro hk
    have hkI : survivors l a b k = true := by rw [← contains_merge]; exact hk
    -- element agreement (needs only `eq l l'` on the live domain)
    have hel : el (merge l a b) k = el (merge l' a b) k := by
      show (if contains l k then el l k else if contains a k then el a k else el b k)
         = (if contains l' k then el l' k else if contains a k then el a k else el b k)
      rw [(h k).1]
      split_ifs with hc hc2
      · exact congrArg Prod.fst ((h k).2 ((h k).1.trans hc))
      · rfl
      · rfl
    -- anchor agreement (the climb-congruence crux)
    have hanc : anc (merge l a b) k = anc (merge l' a b) k := by
      rw [anc_merge, anc_merge]
      -- birth-anchor coincides: read on live `l` (≈-fixed) else off-`l` branch
      have hbirth : birthAnc l a b k = birthAnc l' a b k := by
        unfold birthAnc
        rw [(h k).1]
        split_ifs with hc hc2
        · exact congrArg Prod.snd ((h k).2 ((h k).1.trans hc))
        · rfl
        · rfl
      rw [← hsurv, ← hbirth]
      -- climb (anc l) I x = climb (anc l') I x  with the shared survivor/anchor
      exact climb_anc_congr l l' (survivors l a b) hlwf
        (fun y hy => congrArg Prod.snd ((h y).2 hy)) (birthAnc l a b k)
        (betaf_start l a b hlwf hawf hbwf k hkI)
    exact Prod.ext_iff.mpr ⟨hel, hanc⟩

/-! ## §3  The full ternary merge `≈`-congruence on `Inv`-states

Composes the `l`-step (§2, conditioned) with the two unconditional branch steps
(`merge_eq_congr_a`, `merge_eq_congr_b`).  Matches
`GenericEqQuotient.CongVC.mergeL_congr`, with `Inv = wf ∧ contains·0 = false ∧
id_mono` (the RGA's `qInv`).  Only the `wf` conjuncts of `l`, `a`, `b` are
consumed; `l'`'s `Inv`, both `contains·0` and all three `id_mono`s are carried for
signature shape but not used — the congruence lives on the forest structure,
transported from `l` to `l'` by `≈`. -/
theorem merge_eq_congr_inv (l l' a a' b b' : concrete_st)
    (Il : wf l ∧ contains l 0 = false ∧ id_mono l)
    (_Il' : wf l' ∧ contains l' 0 = false ∧ id_mono l')
    (Ia : wf a ∧ contains a 0 = false ∧ id_mono a)
    (_Ia' : wf a' ∧ contains a' 0 = false ∧ id_mono a')
    (Ib : wf b ∧ contains b 0 = false ∧ id_mono b)
    (_Ib' : wf b' ∧ contains b' 0 = false ∧ id_mono b')
    (hl : eq l l') (ha : eq a a') (hb : eq b b') :
    eq (merge l a b) (merge l' a' b') := by
  have step1 : eq (merge l a b) (merge l' a b) :=
    merge_eq_congr_l_inv l l' a b Il.1 Ia.1 Ib.1 hl
  have step2 : eq (merge l' a b) (merge l' a' b) :=
    merge_eq_congr_a l' a a' b ha
  have step3 : eq (merge l' a' b) (merge l' a' b') :=
    merge_eq_congr_b l' a' b b' hb
  exact eq_trans _ _ _ (eq_trans _ _ _ step1 step2) step3

/-! ## §4  Axiom audit -/

#print axioms merge_eq_congr_l_inv
#print axioms merge_eq_congr_inv

end RGAMergeCong
