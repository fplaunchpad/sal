import Sal.ConditionedMRDTs.Development.RGA_BirthBridge_Split

/-!
# The `hRc` producer — case B-i (the LCA-node survivor), `BranchInv`-free

*Additive; modifies no existing file; 0 `sorry`.*

Assembles the `hRc` residual of `RGA_BirthBridge_Bundle.canonBirthBridge_bundle` for a survivor `t`
that is an LCA node (`contains σ₀' t`). Then `bw = birthAnc = anc σ₀' t`, the birth branch IS `σ₀'`,
and `split_liveChain` at `s := σ₀'` yields the split together with `hlive = IsAncPath σ₀' bw
(liveSub σ₀' rcSuf)` — no `BranchInv`. The reconciliation is then `hin_via_liveSub` verbatim. The
ONLY residuals are the two set-algebra facts over the recorded chain: `hpreDead` (σ₀'-dead recorded
ancestor ⟹ non-survivor) and `hsurv` (surviving recorded ancestor ⟹ σ₀'-live) — both from
`deletedIn ρ₀ ⊆ deletedIn F` + reference-causality, and admitted here.

Case B-ii (branch-new survivor) is the analogous assembly at `s := σ₁'/σ₂'` composed with the σ→σ₀'
forest transport `BranchInv σ₀'σ₁'/σ₀'σ₂'` — the sole crux — and is done separately.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGABirthBridgeHRc

open Sal.Emulation
open RGACanonConvergence (survP canonAnc CanonInv insertedIn)
open RGAHinFilterEq (hin_via_liveSub)
open RGABranchCanon (survB canonAnc_filter_surv)
open Sal.ConditionedMRDTs.RGABirthBridgeSplit (split_liveChain)

/-- **`hRc` for an LCA-node survivor** (`contains σ₀' t`).  Produces the recorded-chain reconstruction
bundle `canonBirthBridge_bundle` consumes, from the branch `LiveChain σ₀' t (a::p)` (carried by
`CanonInv ρ₀`) and the two set-algebra facts `hpreDead`/`hsurv`. No `BranchInv`. -/
theorem hRc_bi (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t) (t r e a : ℕ) (p : List ℕ)
    (hct0 : contains σ₀' t = true)
    (hlc0 : LiveChain σ₀' t (a :: p))
    (hbwne : birthAnc σ₀' σ₁' σ₂' t ≠ 0)
    (hpreDead : ∀ c ∈ (a :: p), contains σ₀' c = false → ¬ survP F c)
    (hsurv : ∀ c ∈ (a :: p), survP F c → contains σ₀' c = true) :
    ∃ rcPre rcSuf : List ℕ,
      (a :: p) = rcPre ++ birthAnc σ₀' σ₁' σ₂' t :: rcSuf
      ∧ (∀ c ∈ rcPre, ¬ survP F c)
      ∧ (contains σ₀' (birthAnc σ₀' σ₁' σ₂' t) = true →
          ∃ cw, IsAncPath σ₀' (birthAnc σ₀' σ₁' σ₂' t) cw ∧ canonAnc F cw = canonAnc F rcSuf) := by
  have hbeq : birthAnc σ₀' σ₁' σ₂' t = anc σ₀' t := by unfold birthAnc; exact if_pos hct0
  rw [hbeq] at hbwne ⊢
  obtain ⟨rcPre, rcSuf, hsp, hpd, hlive⟩ := split_liveChain σ₀' t a p hlc0 hbwne
  refine ⟨rcPre, rcSuf, hsp, ?_, ?_⟩
  · intro c hc
    exact hpreDead c (by rw [hsp]; exact List.mem_append.mpr (Or.inl hc)) (hpd c hc)
  · exact hin_via_liveSub σ₀' F (anc σ₀' t) rcSuf hlive
      (fun c hc hsc => hsurv c
        (by rw [hsp]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hc)))) hsc)

#print axioms hRc_bi

/-- **`hRc` for a branch-new survivor** (`¬contains σ₀' t`, `contains σ₁' t`).  Same split as `hRc_bi`
but at the birth branch `s := σ₁'`: `split_liveChain` gives the split and `bw`'s **σ₁'**-forest chain
`IsAncPath σ₁' bw (liveSub σ₁' rcSuf)`.

**Correction (pen-and-paper).**  Unlike B-i, one must NOT force the reconciliation witness to
`liveSub σ₀' rcSuf`: `rcSuf` is `k`'s recorded chain, captured in branch a, so it SKIPS `bw`-ancestors
that branch a had already deleted — even ones that are σ₀'-live. Then `liveSub σ₀' rcSuf` has a gap and
`IsAncPath σ₀' bw (liveSub σ₀' rcSuf)` is *false*. But the reconciliation's witness `cw` is
EXISTENTIAL: take `bw`'s genuine σ₀'-chain (which includes the gap node `c`); since `c` is
`deletedIn`-branch-a ⟹ non-survivor of `F`, `canonAnc F` skips it on both sides. So the residual is the
two-sided F-survivor agreement `canonAnc F cw = canonAnc F rcSuf` — the RGA's `hFiltEq`, THE crux —
supplied here as `hFiltRecon`, which directly returns the `∃cw` reconciliation. No `hin_via_liveSub`,
no `hsurv` needed. Symmetric for branch b via `σ₂'`. -/
theorem hRc_bii (σ₀' σ₁' σ₂' : concrete_st) (F : List op_t) (t r e a : ℕ) (p : List ℕ)
    (hct0 : contains σ₀' t = false) (hct1 : contains σ₁' t = true)
    (hlc1 : LiveChain σ₁' t (a :: p))
    (hbwne : birthAnc σ₀' σ₁' σ₂' t ≠ 0)
    (hpreDead : ∀ c ∈ (a :: p), contains σ₁' c = false → ¬ survP F c)
    (hwf1 : ∀ y, contains σ₁' y = true → (anc σ₁' y = 0 ∨ contains σ₁' (anc σ₁' y) = true))
    (hsurvAP1 : ∀ c ∈ (a :: p), survP F c → contains σ₁' c = true)
    (hFiltRecon : ∀ (w : ℕ) (rc : List ℕ),
        contains σ₀' w = true → contains σ₁' w = true →
        (∀ c ∈ rc, survP F c → contains σ₁' c = true) →
        IsAncPath σ₁' w (liveSub σ₁' rc) →
        ∃ cw, IsAncPath σ₀' w cw ∧ canonAnc F cw = canonAnc F rc) :
    ∃ rcPre rcSuf : List ℕ,
      (a :: p) = rcPre ++ birthAnc σ₀' σ₁' σ₂' t :: rcSuf
      ∧ (∀ c ∈ rcPre, ¬ survP F c)
      ∧ (contains σ₀' (birthAnc σ₀' σ₁' σ₂' t) = true →
          ∃ cw, IsAncPath σ₀' (birthAnc σ₀' σ₁' σ₂' t) cw ∧ canonAnc F cw = canonAnc F rcSuf) := by
  have hbeq : birthAnc σ₀' σ₁' σ₂' t = anc σ₁' t := by
    unfold birthAnc; rw [if_neg (by rw [hct0]; decide), if_pos hct1]
  rw [hbeq] at hbwne ⊢
  obtain ⟨rcPre, rcSuf, hsp, hpd, hlive⟩ := split_liveChain σ₁' t a p hlc1 hbwne
  refine ⟨rcPre, rcSuf, hsp, ?_, ?_⟩
  · intro c hc
    exact hpreDead c (by rw [hsp]; exact List.mem_append.mpr (Or.inl hc)) (hpd c hc)
  · intro hcbw
    have hc1bw : contains σ₁' (anc σ₁' t) = true := by
      rcases hwf1 t hct1 with h | h
      · exact absurd h hbwne
      · exact h
    have hrcSurv : ∀ c ∈ rcSuf, survP F c → contains σ₁' c = true :=
      fun c hc hsv => hsurvAP1 c
        (by rw [hsp]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hc)))) hsv
    exact hFiltRecon (anc σ₁' t) rcSuf hcbw hc1bw hrcSurv hlive

#print axioms hRc_bii

/-- **`hFiltRecon` reduced to `hFiltEq` — the irreducible two-sided residual.**  Discharges the
branch-new crux `hFiltRecon` down to exactly `hFiltEq`, the RGA's survivor-subsequence coincidence.
The witness `cw` is `w`'s genuine σ₀'-forest chain, extracted from `CanonInv ρ₀` (`w ∈ σ₀' ⟹ survP ρ₀ w
⟹ w`'s `Ins ∈ ρ₀ ⟹ LiveChain σ₀' w`). Then `canonAnc F cw = canonAnc F rc` is `canonAnc_filter_surv`
on both sides plus `hFiltEq`. NO `BranchInv`, NO branch-decomposition — the ONLY residual is `hFiltEq`
(`RGA_BranchCanon`'s located two-sided reconstruction fact). -/
theorem hFiltRecon_of_canonInv (σ₀' σ₁' : concrete_st) (F ρ₀ : List op_t)
    (hCI0 : CanonInv ρ₀ σ₀')
    (hdomeq : ∀ c, contains σ₀' c = true ↔ survP ρ₀ c)
    (hFiltEq : ∀ (w : ℕ) (cw rc : List ℕ),
        contains σ₀' w = true → contains σ₁' w = true →
        (∀ c ∈ rc, survP F c → contains σ₁' c = true) →
        IsAncPath σ₀' w cw → IsAncPath σ₁' w (liveSub σ₁' rc) →
        cw.filter (survB F) = rc.filter (survB F)) :
    ∀ (w : ℕ) (rc : List ℕ),
        contains σ₀' w = true → contains σ₁' w = true →
        (∀ c ∈ rc, survP F c → contains σ₁' c = true) →
        IsAncPath σ₁' w (liveSub σ₁' rc) →
        ∃ cw, IsAncPath σ₀' w cw ∧ canonAnc F cw = canonAnc F rc := by
  intro w rc hcw hcw1 hrc1 hp1
  obtain ⟨_h0, _hwf, _hdom, hper⟩ := hCI0
  have hsv : survP ρ₀ w := (hdomeq w).mp hcw
  obtain ⟨r_w, e_w, p_w, a_w, hins⟩ := hsv.1
  obtain ⟨_hel, hlc⟩ := hper w r_w e_w p_w a_w hins hsv
  obtain ⟨_, _, hpath⟩ := hlc
  refine ⟨liveSub σ₀' (a_w :: p_w), hpath, ?_⟩
  rw [canonAnc_filter_surv F (liveSub σ₀' (a_w :: p_w)), canonAnc_filter_surv F rc,
    hFiltEq w (liveSub σ₀' (a_w :: p_w)) rc hcw hcw1 hrc1 hpath hp1]

#print axioms hFiltRecon_of_canonInv

end Sal.ConditionedMRDTs.RGABirthBridgeHRc
