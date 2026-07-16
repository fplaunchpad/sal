import Sal.ConditionedMRDTs.Development.RGA_BirthBridge_HRc
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeBranchNew
import Sal.ConditionedMRDTs.Development.RGA_ChainFaithful_doDel

/-!
# `BranchInv` chain transport — `hFiltEq`'s engine

*Additive; modifies no existing file; 0 `sorry`.*

The cross-forest core of `hFiltEq` (`RGA_BirthBridge_HRc`). Key fact: `BranchInv σ₀' σ₁'`'s I4 makes
`w`'s σ₁'-forest chain equal to the **σ₁'-live entries of `w`'s σ₀'-chain**:

    branchChain_transport :  IsAncPath σ₀' w cw  →  IsAncPath σ₁' w (liveSub σ₁' cw)

Engine: at each node, `resolve_climb_start` turns I4's `climb` (σ₀'-pointer walk skipping σ₁'-dead) into
`resolve σ₁'` of the recorded chain (list walk), giving `anc σ₁' w = resolve σ₁' cw` = the first σ₁'-live
entry; the tail recurses on the σ₀'-suffix after that node (`split_at_firstLive` + `isAncPath_suffix`).
From it, `hFiltEq` is immediate: survivors are σ₁'-live, so `cw.filter survB = (liveSub σ₁' cw).filter
survB`, and `liveSub σ₁' cw` is `w`'s σ₁'-chain (this lemma) = `liveSub σ₁' rc` by `IsAncPath_unique`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGABranchInvChainTransport

open Sal.Emulation
open RGACanonConvergence (survP CanonInv canonAnc)
open RGABranchCanon (survB)
open RGAHinFilterEq (survP_of_survB)
open Sal.ConditionedMRDTs.RGABirthBridgeSplit (split_at_firstLive)
open RGAMergeBranchNew (resolve_climb_start)
open Sal.ConditionedMRDTs.RGAChainFaithfulDoDel (resolve_mem_of_live)
open Sal.ConditionedMRDTs.RGABirthBridgeHRc (hFiltRecon_of_canonInv)

/-- A suffix of an ancestor chain is itself an ancestor chain. -/
theorem isAncPath_suffix (s : concrete_st) (d : ℕ) (suf : List ℕ) :
    ∀ (w : ℕ) (pre : List ℕ), IsAncPath s w (pre ++ d :: suf) → IsAncPath s d suf := by
  intro w pre
  induction pre generalizing w with
  | nil => intro h; obtain ⟨_, _, h3⟩ := h; exact h3
  | cons c cs ih => intro h; obtain ⟨_, _, h3⟩ := h; exact ih c h3

/-- A nonzero `resolve` is live. -/
theorem resolve_live (s : concrete_st) :
    ∀ (L : List ℕ), resolve s L ≠ 0 → contains s (resolve s L) = true := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons c rest ih =>
    intro h
    by_cases hc : contains s c = true
    · rw [show resolve s (c :: rest) = c from if_pos hc]; exact hc
    · rw [show resolve s (c :: rest) = resolve s rest from if_neg hc] at h ⊢
      exact ih h

/-- If nothing in `L` is live, its live sublist is empty. -/
theorem liveSub_nil_of_resolve_zero (s : concrete_st) (h0 : contains s 0 = false) :
    ∀ (L : List ℕ), resolve s L = 0 → liveSub s L = [] := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro hres
    by_cases hc : contains s c = true
    · rw [show resolve s (c :: rest) = c from if_pos hc] at hres
      rw [hres, h0] at hc; exact absurd hc (by decide)
    · have hrest : resolve s rest = 0 := by
        rw [show resolve s (c :: rest) = resolve s rest from if_neg hc] at hres; exact hres
      have hcf : contains s c = false := by
        cases h : contains s c with
        | true => exact absurd h hc
        | false => rfl
      show liveSub s (c :: rest) = []
      rw [show liveSub s (c :: rest) = liveSub s rest from by
        simp only [liveSub]; exact List.filter_cons_of_neg hc]
      exact ih hrest

/-- **Head fact.**  `anc σ₁' w = resolve σ₁' cw`: I4's `climb` from `w`'s σ₀'-parent is the first
σ₁'-live entry of `w`'s σ₀'-chain. -/
theorem anc_eq_resolve (σ₀' σ₁' : concrete_st)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hI4 : ∀ k, contains σ₀' k = true → contains σ₁' k = true →
        climb (fun y => anc σ₀' y) (domain σ₁') (anc σ₀' k) = anc σ₁' k)
    (w : ℕ) (cw : List ℕ) (hc0 : contains σ₀' w = true) (hc1 : contains σ₁' w = true)
    (hpath : IsAncPath σ₀' w cw) :
    resolve σ₁' cw = anc σ₁' w := by
  cases cw with
  | nil =>
    have hac : anc σ₀' w = 0 := hpath
    have hclimb0 : climb (fun y => anc σ₀' y) (domain σ₁') 0 = 0 := climb_fixpoint _ _ 0 (Or.inl rfl)
    have hkey := hI4 w hc0 hc1
    rw [hac, hclimb0] at hkey
    show resolve σ₁' ([] : List ℕ) = anc σ₁' w
    rw [show resolve σ₁' ([] : List ℕ) = 0 from rfl]
    exact hkey
  | cons c cs =>
    obtain ⟨hac, hcc, hpc⟩ := hpath
    have hrc := resolve_climb_start σ₀' σ₁' Hdec Hstay h0 c cs hcc hpc
    rw [hrc, ← hac]
    exact hI4 w hc0 hc1

/-- **The chain transport** (length-indexed).  `IsAncPath σ₁' w (liveSub σ₁' cw)` — `w`'s σ₁'-chain is
the σ₁'-live entries of `w`'s σ₀'-chain. -/
theorem branchChain_transport_aux (σ₀' σ₁' : concrete_st)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false) (h0₁ : contains σ₁' 0 = false)
    (hI4 : ∀ k, contains σ₀' k = true → contains σ₁' k = true →
        climb (fun y => anc σ₀' y) (domain σ₁') (anc σ₀' k) = anc σ₁' k) :
    ∀ (n : ℕ) (w : ℕ) (cw : List ℕ), cw.length ≤ n →
      contains σ₀' w = true → contains σ₁' w = true → IsAncPath σ₀' w cw →
      IsAncPath σ₁' w (liveSub σ₁' cw) := by
  intro n
  induction n with
  | zero =>
    intro w cw hlen hc0 hc1 hpath
    cases cw with
    | cons c cs => simp at hlen
    | nil =>
      have hres := anc_eq_resolve σ₀' σ₁' Hdec Hstay h0 hI4 w [] hc0 hc1 hpath
      rw [show resolve σ₁' ([] : List ℕ) = 0 from rfl] at hres
      show IsAncPath σ₁' w (liveSub σ₁' [])
      rw [show liveSub σ₁' ([] : List ℕ) = [] from rfl]
      show anc σ₁' w = 0
      exact hres.symm
  | succ n ih =>
    intro w cw hlen hc0 hc1 hpath
    have hres := anc_eq_resolve σ₀' σ₁' Hdec Hstay h0 hI4 w cw hc0 hc1 hpath
    by_cases hr0 : resolve σ₁' cw = 0
    · rw [liveSub_nil_of_resolve_zero σ₁' h0₁ cw hr0]
      show anc σ₁' w = 0
      rw [← hres]; exact hr0
    · obtain ⟨rcPre, rcSuf, hsp, _hpd, hls⟩ := split_at_firstLive σ₁' cw hr0
      have hd1 : contains σ₁' (resolve σ₁' cw) = true := resolve_live σ₁' cw hr0
      have hd0 : contains σ₀' (resolve σ₁' cw) = true :=
        isAncPath_mem σ₀' w cw hpath _ (resolve_mem_of_live σ₁' h0₁ cw hd1)
      have hpathd : IsAncPath σ₀' (resolve σ₁' cw) rcSuf :=
        isAncPath_suffix σ₀' (resolve σ₁' cw) rcSuf w rcPre (hsp ▸ hpath)
      have hlend : rcSuf.length ≤ n := by
        have hcwlen : cw.length = rcPre.length + rcSuf.length + 1 := by
          rw [hsp]; simp [List.length_append, List.length_cons]; omega
        omega
      rw [hls]
      exact ⟨hres.symm, hd1, ih (resolve σ₁' cw) rcSuf hlend hd0 hd1 hpathd⟩

/-- **`branchChain_transport`.**  `IsAncPath σ₁' w (liveSub σ₁' cw)` from `BranchInv`'s I4. -/
theorem branchChain_transport (σ₀' σ₁' : concrete_st)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false) (h0₁ : contains σ₁' 0 = false)
    (hI4 : ∀ k, contains σ₀' k = true → contains σ₁' k = true →
        climb (fun y => anc σ₀' y) (domain σ₁') (anc σ₀' k) = anc σ₁' k)
    (w : ℕ) (cw : List ℕ) (hc0 : contains σ₀' w = true) (hc1 : contains σ₁' w = true)
    (hpath : IsAncPath σ₀' w cw) :
    IsAncPath σ₁' w (liveSub σ₁' cw) :=
  branchChain_transport_aux σ₀' σ₁' Hdec Hstay h0 h0₁ hI4 cw.length w cw le_rfl hc0 hc1 hpath

#print axioms branchChain_transport

/-- Filtering a live-sublist by `survB` is the same as filtering the raw list: survivors are already
σ₁'-live, so the `contains σ₁'` pre-filter drops nothing a survivor filter keeps. -/
theorem filter_liveSub_survB (σ₁' : concrete_st) (F : List op_t) (L : List ℕ)
    (hsurv1 : ∀ c ∈ L, survP F c → contains σ₁' c = true) :
    (liveSub σ₁' L).filter (survB F) = L.filter (survB F) := by
  simp only [liveSub, List.filter_filter]
  apply List.filter_congr
  intro a ha
  by_cases hs : survB F a = true
  · rw [hs, Bool.true_and]; exact hsurv1 a ha (survP_of_survB F a hs)
  · simp only [Bool.not_eq_true] at hs
    rw [hs, Bool.false_and]

/-- **`hFiltEq` from `BranchInv`.**  The two-sided survivor-subsequence coincidence, discharged: `w`'s
σ₀'-chain and its σ₁'-chain have the same `F`-survivor subsequence. Via `branchChain_transport`
(σ₁'-chain = σ₁'-live of σ₀'-chain) + `IsAncPath_unique` + `filter_liveSub_survB`. This is exactly the
`hFiltEq` hypothesis `RGA_BirthBridge_HRc.hFiltRecon_of_canonInv` consumes (with `w`'s two liveness
facts added — both available where `w` is the birth anchor). -/
theorem hFiltEq_of_branchInv (σ₀' σ₁' : concrete_st) (F : List op_t)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false) (h0₁ : contains σ₁' 0 = false)
    (hI4 : ∀ k, contains σ₀' k = true → contains σ₁' k = true →
        climb (fun y => anc σ₀' y) (domain σ₁') (anc σ₀' k) = anc σ₁' k)
    (hsurv01 : ∀ c, contains σ₀' c = true → survP F c → contains σ₁' c = true) :
    ∀ (w : ℕ) (cw rc : List ℕ),
        contains σ₀' w = true → contains σ₁' w = true →
        (∀ c ∈ rc, survP F c → contains σ₁' c = true) →
        IsAncPath σ₀' w cw → IsAncPath σ₁' w (liveSub σ₁' rc) →
        cw.filter (survB F) = rc.filter (survB F) := by
  intro w cw rc hc0 hc1 hrc1 hp0 hp1
  have htrans := branchChain_transport σ₀' σ₁' Hdec Hstay h0 h0₁ hI4 w cw hc0 hc1 hp0
  have huniq : liveSub σ₁' cw = liveSub σ₁' rc :=
    IsAncPath_unique σ₁' h0₁ w _ _ htrans hp1
  have hcw1 : ∀ c ∈ cw, survP F c → contains σ₁' c = true :=
    fun c hcmem hsv => hsurv01 c (isAncPath_mem σ₀' w cw hp0 c hcmem) hsv
  rw [← filter_liveSub_survB σ₁' F cw hcw1, huniq, filter_liveSub_survB σ₁' F rc hrc1]

#print axioms hFiltEq_of_branchInv

/-- **`hFiltRecon` from `CanonInv ρ₀` + `BranchInv`.**  Composes `hFiltEq_of_branchInv` into
`RGA_BirthBridge_HRc.hFiltRecon_of_canonInv`, closing the branch-new reconciliation crux entirely:
`hRc_bii`'s `hFiltRecon` hypothesis now follows from the σ₀' branch canon + the σ₀'↔σ₁' `BranchInv`
relation (I4 + `hsurv1`). Only `BranchInv` itself (the branch-decomposition) remains. -/
theorem hFiltRecon_of_branchInv (σ₀' σ₁' : concrete_st) (F ρ₀ : List op_t)
    (hCI0 : CanonInv ρ₀ σ₀')
    (hdomeq : ∀ c, contains σ₀' c = true ↔ survP ρ₀ c)
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false) (h0₁ : contains σ₁' 0 = false)
    (hI4 : ∀ k, contains σ₀' k = true → contains σ₁' k = true →
        climb (fun y => anc σ₀' y) (domain σ₁') (anc σ₀' k) = anc σ₁' k)
    (hsurv01 : ∀ c, contains σ₀' c = true → survP F c → contains σ₁' c = true) :
    ∀ (w : ℕ) (rc : List ℕ),
        contains σ₀' w = true → contains σ₁' w = true →
        (∀ c ∈ rc, survP F c → contains σ₁' c = true) →
        IsAncPath σ₁' w (liveSub σ₁' rc) →
        ∃ cw, IsAncPath σ₀' w cw ∧ canonAnc F cw = canonAnc F rc :=
  hFiltRecon_of_canonInv σ₀' σ₁' F ρ₀ hCI0 hdomeq
    (hFiltEq_of_branchInv σ₀' σ₁' F Hdec Hstay h0 h0₁ hI4 hsurv01)

#print axioms hFiltRecon_of_branchInv

end Sal.ConditionedMRDTs.RGABranchInvChainTransport
