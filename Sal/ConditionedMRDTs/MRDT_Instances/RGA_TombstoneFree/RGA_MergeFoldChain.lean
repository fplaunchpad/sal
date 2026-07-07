import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeBranchNew
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonConvergence

/-!
# Closing `FoldBirthChain` from the canonical-state characterization

`RGA_MergeBranchNew` reduced the two-sided merge bridge to the branch-new
fold-chain identity `FoldBirthChain l a b (applySeqR l π₀) k` (for branch-new
survivors `k`), and its own residual `foldChain_of_goodFold` was stuck on an
event-list induction over the branch fold.

`RGA_CanonConvergence.canon_fold` now supplies exactly the per-id anchor
characterization that induction was after: a disciplined fold of an applied
event set `F` is observationally the *canonical state* of `F` — its domain is
the survivor set, and every survivor's stored anchor is `canonAnc F` of its
**recorded** ancestor chain (`resolve` of that chain against the survivor set).

This file discharges `FoldBirthChain` from `CanonMatch` (the projection of
`canon_fold`).  The fold half is immediate: `anc p k = canonAnc F rc`
(recorded chain `rc`), and on the survivor domain `resolve p = canonAnc F`.
The genuinely two-sided content — that `k`'s *branch-final* birth-anchor
`birthAnc l a b k` (which is `anc a k` / `anc b k`, NOT the recorded head)
together with its LCA chain resolves to the same survivor as the recorded
chain — is isolated as the pure event-set/LCA-forest predicate
`CanonBirthBridge`.  That predicate mentions no fold state at all; it is the
cross-branch identity discharged by the branch canonical characterizations
(workstream A / GenDisc2), strictly below `FoldBirthChain`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace RGAMergeFoldChain

open Sal.Emulation
open RGACanonConvergence
open RGAMergeBranchNew (FoldBirthChain eq_merge_two_sided_of_foldChain)
open RGAMergeLinearization (applySeqR)

/-! ## §1  The reduced residual: a pure event-set / LCA-forest bridge

`CanonBirthBridge l F bw rc` says the merge's birth-anchor `bw` and its LCA
ancestor chain resolve — *against the applied set `F`* — to the same survivor as
the recorded chain `rc`.  It is stated entirely with `canonAnc` (a pure function
of the event set `F`) and `IsAncPath l` (the LCA forest); NO fold state occurs.
This is the honest cross-forest content: `bw = birthAnc l a b k = anc a k` is
`k`'s branch-final anchor, generally distinct from the recorded head of `rc`. -/
def CanonBirthBridge (l : concrete_st) (F : List op_t) (bw : ℕ) (rc : List ℕ) : Prop :=
  (contains l bw = true →
      ∃ cw, IsAncPath l bw cw ∧ canonAnc F (bw :: cw) = canonAnc F rc)
  ∧ (contains l bw = false → canonAnc F rc = bw)

/-! ## §2  `FoldBirthChain` from `CanonMatch` + the bridge

`CanonMatch F p` gives, for `k`'s recorded insert `(k, r, .Ins e_k p_k a_k) ∈ F`
with `survP F k`, that `anc p k = canonAnc F (a_k :: p_k)`; and on the survivor
domain `resolve p L = canonAnc F L` for every chain `L`.  Feeding the bridge in,
both branches of `FoldBirthChain` fall out by rewriting `anc p k` and
`resolve p (bw :: cw)` through `canonAnc`. -/
theorem foldChain_of_canon (l a b p : concrete_st) (F : List op_t)
    (hcm : CanonMatch F p)
    (k r e_k a_k : ℕ) (p_k : List ℕ)
    (hins : (k, r, .Ins e_k p_k a_k) ∈ F)
    (hsv : survP F k)
    (hbridge : CanonBirthBridge l F (birthAnc l a b k) (a_k :: p_k)) :
    FoldBirthChain l a b p k := by
  obtain ⟨hdom, hanc⟩ := hcm
  have hres : ∀ L, resolve p L = canonAnc F L := resolve_eq_canonAnc F p hdom
  have hancpk : anc p k = canonAnc F (a_k :: p_k) := (hanc k r e_k p_k a_k hins hsv).2
  obtain ⟨hbin, hbout⟩ := hbridge
  refine ⟨?_, ?_⟩
  · intro hlw
    obtain ⟨cw, hpath, hceq⟩ := hbin hlw
    exact ⟨cw, hpath, by rw [hancpk, ← hceq, ← hres]⟩
  · intro hlwf
    rw [hancpk]; exact hbout hlwf

#print axioms foldChain_of_canon

/-! ## §3  The two-sided merge bridge, closed on the honest residual

`eq_merge_two_sided_of_foldChain` carried a free `hFC : FoldBirthChain …`.
Here `hFC` is built for every branch-new survivor from the canonical state of
the branch fold (`hcm : CanonMatch F (applySeqR l π₀)` — `canon_fold` applied to
the branch fold) plus the reduced bridge `hbridge` (`CanonBirthBridge`, the pure
event-set/LCA identity).  The recorded insert event and `survP F k` are read off
`CanonMatch`'s domain clause, so the residual is exactly the cross-branch bridge
— NO free `FoldBirthChain`, NO `hBN`. -/
theorem eq_merge_two_sided_final
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (F : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hawf : wf a) (hbwf : wf b)
    (h0 : contains l 0 = false)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : RGAMergeLinearization.BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = RGAMergeLinearizationTwoSided.birthEl l a b k)
    (hcm : CanonMatch F (applySeqR l π₀))
    (hbridge : ∀ k, survivors l a b k = true → contains l k = false →
        ∀ r e_k a_k : ℕ, ∀ p_k : List ℕ, (k, r, .Ins e_k p_k a_k) ∈ F →
          CanonBirthBridge l F (birthAnc l a b k) (a_k :: p_k))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful x (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash x y
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hFC : ∀ k, survivors l a b k = true → contains l k = false →
      FoldBirthChain l a b (applySeqR l π₀) k := by
    intro k hsvk hlkf
    have hck : contains (applySeqR l π₀) k = true := by rw [← hD k]; exact hsvk
    have hsurvF : survP F k := (hcm.1 k).mp hck
    obtain ⟨⟨r, e_k, p_k, a_k, hins⟩, _⟩ := id hsurvF
    exact foldChain_of_canon l a b (applySeqR l π₀) F hcm k r e_k a_k p_k hins hsurvF
      (hbridge k hsvk hlkf r e_k a_k p_k hins)
  exact eq_merge_two_sided_of_foldChain l a b lo ev π₀ π hlwf hlmono hawf hbwf h0
    hD hB hBE hFC h₀p hπp h₀r hπr hMSR

#print axioms eq_merge_two_sided_final

end RGAMergeFoldChain
