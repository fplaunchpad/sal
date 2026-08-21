import Sal.MRDTs.Instances.SidedPeritextStateGC

/-! # Cross-epoch Sided Peritext state-GC interaction

Independently collected replicas align their certified Lamport cutoffs before
merge. This module proves that cutoff alignment and the resulting exact text
merge. The LCA remains semantic ghost state; the physical result is computed
from compact heads.
-/

namespace Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction

open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedPeritext.StateGC

noncomputable section

def keepAbove (stableCut : Nat) (x : Nat) : Bool :=
  decide (stableCut < x)

def commonStableCut (cl ca cb : CompactState) : Nat :=
  max cl.stableCut (max ca.stableCut cb.stableCut)

def alignStableCut (target : Nat) (s : CompactState) : CompactState :=
  { sided :=
      { text := s.sided.text.filter (fun r => keepAbove target r.1)
        gaps := s.sided.gaps }
    deleted := s.deleted
    marks := s.marks
    stableCut := target }

/-- Physical epoch alignment uses only the finite reclaimed-ID certificates;
it does not need the discarded semantic states. -/
theorem alignStableCut_text (target : Nat) (s : CompactState) :
    (alignStableCut target s).sided.text =
      s.sided.text.filter (fun r => keepAbove target r.1) := rfl

theorem fresh_survives_commonEpoch {cl ca cb : CompactState} {x : Nat}
    (hfresh : commonStableCut cl ca cb < x) :
    keepAbove (commonStableCut cl ca cb) x = true := by
  simp [keepAbove, hfresh]

structure CutProjection (full : SState) (compact : CompactState) : Prop where
  exact : compact.sided.text =
    full.filter (fun r => keepAbove compact.stableCut r.1)

theorem alignStableCut_exact {full : SState} {compact : CompactState}
    (hproj : CutProjection full compact) {target : Nat}
    (hle : compact.stableCut ≤ target) :
    (alignStableCut target compact).sided.text =
      full.filter (fun r => keepAbove target r.1) := by
  rw [alignStableCut_text, hproj.exact, List.filter_filter]
  apply List.filter_congr
  intro r _
  by_cases ht : target < r.1
  · have hc : compact.stableCut < r.1 := lt_of_le_of_lt hle ht
    simp [keepAbove, ht, hc]
  · simp [keepAbove, ht]

/-- A common retention predicate commutes with ternary SidedRGA merge. -/
theorem sMergeL_filter (keep : Nat → Bool) (l a b : SState)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL (l.filter fun r => keep r.1)
        (a.filter fun r => keep r.1) (b.filter fun r => keep r.1) =
      (sMergeL l a b).filter fun r => keep r.1 := by
  apply ssorted_ext
  · apply sMergeL_sorted (List.Pairwise.filter _ ha)
      (List.Pairwise.filter _ hb)
    intro x hx y hy hkey
    exact hdisj x (List.mem_of_mem_filter hx) y
      (List.mem_of_mem_filter hy) hkey
  · exact List.Pairwise.filter _ (sMergeL_sorted ha hb hdisj)
  · intro x
    simp only [sMergeL, mem_sMerge2, List.mem_filter, decide_eq_true_eq,
      sIds, List.mem_map]
    aesop

theorem merge_text_after_cut_alignment
    {l a b : SState} {cl ca cb : CompactState}
    (hl : CutProjection l cl) (ha : CutProjection a ca)
    (hb : CutProjection b cb)
    (hasort : SSorted a) (hbsort : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    let cut := commonStableCut cl ca cb
    sMergeL (alignStableCut cut cl).sided.text
      (alignStableCut cut ca).sided.text
      (alignStableCut cut cb).sided.text =
    (sMergeL l a b).filter (fun r => keepAbove cut r.1) := by
  dsimp only
  unfold commonStableCut
  rw [alignStableCut_exact hl (Nat.le_max_left _ _)]
  rw [alignStableCut_exact ha (le_trans (Nat.le_max_left _ _)
    (Nat.le_max_right _ _))]
  rw [alignStableCut_exact hb (le_trans (Nat.le_max_right _ _)
    (Nat.le_max_right _ _))]
  exact sMergeL_filter _ l a b hasort hbsort hdisj

#print axioms sMergeL_filter
#print axioms alignStableCut_exact
#print axioms merge_text_after_cut_alignment

end

end Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction
