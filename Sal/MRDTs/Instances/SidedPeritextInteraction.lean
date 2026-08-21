import Sal.MRDTs.Instances.SidedPeritextStateGC

/-! # Cross-epoch Sided Peritext state-GC interaction

Independently collected replicas cannot interpret absence relative to an LCA
until their retention predicates have been translated to one common epoch.
This module proves that translation and the resulting exact text merge.  The
LCA remains semantic ghost state; the physical result is computed from compact
heads after epoch alignment.
-/

namespace Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction

open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedPeritext.StateGC

noncomputable section

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

/-- The boundary required before a compact ternary merge: all three physical
inputs represent one common retention predicate. -/
structure CommonProjectionFrame (l a b : SState)
    (cl ca cb : CompactState) where
  keep : Nat → Bool
  lproj : cl.sided.text = l.filter (fun r => keep r.1)
  aproj : ca.sided.text = a.filter (fun r => keep r.1)
  bproj : cb.sided.text = b.filter (fun r => keep r.1)

theorem CommonProjectionFrame.merge_text_exact
    {l a b : SState} {cl ca cb : CompactState}
    (F : CommonProjectionFrame l a b cl ca cb)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL cl.sided.text ca.sided.text cb.sided.text =
      (sMergeL l a b).filter (fun r => F.keep r.1) := by
  rw [F.lproj, F.aproj, F.bproj]
  exact sMergeL_filter F.keep l a b ha hb hdisj

/-- An epoch constrains an id only if that id occurs in its semantic text.
Thus an older concurrent branch cannot veto an id minted only on another
branch. -/
def epochFactor (s : SState) (keep : Nat → Bool) (x : Nat) : Bool :=
  decide (x ∉ sIds s) || keep x

def commonEpochKeep (l a b : SState)
    (kl ka kb : Nat → Bool) (x : Nat) : Bool :=
  epochFactor l kl x && epochFactor a ka x && epochFactor b kb x

/-- Apply the other two epoch constraints to a compact state whose own
constraint is already represented physically. -/
def translateText (compact : CompactState) (s₁ s₂ : SState)
    (k₁ k₂ : Nat → Bool) : CompactState :=
  { compact with sided :=
    { compact.sided with text := compact.sided.text.filter (fun q =>
      epochFactor s₁ k₁ q.1 && epochFactor s₂ k₂ q.1) } }

theorem translateText_exact {full own₁ own₂ : SState}
    {compact : CompactState} {keep k₁ k₂ : Nat → Bool}
    (hexact : compact.sided.text = full.filter (fun q => keep q.1)) :
    (translateText compact own₁ own₂ k₁ k₂).sided.text =
      full.filter (fun q =>
        keep q.1 && epochFactor own₁ k₁ q.1 && epochFactor own₂ k₂ q.1) := by
  unfold translateText
  simp only
  rw [hexact, List.filter_filter]
  apply List.filter_congr
  intro q hq
  cases keep q.1 <;> cases epochFactor own₁ k₁ q.1 <;>
    cases epochFactor own₂ k₂ q.1 <;> decide

structure EpochProjection (keep : Nat → Bool)
    (full : SState) (compact : CompactState) : Prop where
  exact : compact.sided.text = full.filter (fun r => keep r.1)

/-- Three independently collected versions always translate to one common
projection.  This is the constructive cross-epoch alignment step. -/
def commonProjectionFrame_of_epochs
    {kl ka kb : Nat → Bool} {l a b : SState}
    {cl ca cb : CompactState}
    (hl : EpochProjection kl l cl)
    (ha : EpochProjection ka a ca)
    (hb : EpochProjection kb b cb) :
    CommonProjectionFrame l a b
      (translateText cl a b ka kb)
      (translateText ca l b kl kb)
      (translateText cb l a kl ka) := by
  let common := commonEpochKeep l a b kl ka kb
  refine ⟨common, ?_, ?_, ?_⟩
  · rw [translateText_exact hl.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds l := List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid]
  · rw [translateText_exact ha.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds a := List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]
  · rw [translateText_exact hb.exact]
    apply List.filter_congr
    intro q hq
    have hid : q.1 ∈ sIds b := List.mem_map.mpr ⟨q, hq, rfl⟩
    simp [common, commonEpochKeep, epochFactor, hid, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]

/-- Cross-epoch compact merge computes exactly the common projection of the
uncollected semantic merge. -/
theorem merge_text_after_epoch_translation
    {kl ka kb : Nat → Bool} {l a b : SState}
    {cl ca cb : CompactState}
    (hl : EpochProjection kl l cl)
    (hra : EpochProjection ka a ca)
    (hrb : EpochProjection kb b cb)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMergeL (translateText cl a b ka kb).sided.text
      (translateText ca l b kl kb).sided.text
      (translateText cb l a kl ka).sided.text =
    (sMergeL l a b).filter
      (commonEpochKeep l a b kl ka kb ∘ Prod.fst) := by
  exact (commonProjectionFrame_of_epochs hl hra hrb).merge_text_exact
    ha hb hdisj

#print axioms sMergeL_filter
#print axioms commonProjectionFrame_of_epochs
#print axioms merge_text_after_epoch_translation

end

end Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction

