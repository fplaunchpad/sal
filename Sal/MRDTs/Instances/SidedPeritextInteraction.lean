import Sal.MRDTs.Instances.SidedPeritextStateGC

/-! # Cross-epoch Sided Peritext state-GC interaction

Each collection epoch has a retained-node predicate and a Lamport cutoff.
The predicate preserves live paths, mark boundaries, and declared in-flight
nodes; the cutoff proves that every omitted identifier is old. Independently
collected replicas translate their predicates to one common projection before
merge. The GCA remains semantic ghost state.
-/

namespace Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction

open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Instances.SidedPeritext.StateGC

noncomputable section

/-- A common retention predicate commutes with ternary SidedRGA merge. -/
theorem sMerge_filter (keep : Nat → Bool) (l a b : SState)
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMerge (l.filter fun r => keep r.1)
        (a.filter fun r => keep r.1) (b.filter fun r => keep r.1) =
      (sMerge l a b).filter fun r => keep r.1 := by
  apply ssorted_ext
  · apply sMerge_sorted (List.Pairwise.filter _ ha)
      (List.Pairwise.filter _ hb)
    intro x hx y hy hkey
    exact hdisj x (List.mem_of_mem_filter hx) y
      (List.mem_of_mem_filter hy) hkey
  · exact List.Pairwise.filter _ (sMerge_sorted ha hb hdisj)
  · intro x
    simp only [sMerge, mem_sMerge2, List.mem_filter, decide_eq_true_eq,
      sIds, List.mem_map]
    aesop

structure EpochProjection (keep : Nat → Bool)
    (full : SState) (compact : CompactState) : Prop where
  exact : compact.sided.text = full.filter (fun r => keep r.1)
  omitted_old : ∀ x, keep x = false → x ≤ compact.stableCut

theorem EpochProjection.keeps_fresh {keep : Nat → Bool}
    {full : SState} {compact : CompactState}
    (h : EpochProjection keep full compact) {x : Nat}
    (hfresh : compact.stableCut < x) : keep x = true := by
  cases hk : keep x with
  | false => exact False.elim (Nat.not_le_of_lt hfresh (h.omitted_old x hk))
  | true => rfl

/-- An epoch constrains an identifier only when it occurs in that semantic
state. Therefore an older concurrent branch cannot veto a fresh identifier
minted only on another branch. -/
def epochFactor (s : SState) (keep : Nat → Bool) (x : Nat) : Bool :=
  decide (x ∉ sIds s) || keep x

def commonEpochKeep (l a b : SState)
    (kl ka kb : Nat → Bool) (x : Nat) : Bool :=
  epochFactor l kl x && epochFactor a ka x && epochFactor b kb x

def translateText (compact : CompactState) (s₁ s₂ : SState)
    (k₁ k₂ : Nat → Bool) : CompactState :=
  { compact with sided :=
    { compact.sided with text := compact.sided.text.filter (fun q =>
      epochFactor s₁ k₁ q.1 && epochFactor s₂ k₂ q.1) } }

theorem translateText_exact {full own₁ own₂ : SState}
    {compact : CompactState} {keep k₁ k₂ : Nat → Bool}
    (hexact : compact.sided.text = full.filter (fun q => keep q.1)) :
    (translateText compact own₁ own₂ k₁ k₂).sided.text =
      full.filter (fun q => keep q.1 && epochFactor own₁ k₁ q.1 &&
        epochFactor own₂ k₂ q.1) := by
  unfold translateText
  simp only
  rw [hexact, List.filter_filter]
  apply List.filter_congr
  intro q _
  cases keep q.1 <;> cases epochFactor own₁ k₁ q.1 <;>
    cases epochFactor own₂ k₂ q.1 <;> decide

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
    sMerge cl.sided.text ca.sided.text cb.sided.text =
      (sMerge l a b).filter (fun r => F.keep r.1) := by
  rw [F.lproj, F.aproj, F.bproj]
  exact sMerge_filter F.keep l a b ha hb hdisj

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

/-- Cross-epoch compact text merge computes the common projection of the
uncollected semantic merge. -/
theorem merge_text_after_epoch_translation
    {kl ka kb : Nat → Bool} {l a b : SState}
    {cl ca cb : CompactState}
    (hl : EpochProjection kl l cl) (ha : EpochProjection ka a ca)
    (hb : EpochProjection kb b cb)
    (hasort : SSorted a) (hbsort : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b,
      Sal.EmbedRGA.sKey x.2.2 = Sal.EmbedRGA.sKey y.2.2 → x = y) :
    sMerge (translateText cl a b ka kb).sided.text
      (translateText ca l b kl kb).sided.text
      (translateText cb l a kl ka).sided.text =
    (sMerge l a b).filter
      (commonEpochKeep l a b kl ka kb ∘ Prod.fst) := by
  exact (commonProjectionFrame_of_epochs hl ha hb).merge_text_exact
    hasort hbsort hdisj

#print axioms sMerge_filter
#print axioms EpochProjection.keeps_fresh
#print axioms merge_text_after_epoch_translation

end

end Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction
