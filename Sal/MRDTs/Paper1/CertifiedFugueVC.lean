import Sal.MRDTs.Paper1.CertifiedFugueVCAlgebra

set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CertifiedFugueVC
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay CertifiedFugueVCAlgebra
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

private theorem state_ext {s t : State} (live : s.live = t.live) (births : s.births = t.births) : s = t := by
  cases s; cases t; cases live; cases births; rfl

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ l a b ha hb)
        (merge_sorted Γ C _ _ l b a hb ha)
      rw [merge_toFinset Γ C _ _ _ l a b hl ha hb,
        merge_toFinset Γ C _ _ _ l b a hl hb ha]
      ext p
      simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    · simp [rawMerge,Finset.union_comm]
  · intro C H s _ _ rep
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ (datatype Γ).init (datatype Γ).init s (initial Γ C H s rep) rep) (sorted Γ C H s rep)
      rw [merge_toFinset Γ C _ _ _ (datatype Γ).init (datatype Γ).init s
        (initial Γ C H s rep) (initial Γ C H s rep) rep]
      simp [SetMergeAlgebra.merge,datatype]
    · simp [rawMerge]
  · intro C U s B e _ _ supported closed member _ _ hs hB hD hu
    have he : e ∈ C.events := hu.2.2.2.1 member
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ B s (rawUpdate Γ B e) hs hD)
        (sorted Γ C U (rawUpdate Γ s e) hu)
      rw [merge_toFinset Γ C _ _ _ B s (rawUpdate Γ B e) hB hs hD,
        update_toFinset Γ C _ B hB e he (by simp),
        update_toFinset Γ C _ s hs e he (by simp)]
      apply finite_causal Γ e
      · intro p hp mem
        exact fresh_born Γ C _ B hB e he (by simp) p hp (List.mem_toFinset.mp mem)
      · intro p mem kill
        exact List.mem_toFinset.mpr
          (killed_covered Γ C U s B e member he closed hs hB p (List.mem_toFinset.mp mem) kill)
    · change s.births ∪ (rawUpdate Γ B e).births = (rawUpdate Γ s e).births
      simp only [rawUpdate]
      have sub : B.births ⊆ s.births := by
        intro g hg
        obtain ⟨o,ho,eq,hi⟩ := (births_membership Γ C _ B hB g).mp hg
        apply (births_membership Γ C _ s hs g).mpr
        exact ⟨o,⟨(scheme Γ C).past_subset U e closed member ho.1,ho.2⟩,eq,hi⟩
      split <;> ext g <;> simp only [Finset.mem_union,Finset.mem_insert]
      · have h := sub (a := g); tauto
      · exact or_iff_left_of_imp (sub (a := g))
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ l _ b hi hb)
        (merge_sorted Γ C _ _ B _ _ hm hD)
      rw [merge_toFinset Γ C _ _ _ l _ b hl hi hb,
        merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
        merge_toFinset Γ C _ _ _ B t _ hB ht hD,
        merge_toFinset Γ C _ _ _ l t b hl ht hb]
      apply SetMergeAlgebra.local_redistribute
      · intro p hp _ other
        exact List.mem_toFinset.mpr (common_record Γ C E₁ E₂ l B b e member ctx.closed₁
          hl hB hb p (List.mem_toFinset.mp hp) (List.mem_toFinset.mp other))
      · intro p notpast updated
        have he := hi.2.2.2.1 member
        rw [update_toFinset Γ C _ B hB e he (by simp),recordStep_mem] at updated
        have birth : born Γ e p := updated.resolve_right (fun h => notpast h.1)
        intro base
        exact fresh_born Γ C _ l hl e he (fun h => absent h.2) p birth
          (List.mem_toFinset.mp base)
    · change _ ∪ b.births = _ ∪ (rawUpdate Γ B e).births
      simp only [rawMerge]
      ext g
      simp only [Finset.mem_union]
      tauto
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    dsimp only [datatype] at *
    apply state_ext
    · apply eq_of_toFinset (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
        (merge_sorted Γ C _ _ B _ _ hm hD)
      rw [merge_toFinset Γ C _ _ _ _ _ _ hi₀ hi₁ hi₂,
        merge_toFinset Γ C _ _ _ B _ _ hB hm hD,
        merge_toFinset Γ C _ _ _ B t₀ _ hB h₀ hD,
        merge_toFinset Γ C _ _ _ B t₁ _ hB h₁ hD,
        merge_toFinset Γ C _ _ _ B t₂ _ hB h₂ hD,
        merge_toFinset Γ C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂]
      ext p
      simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    · change _ ∪ _ = _ ∪ (rawUpdate Γ B e).births
      simp only [rawMerge]
      ext g
      simp only [Finset.mem_union]
      tauto

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin
    (representation Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ)
    (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply Γ C ha.1 trans irrefl

#print axioms representationJoin
#print axioms mergeVCs
end Sal.MRDTs.Paper1.CertifiedFugueVC
