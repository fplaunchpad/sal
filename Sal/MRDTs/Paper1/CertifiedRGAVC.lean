import Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra

set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CertifiedRGAVC
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA CertifiedRGAVCReplay.Embedded CertifiedRGAVCAlgebra.Embedded
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem mergeVCs (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.MergeVCs
    (model (α := α) Γ) policy (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    simp only [E] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ l a b ha hb)
      (merge_sorted Γ C _ _ l b a hb ha)
    rw [merge_toFinset Γ C _ _ _ l a b hl ha hb,
      merge_toFinset Γ C _ _ _ l b a hl hb ha]
    ext p
    simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  · intro C H s _ _ rep
    simp only [E] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ [] [] s (initial Γ C H s rep) rep) (sorted Γ C H s rep)
    rw [merge_toFinset Γ C _ _ _ [] [] s
      (initial Γ C H s rep) (initial Γ C H s rep) rep]
    simp [SetMergeAlgebra.merge]
  · intro C U s B e _ _ supported closed member _ _ hs hB hD hu
    have he : e ∈ C.events := hu.2.2.2.1 member
    simp only [E] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ B s (eUpdate Γ B e) hs hD)
      (sorted Γ C U (eUpdate Γ s e) hu)
    rw [merge_toFinset Γ C _ _ _ B s (eUpdate Γ B e) hB hs hD,
      update_toFinset Γ C _ B hB e he (by simp),
      update_toFinset Γ C _ s hs e he (by simp)]
    apply finite_causal Γ e
    · intro p hp mem
      exact fresh_born Γ C _ B hB e he (by simp) p hp (List.mem_toFinset.mp mem)
    · intro p mem kill
      exact List.mem_toFinset.mpr
        (killed_covered Γ C U s B e member he closed hs hB p (List.mem_toFinset.mp mem) kill)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    simp only [E] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ l _ b hi hb)
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
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    simp only [E] at *
    apply eq_of_toFinset (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
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

theorem representationJoin (Γ : OrderedPrefixCode) : AbstractMRDT.RepresentationJoin
    (representation (α := α) Γ) := by
  apply AbstractMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ)
    (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irrefl _ _ ha _
  exact replaySupply Γ C ha.1 trans irrefl

#print axioms representationJoin
#print axioms mergeVCs
end Embedded
end Sal.MRDTs.Paper1.CertifiedRGAVC
