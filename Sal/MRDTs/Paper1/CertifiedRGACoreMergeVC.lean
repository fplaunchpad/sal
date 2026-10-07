import Sal.MRDTs.Paper1.CertifiedRGACoreAlgebra

namespace Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC
open Foundation Classical Sal.EmbedRGA Instances.SidedPeritext Instances.SidedEmbedRGA
open CertifiedRGACoreVC CertifiedRGACoreAlgebra

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) : SSorted s.1 :=
  CertifiedRGAVCAlgebra.Sided.sorted Γ _ _ _ (represented_text Γ C H s rep)

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (ha : representation Γ C A a) (hb : representation Γ C B b) :
    SSorted ((Core Γ).merge l a b).1 :=
  CertifiedRGAVCAlgebra.Sided.merge_sorted Γ _ _ _ _ _ _
    (represented_text Γ C A a ha) (represented_text Γ C B b hb)

theorem mergeVCs (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.MergeVCs
    (model Γ) (policy Γ) (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ l a b ha hb)
      (merge_sorted Γ C _ _ l b a hb ha)
    rw [normalize_merge Γ C _ _ _ l a b hl ha hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ l b a hl hb ha Set.inter_subset_right Set.inter_subset_left]
    simp [unite,Finset.union_comm]
  · intro C H s _ _ rep
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ _ _ _ (initial Γ C H s rep) rep)
      (sorted Γ C H s rep)
    rw [normalize_merge Γ C _ _ _ _ _ s (initial Γ C H s rep) (initial Γ C H s rep) rep
      (by simp) (by simp)]
    simp [CertifiedRGACoreAlgebra.normalize,unite,Core,Stores,prodSig,S,DeleteStore,MarkStore,Instances.FinsetStore.D]
  · intro C U s B e _ _ _ closed member _ _ hs hB hD hu
    have pastSub := (scheme Γ C).past_subset U e closed member
    have sub : (scheme Γ C).Past e \ {e} ⊆ U \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have he := hu.2.2.2.2.1 member
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ B s _ hs hD) (sorted Γ C U _ hu)
    rw [normalize_merge Γ C _ _ _ B s _ hB hs hD sub Set.diff_subset,
      normalize_update Γ C _ B hB e he (by simp),normalize_update Γ C _ s hs e he (by simp)]
    exact step_union Γ _ _ e (normalized_mono Γ C _ _ B s hB hs sub) (hB.2.1 e he)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    have pastSub := (scheme Γ C).past_subset E₁ e ctx.closed₁ member
    have pb : (scheme Γ C).Past e \ {e} ⊆ E₁ \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have pu : (scheme Γ C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (pastSub h.1),h.2⟩
    have lt : E₁ ∩ E₂ ⊆ E₁ \ {e} := by
      intro x h; exact ⟨h.1,fun eq => absent (eq ▸ h.2)⟩
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ l _ b hi hb)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [normalize_merge Γ C _ _ _ l _ b hl hi hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge Γ C _ _ _ B t _ hB ht hD pb Set.diff_subset,
      normalize_merge Γ C _ _ _ l t b hl ht hb lt Set.inter_subset_right]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx m₁ m₂ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    have p₁ := (scheme Γ C).past_subset E₁ e ctx.closed₁ m₁
    have p₂ := (scheme Γ C).past_subset E₂ e ctx.closed₂ m₂
    have pu : (scheme Γ C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (p₁ h.1),h.2⟩
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [normalize_merge Γ C _ _ _ _ _ _ hi₀ hi₁ hi₂ Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge Γ C _ _ _ B t₁ _ hB h₁ hD (fun _ h => ⟨p₁ h.1,h.2⟩) Set.diff_subset,
      normalize_merge Γ C _ _ _ B t₂ _ hB h₂ hD (fun _ h => ⟨p₂ h.1,h.2⟩) Set.diff_subset,
      normalize_merge Γ C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂ (fun _ h => ⟨h.1.1,h.2⟩) (fun _ h => ⟨h.1.2,h.2⟩)]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]

theorem representationJoin (Γ : OrderedPrefixCode) : AbstractMRDT.RepresentationJoin (representation Γ) := by
  apply AbstractMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ) (unique Γ) (initial Γ) (finite Γ)
  intro C E₁ E₂ a b trans irr _ _ ha _
  exact replaySupply Γ C ha.1 ha.2.1 trans irr

#print axioms mergeVCs
#print axioms representationJoin
end Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC
