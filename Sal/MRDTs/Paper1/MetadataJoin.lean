import Sal.MRDTs.Paper1.MetadataDecomposition

/-! Strong induction deriving represented Join from observational VCs and
directed metadata obligations. Representation and peel supplies are replay
obligations, not assumptions that merging preserves representation. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

theorem join_at_sizes {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (canonical : RepresentsCanonical A P R) (substitute : MetadataSubstitution A R)
    (initial : InitialMetadata R) (initMetadata : InitMetadata R)
    (symmetry : MergeCommMetadata R) (causal : CausalMetadata A P R scheme)
    (localMetadata : LocalMetadata A P R scheme) (sharedMetadata : SharedMetadata A P R scheme)
    (C : ReplayContext D.toUpdateSig) (trans : Transitive C.vis)
    (irrefl : ∀ x, ¬ C.vis x x)
    (supply : ∀ E π, listPermOf π E → Supported C E → ∃ s, R C E s)
    (peel : ∀ E s, R C E s → Supported C E → E.Nonempty → (scheme C).Closed E →
      Nonempty (DependencyPeelChoice A P R C (scheme C) E)) :
    ∀ n, RepresentedJoinAtSize A P R C (scheme C) n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro E₁ E₂ l a b π perm length sup₁ sup₂ closed₁ closed₂ hl ha hb
    rcases Set.eq_empty_or_nonempty E₁ with empty | nonempty₁
    · subst E₁
      simpa only [Set.empty_inter,Set.empty_union] using
        join_empty_left vcs canonical substitute initial initMetadata C E₂ l a b sup₂
          (by simpa using hl) ha hb
    rcases Set.eq_empty_or_nonempty E₂ with empty | nonempty₂
    · subst E₂
      have swapped := join_empty_left vcs canonical substitute initial initMetadata C E₁ l b a sup₁
        (by simpa using hl) hb ha
      have sameIndex : Admissible A P R C (E₁ ∪ ∅) (D.merge l b a) := by
        simpa only [Set.union_empty] using swapped
      exact swap_step vcs symmetry C E₁ ∅ l a b sameIndex
    have supU : Supported C (E₁ ∪ E₂) := fun x h => h.elim (sup₁ x) (sup₂ x)
    have closedU : (scheme C).Closed (E₁ ∪ E₂) := fun x y edge h =>
      h.elim (fun h => Or.inl (closed₁ x y edge h)) (fun h => Or.inr (closed₂ x y edge h))
    obtain ⟨s,hs⟩ := supply (E₁ ∪ E₂) π perm supU
    obtain ⟨choice⟩ := peel (E₁ ∪ E₂) s hs supU
      (nonempty₁.mono Set.subset_union_left) closedU
    have recurs : ∀ m, m < π.length → RepresentedJoinAtSize A P R C (scheme C) m := by
      simpa only [length] using IH
    have eventMem := (perm.2 choice.event).mpr choice.member
    have permDiff : listPermOf (π.filter (· ≠ choice.event)) ((E₁ ∪ E₂) \ {choice.event}) :=
      filter_ne_listPermOf_basic (D := D.toUpdateSig) perm eventMem
    have smaller : (π.filter (· ≠ choice.event)).length < n := by
      have size := listPermOf_diff_length perm eventMem permDiff
      have positive := List.length_pos_of_mem eventMem
      omega
    have closedPre₁ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ choice.event
      Set.subset_union_left closed₁ choice.metadata_maximal
    have closedPre₂ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₂ choice.event
      Set.subset_union_right closed₂ choice.metadata_maximal
    have ctx : PeelContext A P scheme C E₁ E₂ choice.event :=
      ⟨trans,irrefl,sup₁,sup₂,closed₁,closed₂,choice.semantic_maximal,choice.metadata_maximal⟩
    have sideSupply : ∀ E, E ⊆ E₁ ∪ E₂ → ∃ t, Admissible A P R C (E \ {choice.event}) t := by
      intro E subset
      obtain ⟨xs,hp⟩ := enumeration_subset perm
        (show E \ {choice.event} ⊆ E₁ ∪ E₂ from fun _ h => subset h.1)
      obtain ⟨t,ht⟩ := supply _ xs hp (fun x h => supU x (subset h.1))
      exact ⟨t,canonical C _ t ht,ht⟩
    by_cases member₁ : choice.event ∈ E₁
    · obtain ⟨t₁,ht₁⟩ := sideSupply E₁ Set.subset_union_left
      have dec₁ := side_decomposition laws vcs canonical causal substitute C (E₁ ∪ E₂)
        choice trans irrefl supU closedU π perm recurs E₁ a t₁
        Set.subset_union_left closed₁ member₁ ha ht₁.2
      by_cases member₂ : choice.event ∈ E₂
      · obtain ⟨t₂,ht₂⟩ := sideSupply E₂ Set.subset_union_right
        obtain ⟨t₀,ht₀⟩ := sideSupply (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
        have closedBase : (scheme C).Closed (E₁ ∩ E₂) :=
          fun x y edge h => ⟨closed₁ x y edge h.1,closed₂ x y edge h.2⟩
        have dec₂ := side_decomposition laws vcs canonical causal substitute C (E₁ ∪ E₂)
          choice trans irrefl supU closedU π perm recurs E₂ b t₂
          Set.subset_union_right closed₂ member₂ hb ht₂.2
        have dec₀ := side_decomposition laws vcs canonical causal substitute C (E₁ ∪ E₂)
          choice trans irrefl supU closedU π perm recurs (E₁ ∩ E₂) l t₀
          (fun _ h => Or.inl h.1) closedBase ⟨member₁,member₂⟩ hl ht₀.2
        have union : (E₁ \ {choice.event}) ∪ (E₂ \ {choice.event}) =
            (E₁ ∪ E₂) \ {choice.event} := by ext x; simp only [Set.mem_union,Set.mem_diff]; tauto
        have intersection : (E₁ \ {choice.event}) ∩ (E₂ \ {choice.event}) =
            (E₁ ∩ E₂) \ {choice.event} := by ext x; simp only [Set.mem_inter_iff,Set.mem_diff]; tauto
        have mid := IH _ smaller (E₁ \ {choice.event}) (E₂ \ {choice.event}) t₀ t₁ t₂
          (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
          (fun x h => sup₁ x h.1) (fun x h => sup₂ x h.1) closedPre₁ closedPre₂
          (by simpa only [intersection] using ht₀.2) ht₁.2 ht₂.2
        exact shared_step laws vcs causal sharedMetadata substitute C E₁ E₂ choice ctx
          l a b t₀ t₁ t₂ member₁ member₂ hl ha hb ht₀ ht₁ ht₂ dec₀.2 dec₁.2 dec₂.2
          (by simpa only [union] using mid.2)
      · have union : (E₁ \ {choice.event}) ∪ E₂ = (E₁ ∪ E₂) \ {choice.event} := by
          ext x
          simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
          constructor
          · rintro (h | h)
            · exact ⟨Or.inl h.1,h.2⟩
            · exact ⟨Or.inr h,fun equal => member₂ (equal ▸ h)⟩
          · rintro ⟨h | h,ne⟩
            · exact Or.inl ⟨h,ne⟩
            · exact Or.inr h
        have intersection : (E₁ \ {choice.event}) ∩ E₂ = E₁ ∩ E₂ := by
          ext x
          simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
          constructor
          · exact fun h => ⟨h.1.1,h.2⟩
          · exact fun h => ⟨⟨h.1,fun equal => member₂ (equal ▸ h.2)⟩,h.2⟩
        have mid := IH _ smaller (E₁ \ {choice.event}) E₂ l t₁ b
          (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
          (fun x h => sup₁ x h.1) sup₂ closedPre₁ closed₂
          (by simpa only [intersection] using hl) ht₁.2 hb
        exact local_step laws vcs causal localMetadata substitute C E₁ E₂ choice ctx
          l a b t₁ member₁ member₂ ⟨canonical C _ l hl,hl⟩ ha ⟨canonical C _ b hb,hb⟩ ht₁
          dec₁.2 (by simpa only [union] using mid.2)
    · have member₂ : choice.event ∈ E₂ := choice.member.resolve_left member₁
      obtain ⟨t₂,ht₂⟩ := sideSupply E₂ Set.subset_union_right
      have dec₂ := side_decomposition laws vcs canonical causal substitute C (E₁ ∪ E₂)
        choice trans irrefl supU closedU π perm recurs E₂ b t₂
        Set.subset_union_right closed₂ member₂ hb ht₂.2
      have union : (E₂ \ {choice.event}) ∪ E₁ = (E₁ ∪ E₂) \ {choice.event} := by
        ext x
        simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
        constructor
        · rintro (h | h)
          · exact ⟨Or.inr h.1,h.2⟩
          · exact ⟨Or.inl h,fun equal => member₁ (equal ▸ h)⟩
        · rintro ⟨h | h,ne⟩
          · exact Or.inr h
          · exact Or.inl ⟨h,ne⟩
      have intersection : (E₂ \ {choice.event}) ∩ E₁ = E₁ ∩ E₂ := by
        ext x
        simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
        constructor
        · exact fun h => ⟨h.2,h.1.1⟩
        · exact fun h => ⟨⟨h.2,fun equal => member₁ (equal ▸ h.1)⟩,h.1⟩
      have mid := IH _ smaller (E₂ \ {choice.event}) E₁ l t₂ a
        (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
        (fun x h => sup₂ x h.1) sup₁ closedPre₂ closed₁
        (by simpa only [intersection] using hl) ht₂.2 ha
      have midU : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge l t₂ a) := by
        simpa only [union] using mid.2
      let swappedChoice : DependencyPeelChoice A P R C (scheme C) (E₂ ∪ E₁) := {
        event := choice.event
        member := by simpa only [Set.union_comm] using choice.member
        semantic_maximal := by simpa only [Set.union_comm] using choice.semantic_maximal
        metadata_maximal := by simpa only [Set.union_comm] using choice.metadata_maximal
        remainder := choice.remainder
        past := choice.past
        remainder_admissible := by simpa only [Set.union_comm] using choice.remainder_admissible
        past_admissible := choice.past_admissible
        reconstructed_past := choice.reconstructed_past
        reconstructed_union := by simpa only [Set.union_comm] using choice.reconstructed_union }
      have swappedCtx : PeelContext A P scheme C E₂ E₁ swappedChoice.event := by
        simpa only [swappedChoice,Set.union_comm] using
          (show PeelContext A P scheme C E₂ E₁ choice.event from
            ⟨trans,irrefl,sup₂,sup₁,closed₂,closed₁,
              by simpa only [Set.union_comm] using choice.semantic_maximal,
              by simpa only [Set.union_comm] using choice.metadata_maximal⟩)
      have result := local_step laws vcs causal localMetadata substitute C E₂ E₁ swappedChoice swappedCtx
        l b a t₂ (by simpa only [swappedChoice] using member₂)
        (by simpa only [swappedChoice] using member₁)
        (by simpa only [Set.inter_comm] using (show Admissible A P R C (E₁ ∩ E₂) l from
          ⟨canonical C _ l hl,hl⟩)) hb ⟨canonical C _ a ha,ha⟩
        (by simpa only [swappedChoice] using ht₂)
        (by simpa only [swappedChoice] using dec₂.2)
        (by simpa only [swappedChoice,Set.union_comm] using midU)
      exact swap_step vcs symmetry C E₁ E₂ l a b (by simpa only [Set.union_comm] using result)

/-- Replay-side evidence at one context. Neither field refers to merge. -/
structure ReplaySupply (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies A C)
    (C : ReplayContext D.toUpdateSig) where
  represented : ∀ E π, listPermOf π E → Supported C E → ∃ s, R C E s
  peel : ∀ E s, R C E s → Supported C E → E.Nonempty → (scheme C).Closed E →
    Nonempty (DependencyPeelChoice A P R C (scheme C) E)

/-- Representation Join is derived by the strong induction above. Its
supplies may depend on evidence carried by the two input representations,
such as efficient OR-set's timestamp-monotone replay context. -/
theorem representationJoin_of_vcs {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (canonical : RepresentsCanonical A P R) (substitute : MetadataSubstitution A R)
    (initial : InitialMetadata R) (initMetadata : InitMetadata R)
    (symmetry : MergeCommMetadata R) (causal : CausalMetadata A P R scheme)
    (localMetadata : LocalMetadata A P R scheme) (sharedMetadata : SharedMetadata A P R scheme)
    (supply : ∀ C E₁ E₂ a b, Transitive C.vis → (∀ x, ¬ C.vis x x) →
      Supported C E₁ → Supported C E₂ → R C E₁ a → R C E₂ b → ReplaySupply A P R scheme C) :
    RepresentationJoin R := by
  intro C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  obtain ⟨π₁,hp₁,_,_⟩ := canonical C E₁ a ha
  obtain ⟨π₂,hp₂,_,_⟩ := canonical C E₂ b hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have kit := supply C E₁ E₂ a b trans irrefl sup₁ sup₂ ha hb
  have sizes := join_at_sizes laws vcs canonical substitute initial initMetadata
    symmetry causal localMetadata sharedMetadata C trans irrefl kit.represented kit.peel
  exact (sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun x y edge h => closed₁ x y ((scheme C).causal x y edge) h)
    (fun x y edge h => closed₂ x y ((scheme C).causal x y edge) h) hl ha hb).2

end Sal.MRDTs.Paper1.AbstractMRDT
