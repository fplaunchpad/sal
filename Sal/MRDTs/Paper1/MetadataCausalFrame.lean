import Sal.MRDTs.Paper1.MetadataRewrite

/-! Guarded framing of causal reconstruction permits the induction's smaller
merge result to replace the chosen remainder. The framing uses identical
represented histories, not unrestricted observational merge congruence. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

theorem causal_frame {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (metadata : CausalMetadata A P R scheme) (substitute : MetadataSubstitution A R)
    (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (choice : DependencyPeelChoice A P R C (scheme C) U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme C).Closed U)
    (mid : D.State) (represented : R C (U \ {choice.event}) mid) :
    Admissible A P R C U
      (D.merge choice.past mid (D.update choice.past choice.event)) := by
  have pastSub := (scheme C).past_subset U choice.event closed choice.member
  have intersection : (U \ {choice.event}) ∩ (scheme C).Past choice.event =
      (scheme C).Past choice.event \ {choice.event} := by
    ext x
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨pastSub h.1,h.2⟩,h.1⟩
  have union : (U \ {choice.event}) ∪ (scheme C).Past choice.event = U := by
    ext x
    constructor
    · exact fun h => h.elim (fun h => h.1) (fun h => pastSub h)
    · intro hx
      by_cases equal : x = choice.event
      · exact Or.inr (Or.inl equal)
      · exact Or.inl ⟨hx,equal⟩
  have base : R C ((U \ {choice.event}) ∩ (scheme C).Past choice.event) choice.past := by
    rw [intersection]
    exact choice.past_admissible.2
  have original := causal_reconstruction laws vcs metadata C U choice
    trans irrefl supported closed
  have frame := substitute C (U \ {choice.event}) ((scheme C).Past choice.event)
    choice.past mid (D.update choice.past choice.event)
    choice.past choice.remainder (D.update choice.past choice.event)
    (fun x h => supported x h.1) (fun x h => supported x (pastSub h))
    base represented choice.reconstructed_past base choice.remainder_admissible.2
    choice.reconstructed_past
  refine ⟨canonical_congr original.1 (equivalent_symm frame.1),?_⟩
  rw [union] at frame
  exact frame.2 original.2

end Sal.MRDTs.Paper1.AbstractMRDT
