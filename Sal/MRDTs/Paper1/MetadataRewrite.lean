import Sal.MRDTs.Paper1.MetadataReconstruction

/-! Directed metadata preservation accompanies an observational VC. The
conclusion is restricted to its represented, history-indexed operands; it
does not assert saturation under arbitrary observational equivalence. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def CausalMetadata (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies A C) : Prop :=
  ∀ (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (s t : D.State) (e : Op D.AppOp),
    Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U →
    (scheme C).Closed U → e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ order A P C U e x) →
    (∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x) →
    Admissible A P R C (U \ {e}) s →
    Admissible A P R C ((scheme C).Past e \ {e}) t →
    R C U (D.update s e) →
    R C U (D.merge t s (D.update t e))

/-- The causal reconstruction case follows from the observational causal VC
and its directed metadata companion. No smaller or global Join is assumed. -/
theorem causal_reconstruction {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (metadata : CausalMetadata A P R scheme)
    (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (choice : DependencyPeelChoice A P R C (scheme C) U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme C).Closed U) :
    Admissible A P R C U
      (D.merge choice.past choice.remainder (D.update choice.past choice.event)) := by
  have target := canonical_snoc laws choice.member choice.semantic_maximal
    choice.remainder_admissible.1
  have observable := vcs.causal_delta C U choice.remainder choice.past choice.event
    trans irrefl supported ((scheme C).closed_implies_conflictClosed U closed)
    choice.member choice.semantic_maximal choice.remainder_admissible choice.past_admissible
  refine ⟨canonical_congr target (equivalent_symm observable),?_⟩
  exact metadata C U choice.remainder choice.past choice.event trans irrefl supported
    closed choice.member choice.semantic_maximal choice.metadata_maximal
    choice.remainder_admissible choice.past_admissible choice.reconstructed_union

end Sal.MRDTs.Paper1.AbstractMRDT
