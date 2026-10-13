import Sal.MRDTs.Paper1.CertifiedSidedInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedSidedRawOrderObstruction

namespace Sal.MRDTs.Paper1.CertifiedSidedInvariantControls
open Foundation Sal.EmbedRGA Instances.SidedEmbedRGA Instances.ProductionRGA
open CertifiedSidedRawOrderObstruction

abbrev context := (config 6).replayContext
abbrev valid := CertifiedSidedInvariant.Valid unaryCode context

theorem honest : SHonestCore unaryCode context :=
  sHonest_core (sHonest_of_mint (mint_honest 6))

/-- The original issuer, query and independent language are identical in both
verdicts. Only the quantified concrete state domain differs. -/
theorem certified_execution_comparison :
    MintCertifiedReach RGAM issuance (config 6) ∧
    InvariantOrder.VersionsRA RGAM valid CertifiedSidedInvariantCertificate.policy
      (GuardedHistory.language (sidedClientSpec unaryCode)) (config 6) ∧
    ¬ EventVersionsSpecificationRA RGAM (commutingPolicy RGAM.AppOp)
      (GuardedHistory.language (sidedClientSpec unaryCode)) (config 6) :=
  ⟨mint_certified,CertifiedSidedInvariantCertificate.versions unaryCode (.ordinary mint_certified),
    (certified_raw_criterion_failure (commutingPolicy RGAM.AppOp)).2⟩

/-- Hand-derived live values exclude losing the concurrent anchored insertion. -/
theorem final_query_control : RGAM.query (records 6).1 () = [30,40] ∧
    RGAM.query (records 6).1 () ≠ [30] := final_read

/-- Nonvacuity: the empty valid state still distinguishes allocating a birth
from deleting it. Unrelated insertion/deletion really commute on the invariant. -/
theorem commutation_control :
    valid [] ∧
    InvariantOrder.Commutes RGAM.toUpdateSig valid (event 1) (event 2) ∧
    ¬ InvariantOrder.Commutes RGAM.toUpdateSig valid (event 0) (event 1) := by
  have supported (i : I) : event i ∈ context.events := by
    refine ⟨0,(↑((indices 6).image event) : Set Event),?_,?_⟩
    · rfl
    · change event i ∈ (indices 6).image event
      simp [indices]
  refine ⟨CertifiedSidedInvariant.empty_valid unaryCode context,?_,?_⟩
  · apply (CertifiedSidedInvariant.invariant_commutes_iff unaryCode context honest
      _ _ (supported 1) (supported 2)).mpr
    simp [sidedSemanticCommutes,event]
  · rw [CertifiedSidedInvariant.invariant_commutes_iff unaryCode context honest
      _ _ (supported 0) (supported 1)]
    simp [sidedSemanticCommutes,event]

#print axioms certified_execution_comparison
#print axioms commutation_control
end Sal.MRDTs.Paper1.CertifiedSidedInvariantControls
