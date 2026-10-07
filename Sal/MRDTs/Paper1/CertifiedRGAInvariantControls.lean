import Sal.MRDTs.Paper1.CertifiedRGAInvariant
import Sal.MRDTs.Paper1.CertifiedRGAOrderComparison
import Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate

namespace Sal.MRDTs.Paper1.CertifiedRGAInvariantControls
open Foundation Sal.EmbedRGA Instances.EmbedRGA Instances.ProductionRGA
open CertifiedRGARawOrderObstruction

abbrev context := (config 6).replayContext
abbrev valid := CertifiedRGAInvariant.Valid unaryCode context
abbrev revised := InvariantOrder.order valid (commutingPolicy RGAM.AppOp) context
  (↑((indices 6).image event) : Set Event)

theorem honest : EHonestCore unaryCode context :=
  eHonest_core (eHonest_of_mint (mint_honest 6))

theorem event_supported (i : I) : event i ∈ context.events := by
  refine ⟨0,(↑((indices 6).image event) : Set Event),?_,?_⟩
  · rfl
  · exact Finset.mem_image.mpr ⟨i,by fin_cases i <;> decide +kernel,rfl⟩

theorem pair_order (i j : I) : revised (event i) (event j) ↔
    vis 6 (event i) (event j) ∧ ¬ embedSemanticCommutes (event i) (event j) := by
  simp only [revised,InvariantOrder.order,commutingPolicy]
  rw [CertifiedRGAInvariant.invariant_commutes_iff unaryCode context honest
    (event i) (event j) (event_supported i) (event_supported j)]
  simp
  intro _
  rfl

/-- The same hand-derived original-spec explanation passes the revised order
and still fails the retained global raw criterion. -/
theorem explanation_control :
    respects goodHistory revised ∧
    (GuardedHistory.language (embedClientSpec (α := Nat) unaryCode)).admits
      (projectedLabels id goodHistory ++ [.query () [30,40]]) ∧
    RGAM.query (records 6).1 () = [30,40] ∧
    RGAM.query (records 6).1 () ≠ [30] ∧
    ¬ respects goodHistory (paperOrder (commutingPolicy RGAM.AppOp) context
      (↑((indices 6).image event) : Set Event)) := by
  refine ⟨?_,admitted_history_control.1,final_read.1,?_,admitted_history_control.2⟩
  · simp only [goodHistory,respects,List.pairwise_cons,List.mem_cons,
      List.mem_singleton,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    simp only [pair_order]
    simp [embedSemanticCommutes,event]
    change ¬ vis 6 (event 1) (event 0)
    decide
  · change [30,40] ≠ [30]
    decide

theorem extra_edge_control :
    paperOrder (commutingPolicy RGAM.AppOp) context
      (↑((indices 6).image event) : Set Event) (event 1) (event 2) ∧
    ¬ revised (event 1) (event 2) := by
  refine ⟨CertifiedRGAOrderComparison.paper_has_extra_edge _,?_⟩
  rw [pair_order]
  simp [embedSemanticCommutes,event]

/-- The real birth/delete dependency remains; validity does not make causal
noncommutation vacuous. -/
theorem own_birth_control :
    valid [] ∧
    ¬ InvariantOrder.Commutes RGAM.toUpdateSig valid (event 0) (event 1) ∧
    revised (event 0) (event 1) := by
  refine ⟨CertifiedRGAInvariant.empty_valid unaryCode context,?_,?_⟩
  · rw [CertifiedRGAInvariant.invariant_commutes_iff unaryCode context honest
      _ _ (event_supported 0) (event_supported 1)]
    simp [embedSemanticCommutes,event]
  · rw [pair_order]
    constructor
    · change vis 6 (event 0) (event 1)
      decide
    · simp [embedSemanticCommutes,event]

/-- The malformed carrier that witnesses the old extra edge is outside the
explicit sorted-and-provenance domain. -/
theorem scratch_excluded : ¬ valid CertifiedRGAHistory.Controls.scratch := by
  intro h
  obtain ⟨o,ho,_,rec⟩ := h.2 (1,9,[false]) (by simp [CertifiedRGAHistory.Controls.scratch])
  have stamp : o.1 = (event 0).1 := by simpa [eRecOf,event] using (congrArg Prod.fst rec).symm
  have eq := context.ts_unique ho (event_supported 0) stamp
  rw [eq] at rec
  simp [event,eRecOf] at rec

/-- The revised and retained criteria give different answers on exactly the
same original-issuer execution and unchanged independent public language. -/
theorem certified_execution_comparison :
    MintCertifiedReach RGAM issuance (config 6) ∧
    InvariantOrder.VersionsRA RGAM valid
      CertifiedRGAInvariantCertificate.policy
      (GuardedHistory.language (embedClientSpec (α := Nat) unaryCode)) (config 6) ∧
    ¬ EventVersionsSpecificationRA RGAM (commutingPolicy RGAM.AppOp)
      (GuardedHistory.language (embedClientSpec (α := Nat) unaryCode)) (config 6) :=
  ⟨mint_certified,CertifiedRGAInvariantCertificate.versions unaryCode (.ordinary mint_certified),
    (certified_raw_criterion_failure (commutingPolicy RGAM.AppOp)).2⟩

#print axioms certified_execution_comparison

#print axioms explanation_control
#print axioms extra_edge_control
#print axioms own_birth_control
#print axioms scratch_excluded
end Sal.MRDTs.Paper1.CertifiedRGAInvariantControls
