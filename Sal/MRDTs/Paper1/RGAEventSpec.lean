import Sal.MRDTs.Paper1.HistoryInputs
import Sal.MRDTs.Paper1.RGAIdentified
import Sal.MRDTs.Paper1.RGACrossedEvidence

/-! The agreed RGA sequential alphabet retains the exact MRDT update inputs:
timestamp, replica, and operation. Insertion uses the supplied timestamp as its
identifier. The abstract machine is still an independent list plus allocation
registry; no concrete state or implementation replay is consulted. Replica
input is accepted and has no effect on the current datatype's list semantics.
Freshness is unchanged, and no increasing-timestamp replay guard is added. -/
namespace Sal.MRDTs.Paper1.RGA.EventSpec
open Foundation
open Sal.MRDTs.Instances.RGA

def machine : HistoryMachine (Op RGAOp) Unit (List Nat) :=
  (Identified.machine true).withInputs Identified.project

def spec : HistorySpec (Op RGAOp) Unit (List Nat) := machine.toSpec

def missingMachine : HistoryMachine (Op RGAOp) Unit (List Nat) :=
  (Identified.machine false).withInputs Identified.project

def missingSpec : HistorySpec (Op RGAOp) Unit (List Nat) := missingMachine.toSpec

theorem spec_eq : spec = Identified.strictSpec.withInputs Identified.project :=
  (Identified.machine true).toSpec_withInputs Identified.project

theorem missingSpec_eq :
    missingSpec = Identified.missingNoopSpec.withInputs Identified.project :=
  (Identified.machine false).toSpec_withInputs Identified.project

theorem insertion_uses_timestamp (s t : List Nat × Finset Nat)
    (ts replica anchor : Nat) :
    machine.transition s (.update (ts,replica,.addAfter anchor)) t ↔
      ts ∉ s.2 ∧ (anchor = 0 ∨ anchor ∈ s.1) ∧
        t = (insertAfter anchor ts s.1, insert ts s.2) := by
  simp [machine, HistoryMachine.withInputs, Identified.machine,
    SeqLabel.mapUpdate, Identified.project, Op.time, Op.op]

theorem deletion_uses_target (s t : List Nat × Finset Nat)
    (ts replica target : Nat) :
    machine.transition s (.update (ts,replica,.remove target)) t ↔
      t = (s.1.filter (· ≠ target),s.2) := Iff.rfl

theorem replica_independent (s t : List Nat × Finset Nat)
    (ts r₁ r₂ : Nat) (op : RGAOp) :
    machine.transition s (.update (ts,r₁,op)) t ↔
      machine.transition s (.update (ts,r₂,op)) t := by
  cases op <;> rfl

theorem project_surjective : Function.Surjective Identified.project := by
  intro u
  cases u with
  | addAfter id anchor => exact ⟨(id,0,.addAfter anchor),rfl⟩
  | remove id => exact ⟨(0,0,.remove id),rfl⟩

/-- Adding the original replica and timestamp inputs preserves exactly the
identified specification conflicts, rather than approximating them. -/
theorem commutes_iff (a b : Op RGAOp) :
    spec.Commutes a b ↔
      Identified.strictSpec.Commutes (Identified.project a) (Identified.project b) := by
  rw [spec_eq]
  exact Identified.strictSpec.withInputs_commutes_iff _ project_surjective a b

theorem versions_of_execution {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) :
    ∀ v s E, C.ver v = some (s,E) → ∀ q,
      ∃ π : List (Op RGAOp), listPermOf π E ∧
        respects π (paperOrder emptyPolicy C.replayContext E) ∧
        respects π (projectedSpecVisibility id spec C.replayContext) ∧
        spec.admits (projectedLabels (D := RGAM) id π ++ [.query q (RGAM.query s q)]) := by
  intro v s E hv q
  obtain ⟨π,hp,ho,hs,ha⟩ := Identified.versions_of_execution true exec v s E hv q
  refine ⟨π,hp,ho,?_,?_⟩
  · apply hs.imp
    intro a b hab hnew
    exact hab ⟨hnew.1, fun hc => hnew.2 ((commutes_iff b a).mpr hc)⟩
  · rw [spec_eq]
    simpa only [HistorySpec.withInputs, projectedLabels, List.map_append,
      List.map_cons, List.map_nil, List.map_map, SeqLabel.mapUpdate] using ha

theorem certifiedRA (C : Configuration RGAM)
    (reach : MintCertifiedReach RGAM generation C) :
    EventSpecificationRALinearizable RGAM emptyPolicy spec C := by
  rw [spec_eq]
  exact projected_withInputs (project := id) (Identified.certifiedStrictRA C reach)

theorem certifiedRAV (C : Configuration RGAM)
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    EventSpecificationRALinearizable RGAM emptyPolicy spec C := by
  rw [spec_eq]
  exact projected_withInputs (project := id) (Identified.certifiedStrictRAV C reach)

theorem certifiedLiteralRA (C : Configuration RGAM)
    (reach : MintCertifiedReach RGAM generation C) :
    EventRALinearizable RGAM emptyPolicy spec C := (certifiedRA C reach).active

theorem certifiedLiteralRAV (C : Configuration RGAM)
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    EventRALinearizable RGAM emptyPolicy spec C := (certifiedRAV C reach).active

theorem certifiedMissingRA (C : Configuration RGAM)
    (reach : MintCertifiedReach RGAM generation C) :
    EventSpecificationRALinearizable RGAM emptyPolicy missingSpec C := by
  rw [missingSpec_eq]
  exact projected_withInputs (project := id) (Identified.certifiedMissingNoopRA C reach)

theorem certifiedMissingRAV (C : Configuration RGAM)
    (reach : MintCertifiedReachV RGAM (canonicalVirtualMergeBase RGAM) generation C) :
    EventSpecificationRALinearizable RGAM emptyPolicy missingSpec C := by
  rw [missingSpec_eq]
  exact projected_withInputs (project := id) (Identified.certifiedMissingNoopRAV C reach)

theorem certifiedExecutions (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTS RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy id spec (initConfig RGAM) trace :=
  projected_certified_executions certifiedRA trace execution

theorem certifiedExecutionsV (trace : List (Label RGAM × Configuration RGAM))
    (execution : (certifiedTSV RGAM generation).Execution (initConfig RGAM) trace) :
    ProjectedSpecificationExecution RGAM emptyPolicy id spec (initConfig RGAM) trace :=
  projected_certified_executionsV certifiedRAV trace execution

/-- Nonvacuity: the original crossed execution has a full-input witness. -/
theorem crossed_accepted :
    MintCertifiedReach RGAM generation (CrossedExecution.config 10) ∧
    EventSpecificationRALinearizable RGAM emptyPolicy spec (CrossedExecution.config 10) ∧
    RGAM.query (CrossedExecution.records 10).1 () = [5,4,8,7] ∧
    RGAM.query (CrossedExecution.records 10).1 () ≠ [] := by
  refine ⟨CrossedExecution.Evidence.mint_certified,
    certifiedRA _ CrossedExecution.Evidence.mint_certified,
    CrossedExecution.Evidence.final_read, ?_⟩
  rw [CrossedExecution.Evidence.final_read]
  change ([5,4,8,7] : List Nat) ≠ []
  decide

/-- PASS+FAIL: a legal full-input history preserves supplied IDs, ignores
replica placement, and permits a removal timestamp earlier than its replay
predecessor. The ID is never allocated again by the specification. -/
theorem supplied_inputs_control :
    spec.admits [.update (4,0,.addAfter 0), .update (7,1,.addAfter 4),
      .update (5,0,.remove 4), .query () [7]] ∧
    ¬ spec.admits [.update (4,0,.addAfter 0), .update (7,1,.addAfter 4),
      .update (5,0,.remove 4), .query () [4,7]] := by
  rw [spec_eq]
  change Identified.strictSpec.admits
      [.update (.addAfter 4 0),.update (.addAfter 7 4),.update (.remove 4),.query () [7]] ∧
    ¬ Identified.strictSpec.admits
      [.update (.addAfter 4 0),.update (.addAfter 7 4),.update (.remove 4),.query () [4,7]]
  constructor
  · refine ⟨([7],{4,7}), .cons (m := ([4],{4})) ?_
      (.cons (m := ([4,7],{4,7})) ?_
        (.cons (m := ([7],{4,7})) rfl (.cons ⟨rfl,rfl⟩ (.nil _))))⟩
    · exact ⟨by decide,Or.inr (Or.inl rfl),rfl⟩
    · exact ⟨by decide,Or.inr (Or.inr (by decide)),by decide⟩
  · rintro ⟨final,run⟩
    cases run with
    | cons h₁ rest =>
      cases rest with
      | cons h₂ rest =>
        cases rest with
        | cons h₃ rest =>
          cases rest with
          | cons hq rest =>
            cases rest
            simp_all [Identified.machine, insertAfter]

end Sal.MRDTs.Paper1.RGA.EventSpec
