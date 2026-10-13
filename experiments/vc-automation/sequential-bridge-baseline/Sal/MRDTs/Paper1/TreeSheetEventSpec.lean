import Sal.MRDTs.Paper1.GuardedHistory
import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.Instances.AegisSheetSequential

/-! Full-input history-language ports for TreeMove and AegisSheet. Abstract
transitions are the existing independent in-place tree and sheet machines.
Their public causal-origin legality contracts are retained, including through
merge witnesses; neither language calls concrete update or merge. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace TreeMoveEvent
open Instances.TreeMove

noncomputable def spec := GuardedHistory.language sequentialSpec

theorem restricted : RestrictedLaws D.toUpdateSig (commutingPolicy D.AppOp) :=
  restricted_of_all_commute all_comm

theorem legal_prefix (pre suf : List Event) (h : ClientLegal (pre ++ suf)) :
    ClientLegal pre := by
  refine ⟨⟨(List.nodup_append.mp h.1.1).1, (List.pairwise_append.mp h.1.2).1⟩, ?_⟩
  intro before e after split
  apply h.2 before e (after ++ suf)
  simp [split, List.append_assoc]

theorem legal_respects_vis (C : Configuration D) (ops : List Event)
    (h : ClientLegal ops) : respects ops C.vis := by
  unfold respects
  refine h.1.2.imp ?_
  intro a b hab hba
  have hbaLE := eventLE_of_timestamp_lt (C.causal_mono hba)
  have heq := eventKey_injective (le_antisymm hab hbaLE)
  subst b
  exact Nat.lt_irrefl _ (C.causal_mono hba)

theorem versions {C : Configuration D} (exec : CertifiedExecution D generation C) :
    EventVersionsSpecificationRA D (commutingPolicy D.AppOp) spec C :=
  event_versions_of_guarded_certificate sequentialCorrectness legal_prefix all_comm
    (fun C _ => join C.replayContext) legal_respects_vis exec

theorem certifiedV : EventCertifiedSpecificationRAV D (commutingPolicy D.AppOp) spec generation :=
  fun _ reach => versions (.virtual reach)

theorem certified : EventCertifiedSpecificationRA D (commutingPolicy D.AppOp) spec generation :=
  certifiedV.ordinary

theorem reserved_move_rejected :
    ¬ spec.admits [.update (3,1,⟨0,9,root⟩)] :=
  GuardedHistory.rejects_first_update sequentialSpec _ clientLegal_rejects_reserved []

/-- PASS+FAIL on retained origin legality, with hand-specified move inputs. -/
theorem origin_control : sequentialSpec.Legal [firstMove] ∧
    ¬ spec.admits [.update (3,1,⟨0,9,root⟩)] :=
  ⟨clientLegal_firstMove,reserved_move_rejected⟩

end TreeMoveEvent

namespace AegisSheetEvent
open Instances.AegisSheet
open Instances.AegisSheet.Sequential

def spec := GuardedHistory.language clientSpec

theorem restricted : RestrictedLaws D.toUpdateSig (commutingPolicy D.AppOp) :=
  restricted_of_all_commute all_comm

theorem legal_prefix (pre suf : List Event) (h : clientSpec.Legal (pre ++ suf)) :
    clientSpec.Legal pre := causalOriginLegal_prefix h rfl

theorem legal_respects_vis (C : Configuration D) (ops : List Event)
    (h : clientSpec.Legal ops) : respects ops C.vis :=
  chronological_respects_vis C h.1

theorem versions {C : Configuration D} (exec : CertifiedExecution D generation C) :
    EventVersionsSpecificationRA D (commutingPolicy D.AppOp) spec C :=
  event_versions_of_guarded_certificate sequentialCorrectness legal_prefix all_comm
    (fun C _ => join C.replayContext) legal_respects_vis exec

theorem certifiedV : EventCertifiedSpecificationRAV D (commutingPolicy D.AppOp) spec generation :=
  fun _ reach => versions (.virtual reach)

theorem certified : EventCertifiedSpecificationRA D (commutingPolicy D.AppOp) spec generation :=
  certifiedV.ordinary

theorem missing_origin_rejected :
    ¬ spec.admits [.update unavailableOriginColumn] := by
  apply GuardedHistory.rejects_first_update clientSpec
  intro legal
  obtain ⟨origin,subset,guard⟩ := legal.2 [] unavailableOriginColumn [] rfl
  have empty : origin = ∅ := Finset.Subset.antisymm subset (by simp)
  subst origin
  have good := guard.1
  change applicableB unavailableOriginColumn ∅ = true at good
  have bad : applicableB unavailableOriginColumn ∅ = false := by decide +kernel
  rw [bad] at good
  exact Bool.noConfusion good

/-- Retain the established causal-origin positive and negative controls. -/
theorem origin_control :
    clientSpec.Legal [independentRow,independentColumn] ∧
      ¬ spec.admits [.update unavailableOriginColumn] := by
  refine ⟨?_,missing_origin_rejected⟩
  constructor
  · apply chronological_of_pairwise
    decide +kernel
  · intro pre e post split
    have member : e ∈ [independentRow,independentColumn] := by
      rw [split]
      simp
    simp at member
    rcases member with rfl | rfl
    · exact ⟨∅,by simp,by decide +kernel⟩
    · exact ⟨∅,by simp,by decide +kernel⟩

end AegisSheetEvent
end Sal.MRDTs.Paper1
