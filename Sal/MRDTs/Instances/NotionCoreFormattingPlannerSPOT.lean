import Sal.MRDTs.Instances.NotionCoreFormattingPlanner
import Sal.MRDTs.Instances.NotionCoreFormattingSourceSPOT

/-! Hand-derived PASS+FAIL tests for maximal whole-instance runs. Original
N002/N003 falsifiers remain in SourceSPOT; these candidate controls do not
replace those failures or alter the pinned original compiler. -/
namespace Sal.MRDTs.Instances.NotionCoreFormattingPlannerSPOT
open NotionCoreFormattingSource
open NotionCoreFormattingSourceSPOT
open NotionCoreFormattingPlanner
open NotionCoreSpec
open NotionCoreFormattingSpec

abbrev decode := NotionCorePhysicalReplay.address

def candidate (forest : NotionCoreOriginTree.Forest) (counter : Nat)
    (selection : List Character) : List MarkOp :=
  operationsFor 0 (planToggle (fun _ => forest) [0] [65] counter selection)

/-- PASS+FAIL: displayed ba becomes one maximal physical run ab. The original
compiler still emits its empty interval; the candidate is not singleton-per-ID. -/
theorem N002_candidate_maximal_run :
    candidate fullN002 6 [selected sourceB, selected sourceA] =
      [⟨⟨6,[65]⟩, before sourceA, finish, true⟩] ∧
    values fullN002 (candidate fullN002 6 [selected sourceB, selected sourceA]) = [true,true] ∧
    (candidate fullN002 6 [selected sourceB, selected sourceA]).length ≠ 2 ∧
    values fullN002 (candidate fullN002 6 [selected sourceB, selected sourceA]) ≠
      values fullN002 (operationsFor 0
        (toggleBold (fun _ => fullN002) [65] 6 [selected sourceB, selected sourceA])) := by decide +kernel

/-- PASS+FAIL: ac is two maximal physical runs. Hidden marker positions remain
inside intervals, while the unselected live b is excluded. -/
theorem N003_candidate_two_runs :
    candidate fullN003 7 [selected sourceA, selected sourceC] =
      [⟨⟨7,[65]⟩, before sourceA, before sourceB, true⟩,
       ⟨⟨8,[65]⟩, before sourceC, finish, true⟩] ∧
    values fullN003 (candidate fullN003 7 [selected sourceA, selected sourceC]) = [true,false,true] ∧
    values fullN003 (candidate fullN003 7 [selected sourceA, selected sourceC]) ≠ [true,true,true] ∧
    (candidate fullN003 7 [selected sourceA, selected sourceC]).length ≠ 1 := by decide +kernel

/-- PASS+FAIL: deleted text and markers do not split a maximal visible run.
Their physical entries remain covered; the following live c stays plain. -/
theorem hidden_candidate_control :
    candidate NotionCoreFormattingSourceSPOT.hidden 20 [selected a] = [⟨⟨20,[65]⟩, before a, before c, true⟩] ∧
    values NotionCoreFormattingSourceSPOT.hidden (candidate NotionCoreFormattingSourceSPOT.hidden 20 [selected a]) = [true,false] ∧
    covers NotionCoreFormattingSourceSPOT.hidden ⟨⟨20,[65]⟩, before a, before c, true⟩ 1 = true ∧
    covers NotionCoreFormattingSourceSPOT.hidden ⟨⟨20,[65]⟩, before a, before c, true⟩ 2 = true ∧
    values NotionCoreFormattingSourceSPOT.hidden (candidate NotionCoreFormattingSourceSPOT.hidden 20 [selected a]) ≠ [true,true] := by decide +kernel

/-- PASS+FAIL: verdict is once over the whole selection, including independent
instances. Instance traversal order determines fresh IDs; mixed marks add both. -/
theorem multi_instance_verdict_control :
    (planToggle (fun _ => abc) [0,1] [65] 20
      [selected a true 1, selected b false 0]).map (fun pair => (pair.1, pair.2.id.counter, pair.2.value)) =
      [(0,20,true),(1,21,true)] ∧
    (planToggle (fun _ => abc) [0,1] [65] 20
      [selected a true 1, selected b true 0]).map (fun pair => pair.2.value) = [false,false] ∧
    (planToggle (fun _ => abc) [0,1] [65] 20
      [selected a true 1, selected b false 0]).map (fun pair => pair.2.value) ≠ [true,false] := by decide +kernel

private def reordered : State := plain
  [⟨10, 0, [root 0, character 0 (Encodable.encode ([83] : List Nat), 3) 98, character 0 (Encodable.encode ([83] : List Nat), 2) 97], true⟩]
private def coord : Address → Nat := fun address => if address = decode 0 sourceA.id then 1 else 3

private theorem reordered_related :
    DisplayCoordinates reordered.document (fun _ => fullN002) decode coord [0] := by
  intro block member _ slot retained live
  simp only [reordered, plain, List.mem_singleton] at member
  subst block
  simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with rfl | rfl | rfl
  · simp [root] at live
  · exact ⟨by decide, by decide, ⟨sourceB, 3, 4⟩, by decide, rfl, by decide⟩
  · exact ⟨by decide, by decide, ⟨sourceA, 1, 4⟩, by decide, rfl, by decide⟩

/-- Nonvacuous use of the general refinement theorem on the reversed display;
selected physical IDs are decoded to actual retained core addresses. -/
theorem reordered_refinement_control :
    richView (NotionCoreFormattingBridge.sourceUpdate reordered (fun _ => fullN002) coord
      (planToggle (fun _ => fullN002) [0] [65] 6 [selected sourceB, selected sourceA])) =
      richView (toggle reordered [decode 0 sourceB.id, decode 0 sourceA.id]) ∧
    richView (NotionCoreFormattingBridge.sourceUpdate reordered (fun _ => fullN002) coord
      (planToggle (fun _ => fullN002) [0] [65] 6 [selected sourceB, selected sourceA])) ≠
      richView reordered := by
  refine ⟨?_, by decide +kernel⟩
  exact planToggle_refines reordered (fun _ => fullN002) coord [0] [65] 6
    [selected sourceB, selected sourceA] reordered_related rfl

#print axioms N002_candidate_maximal_run
#print axioms N003_candidate_two_runs
#print axioms reordered_refinement_control
end Sal.MRDTs.Instances.NotionCoreFormattingPlannerSPOT
