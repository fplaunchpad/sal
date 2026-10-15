import Sal.MRDTs.Paper1.GuardedORSet
import Sal.MRDTs.Instances.PeritextRender

/-! Hand-derived controls for appendix review R2-6. Character IDs share the
mark's timestamp space. PASS+FAIL statements are checked by kernel reduction;
they do not use a runtime evaluator as the expected-answer oracle. -/
namespace Sal.MRDTs.Paper1.AppendixReviewControls
open Instances.PeritextRender
open Sal.EmbedRGA (unaryCode)

private def boundaryDoc : DocD := {
  shadow := buildShadow unaryCode [(1,122,0),(2,97,1),(3,98,2),(5,120,1),(6,121,2)] }
private def boundaryMark : MarkD := {
  mid := 4, mtype := .bold, start_id := 2, end_id := 2 }

/-- Live order [1,5,2,6,3]: only before-start ignores the adjacent newer run.
After-start skips right over 6; before-end skips left over 5; after-end grows
right over 6. IDs 1,2,3 are older than mark 4 and IDs 5,6 are newer. -/
theorem all_four_boundary_kinds :
    boundaryDoc.liveIds = [1,5,2,6,3] ∧
    startIncl boundaryDoc {boundaryMark with startSide := .before} = some 2 ∧
    startIncl boundaryDoc {boundaryMark with startSide := .after} = some 4 ∧
    endExcl boundaryDoc {boundaryMark with endSide := .before} = some 1 ∧
    endExcl boundaryDoc {boundaryMark with endSide := .after} = some 4 ∧
    startIncl boundaryDoc {boundaryMark with startSide := .after} ≠ some 3 ∧
    endExcl boundaryDoc {boundaryMark with endSide := .before} ≠ some 2 := by
  decide +kernel

private def grownDeleted : DocD := {
  shadow := buildShadow unaryCode [(1,122,0),(2,97,1),(3,98,2),(5,120,3)]
  deleted := [2,3] }
private def oldMark : MarkD := {
  mid := 4, mtype := .bold, start_id := 2, end_id := 3,
  startSide := .before, endSide := .after }

/-- Start with z1,a2,b3; mark [a2,b3] at 4; grow right over x5; delete a2,b3.
The start resolves right to x5, while the end resolves left to z1 then grows
over x5. The original marked span is gone, but grown text remains formatted.
This refutes the review's proposed universal deletion-collapse assertion. -/
theorem deleted_original_span_can_leave_grown_text :
    grownDeleted.birthIds = [1,2,3,5] ∧
    grownDeleted.liveIds = [1,5] ∧
    startIncl grownDeleted oldMark = some 1 ∧ endExcl grownDeleted oldMark = some 2 ∧
    coveredDoc grownDeleted oldMark = [5] ∧
    renderMarksDoc grownDeleted [oldMark] .bold = [(122,false),(120,true)] ∧
    renderMarksDoc grownDeleted [oldMark] .bold ≠ [(122,false),(120,false)] := by
  decide +kernel

/-- A missing before-start inward survivor DOES collapse the mark. This nearby
case keeps the collapse rule observable rather than replacing it by never-empty
coverage: only the newer root sibling d remains, strictly before both anchors. -/
theorem missing_inward_boundary_collapse :
    renderMarksDoc SPOT.dEx3 [SPOT.mEx3] .bold = [(100,false)] ∧
    renderMarksDoc SPOT.dEx3 [SPOT.mEx3] .bold ≠ [(100,true)] := by
  decide +kernel
end Sal.MRDTs.Paper1.AppendixReviewControls

/-! The operation-level conditional-commutation law in the manuscript
is stronger than the guarded event law used by efficient OR-set. -/
namespace Sal.MRDTs.Paper1.AppendixReview.ORSet
open Sal.MRDTs.Foundation Sal.MRDTs.Instances.EfficientORSet
abbrev a : Event Nat := (1,2,.remove 7)
abbrev b : Event Nat := (2,0,.add 7)
abbrev c : Event Nat := (3,1,.add 7)
-- Hand-derived states: the last Add at replica1 cannot replace replica0's row.
theorem prefix_and_final_states :
    update (update (∅ : State Nat) b) a = ∅ ∧
    update (update (∅ : State Nat) a) b = {(0,2,7)} ∧
    update (update (update (∅ : State Nat) b) a) c = {(1,3,7)} ∧
    update (update (update (∅ : State Nat) a) b) c = {(0,2,7),(1,3,7)} ∧
    update (update (update (∅ : State Nat) b) a) c ≠
      update (update (update (∅ : State Nat) a) b) c := by decide
-- Add_7 fails payload-universal commutation, despite b and c commuting.
theorem payload_add_not_universally_commutative :
    ¬ (∀ u v : Event Nat, u.op = .add 7 → v.op = .add 7 → (D Nat).toUpdateSig.commutes u v) := by
  intro all
  have h := all (2,0,.add 7) (4,0,.add 7) rfl rfl (∅ : State Nat)
  have different : update (update (∅ : State Nat) (2,0,.add 7)) (4,0,.add 7) ≠
      update (update (∅ : State Nat) (4,0,.add 7)) (2,0,.add 7) := by decide
  exact different h

theorem actual_absorber_events_commute : (D Nat).toUpdateSig.commutes b c :=
  Sal.MRDTs.Paper1.EfficientORSet.NeemScope.adds_commute_of_replica_ne 2 0 3 1 7 7 (by decide)

/-- The body lifts commutation from events to operation labels universally. -/
def PayloadCommutes (left right : SetOp Nat) : Prop :=
  ∀ u v : Event Nat, u.op = left → v.op = right → (D Nat).toUpdateSig.commutes u v

/-- The corresponding operation-label conditional-commutation obligation.
All event instances and intervening event sequences must work. -/
def PayloadConditionalCommutes (left right absorber : SetOp Nat) : Prop :=
  ∀ (s : State Nat) (u v w : Event Nat) (between : List (Event Nat)),
    u.op = left → v.op = right → w.op = absorber →
    update (applySeq (D Nat).toUpdateSig (update (update s v) u) between) w =
      update (applySeq (D Nat).toUpdateSig (update (update s u) v) between) w

def BodyConditionalLaw : Prop :=
  ∀ left right absorber : SetOp Nat,
    (EfficientORSet.EventSpec.conflict Nat).before left right →
    ¬ PayloadCommutes right absorber → PayloadConditionalCommutes left right absorber

/-- Actual event noncommutation is indispensable in the correct guarded law.
Payload noncommutation wrongly licenses the different-replica absorber above. -/
theorem body_cond_comm_fails : ¬ BodyConditionalLaw := by
  intro law
  have conditional := law (.remove 7) (.add 7) (.add 7) ⟨7,rfl,rfl⟩
    payload_add_not_universally_commutative
  have equal := conditional ∅ a b c [] rfl rfl rfl
  exact prefix_and_final_states.2.2.2.2 equal

theorem equal_adds_have_no_policy_edge :
    ¬ (EfficientORSet.EventSpec.conflict Nat).before (SetOp.add 7) (SetOp.add 7) := by
  rintro ⟨x,equal,_⟩
  cases equal

#print axioms body_cond_comm_fails
#print axioms prefix_and_final_states
#print axioms payload_add_not_universally_commutative
#print axioms actual_absorber_events_commute
end Sal.MRDTs.Paper1.AppendixReview.ORSet
