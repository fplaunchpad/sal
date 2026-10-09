import Sal.MRDTs.Paper1.ORSetCanonical
import Sal.MRDTs.Paper1.Automation.FiniteSetSimulation
import Sal.MRDTs.Paper1.ProjectedSimulation

namespace Sal.MRDTs.Paper1.ORSet
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

/-- The paper policy relates application operations, independently of event
identifiers: remove x is before add x. -/
def conflict (α : Type) : OperationPolicy (Update α) where
  before a b := ∃ x, a = .remove x ∧ b = .add x

theorem conflict_lift_eq : (conflict α).lift = (policy : ReplayPolicy (D α).toUpdateSig) := by
  apply congrArg (fun f => (⟨f⟩ : ReplayPolicy (D α).toUpdateSig))
  funext a b
  rcases a with ⟨t, r, ao⟩; rcases b with ⟨t', r', bo⟩
  dsimp only [OperationPolicy.lift, policy]
  cases ao <;> cases bo <;>
    simp [conflict, Op.op, order]
  all_goals split <;> simp_all [eq_comm]

theorem restrictedLaws : RestrictedLaws (D α).toUpdateSig (conflict α) := by
  constructor
  · intro a b
    simpa only [rc_iff, conflict, Op.op] using noncomm_iff_rc a b
  · rintro a b c ⟨⟨x, ha, hb⟩, ⟨y, hb', hc⟩⟩
    rw [hb] at hb'; cases hb'
  · intro s e a r ops hea hnc
    have hrc : (D α).toUpdateSig.rc e a := by
      simpa only [rc_iff, conflict, Op.op] using hea
    obtain ⟨x, he, ha⟩ := (rc_iff e a).mp hrc
    have har := (noncomm_iff_rc a r).mp hnc
    have hr : r.2.2 = .remove x := by
      rcases har with h | h
      · obtain ⟨y, ha', _⟩ := (rc_iff a r).mp h
        rw [ha] at ha'; cases ha'
      · obtain ⟨y, hr, ha'⟩ := (rc_iff r a).mp h
        rw [ha] at ha'; injection ha' with hxy; subst y; exact hr
    have hbase : EqExcept x (step (step s a) e) (step (step s e) a) := by
      intro p hp; simp [step, he, ha, hp]
    have hfold := eqExcept_fold hbase ops
    change step _ r = step _ r
    ext p
    simp only [step, hr, Finset.mem_filter]
    by_cases hp : p.1 = x
    · simp [hp]
    · exact and_congr (hfold p hp) Iff.rfl

/-- Finite record actions for the independent ordinary-set model. -/
def finiteDescription : Automation.FiniteSetDescription (α × Timestamp) α
    (Op (Update α)) step (fun s e => abstractStep s e.op) where
  key := Prod.fst
  action e := match e.op with
    | .add x => .add (x, e.time) (fun _ => true)
    | .remove x => .remove x
  valid := by derive_finite_set_law [step, abstractStep]
  concrete := by derive_finite_set_law [step, abstractStep]
  abstract := by derive_finite_set_law [step, abstractStep]

def projectionDescription : MachineProjection (D α) (spec α) Op.op where
  project := view
  initial := by simp [D, spec, view]
  update := finiteDescription.project_update
  observes _ _ := rfl

def simulation : SequentialSimulation (D α) (spec α) := by
  derive_projected_simulation projectionDescription

theorem foldHistorySound : FoldHistorySound (D α) (spec α).toSpec :=
  simulation.sound

/-- Exact paper OR-set needs no operation payload or issuance side condition. -/
def issuance (α : Type) [DecidableEq α] : Issuance (D α) where
  CanIssue := fun _ _ => True

theorem certifiedRAV : CertifiedRAV (D α) (conflict α) (spec α).toSpec (issuance α) := by
  apply certifiedRA_of_join_total restrictedLaws _ foldHistorySound
  intro C _
  rw [conflict_lift_eq]
  exact join.at C.replayContext

theorem certifiedRA : CertifiedRA (D α) (conflict α) (spec α).toSpec (issuance α) :=
  certifiedRAV.ordinary

#print axioms restrictedLaws
#print axioms join
#print axioms certifiedRAV
#print axioms certifiedRA
end Sal.MRDTs.Paper1.ORSet
