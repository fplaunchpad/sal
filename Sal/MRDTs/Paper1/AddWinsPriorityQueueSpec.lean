import Sal.MRDTs.Instances.AddWinsPriorityQueue
import Sal.MRDTs.Paper1.ProjectedSimulation
import Sal.MRDTs.Paper1.EventBridge

/-! Independent sequential priority cells: only the greatest live Add is kept
per element, together with a set of increment identifiers and signed amounts.
The identifiers make duplicate delivery idempotent on arbitrary input histories;
on honest executions every increment has a fresh globally unique timestamp.
There are no ancestors, merge operations, or sets of live Add records here. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue
open Foundation Instances.AddWinsPriorityQueue
variable {α : Type} [DecidableEq α]

abbrev Cell := WithBot (Lex (Timestamp × Nat)) × Finset (Timestamp × Int)
abbrev AbstractState (α : Type) := α → Cell

def abstractStep (s : AbstractState α) (e : Op (Update α)) : AbstractState α :=
  fun x => match e.op with
    | .add y v => if x = y then (max ((↑(toLex (e.time,v) : Lex (Timestamp × Nat)) : WithBot (Lex (Timestamp × Nat)))) (s x).1,(s x).2) else s x
    | .inc y n => if x = y then ((s x).1,insert (e.time,n) (s x).2) else s x
    | .remove y => if x = y then (⊥,(s x).2) else s x

def abstractQuery (s : AbstractState α) (x : α) : Option Int :=
  Option.map (fun p => ((ofLex p).2 : Int) + ∑ q ∈ (s x).2, q.2) (s x).1

def model (α : Type) [DecidableEq α] : DeterministicSpec (Op (Update α)) α (Option Int) where
  State := AbstractState α
  initial := fun _ => (⊥,∅)
  update := abstractStep
  query := abstractQuery

def spec (α : Type) [DecidableEq α] := (model α).toSpec

def incsAt (s : State α) (x : α) : Finset (Timestamp × Int) :=
  (s.2.filter (fun p => p.1 = x)).image Prod.snd

def project (s : State α) : AbstractState α := fun x => (winner s x,incsAt s x)

theorem acquired_project (s : State α) (x : α) :
    acquired s x = ∑ q ∈ incsAt s x, q.2 := by
  unfold acquired incsAt
  rw [Finset.sum_image]
  intro p hp q hq equal
  have px := (Finset.mem_filter.mp hp).2
  have qx := (Finset.mem_filter.mp hq).2
  exact Prod.ext (px.trans qx.symm) equal

theorem winner_add (s : State α) (t r : Nat) (y : α) (v : Nat) (x : α) :
    winner (step s (t,r,.add y v)) x =
      if x = y then max ((↑(toLex (t,v) : Lex (Timestamp × Nat)) : WithBot (Lex (Timestamp × Nat)))) (winner s x) else winner s x := by
  by_cases same : x = y
  · subst y
    simp [winner,step,Finset.filter_insert,Finset.max_insert]
  · have other : y ≠ x := Ne.symm same
    simp [winner,step,Finset.filter_insert,same,other]

theorem winner_remove (s : State α) (t r : Nat) (y x : α) :
    winner (step s (t,r,.remove y)) x = if x = y then ⊥ else winner s x := by
  by_cases same : x = y
  · subst y
    simp [winner,step,Finset.filter_filter]
  · have filters : (s.1.filter (fun p => p.1 ≠ y)).filter (fun p => p.1 = x) =
        s.1.filter (fun p => p.1 = x) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,fun eq => same (h.2.symm.trans eq)⟩,h.2⟩
    simp [winner,step,same,filters]

theorem project_step (s : State α) (e : Op (Update α)) :
    project (step s e) = abstractStep (project s) e := by
  funext x
  rcases e with ⟨t,r,op⟩
  cases op with
  | add y v =>
    simp only [project,abstractStep,Op.op,Op.time,winner_add]
    by_cases h : x = y <;> simp [h,incsAt,step]
  | remove y =>
    simp only [project,abstractStep,Op.op,winner_remove]
    by_cases h : x = y <;> simp [h,incsAt,step]
  | inc y n =>
    by_cases h : x = y
    · subst y
      simp [project,abstractStep,Op.op,Op.time,incsAt,step,winner,Finset.filter_insert]
    · simp [project,abstractStep,Op.op,incsAt,step,winner,Finset.filter_insert,h,Ne.symm h]

def projection : MachineProjection (D α) (model α) id where
  project := project
  initial := by funext x; simp [project,winner,incsAt,D,model]
  update := project_step
  observes := by intro s x; simp [D,model,project,query,abstractQuery,acquired_project]

def simulation : EventSequentialSimulation (D α) (model α) := by
  derive_projected_simulation projection

theorem historySound : EventFoldHistorySound (D α) (spec α) := simulation.sound

set_option maxHeartbeats 2000000 in
theorem abstract_commutes (a b : Op (Update α))
    (commute : (D α).toUpdateSig.commutes a b) (s : AbstractState α) :
    abstractStep (abstractStep s a) b = abstractStep (abstractStep s b) a := by
  have hh : ¬ ((∃ x v, a.2.2 = .remove x ∧ b.2.2 = .add x v) ∨
      (∃ x v, b.2.2 = .remove x ∧ a.2.2 = .add x v)) := by
    intro hc
    apply (noncomm_iff_replayOrder a b).mpr _ commute
    simpa only [replayOrder_iff] using hc
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  change abstractStep (abstractStep s (ta,ra,oa)) (tb,rb,ob) =
    abstractStep (abstractStep s (tb,rb,ob)) (ta,ra,oa)
  cases oa <;> cases ob <;> funext x <;>
    simp only [abstractStep,Op.op,Op.time] <;>
    (repeat' split <;> simp_all [max_left_comm,Finset.insert_comm])
  all_goals grind

theorem compatible : CommutationCompatibility (D α) id (spec α) := by
  intro a b commute
  exact (model α).language_commutes a b (abstract_commutes a b commute)

#print axioms historySound
#print axioms compatible
end Sal.MRDTs.Paper1.AddWinsPriorityQueue
