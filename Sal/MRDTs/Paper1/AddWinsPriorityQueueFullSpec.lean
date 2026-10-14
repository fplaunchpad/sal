import Sal.MRDTs.Paper1.AddWinsPriorityQueueSpec
import Sal.MRDTs.Instances.AddWinsPriorityQueueFull

/-! The complete independent finite priority-map machine. Its support tracks
live elements, while each cell retains one best innate candidate and immutable
increment identifiers. All four query forms observe this finite machine. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full
open Foundation Instances.AddWinsPriorityQueue

abbrev SeqState := Finset Nat × AbstractState Nat

def elementStep (support : Finset Nat) (e : Op (Update Nat)) : Finset Nat :=
  match e.op with
  | .add x _ => insert x support
  | .inc _ _ => support
  | .remove x => support.erase x

def seqStep (s : SeqState) (e : Op (Update Nat)) : SeqState :=
  (elementStep s.1 e,abstractStep s.2 e)

def seqRead (s : SeqState) : FullQuery → Answer
  | .empty => .boolean (decide (s.1 = ∅))
  | .lookup x => .boolean (decide (x ∈ s.1))
  | .getPri x => .priority (abstractQuery s.2 x)
  | .getMax => .maximum (selectMax s.1 (abstractQuery s.2))

def model : DeterministicSpec (Op (Update Nat)) FullQuery Answer where
  State := SeqState
  initial := (∅,fun _ => (⊥,∅))
  update := seqStep
  query := seqRead

def spec := model.toSpec

def project (s : State Nat) : SeqState := (elements s,AddWinsPriorityQueue.project s)

theorem elements_step (s : State Nat) (e : Op (Update Nat)) :
    elements (step s e) = elementStep (elements s) e := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v => simp [elements,step,elementStep,Op.op]
  | inc x n => rfl
  | remove x =>
    ext y
    simp only [elements,step,elementStep,Op.op,Finset.mem_image,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨p,⟨hp,ne⟩,rfl⟩
      exact ⟨ne,p,hp,rfl⟩
    · rintro ⟨ne,p,hp,py⟩
      exact ⟨p,⟨hp,py ▸ ne⟩,py⟩

def projection : MachineProjection FullD model id where
  project := project
  initial := by apply Prod.ext; rfl; exact AddWinsPriorityQueue.projection.initial
  update := by
    intro s e
    exact Prod.ext (elements_step s e) (project_step s e)
  observes := by
    intro s q
    have point : query s = abstractQuery (AddWinsPriorityQueue.project s) := by
      funext x
      exact AddWinsPriorityQueue.projection.observes s x
    cases q <;> simp [FullD,Automation.QueryLift.withQuery,Instances.AddWinsPriorityQueue.read,model,project,seqRead,getMax,point]

def simulation : EventSequentialSimulation FullD model := by
  derive_projected_simulation projection

theorem historySound : EventFoldHistorySound FullD spec := simulation.sound

theorem elementStep_commutes (a b : Op (Update Nat))
    (commute : (D Nat).toUpdateSig.commutes a b) (support : Finset Nat) :
    elementStep (elementStep support a) b = elementStep (elementStep support b) a := by
  have hh : ¬ ((∃ x v, a.op = .remove x ∧ b.op = .add x v) ∨
      (∃ x v, b.op = .remove x ∧ a.op = .add x v)) := by
    intro conflict
    apply (noncomm_iff_replayOrder a b).mpr _ commute
    simpa only [replayOrder_iff,Op.op] using conflict
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;> ext x <;> simp [elementStep,Op.op] at hh ⊢ <;> grind

theorem compatible : CommutationCompatibility FullD id spec := by
  intro a b commute
  apply model.language_commutes
  intro s
  exact Prod.ext (elementStep_commutes a b commute s.1) (abstract_commutes a b commute s.2)

/-- Specification-level derived extraction: return the currently selected
pair, then remove its identity. There is no replay-time maximum update. -/
def seqRmvMax (s : SeqState) (timestamp replica : Nat) : Option ((Nat × Int) × SeqState) :=
  (selectMax s.1 (abstractQuery s.2)).map
    (fun selected => (selected,seqStep s (timestamp,replica,.remove selected.1)))

/-- The selected pair and complete local resulting abstract state agree. -/
theorem rmvMax_refines (s : State Nat) (timestamp replica : Nat) :
    (rmvMax s timestamp replica).map (fun result => (result.1,project result.2)) =
      seqRmvMax (project s) timestamp replica := by
  have point : query s = abstractQuery (AddWinsPriorityQueue.project s) := by
    funext x; exact AddWinsPriorityQueue.projection.observes s x
  unfold rmvMax prepareRmvMax seqRmvMax getMax
  simp only [Option.map_map,project,point]
  congr 1
  funext selected
  simp only [Function.comp_def,Prod.mk.injEq,true_and]
  exact Prod.ext (elements_step s _) (project_step s _)

/-- After preparation, local removal extinguishes the selected identity and
retains acquired increments. Concurrent replicas may still select the same
identity; this theorem asserts no atomic global extraction guarantee. -/
theorem prepared_remove_effect (s : State Nat) (t r x : Nat) (p : Int)
    (selected : getMax s = some (x,p)) :
    prepareRmvMax s t r = some ((t,r,.remove x),(x,p)) ∧
    query (step s (t,r,.remove x)) x = none ∧
    acquired (step s (t,r,.remove x)) x = acquired s x := by
  refine ⟨by simp [prepareRmvMax,selected],?_,rfl⟩
  rw [query,winner_remove,if_pos rfl]
  rfl

#print axioms historySound
#print axioms compatible
#print axioms rmvMax_refines
end Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full
