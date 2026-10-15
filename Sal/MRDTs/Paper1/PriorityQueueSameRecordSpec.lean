import Sal.MRDTs.Instances.PriorityQueueSameRecord
import Sal.MRDTs.Paper1.SpecificationVisibility

/-! Ordinary finite priority map, independent of birth IDs and observed
snapshots. Add is total overwrite, Inc adds if present and is an absent no-op,
Remove clears and is an absent no-op. Preparation guards constrain issuance,
not every prefix of an explaining sequential history. No acquired/history/log
metadata occurs in this abstract state. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord

abbrev SeqState := Finset Nat × (Nat → Option Int)

def elementOf : Payload → Nat
  | .add x _ | .inc x _ _ | .remove x _ => x

def supportStep (support : Finset Nat) : Request → Finset Nat
  | .add x _ => insert x support
  | .inc _ _ => support
  | .remove x => support.erase x

def cellStep (cells : Nat → Option Int) (request : Request) : Nat → Option Int :=
  fun x => match request with
    | .add y value => if x = y then some value else cells x
    | .inc y amount => if x = y then (cells x).map (fun p => p + amount) else cells x
    | .remove y => if x = y then none else cells x

def seqStep (s : SeqState) (e : Event) : SeqState :=
  let request := Instances.PublishedAddWinsPriorityQueue.requestOf e.op
  (supportStep s.1 request,cellStep s.2 request)

def seqRead (s : SeqState) : Query → Answer
  | .empty => .boolean (decide (s.1 = ∅))
  | .lookup x => .boolean (decide (x ∈ s.1))
  | .getPri x => .priority (s.2 x)
  | .getMax => .maximum (Instances.AddWinsPriorityQueue.selectMax s.1 s.2)

def model : DeterministicSpec Event Query Answer where
  State := SeqState
  initial := (∅,fun _ => none)
  update := seqStep
  query := seqRead

def spec := model.toSpec

/-- The abstract extraction client also observes then removes one identity. -/
def seqRmvMax (s : SeqState) : Option ((Nat × Int) × SeqState) :=
  (Instances.AddWinsPriorityQueue.selectMax s.1 s.2).map (fun pair =>
    (pair,(s.1.erase pair.1,fun x => if x = pair.1 then none else s.2 x)))

/-- The current ordinary map observation; this is NOT an all-update simulation.
In particular, explaining a concurrent merge requires choosing an order. -/
def project (s : Instances.PriorityQueueSameRecord.State) : SeqState := (elements s,priority s)

theorem observe_project (s : Instances.PriorityQueueSameRecord.State) (q : Query) :
    read s q = seqRead (project s) q := by cases q <;> rfl

/-- The derived local client agrees with ordinary map extraction, including
its returned pair and every resulting priority cell. This does not assert a
single globally atomic extraction across replicas. -/
theorem rmvMax_refines (s : Instances.PriorityQueueSameRecord.State) (t r : Nat) :
    (rmvMax s t r).map (fun result => (result.1,project result.2)) = seqRmvMax (project s) := by
  unfold rmvMax prepareRmvMax seqRmvMax getMax
  simp only [project,Option.map_map]
  congr 1
  funext selected
  simp only [Function.comp_def,Prod.mk.injEq,true_and]
  constructor
  · exact elements_remove s t r selected.1
  · funext x
    exact priority_remove s t r selected.1 x

/-- Different elements commute in the full contextual history language,
including maximum and empty queries in arbitrary contexts. -/
theorem cross_key_commutes (a b : Event) (different : elementOf a.op ≠ elementOf b.op) :
    spec.Commutes a b := by
  apply model.language_commutes
  intro s
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  apply Prod.ext
  · cases oa <;> cases ob <;> ext x <;>
      simp [model,seqStep,supportStep,Instances.PublishedAddWinsPriorityQueue.requestOf,
        Op.op,elementOf] at different ⊢ <;> grind
  · funext x
    cases oa <;> cases ob <;>
      simp [model,seqStep,cellStep,Instances.PublishedAddWinsPriorityQueue.requestOf,
        Op.op,elementOf] at different ⊢ <;> grind

/-- A specification-conflicting visibility edge stays within one element.
Consequently per-element explaining orders can be concatenated. -/
theorem conflict_same_key (a b : Event) (conflict : ¬ spec.Commutes a b) :
    elementOf a.op = elementOf b.op := by
  by_contra different
  exact conflict (cross_key_commutes a b different)

/-- Guard differences are explicit: this independent sequential machine admits
Add/upsert on a present key, and Inc/Remove on an absent key. -/
theorem total_update_controls :
    (seqStep (seqStep model.initial (1,0,.add 7 10)) (2,0,.add 7 2)).2 7 = some 2 ∧
    (seqStep model.initial (1,0,.inc 7 5 ∅)).2 7 = none ∧
    (seqStep model.initial (1,0,.remove 7 ∅)).2 7 = none ∧
    (seqStep (seqStep model.initial (1,0,.add 7 10)) (2,0,.add 7 2)).2 7 ≠ some 10 := by
  decide

#print axioms cross_key_commutes
#print axioms rmvMax_refines
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
