import Sal.MRDTs.Paper1.PriorityQueueSameRecordProvenance

/-! Identified increment attachments agree with ordinary addition over a finite
list of distinct event timestamps. This aggregation theorem does not assert
that arbitrary replay orders respect the intended sequential specification. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord
open scoped BigOperators

def incrementAmountFor (tag : Instances.PublishedAddWinsPriorityQueue.Tag) (e : Event) : Int :=
  match e.op with
  | .inc x n observed => if tag.1 = x ∧ tag.2 ∈ observed then n else 0
  | _ => 0

private def weight (tag : Instances.PublishedAddWinsPriorityQueue.Tag)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment) : Int := if a.1 = tag then a.2.2 else 0

private theorem acquired_weight (s : State) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    Instances.PublishedAddWinsPriorityQueue.acquired s tag = ∑ a ∈ s.increments, weight tag a := by
  simp only [Instances.PublishedAddWinsPriorityQueue.acquired,Finset.sum_filter,weight]

private theorem effect_weight (e : Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    (∑ a ∈ (step {} e).increments, weight tag a) = incrementAmountFor tag e := by
  rcases tag with ⟨key,timestamp⟩
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v => simp [step,Instances.PublishedAddWinsPriorityQueue.step,incrementAmountFor,Op.op]
  | remove x observed => simp [step,Instances.PublishedAddWinsPriorityQueue.step,incrementAmountFor,Op.op]
  | inc x n observed =>
    simp only [step,Instances.PublishedAddWinsPriorityQueue.step,Finset.empty_union]
    rw [Finset.sum_image]
    · by_cases equal : x = key
      · subst x
        simp [weight,incrementAmountFor,Op.op,Prod.mk.injEq]
      · have other : key ≠ x := Ne.symm equal
        simp [weight,incrementAmountFor,Op.op,Prod.mk.injEq,equal,other]
    · intro a _ b _ equal
      exact congrArg (fun p : Instances.PublishedAddWinsPriorityQueue.Attachment => p.1.2) equal

private theorem increment_effect_time (e : Event)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment) (member : a ∈ (step {} e).increments) :
    a.2.1 = e.time := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v => exact False.elim (Finset.notMem_empty _ member)
  | remove x observed => exact False.elim (Finset.notMem_empty _ member)
  | inc x n observed =>
    have generated : a ∈ observed.image (fun tag => ((x,tag),t,n)) := by
      simpa [step,Instances.PublishedAddWinsPriorityQueue.step] using member
    obtain ⟨tag,_,equal⟩ := Finset.mem_image.mp generated
    exact congrArg (fun p : Instances.PublishedAddWinsPriorityQueue.Attachment => p.2.1) equal.symm

private theorem increments_step (s : State) (e : Event) :
    (step s e).increments = s.increments ∪ (step {} e).increments := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step]

theorem acquired_step_fresh (s : State) (e : Event)
    (fresh : ∀ a ∈ s.increments, a.2.1 ≠ e.time)
    (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    Instances.PublishedAddWinsPriorityQueue.acquired (step s e) tag =
      Instances.PublishedAddWinsPriorityQueue.acquired s tag + incrementAmountFor tag e := by
  rw [acquired_weight,increments_step,Finset.sum_union,← acquired_weight,effect_weight]
  exact Finset.disjoint_left.mpr (fun a old newborn => fresh a old (increment_effect_time e a newborn))

/-- Distinct IDs deduplicate delivery without discarding distinct signed
increments. The result uses ordinary integer addition, not MCW magnitudes. -/
theorem acquired_fold_fresh (s : State) (events : List Event)
    (distinct : events.Pairwise (fun a b => a.time ≠ b.time))
    (fresh : ∀ e ∈ events, ∀ a ∈ s.increments, a.2.1 ≠ e.time)
    (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    Instances.PublishedAddWinsPriorityQueue.acquired (applySeq D.toUpdateSig s events) tag =
      Instances.PublishedAddWinsPriorityQueue.acquired s tag + (events.map (incrementAmountFor tag)).sum := by
  induction events generalizing s with
  | nil => simp [applySeq]
  | cons e events ih =>
    obtain ⟨headFresh,restDistinct⟩ := List.pairwise_cons.mp distinct
    have laterFresh : ∀ next ∈ events, ∀ a ∈ (step s e).increments, a.2.1 ≠ next.time := by
      intro next hn a ha
      rw [increments_step] at ha
      rcases Finset.mem_union.mp ha with old | newborn
      · exact fresh next (List.mem_cons_of_mem _ hn) a old
      · rw [increment_effect_time e a newborn]
        exact headFresh next hn
    change Instances.PublishedAddWinsPriorityQueue.acquired
      (applySeq D.toUpdateSig (step s e) events) tag = _
    rw [ih _ restDistinct laterFresh,acquired_step_fresh s e (fresh e List.mem_cons_self)]
    simp only [List.map_cons,List.sum_cons]
    exact add_assoc _ _ _

theorem acquired_fold (events : List Event)
    (distinct : events.Pairwise (fun a b => a.time ≠ b.time))
    (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    Instances.PublishedAddWinsPriorityQueue.acquired (applySeq D.toUpdateSig D.init events) tag =
      (events.map (incrementAmountFor tag)).sum := by
  have empty : ∀ e ∈ events, ∀ a ∈ (D.init).increments, a.2.1 ≠ e.time := by
    intro e he a ha
    exact False.elim (Finset.notMem_empty _ ha)
  simpa [D,Instances.PublishedAddWinsPriorityQueue.acquired] using acquired_fold_fresh D.init events distinct empty tag

#print axioms acquired_fold
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
