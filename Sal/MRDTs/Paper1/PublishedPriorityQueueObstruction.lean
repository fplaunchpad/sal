import Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue
import Sal.MRDTs.Paper1.HistorySpec
import Sal.MRDTs.Paper1.SpecificationVisibility
import Mathlib.Data.List.Permutation

/-! The published MCW query is not explained by ordinary resetting Add and
additive Inc, even after relaxing Add's serialized absent-element guard.
The strict independent machine retains all three source preparation guards.
The witness avoids both MCW ties and unknown-innate early-delivery states. -/
namespace Sal.MRDTs.Paper1.PublishedPriorityQueueObstruction
open Foundation Instances.PublishedAddWinsPriorityQueue

abbrev OrdinaryState := Nat → Option Int

def ordinaryStep (s : OrdinaryState) (e : Event) : OrdinaryState :=
  fun x => match requestOf e.op with
    | .add y v => if x = y then some v else s x
    | .inc y n => if x = y then (s x).map (fun v => v + n) else s x
    | .remove y => if x = y then none else s x

def ordinaryLegal (s : OrdinaryState) (e : Event) : Prop :=
  match requestOf e.op with
    | .add x _ => s x = none
    | .inc x _ => s x ≠ none
    | .remove x => s x ≠ none

instance ordinaryLegalDecidable (s : OrdinaryState) (e : Event) :
    Decidable (ordinaryLegal s e) := by
  unfold ordinaryLegal
  cases h : requestOf e.op <;> infer_instance

def relaxed : DeterministicSpec Event Nat (Option Int) where
  State := OrdinaryState
  initial := fun _ => none
  update := ordinaryStep
  query s x := s x

/-- Exact ordinary guards; get_pri requires a present element and returns its
integer value. Birth IDs, increment snapshots, MCW and merge do not occur here. -/
def ordinaryMachine : HistoryMachine Event Nat (Option Int) where
  State := OrdinaryState
  initial := fun _ => none
  transition s label t := match label with
    | .update e => ordinaryLegal s e ∧ t = ordinaryStep s e
    | .query x answer => t = s ∧ s x ≠ none ∧ answer = s x

def ordinary := ordinaryMachine.toSpec

private theorem ordinary_runs_relaxed {s t : OrdinaryState}
    {labels : List (SeqLabel Event Nat (Option Int))}
    (run : Runs ordinaryMachine.transition s labels t) :
    Runs relaxed.machine.transition s labels t := by
  induction run with
  | nil => exact .nil _
  | @cons s m t label labels step rest ih =>
    apply Runs.cons _ ih
    cases label with
    | update e => exact step.2
    | query x answer => exact ⟨step.1,step.2.2⟩

theorem ordinary_admission_relaxed (labels : List (SeqLabel Event Nat (Option Int)))
    (accepted : ordinary.admits labels) : relaxed.toSpec.admits labels := by
  obtain ⟨final,run⟩ := accepted
  exact ⟨final,ordinary_runs_relaxed run⟩

def addA : Event := (1,0,.add 7 0)
def addB : Event := (2,1,.add 7 10)
def incA : Event := (3,0,.inc 7 2 {1})
def incB : Event := (4,1,.inc 7 1 {2})
def branchA : State := step (step {} addA) incA
def branchB : State := step (step {} addB) incB
def joined : State := merge {} branchA branchB

def events : List Event := [addA,incA,addB,incB]

/-- Precisely the two source causal Add→Inc edges. -/
def vis (a b : Event) : Prop := (a = addA ∧ b = incA) ∨ (a = addB ∧ b = incB)
instance visDecidable (a b : Event) : Decidable (vis a b) := by unfold vis; infer_instance

def causal (ops : List Event) := respects ops vis
instance causalDecidable (ops : List Event) : Decidable (causal ops) := by
  unfold causal respects; infer_instance

/-- Both Add preparations see absence; each Inc sees exactly its own Add. -/
theorem honest_preparation :
    prepare {} 1 0 (.add 7 0) = some addA ∧
    prepare {} 2 1 (.add 7 10) = some addB ∧
    prepare (step {} addA) 3 0 (.inc 7 2) = some incA ∧
    prepare (step {} addB) 4 1 (.inc 7 1) = some incB := by decide

theorem unique_timestamps : (events.map Op.time).Nodup := by decide

/-- Hand-derived source records: the latest innate and greatest-magnitude
acquired value come from different live insertion records. -/
theorem source_records_and_unique_winner :
    record joined (7,1) = ⟨(7,1),{0},2,2⟩ ∧
    record joined (7,2) = ⟨(7,2),{10},1,1⟩ ∧
    latestTags joined 7 = {(7,2)} ∧
    mostChangedTags joined 7 = {(7,1)} ∧
    priorities joined 7 = {12} ∧ priorities joined 7 ≠ {13} := by decide

/-- All 24 permutations are kernel-enumerated; every one preserving the two
causal edges has final ordinary priority in the hand-derived set below. -/
private theorem exhaustive_causal_outcomes :
    ∀ ops ∈ events.permutations', causal ops →
      (ops.foldl ordinaryStep (fun _ => none)) 7 ∈
        ({some 2,some 3,some 11,some 13} : Finset (Option Int)) := by decide

theorem relaxed_no_causal_serialization (ops : List Event) (perm : ops.Perm events)
    (ordered : causal ops) :
    (ops.foldl ordinaryStep (fun _ => none)) 7 ≠ some 12 := by
  have possible := exhaustive_causal_outcomes ops (List.mem_permutations'.mpr perm) ordered
  intro result
  rw [result] at possible
  exact (by decide : some (12 : Int) ∉ ({some 2,some 3,some 11,some 13} : Finset (Option Int))) possible

theorem relaxed_history_refuted (ops : List Event) (perm : ops.Perm events)
    (ordered : causal ops) :
    ¬ relaxed.toSpec.admits (DeterministicSpec.updateLabels ops ++ [.query 7 (some 12)]) := by
  rw [DeterministicSpec.updates_query_iff]
  exact fun result => relaxed_no_causal_serialization ops perm ordered result.symm

theorem ordinary_history_refuted (ops : List Event) (perm : ops.Perm events)
    (ordered : causal ops) :
    ¬ ordinary.admits (DeterministicSpec.updateLabels ops ++ [.query 7 (some 12)]) :=
  fun accepted => relaxed_history_refuted ops perm ordered (ordinary_admission_relaxed _ accepted)

/-- The exact ordinary machine requires these source guards at each prefix. -/
def legalSequence (s : OrdinaryState) : List Event → Prop
  | [] => True
  | e :: ops => ordinaryLegal s e ∧ legalSequence (ordinaryStep s e) ops

instance legalSequenceDecidable (s : OrdinaryState) (ops : List Event) :
    Decidable (legalSequence s ops) := by
  induction ops generalizing s with
  | nil => exact isTrue True.intro
  | cons e ops ih =>
    unfold legalSequence
    have hlegal : Decidable (ordinaryLegal s e) := by
      unfold ordinaryLegal
      cases h : requestOf e.op <;> infer_instance
    exact instDecidableAnd

private theorem legal_of_runs_updates (ops : List Event) (suffix : List (SeqLabel Event Nat (Option Int)))
    {s t : OrdinaryState}
    (run : Runs ordinaryMachine.transition s (DeterministicSpec.updateLabels ops ++ suffix) t) :
    legalSequence s ops := by
  induction ops generalizing s with
  | nil => exact True.intro
  | cons e ops ih =>
    cases run with
    | cons step rest =>
      change ordinaryLegal s e ∧ _ = ordinaryStep s e at step
      rcases step with ⟨guard,rfl⟩
      exact ⟨guard,ih rest⟩

private theorem exhaustive_strict_guard_failure :
    ∀ ops ∈ events.permutations', ¬ legalSequence (fun _ => none) ops := by decide

/-- With the exact Add-absent guard, no permutation is legal, regardless of
causal ordering or policy. This directly refutes the strict ordinary language. -/
theorem ordinary_no_serialization (ops : List Event) (perm : ops.Perm events) :
    ¬ ordinary.admits (DeterministicSpec.updateLabels ops ++ [.query 7 (some 12)]) := by
  rintro ⟨final,run⟩
  exact exhaustive_strict_guard_failure ops (List.mem_permutations'.mpr perm)
    (legal_of_runs_updates ops [.query 7 (some 12)] run)

/-- Minimal guard obstruction: two independently prepared successful Adds
cannot both occur in one ordinary Add-absent history without a removal. -/
theorem strict_two_adds_obstruction (ops : List Event) (perm : ops.Perm [addA,addB]) :
    ¬ ordinary.admits (DeterministicSpec.updateLabels ops ++ [.query 7 (some 10)]) := by
  have enumeration : ∀ xs ∈ [addA,addB].permutations',
      ¬ legalSequence (fun _ => none) xs := by decide
  rintro ⟨final,run⟩
  exact enumeration ops (List.mem_permutations'.mpr perm)
    (legal_of_runs_updates ops [.query 7 (some 10)] run)

/-- The relaxed ordinary language regards Add and Inc as conflicting, despite
commutation of their prepared metadata effects. Therefore source causal
Add→Inc edges belong to the specification-conflict visibility candidate. -/
theorem relaxed_add_inc_conflict : ¬ relaxed.toSpec.Commutes addB incB := by
  intro commutes
  have accepted : relaxed.toSpec.admits
      (DeterministicSpec.updateLabels [addA,addB,incB] ++ [.query 7 (some 11)]) := by
    rw [DeterministicSpec.updates_query_iff]
    rfl
  have swapped := (commutes [.update addA] [.query 7 (some 11)]).mp accepted
  change relaxed.toSpec.admits
    (DeterministicSpec.updateLabels [addA,incB,addB] ++ [.query 7 (some 11)]) at swapped
  rw [DeterministicSpec.updates_query_iff] at swapped
  have different : (some (11 : Int)) ≠ (some 10) := by decide
  exact different swapped

/-- The exact ordinary language is inhabited by a source-valid one-branch run. -/
theorem ordinary_positive_control :
    ordinary.admits (DeterministicSpec.updateLabels [addA,incA] ++ [.query 7 (some 2)]) ∧
    ¬ ordinary.admits (DeterministicSpec.updateLabels [addA,incA] ++ [.query 7 (some 3)]) := by
  constructor
  · refine ⟨ordinaryStep (ordinaryStep (fun _ => none) addA) incA,?_⟩
    exact .cons ⟨by decide,rfl⟩ (.cons ⟨by decide,rfl⟩
      (.cons ⟨rfl,by decide,rfl⟩ (.nil _)))
  · intro accepted
    have relaxedAccepted := ordinary_admission_relaxed _ accepted
    rw [DeterministicSpec.updates_query_iff] at relaxedAccepted
    exact (by decide : some (3 : Int) ≠ some 2) relaxedAccepted

/-- Positive controls: ordinary executions can finish at 2, 3, 11 and 13.
The obstruction is specifically 12, not universal history rejection. -/
theorem nearby_valid_relaxed_histories :
    ([addB,incB,addA,incA].foldl ordinaryStep (fun _ => none)) 7 = some 2 ∧
    ([addB,addA,incA,incB].foldl ordinaryStep (fun _ => none)) 7 = some 3 ∧
    ([addA,incA,addB,incB].foldl ordinaryStep (fun _ => none)) 7 = some 11 ∧
    ([addA,addB,incA,incB].foldl ordinaryStep (fun _ => none)) 7 = some 13 ∧
    ([addA,addB,incA,incB].foldl ordinaryStep (fun _ => none)) 7 ≠ some 12 := by decide

#print axioms honest_preparation
#print axioms source_records_and_unique_winner
#print axioms relaxed_no_causal_serialization
#print axioms ordinary_history_refuted
#print axioms ordinary_no_serialization
#print axioms strict_two_adds_obstruction
#print axioms relaxed_add_inc_conflict
#print axioms ordinary_positive_control
end Sal.MRDTs.Paper1.PublishedPriorityQueueObstruction
