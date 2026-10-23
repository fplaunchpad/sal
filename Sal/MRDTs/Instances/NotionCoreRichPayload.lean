import Sal.MRDTs.Instances.NotionCoreFormattingMachine
import Sal.MRDTs.Instances.NotionCoreFormattingPlanner

/-! Atomic rich transactions retain one global boolean verdict and reserve
one consecutive source ID per emitted formatting segment. Whole transactions
are the carrier elements; source rich-text arbitration still uses the segment
IDs, which need not place all segments consecutively against concurrent runs.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichPayload
open NotionRunAllocation (Id Run)
open NotionCoreFormattingSource (Anchor MarkOp)

structure Part where
  instanceId : Nat
  lower : Anchor
  upper : Anchor
  deriving DecidableEq, Repr

inductive Payload where
  | edit (payload : NotionCorePayload.Payload)
  | format (parts : List Part) (value : Bool)
  deriving DecidableEq, Repr

def Payload.width : Payload → Nat
  | .edit payload => payload.width
  | .format parts _ => max 1 parts.length

structure Transaction where
  id : Id
  payload : Payload
  deriving DecidableEq, Repr

def Transaction.reservation (transaction : Transaction) : Run :=
  ⟨transaction.id,transaction.payload.width⟩

def Part.operation (part : Part) (id : Id) (value : Bool) : Nat × MarkOp :=
  (part.instanceId,⟨id,part.lower,part.upper,value⟩)

def emit (first : Id) (value : Bool) : List Part → List (Nat × MarkOp)
  | [] => []
  | part :: rest => part.operation first value ::
      emit ⟨first.counter + 1,first.session⟩ value rest

def Transaction.annotations (transaction : Transaction) : List (Nat × MarkOp) :=
  match transaction.payload with
  | .edit _ => []
  | .format parts value => emit transaction.id value parts

def Transaction.request (transaction : Transaction) : NotionCoreFormattingMachine.Request :=
  match transaction.payload with
  | .edit payload => .edit ⟨transaction.id,payload⟩
  | .format parts value => .format (emit transaction.id value parts)

def partsOf (segments : List (Nat × NotionCoreFormattingPlanner.Segment)) : List Part :=
  segments.map fun (inst,segment) =>
    let operation := segment.operation ⟨0,[]⟩ false
    ⟨inst,operation.start,operation.finish⟩

theorem emit_planner (first : Id) (value : Bool)
    (segments : List (Nat × NotionCoreFormattingPlanner.Segment)) :
    emit first value (partsOf segments) =
      NotionCoreFormattingPlanner.emit first.session first.counter value segments := by
  induction segments generalizing first with
  | nil => rfl
  | cons segment rest ih =>
      rcases segment with ⟨inst,segment⟩
      change _ :: emit _ value (partsOf rest) = _ ::
        NotionCoreFormattingPlanner.emit first.session (first.counter + 1) value rest
      rw [ih]
      rfl

theorem emit_ids (first : Id) (value : Bool) (parts : List Part) :
    (emit first value parts).map (fun located => located.2.id) =
      (List.range parts.length).map (NotionCorePayload.offsetId first) := by
  induction parts generalizing first with
  | nil => rfl
  | cons part rest ih =>
      simp only [emit,List.map_cons,List.length_cons,List.range_succ_eq_map,ih,List.map_map]
      congr 1
      apply List.map_congr_left
      intro index member
      simp [NotionCorePayload.offsetId,Nat.add_comm,Nat.add_left_comm]

theorem emit_uniform (first : Id) (value : Bool) (parts : List Part)
    (located : Nat × MarkOp) (member : located ∈ emit first value parts) :
    located.2.value = value := by
  induction parts generalizing first with
  | nil => simp [emit] at member
  | cons part rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst located; rfl
      · exact ih _ later

theorem annotation_reserved (transaction : Transaction) (located : Nat × MarkOp)
    (member : located ∈ transaction.annotations) :
    transaction.reservation.Contains located.2.id := by
  cases transaction with
  | mk first payload =>
    cases payload with
    | edit payload => simp [Transaction.annotations] at member
    | format parts value =>
      have name : located.2.id ∈ (emit first value parts).map (fun op => op.2.id) :=
        List.mem_map.mpr ⟨located,member,rfl⟩
      rw [emit_ids] at name
      obtain ⟨index,bound,equal⟩ := List.mem_map.mp name
      exact ⟨index,Nat.lt_of_lt_of_le (List.mem_range.mp bound) (Nat.le_max_right _ _),equal.symm⟩

theorem annotations_unique (transaction : Transaction) :
    (transaction.annotations.map (fun located => located.2.id)).Nodup := by
  cases transaction with
  | mk first payload =>
    cases payload with
    | edit payload => simp [Transaction.annotations]
    | format parts value =>
      change ((emit first value parts).map _).Nodup
      rw [emit_ids]
      apply List.Nodup.map _ List.nodup_range
      intro left right same
      have counters := congrArg Id.counter same
      simpa [NotionCorePayload.offsetId] using counters

def Ascending (left right : Transaction) : Prop :=
  NotionRunAllocation.Before left.id right.id ∨ left.id = right.id
instance (left right : Transaction) : Decidable (Ascending left right) :=
  inferInstanceAs (Decidable (NotionRunAllocation.Before left.id right.id ∨ left.id = right.id))

instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy a.id b.id with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same)
    · exact Or.inr (Or.inl reverse)

instance : IsTrans Transaction Ascending where
  trans a b c ab bc := by
    rcases ab with ab | ab <;> rcases bc with bc | bc
    · exact Or.inl (NotionCoreSourceInvariant.before_trans ab bc)
    · exact Or.inl (bc ▸ ab)
    · exact Or.inl (ab ▸ bc)
    · exact Or.inr (ab.trans bc)

def sort (transactions : List Transaction) : List Transaction := transactions.insertionSort Ascending

theorem sort_perm (transactions : List Transaction) : (sort transactions).Perm transactions :=
  List.perm_insertionSort _ _

theorem sort_ordered (transactions : List Transaction)
    (unique : (transactions.map Transaction.id).Nodup) :
    (sort transactions).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) := by
  have sorted : (sort transactions).Pairwise Ascending := List.pairwise_insertionSort _ _
  have ids : ((sort transactions).map Transaction.id).Nodup :=
    ((sort_perm transactions).map Transaction.id).nodup_iff.mpr unique
  apply (sorted.and (List.pairwise_map.mp ids)).imp
  intro a b both
  rcases both.1 with before | equal
  · exact before
  · exact False.elim (both.2 equal)

def reconstruct (transactions : List Transaction) : Option NotionCoreFormattingMachine.State :=
  NotionCoreFormattingMachine.replay {} ((sort transactions).map Transaction.request)

def observe (transactions : List Transaction) :=
  reconstruct transactions >>= NotionCoreFormattingMachine.render

#print axioms annotation_reserved
end Sal.MRDTs.Instances.NotionCoreRichPayload
