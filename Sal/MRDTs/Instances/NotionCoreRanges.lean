import Sal.MRDTs.Instances.NotionCoreSourceInvariant
import Sal.MRDTs.Instances.NotionCoreParentErase

/-! Typed bridge for pinned ids.js compressIdsToRanges/expandIdRanges.
Range(first,length) represents the JS two-element array [firstId,length].
Compression's accumulator is stored in reverse order, but emitted ranges have
source order. Input IDs represent counter/UTF16 session values, not decoded JS.
Nat counters model exact arithmetic. Positive safe counters, nonempty sessions,
bounded UTF16 units, and JS wire/range validation remain external boundaries. -/
namespace Sal.MRDTs.Instances.NotionCoreRanges
open NotionRunAllocation (Id)
local instance (a b : List Nat) : Decidable (a < b) := List.decidableLT a b

structure Range where
  first : Id
  length : Nat
  deriving DecidableEq, Repr

def nextId (first : Id) (offset : Nat) : Id :=
  ⟨first.counter + offset, first.session⟩
def expandRange (range : Range) : List Id :=
  (List.range range.length).map (nextId range.first)
def expand (ranges : List Range) : List Id := ranges.flatMap expandRange

def Asc (a b : Id) : Prop := NotionCoreSourceInvariant.Desc b a
instance : DecidableRel Asc := fun _ _ => inferInstanceAs (Decidable (NotionCoreSourceInvariant.Desc _ _))
def sorted (ids : List Id) : List Id := ids.mergeSort (fun a b => decide (Asc a b))

/-- The source examines only the most recent range. Reverse storage makes this
explicit without changing either the condition or emitted order. -/
def push (reversed : List Range) (id : Id) : List Range :=
  match reversed with
  | [] => [⟨id,1⟩]
  | previous::rest =>
    if previous.first.session = id.session ∧ previous.first.counter + previous.length = id.counter then
      {previous with length := previous.length + 1} :: rest
    else ⟨id,1⟩ :: previous :: rest

def accumulate : List Range → List Id → List Range
  | acc, [] => acc
  | acc, id::rest => accumulate (push acc id) rest

def compress (ids : List Id) : List Range := (accumulate [] (sorted ids)).reverse

theorem expandRange_extend (range : Range) :
    expandRange {range with length := range.length+1} =
      expandRange range ++ [nextId range.first range.length] := by
  simp [expandRange, List.range_succ, List.map_append]

theorem push_expands (acc : List Range) (id : Id) :
    expand (push acc id).reverse = expand acc.reverse ++ [id] := by
  cases acc with
  | nil => simp [push, expand, expandRange, nextId]
  | cons previous rest =>
    by_cases adjacent : previous.first.session = id.session ∧
        previous.first.counter + previous.length = id.counter
    · have next : nextId previous.first previous.length = id := by
        cases id
        simp_all [nextId]
      simp [push, adjacent, List.reverse_cons, expand, List.flatMap_append,
        expandRange_extend, next, List.append_assoc]
    · simp [push, adjacent, List.reverse_cons, expand, List.flatMap_append,
        expandRange, nextId, List.append_assoc]

theorem accumulate_expands (ids : List Id) (acc : List Range) :
    expand (accumulate acc ids).reverse = expand acc.reverse ++ ids := by
  induction ids generalizing acc with
  | nil => simp [accumulate]
  | cons id rest ih =>
    rw [accumulate, ih, push_expands]
    simp [List.append_assoc]

/-- Exact sequence equality, including duplicate inputs and nonconsecutive IDs.
No set/permutation relaxation is hidden in the codec theorem. -/
theorem expand_compress (ids : List Id) : expand (compress ids) = sorted ids := by
  simpa [compress, expand] using accumulate_expands (sorted ids) []

/-- Delete side effects depend on membership, so visible traversal order can
be transported through the source's sorting/compression without changing flags. -/
theorem erase_permutation (a b : List Id) (permutation : a.Perm b)
    (rows : NotionCoreParentMap.Table) :
    NotionCoreParentErase.erase a rows = NotionCoreParentErase.erase b rows := by
  unfold NotionCoreParentErase.erase
  apply List.map_congr_left
  intro row _
  unfold NotionCoreParentErase.eraseRow NotionCoreParentErase.eraseItem
  have membership (id : Id) : (id ∈ a) = (id ∈ b) := propext permutation.mem_iff
  cases row.item.kind <;> simp [membership]

theorem pending_permutation (pending a b : List Id) (permutation : a.Perm b) (id : Id) :
    id ∈ pending ++ a ↔ id ∈ pending ++ b := by
  simp only [List.mem_append]
  exact or_congr Iff.rfl permutation.mem_iff

theorem sorted_perm (ids : List Id) : (sorted ids).Perm ids :=
  List.mergeSort_perm ids _

theorem erase_codec (ids : List Id) (rows : NotionCoreParentMap.Table) :
    NotionCoreParentErase.erase (expand (compress ids)) rows =
      NotionCoreParentErase.erase ids rows := by
  rw [expand_compress]
  exact erase_permutation _ _ (sorted_perm ids) rows

theorem pending_codec (pending ids : List Id) (id : Id) :
    id ∈ pending ++ expand (compress ids) ↔ id ∈ pending ++ ids := by
  rw [expand_compress]
  exact pending_permutation pending _ _ (sorted_perm ids) id

private def i (counter : Nat) (session : Nat := 65) : Id := ⟨counter,[session]⟩

/-- Reverse physical traversal is sorted; gaps remain distinct ranges. -/
theorem physical_reverse_control :
    compress [i 5,i 2,i 1] = [⟨i 1,2⟩,⟨i 5,1⟩] ∧
    expand (compress [i 5,i 2,i 1]) ≠ [i 5,i 2,i 1] := by
  simp [compress, sorted, List.mergeSort, Asc,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before, i,
    accumulate, push, expand, expandRange, nextId]
  all_goals decide +kernel

theorem distinct_session_control :
    compress [i 2 66,i 1 65,i 1 66] = [⟨i 1 65,1⟩,⟨i 1 66,2⟩] ∧
    compress [i 2 66,i 1 65,i 1 66] ≠ [⟨i 1 65,3⟩] := by
  have order : ([65] : List Nat) < [66] := by decide +kernel
  simp [compress, sorted, List.mergeSort, Asc,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before, i, order,
    accumulate, push]

theorem duplicate_control :
    compress [i 1,i 1] = [⟨i 1,1⟩,⟨i 1,1⟩] ∧
    expand (compress [i 1,i 1]) ≠ [i 1] := by
  simp [compress, sorted, List.mergeSort, Asc,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before, i,
    accumulate, push, expand, expandRange, nextId]

#print axioms expand_compress
#print axioms erase_permutation
#print axioms physical_reverse_control
#print axioms distinct_session_control
#print axioms duplicate_control
end Sal.MRDTs.Instances.NotionCoreRanges
