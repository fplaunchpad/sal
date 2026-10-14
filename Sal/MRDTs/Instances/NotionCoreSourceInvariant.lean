import Sal.MRDTs.Instances.NotionRunAllocation
import Sal.MRDTs.Instances.NotionCoreRGA
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex

/-! Allocation provenance to descending source sibling sorting.
The source comparator is counter-first, then UTF-16 session lexicographic.
These theorems close a local RGA ordering obligation. They do not extract
source endpoint trees or derive complete source-document issuance guards.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceInvariant
open NotionRunAllocation

local instance (a b : Session) : Decidable (a < b) := List.decidableLT a b

instance (a b : Id) : Decidable (Before a b) := by
  unfold Before
  infer_instance

theorem before_irrefl (a : Id) : ¬ Before a a := by simp [Before]

theorem before_trans {a b c : Id} (ab : Before a b) (bc : Before b c) :
    Before a c := by
  rcases ab with ab | ⟨ab, abs⟩ <;> rcases bc with bc | ⟨bc, bcs⟩
  · exact Or.inl (Nat.lt_trans ab bc)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨ab.trans bc, lt_trans abs bcs⟩

theorem before_asymm {a b : Id} (ab : Before a b) : ¬ Before b a := by
  intro ba
  exact before_irrefl a (before_trans ab ba)

theorem before_trichotomy (a b : Id) : Before a b ∨ a = b ∨ Before b a := by
  rcases lt_trichotomy a.counter b.counter with lt | eq | gt
  · exact Or.inl (Or.inl lt)
  · rcases lt_trichotomy a.session b.session with lt | same | gt
    · exact Or.inl (Or.inr ⟨eq, lt⟩)
    · right; left; cases a; cases b; simp_all
    · exact Or.inr (Or.inr (Or.inr ⟨eq.symm, gt⟩))
  · exact Or.inr (Or.inr (Or.inl gt))

/-- Literal comparison branches of source `compareOpIds`. Sessions use the
allocation model's UTF-16 code-unit lists. -/
def compareIds (a b : Id) : Ordering :=
  if a.counter ≠ b.counter then
    if a.counter < b.counter then .lt else .gt
  else if a.session = b.session then .eq
  else if a.session < b.session then .lt else .gt

theorem compare_lt_iff (a b : Id) : compareIds a b = .lt ↔ Before a b := by
  unfold compareIds Before
  split_ifs <;> simp_all

/-- Non-strict descending sibling relation. The reversed source comparator
puts a before b exactly when a is greater than or equal to b. -/
def Desc (a b : Id) : Prop := Before b a ∨ a = b
instance (a b : Id) : Decidable (Desc a b) := inferInstanceAs (Decidable (Before b a ∨ a = b))

theorem desc_iff_not_before (a b : Id) : Desc a b ↔ ¬ Before a b := by
  constructor
  · rintro (reverse | rfl)
    · exact before_asymm reverse
    · exact before_irrefl a
  · intro no
    rcases before_trichotomy a b with before | same | reverse
    · exact False.elim (no before)
    · exact Or.inr same
    · exact Or.inl reverse

theorem descending_comparator (a b : Id) :
    decide (Desc a b) = (compareIds a b != .lt) := by
  have equivalence : Desc a b ↔ compareIds a b ≠ .lt :=
    (desc_iff_not_before a b).trans (not_congr (compare_lt_iff a b).symm)
  cases compared : compareIds a b <;> simp_all

instance : Std.Total Desc where
  total a b := by
    rcases before_trichotomy a b with before | same | reverse
    · exact Or.inr (Or.inl before)
    · exact Or.inl (Or.inr same)
    · exact Or.inl (Or.inl reverse)

instance : IsTrans Id Desc where
  trans a b c ab bc := by
    rcases ab with reverse | rfl <;> rcases bc with reverse' | rfl
    · exact Or.inl (before_trans reverse' reverse)
    · exact Or.inl reverse
    · exact Or.inl reverse'
    · exact Or.inr rfl

instance : Std.Antisymm Desc where
  antisymm a b ab ba := by
    rcases ab with reverse | same
    · rcases ba with before | same
      · exact False.elim (before_asymm before reverse)
      · exact same.symm
    · exact same

/-- Sort every origin's child IDs with the source's descending comparator.
The sorting algorithm is a library merge sort; only its permutation/order
contract is used, independently of JavaScript's choice of sort algorithm. -/
def sortChildren (children : List Id) : List Id := children.mergeSort (fun a b => decide (Desc a b))

theorem sort_children_pairwise (children : List Id) :
    (sortChildren children).Pairwise Desc := List.pairwise_mergeSort' Desc children

theorem sort_children_perm (children : List Id) : (sortChildren children).Perm children :=
  List.mergeSort_perm children _

/-- Sibling dominance implies literal first-child placement after complete
sorting, even if the stored child map enumerates its keys arbitrarily. -/
theorem sort_fresh_first (fresh : Id) (children : List Id)
    (dominates : ∀ child ∈ children, Before child fresh) :
    sortChildren (fresh :: children) = fresh :: sortChildren children := by
  have sorted : (fresh :: sortChildren children).Pairwise Desc := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, sort_children_pairwise children⟩
    intro child member
    exact Or.inl (dominates child ((sort_children_perm children).mem_iff.mp member))
  have permutation : (sortChildren (fresh :: children)).Perm (fresh :: sortChildren children) :=
    (sort_children_perm (fresh :: children)).trans
      (List.Perm.cons fresh (sort_children_perm children).symm)
  exact permutation.eq_of_pairwise' (sort_children_pairwise _) sorted

/-- The comparator determines the sorted sequence independently of map-key
enumeration, including placement of a newly integrated key at the end. -/
theorem sort_permutation {left right : List Id} (permutation : left.Perm right) :
    sortChildren left = sortChildren right := by
  have both : (sortChildren left).Perm (sortChildren right) :=
    (sort_children_perm left).trans (permutation.trans (sort_children_perm right).symm)
  exact both.eq_of_pairwise' (sort_children_pairwise left) (sort_children_pairwise right)

theorem sort_fresh_enumeration (fresh : Id) (children enumeration : List Id)
    (sameKeys : enumeration.Perm (fresh :: children))
    (dominates : ∀ child ∈ children, Before child fresh) :
    sortChildren enumeration = fresh :: sortChildren children := by
  rw [sort_permutation sameKeys, sort_fresh_first fresh children dominates]

/-- Every listed child comes from a published run. Internal children identify
an immediately preceding item known to the honest issuer; first children use
only the transaction-first replay order. This is source provenance, not a
premise about the desired sorted result. -/
def ChildrenFromRuns (n : Network) (session : Session) (width : Nat)
    (children : List Id) : Prop :=
  ∀ child ∈ children, ∃ run ∈ n.published, ∃ offset,
    offset < run.length ∧ child = run.at offset ∧
    Before run.first (reserve (n.peers session) session width).first ∧
    (0 < offset → Known (n.peers session) (run.at (offset - 1)))

/-- Receipt-derived allocation and source provenance discharge the sorting
premise, including internal run characters with clocks beyond the old first. -/
theorem allocation_sort_fresh_first {n : Network} (reachable : Reach n)
    (session : Session) (width : Nat) (children : List Id)
    (provenance : ChildrenFromRuns n session width children) :
    sortChildren ((reserve (n.peers session) session width).first :: children) =
      (reserve (n.peers session) session width).first :: sortChildren children := by
  apply sort_fresh_first
  intro child member
  obtain ⟨run, published, offset, within, rfl, earlier, reference⟩ := provenance child member
  exact child_dominance reachable published within earlier reference

/-- Reading complete subtrees after sorted child keys places a fresh chain
before the whole previous forest. The subtree function models the source's
unique-ID item map; freshly inserted IDs must not occur in the old key set. -/
theorem sorted_forest_splice {Value : Type} (fresh : Id) (children : List Id)
    (oldSubtree : Id → List Value) (run : List Value)
    (dominates : ∀ child ∈ children, Before child fresh) :
    (sortChildren (fresh :: children)).flatMap
        (fun key => if key = fresh then run else oldSubtree key) =
      run ++ (sortChildren children).flatMap oldSubtree := by
  rw [sort_fresh_first fresh children dominates, List.flatMap_cons]
  simp only [ite_true]
  congr 1
  apply List.flatMap_congr
  intro child member
  have before := dominates child ((sort_children_perm children).mem_iff.mp member)
  have distinct : child ≠ fresh := by
    intro equal
    exact before_irrefl fresh (equal ▸ before)
  simp [distinct]

/-- PASS+FAIL: sibling ordering uses counter first and UTF-16 session second.
The run is read before an older child's complete subtree, not appended. -/
theorem sort_splice_control :
    sortChildren [⟨2, [66]⟩, ⟨1, [90]⟩, ⟨2, [65]⟩] =
      [⟨2, [66]⟩, ⟨2, [65]⟩, ⟨1, [90]⟩] ∧
    sortChildren [⟨2, [66]⟩, ⟨1, [90]⟩, ⟨2, [65]⟩] ≠
      [⟨1, [90]⟩, ⟨2, [65]⟩, ⟨2, [66]⟩] := by
  have tie : ([65] : Session) < [66] := List.Lex.rel (by decide)
  simp [sortChildren, List.mergeSort, Desc, Before, tie]

#print axioms allocation_sort_fresh_first
#print axioms sorted_forest_splice
end Sal.MRDTs.Instances.NotionCoreSourceInvariant
