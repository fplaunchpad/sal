import Sal.MRDTs.Instances.NotionCoreSliceForest

/-! Source creation keeps two orders: blocks Map enumeration appends, while
blockOrder splices after a present predecessor and otherwise at the front.
A merged block leaves the Map but keeps its place in blockOrder as a
tombstone; the shown order filters tombstones out, and a create after a
tombstone lands at its position. Fresh block creation only: source
revival/recreation checks are separate. Nat names use the existing SliceForest
encoding; source string/typed BlockKey injection and truthiness of
afterBlockId remain a decoder boundary. -/
namespace Sal.MRDTs.Instances.NotionCoreDisplayOrder
open NotionCoreSliceForest

def names (forest : Forest) : List Nat := forest.map Block.id

def insertionIndex (order : List Nat) (after : Option Nat) : Nat :=
  match after with
  | none => 0
  | some previous => if previous ∈ order then order.idxOf previous + 1 else 0

def insert (order : List Nat) (fresh : Nat) (after : Option Nat) : List Nat :=
  let index := insertionIndex order after
  order.take index ++ fresh :: order.drop index

/-- Literal splice is a permutation of cons, even for a missing predecessor. -/
theorem insert_perm (order : List Nat) (fresh : Nat) (after : Option Nat) :
    (insert order fresh after).Perm (fresh :: order) := by
  unfold insert
  have p : (order.take (insertionIndex order after) ++ fresh :: order.drop (insertionIndex order after)).Perm
      (fresh :: (order.take (insertionIndex order after) ++ order.drop (insertionIndex order after))) := List.perm_middle
  simpa using p

theorem insert_unique (order : List Nat) (fresh : Nat) (after : Option Nat)
    (unique : order.Nodup) (new : fresh ∉ order) : (insert order fresh after).Nodup := by
  exact (insert_perm order fresh after).nodup_iff.mpr (List.nodup_cons.mpr ⟨new, unique⟩)

/-- The front is the rule for a predecessor absent from the order, including
tombstones; a tombstone itself is present. -/
theorem missing_front (order : List Nat) (fresh previous : Nat) (missing : previous ∉ order) :
    insert order fresh (some previous) = fresh :: order := by
  simp [insert, insertionIndex, missing]

/-- A predecessor in the order, alive or a tombstone, is immediately followed
by the fresh name. -/
theorem insert_after_present (order : List Nat) (fresh previous : Nat) (present : previous ∈ order) :
    insert order fresh (some previous) =
      order.take (order.idxOf previous + 1) ++ fresh :: order.drop (order.idxOf previous + 1) := by
  simp [insert, insertionIndex, present]

/-- At a present unique predecessor, the source index splice is exactly the
independent document specification's insert-after traversal. -/
theorem insert_after_flatMap (order : List Nat) (fresh previous : Nat)
    (unique : order.Nodup) (present : previous ∈ order) :
    insert order fresh (some previous) =
      order.flatMap (fun bid => if bid = previous then [bid,fresh] else [bid]) := by
  induction order with
  | nil => simp at present
  | cons head tail ih =>
    obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : head = previous
    · subst head
      have rest : tail.flatMap (fun bid => if bid = previous then [bid,fresh] else [bid]) = tail := by
        clear unique tailUnique ih present
        induction tail with
        | nil => rfl
        | cons next rest ih =>
          have different : next ≠ previous := fun eq => absent (by simp [eq])
          simp only [List.flatMap_cons,if_neg different,List.singleton_append]
          exact congrArg (next :: ·) (ih (fun mem => absent (List.mem_cons_of_mem _ mem)))
      simp [insert,insertionIndex,rest]
    · have inside : previous ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      have no : (head == previous) = false := by simp [same]
      simp only [insert,insertionIndex,if_pos present,List.idxOf_cons,no,cond_false,
        List.flatMap_cons,if_neg same,List.singleton_append]
      have tailEq := ih tailUnique inside
      simp only [insert,insertionIndex,if_pos inside] at tailEq
      simpa [Nat.add_assoc,List.take_succ_cons,List.drop_succ_cons] using congrArg (head :: ·) tailEq

structure State where
  search : Forest
  display : List Nat

/-- Display entries whose block is in the search Map: tombstones filtered out. -/
def shown (state : State) : List Nat :=
  state.display.filter fun bid => state.search.any fun block => block.id == bid

/-- Unique names, a duplicate-free display order, and the shown order is a
permutation of the search Map's names. Tombstones may remain in the display. -/
def Aligned (state : State) : Prop :=
  (names state.search).Nodup ∧ state.display.Nodup ∧ (shown state).Perm (names state.search)

theorem shown_member (state : State) (bid : Nat) :
    bid ∈ shown state ↔ bid ∈ state.display ∧ bid ∈ names state.search := by
  simp [shown, names]

def create (state : State) (fresh : Nat) (after : Option Nat) : State :=
  ⟨state.search ++ [⟨fresh, freshTitle fresh⟩], insert (state.display.filter (· != fresh)) fresh after⟩

private theorem perm_of_members {xs ys : List Nat} (left : xs.Nodup) (right : ys.Nodup)
    (same : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.Perm ys :=
  (List.perm_ext_iff_of_nodup left right).mpr same

theorem create_aligned (state : State) (fresh : Nat) (after : Option Nat)
    (aligned : Aligned state) (new : fresh ∉ names state.search) :
    Aligned (create state fresh after) := by
  obtain ⟨unique, displayUnique, same⟩ := aligned
  have namesNext : names (create state fresh after).search = names state.search ++ [fresh] := by
    simp [create, names]
  have namesUnique : (names state.search ++ [fresh]).Nodup :=
    List.nodup_append'.mpr ⟨unique, by simp,
      List.disjoint_left.mpr fun id old new' => new (by rw [List.mem_singleton.mp new'] at old; exact old)⟩
  have filteredUnique : (state.display.filter (· != fresh)).Nodup := displayUnique.filter _
  have displayNext : (create state fresh after).display.Nodup :=
    insert_unique _ fresh after filteredUnique (by simp)
  refine ⟨by rw [namesNext]; exact namesUnique, displayNext, ?_⟩
  rw [namesNext]
  refine perm_of_members (xs := shown _) (displayNext.filter _) namesUnique ?_
  intro bid
  rw [shown_member, namesNext]
  have inserted := (insert_perm (state.display.filter (· != fresh)) fresh after).mem_iff (a := bid)
  have shownOld := same.mem_iff (a := bid)
  rw [shown_member] at shownOld
  simp only [create] at inserted ⊢
  rw [inserted]
  simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq, List.mem_append, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨rfl | ⟨inDisplay, _⟩, inNames⟩
    · exact Or.inr rfl
    · rcases inNames with old | rfl
      · exact Or.inl old
      · exact Or.inr rfl
  · rintro (old | rfl)
    · have shownBid := shownOld.mpr old
      refine ⟨Or.inr ⟨shownBid.1, fun equal => new (equal ▸ old)⟩, Or.inl old⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩

/-- Removing names from the search Map, as a merge does, keeps the display
order and stays aligned: the removed names become tombstones. -/
theorem filter_aligned (state : State) (search : Forest) (keep : Nat → Bool)
    (aligned : Aligned state) (filtered : names search = (names state.search).filter keep) :
    Aligned ⟨search, state.display⟩ := by
  obtain ⟨unique, displayUnique, same⟩ := aligned
  have namesUnique : (names search).Nodup := by rw [filtered]; exact unique.filter _
  refine ⟨namesUnique, displayUnique, ?_⟩
  refine perm_of_members (xs := shown _) (displayUnique.filter _) namesUnique ?_
  intro bid
  have shownOld := same.mem_iff (a := bid)
  rw [shown_member] at shownOld
  rw [shown_member]
  simp only
  rw [filtered, List.mem_filter]
  constructor
  · rintro ⟨inDisplay, inNames, kept⟩
    exact ⟨inNames, kept⟩
  · rintro ⟨inNames, kept⟩
    exact ⟨(shownOld.mpr inNames).1, inNames, kept⟩

/-- Materialization queries the search Map by display ID, then selects the
active leaf. Physical endpoint rendering remains a separate interpretation. -/
def lookup (forest : Forest) (id : Nat) : Option (Nat × Ref) :=
  (forest.find? (fun block => block.id == id)).map (fun block => (block.id, active block.title))

def materialize (state : State) : List (Nat × Ref) := state.display.filterMap (lookup state.search)

def canonical (state : State) : List (Nat × Ref) :=
  (names state.search).filterMap (lookup state.search)

private theorem lookup_absent (forest : Forest) (id : Nat)
    (absent : (forest.any fun block => block.id == id) = false) : lookup forest id = none := by
  simp only [lookup, Option.map_eq_none_iff]
  apply List.find?_eq_none.mpr
  intro block member
  simp only [List.any_eq_false] at absent
  exact absent block member

/-- Display materialization enumerates exactly the same lookups as Map order,
with a potentially different order; tombstones look up nothing. -/
theorem materialize_perm (state : State) (aligned : Aligned state) :
    (materialize state).Perm (canonical state) := by
  have filtered : materialize state = (shown state).filterMap (lookup state.search) := by
    simp only [materialize, shown, List.filterMap_filter]
    apply List.filterMap_congr
    intro bid _
    cases present : state.search.any (fun block => block.id == bid) with
    | true => rfl
    | false => simp [lookup_absent state.search bid present]
  rw [filtered]
  exact aligned.2.2.filterMap _

theorem lookup_member (forest : Forest) (unique : (names forest).Nodup)
    (block : Block) (member : block ∈ forest) :
    lookup forest block.id = some (block.id, active block.title) := by
  induction forest with
  | nil => simp at member
  | cons head tail ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | present
    · simp [lookup]
    · have different : head.id ≠ block.id := by
        intro same
        exact nd.1 (List.mem_map.mpr ⟨block, present, same.symm⟩)
      simpa [lookup, different] using ih nd.2 present

/-- Unique search keys make canonical lookup materialization exactly the
forest's active-leaf projection, rather than a self-echo of display IDs. -/
theorem canonical_projection (state : State) (unique : (names state.search).Nodup) :
    canonical state = state.search.map (fun block => (block.id, active block.title)) := by
  have helper : ∀ xs : Forest, (∀ block ∈ xs, block ∈ state.search) →
      (xs.map Block.id).filterMap (lookup state.search) =
        xs.map (fun block => (block.id, active block.title)) := by
    intro xs contained
    induction xs with
    | nil => rfl
    | cons block tail ih =>
        simp only [List.map_cons, List.filterMap_cons]
        rw [lookup_member state.search unique block (contained block (by simp))]
        rw [ih (fun b hb => contained b (List.mem_cons_of_mem _ hb))]
  exact helper state.search (fun _ h => h)

theorem materialize_projection (state : State) (aligned : Aligned state) :
    (materialize state).Perm (state.search.map (fun block => (block.id, active block.title))) := by
  rw [← canonical_projection state aligned.1]
  exact materialize_perm state aligned

private def root (id : Nat) : Block := ⟨id, freshTitle id⟩
private def base : State := ⟨[root 1], [1]⟩
private def twoCreates : State := create (create base 2 (some 1)) 3 (some 1)

/-- PASS+FAIL: two replayed creates after the same block append to Map order
but reverse at the display insertion point. Split's create phase is identical. -/
theorem concurrent_create_control :
    names twoCreates.search = [1,2,3] ∧ twoCreates.display = [1,3,2] ∧
    twoCreates.display ≠ names twoCreates.search ∧
    (materialize twoCreates).map Prod.fst = [1,3,2] ∧
    (materialize twoCreates).map Prod.fst ≠ [1,2,3] := by decide

/-- Missing predecessors use the same front fallback as absent predecessors;
rejecting the operation or appending it would disagree with raw source. -/
theorem missing_predecessor_control :
    (create base 2 (some 99)).display = [2,1] ∧
    (create base 2 none).display = [2,1] ∧
    (create base 2 (some 99)).display ≠ [1,2] ∧
    names (create base 2 (some 99)).search = [1,2] := by decide

private def marker (n : Nat) : NotionCoreSpec.Address := (0, .event (65,n))
private def splitPhysical : List NotionCoreSource.Atom :=
  [NotionCorePartition.boundary (0,.start), ⟨marker 1, .text 97 false⟩,
   NotionCorePartition.boundary (marker 3), ⟨marker 2, .text 98 false⟩,
   NotionCorePartition.boundary (marker 4), ⟨marker 5, .text 99 false⟩]
private def splitSeed : NotionCoreSliceForest.State :=
  ⟨[root 0], fun inst => if inst = 0 then splitPhysical else emptyPhysical inst⟩
private def splitOnce : NotionCoreSliceForest.State :=
  (NotionCoreSliceForest.split splitSeed (marker 3) 10).getD splitSeed
private def splitTwice : NotionCoreSliceForest.State :=
  (NotionCoreSliceForest.split splitOnce (marker 4) 11).getD splitOnce
private def splitDisplay : State :=
  ⟨splitTwice.blocks, insert (insert [0] 10 (some 0)) 11 (some 0)⟩

/-- PASS+FAIL: two source splits were issued against the same original block.
Replay routes the second marker through the inherited slice, but its creation
still inserts after the requested original block. Lookup must use the active
inherited leaf, not its empty title root or the Map enumeration. -/
theorem concurrent_split_control :
    names splitDisplay.search = [0,10,11] ∧
    (materialize splitDisplay).map Prod.fst = [0,11,10] ∧
    (materialize splitDisplay).map (fun cell => cell.2.start) =
      [(0,.start), marker 4, marker 3] ∧
    (materialize splitDisplay).map (fun cell => cell.2.start) ≠
      [(0,.start), (11,.start), (10,.start)] := by decide

#print axioms materialize_projection
#print axioms create_aligned
#print axioms materialize_perm
end Sal.MRDTs.Instances.NotionCoreDisplayOrder
