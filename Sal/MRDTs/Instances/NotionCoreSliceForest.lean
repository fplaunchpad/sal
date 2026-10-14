import Sal.MRDTs.Instances.NotionCorePartition
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Finite source-shaped text-slice trees for the no-merge core. Split rewrites
old children under the new right node, then detach/append moves that complete
subtree. The shape invariant is derived at atomic transaction boundaries;
temporary split trees need not have the final root/leaf shape.
-/
namespace Sal.MRDTs.Instances.NotionCoreSliceForest
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)

structure Ref where
  start : Address
  stop : Option Address
  deriving DecidableEq, Repr

mutual
inductive Tree where
  | node (slice : Ref) (children : Children)
  deriving DecidableEq, Repr
inductive Children where
  | nil
  | cons (tree : Tree) (rest : Children)
  deriving DecidableEq, Repr
end

def Tree.slice : Tree → Ref | .node slice _ => slice
def Tree.children : Tree → Children | .node _ children => children

def Children.append : Children → Children → Children
  | .nil, right => right
  | .cons tree rest, right => .cons tree (rest.append right)

mutual
def preorderTree : Tree → List Ref
  | .node slice children => slice :: preorderChildren children
def preorderChildren : Children → List Ref
  | .nil => []
  | .cons tree rest => preorderTree tree ++ preorderChildren rest
end

/-- Literal source `splitTextSliceTreeNode`: the right interval inherits all
old children. Fresh detachment is a separate operation below. -/
def splitNode (marker : Address) : Tree → Tree
  | .node slice children =>
      .node {slice with stop := some marker}
        (.cons (.node ⟨marker, slice.stop⟩ children) .nil)

/-- Literal append-to-title-root operation. The atomic client creates its
fresh empty target; this function itself accepts arbitrary old children. -/
def appendRoot (tree child : Tree) : Tree :=
  .node tree.slice (tree.children.append (.cons child .nil))

mutual
def detachTree (marker : Address) : Tree → Option (Tree × Tree)
  | .node slice children =>
      (detachChildren marker children).map fun result => (.node slice result.1, result.2)
def detachChildren (marker : Address) : Children → Option (Children × Tree)
  | .nil => none
  | .cons tree rest =>
      if tree.slice.start = marker then some (rest, tree)
      else match detachTree marker tree with
      | some result => some (.cons result.1 rest, result.2)
      | none => (detachChildren marker rest).map fun result => (.cons tree result.1, result.2)
end

/-- The new right node is found by its fresh start marker. Detachment moves
its entire old-child subtree, exactly as the source does. -/
theorem split_detach (tree : Tree) (marker : Address) :
    detachTree marker (splitNode marker tree) =
      some (.node {tree.slice with stop := some marker} .nil,
        .node ⟨marker, tree.slice.stop⟩ tree.children) := by
  cases tree
  simp [splitNode, detachTree, detachChildren, Tree.slice, Tree.children]

def titleRef (bid : Nat) : Ref := ⟨(bid, .start), none⟩
def freshTitle (bid : Nat) : Tree := .node (titleRef bid) .nil

/-- Source raw interval membership includes tombstones and split markers. -/
def contains (physical : Nat → List Atom) (slice : Ref) (item : Address) : Bool :=
  decide (slice.start.1 = item.1) &&
    (NotionCorePartition.extractIds (physical slice.start.1) slice.start slice.stop).contains (some item)

mutual
def splitTree (physical : Nat → List Atom) (marker : Address) : Tree → Option Tree
  | .node slice children =>
      if contains physical slice marker then some (splitNode marker (.node slice children))
      else (splitChildren physical marker children).map (.node slice)
def splitChildren (physical : Nat → List Atom) (marker : Address) : Children → Option Children
  | .nil => none
  | .cons tree rest =>
      match splitTree physical marker tree with
      | some next => some (.cons next rest)
      | none => (splitChildren physical marker rest).map (.cons tree)
end

structure Block where
  id : Nat
  title : Tree
  deriving DecidableEq, Repr

/-- The source `blocks.values()` map insertion order used by `#allNodes`.
Displayed order lives in the separate source `blockOrder` list and is not
represented by this enumeration. -/
abbrev Forest := List Block

def splitForest (physical : Nat → List Atom) (marker : Address) : Forest → Option Forest
  | [] => none
  | block :: rest =>
      match splitTree physical marker block.title with
      | some title => some ({block with title := title} :: rest)
      | none => (splitForest physical marker rest).map (block :: ·)

def detachForest (marker : Address) : Forest → Option (Forest × Tree)
  | [] => none
  | block :: rest =>
      match detachTree marker block.title with
      | some result => some ({block with title := result.1} :: rest, result.2)
      | none => (detachForest marker rest).map fun result => (block :: result.1, result.2)

def appendToBlock (bid : Nat) (child : Tree) (forest : Forest) : Forest :=
  forest.map fun block => if block.id = bid then {block with title := appendRoot block.title child} else block

/-- Atomic source split's tree phases after marker insertion: split the actual
containing node, find the fresh right node, detach it, append to the target. -/
def splitMove (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) : Option Forest := do
  let divided ← splitForest physical marker forest
  let (remaining, moved) ← detachForest marker divided
  pure (appendToBlock target moved remaining)

/-- Transaction-boundary tree shape, stated as a predicate on arbitrary rose
trees. It is not a guard of the split/move algorithms. -/
inductive Normal (bid : Nat) : Tree → Prop where
  | own (stop : Option Address) : Normal bid (.node ⟨(bid, .start), stop⟩ .nil)
  | attached (active : Ref) : Normal bid (.node (titleRef bid) (.cons (.node active .nil) .nil))

def active (tree : Tree) : Ref := match tree.children with
  | .cons child _ => child.slice
  | .nil => tree.slice

def attached (tree : Tree) : Bool := match tree.children with
  | .nil => false
  | .cons _ _ => true

/-- Structural active-only specialization of actual recursive source search.
An inactive root's membership is ruled out by its physically empty instance. -/
theorem splitTree_active (physical : Nat → List Atom) (bid : Nat) (tree : Tree)
    (marker : Address) (normal : Normal bid tree)
    (inactiveEmpty : attached tree = true → contains physical (titleRef bid) marker = false)
    (selected : contains physical (active tree) marker = true) :
    splitTree physical marker tree = some
      (match tree.children with
       | .nil => splitNode marker tree
       | .cons child _ => .node tree.slice (.cons (splitNode marker child) .nil)) := by
  cases normal with
  | own stop =>
      simp only [active, Tree.children, Tree.slice] at selected
      simp [splitTree, selected, Tree.children]
  | attached ref =>
      have rootEmpty := inactiveEmpty rfl
      simp [splitTree, splitChildren, active, Tree.children, Tree.slice, rootEmpty] at selected ⊢
      simp [selected]

def cutActive (tree : Tree) (marker : Address) : Tree := match tree.children with
  | .nil => .node {tree.slice with stop := some marker} .nil
  | .cons child _ => .node tree.slice
      (.cons (.node {child.slice with stop := some marker} .nil) .nil)

def keys (tree : Tree) : List Address := (preorderTree tree).map Ref.start

theorem cutActive_normal (bid : Nat) (tree : Tree) (marker : Address) (normal : Normal bid tree) :
    Normal bid (cutActive tree marker) := by
  cases normal with
  | own stop => exact .own (some marker)
  | attached slice => exact .attached {slice with stop := some marker}

theorem cutActive_profile (bid : Nat) (tree : Tree) (marker : Address) (normal : Normal bid tree) :
    (active (cutActive tree marker)).start = (active tree).start ∧
      attached (cutActive tree marker) = attached tree := by cases normal <;> exact ⟨rfl, rfl⟩

theorem detach_normal_none (bid : Nat) (tree : Tree) (marker : Address)
    (normal : Normal bid tree) (fresh : marker ∉ keys tree) : detachTree marker tree = none := by
  cases normal with
  | own stop => rfl
  | attached slice =>
      have distinct : slice.start ≠ marker := by
        intro eq
        exact fresh (by simp [keys, preorderTree, preorderChildren, eq])
      simp [detachTree, detachChildren, Tree.slice, distinct]

/-- The source's split-plus-detach returns a leaf precisely because the
selected normal active node has no old children. The general `splitNode`
operation still moves arbitrary old subtrees; they are not discarded. -/
theorem splitTree_detach (physical : Nat → List Atom) (bid : Nat) (tree divided : Tree)
    (marker : Address) (normal : Normal bid tree) (fresh : marker ∉ keys tree)
    (inactiveEmpty : attached tree = true → contains physical (titleRef bid) marker = false)
    (accepted : splitTree physical marker tree = some divided) :
    detachTree marker divided = some (cutActive tree marker,
      .node ⟨marker, (active tree).stop⟩ .nil) ∧
    contains physical (active tree) marker = true := by
  cases normal with
  | own stop =>
      by_cases selected : contains physical ⟨(bid, .start), stop⟩ marker = true
      · simp only [splitTree, selected, ↓reduceIte] at accepted
        have equal := Option.some.inj accepted
        subst divided
        exact ⟨split_detach _ _, selected⟩
      · have rejected : contains physical ⟨(bid, .start), stop⟩ marker = false := Bool.eq_false_iff.mpr selected
        simp [splitTree, splitChildren, rejected] at accepted
  | attached slice =>
      have rootRejected := inactiveEmpty rfl
      have distinct : slice.start ≠ marker := by
        intro equal
        exact fresh (by simp [keys, preorderTree, preorderChildren, equal])
      by_cases selected : contains physical slice marker = true
      · simp [splitTree, splitChildren, rootRejected, selected] at accepted
        subst divided
        refine ⟨?_, selected⟩
        simp [detachTree, detachChildren, splitNode, cutActive, active,
          Tree.slice, Tree.children, distinct]
      · have rejected : contains physical slice marker = false := Bool.eq_false_iff.mpr selected
        simp [splitTree, splitChildren, rootRejected, rejected] at accepted

def NormalForest (forest : Forest) : Prop := ∀ block ∈ forest, Normal block.id block.title

def profile (forest : Forest) : List (Nat × Address × Bool) :=
  forest.map fun block => (block.id, (active block.title).start, attached block.title)

def FreshMarker (forest : Forest) (marker : Address) : Prop :=
  ∀ block ∈ forest, marker ∉ keys block.title

def splitDetach (physical : Nat → List Atom) (marker : Address) (forest : Forest) :
    Option (Forest × Tree) := do
  let divided ← splitForest physical marker forest
  detachForest marker divided

private theorem splitDetach_tail (physical : Nat → List Atom) (marker : Address)
    (block : Block) (rest : Forest)
    (noSplit : splitTree physical marker block.title = none)
    (noDetach : detachTree marker block.title = none) :
    splitDetach physical marker (block :: rest) =
      (splitDetach physical marker rest).map (fun result => (block :: result.1, result.2)) := by
  cases found : splitForest physical marker rest with
  | none => simp [splitDetach, splitForest, noSplit, found]
  | some divided =>
      cases detached : detachForest marker divided <;>
        simp [splitDetach, splitForest, noSplit, found, detachForest, noDetach, detached]

/-- Every accepted source split/detach searches the full forest and moves a
single leaf. Existing block root/active identities and attached status remain
unchanged; the selected interval is derived by the actual recursive search. -/
theorem splitDetach_normal (physical : Nat → List Atom) (marker : Address)
    (forest remaining : Forest) (moved : Tree)
    (normal : NormalForest forest) (fresh : FreshMarker forest marker)
    (inactiveEmpty : ∀ block ∈ forest, attached block.title = true →
      contains physical (titleRef block.id) marker = false)
    (accepted : splitDetach physical marker forest = some (remaining, moved)) :
    NormalForest remaining ∧ profile remaining = profile forest ∧
      ∃ source ∈ forest, moved = .node ⟨marker, (active source.title).stop⟩ .nil ∧
        contains physical (active source.title) marker = true := by
  induction forest generalizing remaining with
  | nil => simp [splitDetach, splitForest] at accepted
  | cons block rest ih =>
      have headNormal := normal block (by simp)
      have tailNormal : NormalForest rest := fun b hb => normal b (by simp [hb])
      have tailFresh : FreshMarker rest marker := fun b hb => fresh b (by simp [hb])
      have tailEmpty : ∀ b ∈ rest, attached b.title = true →
          contains physical (titleRef b.id) marker = false :=
        fun b hb => inactiveEmpty b (List.mem_cons_of_mem _ hb)
      cases found : splitTree physical marker block.title with
      | none =>
          have noDetach := detach_normal_none block.id block.title marker headNormal (fresh block (by simp))
          rw [splitDetach_tail physical marker block rest found noDetach] at accepted
          obtain ⟨result, oldResult, equal⟩ := Option.map_eq_some_iff.mp accepted
          rcases result with ⟨tailRemaining, tailMoved⟩
          cases equal
          obtain ⟨tailNormal, tailProfile, source, member, movedEq, selected⟩ :=
            ih tailRemaining tailNormal tailFresh tailEmpty oldResult
          refine ⟨?_, ?_, source, by simp [member], movedEq, selected⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact headNormal
            · exact tailNormal b hb
          · simpa only [profile, List.map_cons] using congrArg
              ((block.id, (active block.title).start, attached block.title) :: ·) tailProfile
      | some divided =>
          have localResult := splitTree_detach physical block.id block.title divided marker
            headNormal (fresh block (by simp)) (inactiveEmpty block (by simp)) found
          have exactResult : splitDetach physical marker (block :: rest) =
              some ({block with title := cutActive block.title marker} :: rest,
                .node ⟨marker, (active block.title).stop⟩ .nil) := by
            simp [splitDetach, splitForest, found, detachForest, localResult.1]
          rw [exactResult] at accepted
          have equal := Option.some.inj accepted
          cases equal
          refine ⟨?_, ?_, block, by simp, rfl, localResult.2⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact cutActive_normal block.id block.title marker headNormal
            · exact tailNormal b hb
          · have unchanged := cutActive_profile block.id block.title marker headNormal
            simp [profile, unchanged.1, unchanged.2]

def emptyPhysical (inst : Nat) : List Atom := [NotionCorePartition.boundary (inst, .start)]

theorem empty_title_rejects (physical : Nat → List Atom) (bid : Nat) (marker : Address)
    (empty : physical bid = emptyPhysical bid) : contains physical (titleRef bid) marker = false := by
  simp [contains, titleRef, empty, emptyPhysical, NotionCorePartition.extractIds,
    NotionCorePartition.ids, NotionCorePartition.boundary,
    NotionCoreSource.Endpoint.extract, NotionCoreSource.Endpoint.afterStart,
    NotionCoreSource.Endpoint.beforeEnd]

private theorem splitForest_append_rejected (physical : Nat → List Atom) (marker : Address)
    (forest : Forest) (target : Block) (rejected : splitTree physical marker target.title = none) :
    splitForest physical marker (forest ++ [target]) =
      (splitForest physical marker forest).map (· ++ [target]) := by
  induction forest with
  | nil => simp [splitForest, rejected]
  | cons block rest ih =>
      cases selected : splitTree physical marker block.title <;>
        simp [splitForest, selected, ih, Option.map_map, Function.comp_def]

private theorem detachForest_append_rejected (marker : Address) (forest : Forest) (target : Block)
    (rejected : detachTree marker target.title = none) :
    detachForest marker (forest ++ [target]) =
      (detachForest marker forest).map (fun result => (result.1 ++ [target], result.2)) := by
  induction forest with
  | nil => simp [detachForest, rejected]
  | cons block rest ih =>
      cases selected : detachTree marker block.title <;>
        simp [detachForest, selected, ih, Option.map_map, Function.comp_def]

private theorem splitDetach_append_rejected (physical : Nat → List Atom) (marker : Address)
    (forest : Forest) (target : Block)
    (noSplit : splitTree physical marker target.title = none)
    (noDetach : detachTree marker target.title = none) :
    splitDetach physical marker (forest ++ [target]) =
      (splitDetach physical marker forest).map (fun result => (result.1 ++ [target], result.2)) := by
  unfold splitDetach
  rw [splitForest_append_rejected physical marker forest target noSplit]
  cases selected : splitForest physical marker forest with
  | none => rfl
  | some divided =>
      simpa using detachForest_append_rejected marker divided target noDetach

private theorem appendToBlock_fresh (forest : Forest) (bid : Nat) (child : Tree)
    (fresh : bid ∉ forest.map Block.id) :
    appendToBlock bid child (forest ++ [⟨bid, freshTitle bid⟩]) =
      forest ++ [⟨bid, appendRoot (freshTitle bid) child⟩] := by
  simp only [appendToBlock, List.map_append, List.map_cons, List.map_nil]
  have untouched : forest.map (fun block =>
      if block.id = bid then {block with title := appendRoot block.title child} else block) = forest := by
    induction forest with
    | nil => rfl
    | cons block rest ih =>
        have absent : block.id ≠ bid ∧ bid ∉ rest.map Block.id := by simpa [eq_comm] using fresh
        simp only [List.map_cons, if_neg absent.1]
        rw [ih absent.2]
  simp [untouched]

def atomicSplit (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) : Option Forest :=
  splitMove physical marker target (forest ++ [⟨target, freshTitle target⟩])

/-- A newly created, physically empty title cannot intercept source marker
routing. Source search/detach through it is equivalent to appending it after
the old forest's actual split/detach, before the final append-child operation. -/
theorem atomicSplit_route (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) (empty : physical target = emptyPhysical target) :
    atomicSplit physical marker target forest =
      (splitDetach physical marker forest).map fun result =>
        appendToBlock target result.2 (result.1 ++ [⟨target, freshTitle target⟩]) := by
  have noSplit : splitTree physical marker (freshTitle target) = none := by
    simp [freshTitle, splitTree, splitChildren, empty_title_rejects physical target marker empty]
  have noDetach : detachTree marker (freshTitle target) = none := rfl
  unfold atomicSplit splitMove
  rw [splitForest_append_rejected physical marker forest ⟨target, freshTitle target⟩ noSplit]
  cases found : splitForest physical marker forest with
  | none => simp [splitDetach, found]
  | some divided =>
      simp only [Option.map_some]
      dsimp only [Bind.bind, Option.bind]
      rw [detachForest_append_rejected marker divided ⟨target, freshTitle target⟩ noDetach]
      cases detached : detachForest marker divided <;> simp [splitDetach, found, detached]

abbrev Profile := Nat × Address × Bool

def ProfileValid (profiles : List Profile) : Prop :=
  (profiles.map Prod.fst).Nodup ∧
  ∀ current ∈ profiles,
    current.2.1.1 ∈ profiles.map Prod.fst ∧
    ∀ other ∈ profiles, other.2.2 = true → current.2.1.1 ≠ other.1

def EmptyInactive (physical : Nat → List Atom) (profiles : List Profile) : Prop :=
  ∀ current ∈ profiles, current.2.2 = true → physical current.1 = emptyPhysical current.1

structure State where
  blocks : Forest
  physical : Nat → List Atom

def Invariant (state : State) : Prop :=
  NormalForest state.blocks ∧ ProfileValid (profile state.blocks) ∧
    EmptyInactive state.physical (profile state.blocks)

def write (physical : Nat → List Atom) (inst : Nat) (items : List Atom) : Nat → List Atom :=
  fun other => if other = inst then items else physical other

def create (state : State) (bid : Nat) : State :=
  ⟨state.blocks ++ [⟨bid, freshTitle bid⟩], write state.physical bid (emptyPhysical bid)⟩

def updateInstance (state : State) (inst : Nat) (items : List Atom) : State :=
  {state with physical := write state.physical inst items}

private theorem ids_profile (forest : Forest) :
    (profile forest).map Prod.fst = forest.map Block.id := by simp [profile, List.map_map, Function.comp_def]

private theorem profile_create_valid (profiles : List Profile) (bid : Nat)
    (valid : ProfileValid profiles) (fresh : bid ∉ profiles.map Prod.fst) :
    ProfileValid (profiles ++ [(bid, (bid, .start), false)]) := by
  refine ⟨?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append'.mpr
    refine ⟨valid.1, by simp, ?_⟩
    apply List.disjoint_left.mpr
    intro id member selected
    have eq : id = bid := by simpa using selected
    exact fresh (eq ▸ member)
  · intro current member
    rcases List.mem_append.mp member with member | member
    · refine ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using
        List.mem_append_left [bid] (valid.2 current member).1, ?_⟩
      intro other otherMember attached
      rcases List.mem_append.mp otherMember with old | newest
      · exact (valid.2 current member).2 other old attached
      · simp only [List.mem_singleton] at newest
        subst other
        simp at attached
    · have newest : current = (bid, (bid, .start), false) := List.mem_singleton.mp member
      subst current
      refine ⟨by simp, ?_⟩
      intro other otherMember attached equal
      rcases List.mem_append.mp otherMember with old | newest
      · apply fresh
        change bid = other.1 at equal
        rw [equal]
        exact List.mem_map.mpr ⟨other, old, rfl⟩
      · have eq := List.mem_singleton.mp newest
        subst other
        simp at attached

theorem create_preserves (state : State) (bid : Nat) (invariant : Invariant state)
    (fresh : bid ∉ state.blocks.map Block.id) : Invariant (create state bid) := by
  have fresh' : bid ∉ (profile state.blocks).map Prod.fst := by simpa only [ids_profile] using fresh
  have profileEq : profile (create state bid).blocks = profile state.blocks ++ [(bid, (bid, .start), false)] := by
    simp [create, profile, freshTitle, active, Tree.children, Tree.slice, attached, titleRef]
  refine ⟨?_, ?_, ?_⟩
  · intro block member
    rcases List.mem_append.mp member with member | member
    · exact invariant.1 block member
    · have equal := List.mem_singleton.mp member
      subst block
      exact .own none
  · rw [profileEq]
    exact profile_create_valid _ bid invariant.2.1 fresh'
  · rw [profileEq]
    intro current member attached
    rcases List.mem_append.mp member with member | member
    · have different : current.1 ≠ bid := by
        intro equal
        exact fresh' (equal ▸ List.mem_map.mpr ⟨current, member, rfl⟩)
      simpa only [create, write, if_neg different] using invariant.2.2 current member attached
    · have equal := List.mem_singleton.mp member
      subst current
      simp at attached

/-- RGA insertion/deletion changes one active instance and does not touch the
slice forest. The update's actual contents are abstract here; the frame theorem
uses only the instance addressed by the operation, not a desired text result. -/
theorem updateInstance_preserves (state : State) (inst : Nat) (items : List Atom)
    (invariant : Invariant state)
    (owned : ∃ block ∈ state.blocks, (active block.title).start.1 = inst) :
    Invariant (updateInstance state inst items) := by
  refine ⟨invariant.1, invariant.2.1, ?_⟩
  obtain ⟨block, member, equal⟩ := owned
  have selected : (block.id, (active block.title).start, attached block.title) ∈ profile state.blocks :=
    List.mem_map.mpr ⟨block, member, rfl⟩
  intro current memberCurrent attachedCurrent
  have different : current.1 ≠ inst := by
    intro collision
    exact ((invariant.2.1.2 _ selected).2 current memberCurrent attachedCurrent)
      (equal.trans collision.symm)
  simpa only [updateInstance, write, if_neg different] using
    invariant.2.2 current memberCurrent attachedCurrent

/-- Exact shape of every successful atomic tree split. The moved leaf and
selected source are derived by the forest search and detachment algorithms. -/
theorem atomicSplit_result (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest result : Forest) (normal : NormalForest forest)
    (fresh : FreshMarker forest marker) (freshTarget : target ∉ forest.map Block.id)
    (inactiveEmpty : ∀ block ∈ forest, attached block.title = true →
      contains physical (titleRef block.id) marker = false)
    (empty : physical target = emptyPhysical target)
    (accepted : atomicSplit physical marker target forest = some result) :
    ∃ remaining source, source ∈ forest ∧ NormalForest remaining ∧
      profile remaining = profile forest ∧
      contains physical (active source.title) marker = true ∧
      result = remaining ++ [⟨target, .node (titleRef target)
        (.cons (.node ⟨marker, (active source.title).stop⟩ .nil) .nil)⟩] := by
  rw [atomicSplit_route physical marker target forest empty] at accepted
  obtain ⟨pair, divided, equal⟩ := Option.map_eq_some_iff.mp accepted
  rcases pair with ⟨remaining, moved⟩
  obtain ⟨normalRemaining, sameProfile, source, member, movedEq, selected⟩ :=
    splitDetach_normal physical marker forest remaining moved normal fresh inactiveEmpty divided
  have sameIds : remaining.map Block.id = forest.map Block.id := by
    rw [← ids_profile, sameProfile, ids_profile]
  have freshRemaining : target ∉ remaining.map Block.id := sameIds ▸ freshTarget
  rw [appendToBlock_fresh remaining target moved freshRemaining, movedEq] at equal
  exact ⟨remaining, source, member, normalRemaining, sameProfile, selected, equal.symm⟩

private theorem profile_attach_valid (profiles : List Profile) (target : Nat) (marker : Address)
    (valid : ProfileValid profiles) (fresh : target ∉ profiles.map Prod.fst)
    (source : Profile) (member : source ∈ profiles) (sameInstance : marker.1 = source.2.1.1) :
    ProfileValid (profiles ++ [(target, marker, true)]) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.map_append, List.map_cons, List.map_nil] using
      (List.nodup_append'.mpr ⟨valid.1, by simp,
        List.disjoint_left.mpr (fun id old new => fresh ((by simpa using new : id = target) ▸ old))⟩ :
        (profiles.map Prod.fst ++ [target]).Nodup)
  · intro current currentMember
    rcases List.mem_append.mp currentMember with old | new
    · refine ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using
        List.mem_append_left [target] (valid.2 current old).1, ?_⟩
      intro other otherMember isAttached
      rcases List.mem_append.mp otherMember with otherOld | otherNew
      · exact (valid.2 current old).2 other otherOld isAttached
      · have same : other = (target, marker, true) := List.mem_singleton.mp otherNew
        subst other
        intro collision
        change current.2.1.1 = target at collision
        exact fresh (collision ▸ (valid.2 current old).1)
    · have same : current = (target, marker, true) := List.mem_singleton.mp new
      subst current
      refine ⟨by simpa only [List.map_append, List.map_cons, List.map_nil] using
        List.mem_append_left [target] (sameInstance ▸ (valid.2 source member).1), ?_⟩
      intro other otherMember isAttached
      rcases List.mem_append.mp otherMember with otherOld | otherNew
      · simpa only [sameInstance] using (valid.2 source member).2 other otherOld isAttached
      · have same : other = (target, marker, true) := List.mem_singleton.mp otherNew
        subst other
        intro collision
        change marker.1 = target at collision
        exact fresh ((sameInstance.symm.trans collision) ▸ (valid.2 source member).1)

/-- Create the fresh title before the actual source tree phases. The physical
marker insertion is an instance update and is supplied before this operation. -/
def split (state : State) (marker : Address) (target : Nat) : Option State :=
  let physical := (create state target).physical
  (atomicSplit physical marker target state.blocks).map fun blocks => ⟨blocks, physical⟩

theorem split_preserves (state result : State) (marker : Address) (target : Nat)
    (invariant : Invariant state) (fresh : FreshMarker state.blocks marker)
    (freshTarget : target ∉ state.blocks.map Block.id)
    (accepted : split state marker target = some result) : Invariant result := by
  let physical := (create state target).physical
  have empty : physical target = emptyPhysical target := by simp [physical, create, write]
  have created := create_preserves state target invariant freshTarget
  have inactiveEmpty : ∀ block ∈ state.blocks, attached block.title = true →
      contains physical (titleRef block.id) marker = false := by
    intro block member isAttached
    apply empty_title_rejects
    apply created.2.2 (block.id, (active block.title).start, attached block.title)
    · exact List.mem_map.mpr ⟨block, List.mem_append_left _ member, rfl⟩
    · exact isAttached
  obtain ⟨blocks, executed, equal⟩ := Option.map_eq_some_iff.mp accepted
  cases equal
  obtain ⟨remaining, source, member, normalRemaining, sameProfile, selected, shape⟩ :=
    atomicSplit_result physical marker target state.blocks blocks invariant.1 fresh freshTarget
      inactiveEmpty empty executed
  have profileEq : profile blocks = profile state.blocks ++ [(target, marker, true)] := by
    rw [shape]
    simp only [profile, List.map_append, List.map_cons, List.map_nil]
    change profile remaining ++ [(target, marker, true)] = _
    rw [sameProfile]
    rfl
  have sourceProfile : (source.id, (active source.title).start, attached source.title) ∈ profile state.blocks :=
    List.mem_map.mpr ⟨source, member, rfl⟩
  have sameInstance : marker.1 = (active source.title).start.1 := by
    have selectedInstance := (Bool.and_eq_true_iff.mp selected).1
    exact (of_decide_eq_true selectedInstance).symm
  refine ⟨?_, ?_, ?_⟩
  · intro block present
    rw [shape] at present
    rcases List.mem_append.mp present with old | new
    · exact normalRemaining block old
    · have same := List.mem_singleton.mp new
      subst block
      exact .attached _
  · change ProfileValid (profile blocks)
    rw [profileEq]
    exact profile_attach_valid _ target marker invariant.2.1
      (by simpa only [ids_profile] using freshTarget) _ sourceProfile sameInstance
  · change EmptyInactive physical (profile blocks)
    rw [profileEq]
    intro current present isAttached
    rcases List.mem_append.mp present with old | new
    · apply created.2.2 current _ isAttached
      have extended : profile (create state target).blocks = profile state.blocks ++
          [(target, (target, .start), false)] := by
        simp [create, profile, freshTitle, titleRef, active, Tree.children, Tree.slice, attached]
      rw [extended]
      exact List.mem_append_left _ old
    · have same := List.mem_singleton.mp new
      subst current
      exact empty

def initial : State := ⟨[], emptyPhysical⟩

/-- Guards concern fresh names and the instance addressed by an operation.
No tree-shape, empty-root or expected-observation predicate is an input. -/
inductive Reach : State → Prop where
  | init : Reach initial
  | create {state : State} (bid : Nat) : Reach state →
      bid ∉ state.blocks.map Block.id → Reach (create state bid)
  | update {state : State} (inst : Nat) (items : List Atom) : Reach state →
      (∃ block ∈ state.blocks, (active block.title).start.1 = inst) →
      Reach (updateInstance state inst items)
  | split {state result : State} (marker : Address) (target : Nat) : Reach state →
      FreshMarker state.blocks marker → target ∉ state.blocks.map Block.id →
      split state marker target = some result → Reach result

theorem reachable_invariant {state : State} (reachable : Reach state) : Invariant state := by
  induction reachable with
  | init => simp [Invariant, initial, NormalForest, ProfileValid, EmptyInactive, profile]
  | create bid _ fresh ih => exact create_preserves _ bid ih fresh
  | update inst items _ owned ih => exact updateInstance_preserves _ inst items ih owned
  | split marker target _ fresh freshTarget accepted ih =>
      exact split_preserves _ _ marker target ih fresh freshTarget accepted

private def itemAddress (counter : Nat) : Address := (0, .event (65, counter))
private def firstPhysical : List Atom :=
  [NotionCorePartition.boundary (0, .start),
   ⟨itemAddress 1, .text 97 false⟩, NotionCorePartition.boundary (itemAddress 3),
   ⟨itemAddress 2, .text 98 false⟩]
private def readyState : State := updateInstance (create initial 0) 0 firstPhysical
private def splitBlocks : Forest :=
  [⟨0, .node ⟨(0, .start), some (itemAddress 3)⟩ .nil⟩,
   ⟨10, .node (titleRef 10) (.cons (.node ⟨itemAddress 3, none⟩ .nil) .nil)⟩]
private def firstResult : State :=
  ⟨splitBlocks, (create readyState 10).physical⟩

/-- PASS+FAIL: actual search/detach/append leaves the old root and gives the
new empty title exactly one inherited leaf. It does not keep that leaf below
the old block. -/
theorem atomic_shape_control :
    (split readyState (itemAddress 3) 10).map State.blocks = some splitBlocks ∧
    (split readyState (itemAddress 3) 10).map State.blocks ≠
      some [⟨0, splitNode (itemAddress 3) (freshTitle 0)⟩, ⟨10, freshTitle 10⟩] := by decide

/-- The positive fixture follows the explicit raw transition relation. Its
normal shape and empty inactive title are consequences of the induction. -/
theorem reachable_shape_control : Reach firstResult ∧
    (firstResult.physical 10 = emptyPhysical 10) ∧
    firstResult.blocks ≠ [⟨0, freshTitle 0⟩, ⟨10, freshTitle 10⟩] := by
  refine ⟨?_, rfl, by decide⟩
  apply Reach.split (itemAddress 3) 10
  · apply Reach.update 0 firstPhysical
    · exact Reach.create 0 .init (by simp [initial])
    · exact ⟨⟨0, freshTitle 0⟩, by simp [create, initial], rfl⟩
  · intro block member
    have same : block = ⟨0, freshTitle 0⟩ := by simpa [readyState, updateInstance, create, initial] using member
    subst block
    decide
  · decide
  · rfl

/-- A later marker in the inherited interval routes through the empty title
root to its leaf. Splitting at that boundary preserves the earlier interval. -/
theorem repeated_split_control :
    let updated := updateInstance firstResult 0
      [NotionCorePartition.boundary (0, .start), ⟨itemAddress 1, .text 97 false⟩,
       NotionCorePartition.boundary (itemAddress 3),
       NotionCorePartition.boundary (itemAddress 4), ⟨itemAddress 2, .text 98 false⟩]
    let result := (split updated (itemAddress 4) 11).map State.blocks
    result = some
      [⟨0, .node ⟨(0, .start), some (itemAddress 3)⟩ .nil⟩,
       ⟨10, .node (titleRef 10) (.cons (.node ⟨itemAddress 3, some (itemAddress 4)⟩ .nil) .nil)⟩,
       ⟨11, .node (titleRef 11) (.cons (.node ⟨itemAddress 4, none⟩ .nil) .nil)⟩] ∧
    result ≠ some splitBlocks := by decide

#print axioms splitDetach_normal
#print axioms atomicSplit_result
#print axioms split_preserves
#print axioms reachable_invariant

end Sal.MRDTs.Instances.NotionCoreSliceForest
