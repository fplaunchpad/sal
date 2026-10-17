import Sal.MRDTs.Instances.NotionCorePartition
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Finite source-shaped text-slice trees. Split rewrites old children under
the new right node, then detach/append moves that complete subtree; merge moves
a whole block's tree under the last node of another. Every tree at a
transaction boundary is a chain, and every dead node is the empty title root of
a split destination.
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

def leftRef (ref : Ref) (marker : Address) : Ref := {ref with stop := some marker}
def rightRef (ref : Ref) (marker : Address) : Ref := ⟨marker,ref.stop⟩

theorem preorderTree_eq (tree : Tree) :
    preorderTree tree = tree.slice :: preorderChildren tree.children := by
  cases tree; rfl

mutual
theorem splitTree_refs (physical : Nat → List Atom) (marker : Address)
    (tree next : Tree) (accepted : splitTree physical marker tree = some next) :
    ∃ before ref after, preorderTree tree = before ++ ref :: after ∧
      contains physical ref marker = true ∧
      preorderTree next = before ++ leftRef ref marker :: rightRef ref marker :: after := by
  cases tree with
  | node ref children =>
    by_cases selected : contains physical ref marker = true
    · simp only [splitTree, selected, if_true, Option.some.injEq] at accepted
      subst next
      exact ⟨[],ref,preorderChildren children,rfl,selected,by
        simp [splitNode,preorderTree,preorderChildren,leftRef,rightRef]⟩
    · have rejected : contains physical ref marker = false := Bool.eq_false_iff.mpr selected
      simp only [splitTree, rejected, Bool.false_eq_true, if_false] at accepted
      obtain ⟨changed, step, same⟩ := Option.map_eq_some_iff.mp accepted
      subst next
      obtain ⟨before,chosen,after,old,found,new⟩ := splitChildren_refs physical marker children changed step
      exact ⟨ref::before,chosen,after,by simp [preorderTree,old],found,by simp [preorderTree,new]⟩
theorem splitChildren_refs (physical : Nat → List Atom) (marker : Address)
    (children next : Children) (accepted : splitChildren physical marker children = some next) :
    ∃ before ref after, preorderChildren children = before ++ ref :: after ∧
      contains physical ref marker = true ∧
      preorderChildren next = before ++ leftRef ref marker :: rightRef ref marker :: after := by
  cases children with
  | nil => simp [splitChildren] at accepted
  | cons tree rest =>
    cases selected : splitTree physical marker tree with
    | some changed =>
      simp only [splitChildren,selected,Option.some.injEq] at accepted
      subst next
      obtain ⟨before,ref,after,old,found,new⟩ := splitTree_refs physical marker tree changed selected
      exact ⟨before,ref,after ++ preorderChildren rest,by
        simp [preorderChildren,old,List.append_assoc],found,by
        simp [preorderChildren,new,List.append_assoc]⟩
    | none =>
      simp only [splitChildren,selected] at accepted
      obtain ⟨changed,step,same⟩ := Option.map_eq_some_iff.mp accepted
      subst next
      obtain ⟨before,ref,after,old,found,new⟩ := splitChildren_refs physical marker rest changed step
      exact ⟨preorderTree tree ++ before,ref,after,by
        simp [preorderChildren,old,List.append_assoc],found,by
        simp [preorderChildren,new,List.append_assoc]⟩
end

theorem preorderChildren_append (a b : Children) :
    preorderChildren (a.append b) = preorderChildren a ++ preorderChildren b := by
  cases a with
  | nil => rfl
  | cons tree rest =>
    simp [Children.append,preorderChildren,preorderChildren_append rest b,List.append_assoc]

theorem preorder_appendRoot (tree child : Tree) :
    preorderTree (appendRoot tree child) = preorderTree tree ++ preorderTree child := by
  cases tree
  simp [appendRoot,Tree.slice,Tree.children,preorderTree,preorderChildren,
    preorderChildren_append]

mutual
theorem detachTree_refs (marker : Address) (tree next child : Tree)
    (accepted : detachTree marker tree = some (next,child)) :
    ∃ before after, preorderTree tree = before ++ preorderTree child ++ after ∧
      preorderTree next = before ++ after ∧ child.slice.start = marker := by
  cases tree with
  | node ref children =>
    simp only [detachTree] at accepted
    obtain ⟨result,step,same⟩ := Option.map_eq_some_iff.mp accepted
    have pair := Prod.mk.inj same
    obtain ⟨before,after,old,new,start⟩ := detachChildren_refs marker children result.1 result.2
      (by exact step)
    have nextEq := pair.1
    have childEq := pair.2
    subst next; subst child
    exact ⟨ref::before,after,by simp [preorderTree,old,List.append_assoc],
      by simp [preorderTree,new],start⟩
theorem detachChildren_refs (marker : Address) (children next : Children) (child : Tree)
    (accepted : detachChildren marker children = some (next,child)) :
    ∃ before after, preorderChildren children = before ++ preorderTree child ++ after ∧
      preorderChildren next = before ++ after ∧ child.slice.start = marker := by
  cases children with
  | nil => simp [detachChildren] at accepted
  | cons tree rest =>
    by_cases selected : tree.slice.start = marker
    · simp only [detachChildren,selected,if_true,Option.some.injEq] at accepted
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj accepted
      exact ⟨[],preorderChildren rest,by simp [preorderChildren],rfl,selected⟩
    · simp only [detachChildren,selected,if_false] at accepted
      cases found : detachTree marker tree with
      | some result =>
        simp only [found,Option.some.injEq] at accepted
        obtain ⟨nextEq,childEq⟩ := Prod.mk.inj accepted
        subst next; subst child
        obtain ⟨before,after,old,new,start⟩ := detachTree_refs marker tree result.1 result.2
          (by exact found)
        exact ⟨before,after ++ preorderChildren rest,by
          simp [preorderChildren,old,List.append_assoc],by
          simp [preorderChildren,new,List.append_assoc],start⟩
      | none =>
        simp only [found] at accepted
        obtain ⟨result,step,same⟩ := Option.map_eq_some_iff.mp accepted
        obtain ⟨nextEq,childEq⟩ := Prod.mk.inj same
        subst next; subst child
        obtain ⟨before,after,old,new,start⟩ := detachChildren_refs marker rest result.1 result.2
          (by exact step)
        exact ⟨preorderTree tree ++ before,after,by
          simp [preorderChildren,old,List.append_assoc],by
          simp [preorderChildren,new,List.append_assoc],start⟩
end

/-! Chains. Every tree reachable at a transaction boundary is a chain: split
gives the right node all old children and makes it the left node's only child,
detachment moves a suffix, and merge attaches a chain under the last node of
another chain. A chain is determined by its preorder. -/

/-- Every node has at most one child. -/
inductive Chain : Tree → Prop where
  | leaf (slice : Ref) : Chain (.node slice .nil)
  | link (slice : Ref) (child : Tree) : Chain child → Chain (.node slice (.cons child .nil))

def chainOf : Ref → List Ref → Tree
  | slice, [] => .node slice .nil
  | slice, next :: rest => .node slice (.cons (chainOf next rest) .nil)

theorem preorder_chainOf (slice : Ref) (rest : List Ref) :
    preorderTree (chainOf slice rest) = slice :: rest := by
  induction rest generalizing slice with
  | nil => simp [chainOf, preorderTree, preorderChildren]
  | cons next rest ih => simp [chainOf, preorderTree, preorderChildren, ih]

theorem chainOf_chain (slice : Ref) (rest : List Ref) : Chain (chainOf slice rest) := by
  induction rest generalizing slice with
  | nil => exact .leaf slice
  | cons next rest ih => exact .link slice _ (ih next)

theorem chain_eq {tree : Tree} (chain : Chain tree) :
    tree = chainOf tree.slice (preorderTree tree).tail := by
  induction chain with
  | leaf slice => simp [chainOf, preorderTree, preorderChildren, Tree.slice]
  | link slice child _ ih =>
      rw [preorderTree_eq child, List.tail_cons] at ih
      simp only [preorderTree, preorderChildren, List.append_nil, List.tail_cons, Tree.slice]
      rw [preorderTree_eq child]
      simp only [chainOf]
      rw [← ih]

/-- Two chains with the same preorder are equal. -/
theorem chain_ext {a b : Tree} (left : Chain a) (right : Chain b)
    (same : preorderTree a = preorderTree b) : a = b := by
  have slices : a.slice = b.slice := by
    have heads := congrArg List.head? same
    simpa [preorderTree_eq] using heads
  rw [chain_eq left, chain_eq right, slices, same]

theorem chain_children {slice : Ref} {children : Children} (chain : Chain (.node slice children)) :
    children = .nil ∨ ∃ child, children = .cons child .nil ∧ Chain child := by
  cases chain with
  | leaf => exact Or.inl rfl
  | link _ child rest => exact Or.inr ⟨child, rfl, rest⟩

theorem splitNode_chain (marker : Address) {tree : Tree} (chain : Chain tree) :
    Chain (splitNode marker tree) := by
  cases tree with
  | node slice children =>
    simp only [splitNode]
    apply Chain.link
    rcases chain_children chain with rfl | ⟨child, rfl, rest⟩
    · exact .leaf _
    · exact .link _ _ rest

theorem splitTree_chain (physical : Nat → List Atom) (marker : Address) {tree next : Tree}
    (chain : Chain tree) (accepted : splitTree physical marker tree = some next) : Chain next := by
  induction chain generalizing next with
  | leaf slice =>
    by_cases selected : contains physical slice marker = true
    · simp only [splitTree, selected, if_true, Option.some.injEq] at accepted
      subst next
      exact splitNode_chain marker (.leaf slice)
    · simp [splitTree, splitChildren, selected] at accepted
  | link slice child rest ih =>
    by_cases selected : contains physical slice marker = true
    · simp only [splitTree, selected, if_true, Option.some.injEq] at accepted
      subst next
      exact splitNode_chain marker (.link slice child rest)
    · cases found : splitTree physical marker child with
      | none => simp [splitTree, splitChildren, selected, found] at accepted
      | some changed =>
        simp [splitTree, splitChildren, selected, found] at accepted
        subst next
        exact .link slice changed (ih found)

/-- Detaching from a chain cuts it in two: the remaining prefix and the
moved suffix, both chains. -/
theorem detachTree_chain (marker : Address) {tree next moved : Tree} (chain : Chain tree)
    (accepted : detachTree marker tree = some (next, moved)) :
    Chain next ∧ Chain moved ∧ preorderTree next ++ preorderTree moved = preorderTree tree := by
  induction chain generalizing next moved with
  | leaf slice => simp [detachTree, detachChildren] at accepted
  | link slice child rest ih =>
    by_cases selected : child.slice.start = marker
    · simp only [detachTree, detachChildren, selected, if_true, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨.leaf slice, rest, by simp [preorderTree, preorderChildren]⟩
    · cases found : detachTree marker child with
      | none => simp [detachTree, detachChildren, selected, found] at accepted
      | some result =>
        simp only [detachTree, detachChildren, selected, if_false, found, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        obtain ⟨left, right, joined⟩ := ih found
        exact ⟨.link slice _ left, right, by
          simp [preorderTree, preorderChildren, ← joined]⟩

/-- On a chain, detachment succeeds whenever some non-root node has the
requested start. -/
theorem detachTree_chain_progress (marker : Address) {tree : Tree} (chain : Chain tree)
    (present : marker ∈ (preorderTree tree).tail.map Ref.start) :
    ∃ next moved, detachTree marker tree = some (next, moved) := by
  induction chain with
  | leaf slice => simp [preorderTree, preorderChildren] at present
  | link slice child rest ih =>
    by_cases selected : child.slice.start = marker
    · exact ⟨.node slice .nil, child, by simp [detachTree, detachChildren, selected]⟩
    · have later : marker ∈ (preorderTree child).tail.map Ref.start := by
        have whole : marker ∈ (preorderTree child).map Ref.start := by
          simpa [preorderTree, preorderChildren] using present
        rw [preorderTree_eq child] at whole ⊢
        simp only [List.map_cons, List.mem_cons] at whole
        rcases whole with equal | inside
        · exact False.elim (selected equal.symm)
        · simpa using inside
      obtain ⟨next, moved, found⟩ := ih later
      exact ⟨.node slice (.cons next .nil), moved, by simp [detachTree, detachChildren, selected, found]⟩

mutual
/-- Attach `child` as the last child of the last preorder node. -/
def appendLast : Tree → Tree → Tree
  | .node slice children, child => .node slice (appendLastChildren children child)
def appendLastChildren : Children → Tree → Children
  | .nil, child => .cons child .nil
  | .cons tree .nil, child => .cons (appendLast tree child) .nil
  | .cons tree (.cons next rest), child => .cons tree (appendLastChildren (.cons next rest) child)
end

/-- The last node in preorder; `appendLast` attaches under it. -/
def lastNode (tree : Tree) : Ref := (preorderTree tree).getLast?.getD tree.slice

mutual
theorem preorder_appendLast (tree child : Tree) :
    preorderTree (appendLast tree child) = preorderTree tree ++ preorderTree child := by
  cases tree with
  | node slice children =>
    simp [appendLast, preorderTree, preorder_appendLastChildren children child]
theorem preorder_appendLastChildren (children : Children) (child : Tree) :
    preorderChildren (appendLastChildren children child) = preorderChildren children ++ preorderTree child := by
  match children with
  | .nil => simp [appendLastChildren, preorderChildren]
  | .cons tree .nil =>
    simp [appendLastChildren, preorderChildren, preorder_appendLast tree child]
  | .cons tree (.cons next rest) =>
    simp only [appendLastChildren, preorderChildren]
    rw [preorder_appendLastChildren (.cons next rest) child]
    simp [preorderChildren, List.append_assoc]
end

theorem appendLast_slice (tree child : Tree) : (appendLast tree child).slice = tree.slice := by
  cases tree; rfl

theorem chain_appendLast {tree child : Tree} (chain : Chain tree) (attached : Chain child) :
    Chain (appendLast tree child) := by
  induction chain with
  | leaf slice => exact .link slice child attached
  | link slice inner _ ih =>
    simp only [appendLast, appendLastChildren]
    exact .link slice _ ih

/-- Appending one chain to another concatenates their node lists. -/
theorem appendLast_chainOf (slice : Ref) (rest : List Ref) (next : Ref) (tail : List Ref) :
    appendLast (chainOf slice rest) (chainOf next tail) = chainOf slice (rest ++ next :: tail) := by
  apply chain_ext (chain_appendLast (chainOf_chain _ _) (chainOf_chain _ _)) (chainOf_chain _ _)
  simp [preorder_appendLast, preorder_chainOf]

theorem lastNode_chainOf (slice : Ref) (rest : List Ref) :
    lastNode (chainOf slice rest) = (slice :: rest).getLast (by simp) := by
  simp [lastNode, preorder_chainOf, List.getLast?_eq_some_getLast]


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

theorem normal_chain {bid : Nat} {tree : Tree} (normal : Normal bid tree) : Chain tree := by
  cases normal with
  | own stop => exact .leaf _
  | attached slice => exact .link _ _ (.leaf slice)

/-! Liveness of chain nodes. A node is dead when the next node of its chain
does not open an instance. On reachable forests the dead nodes are exactly the
empty title roots of split destinations, each followed by the moved slice. -/

def opensInstance (ref : Ref) : Bool := decide (ref.start.2 = .start)

/-- Pair each node with its liveness; `last` is the final node's liveness. -/
def tagBefore : List Ref → Bool → List (Ref × Bool)
  | [], _ => []
  | [ref], last => [(ref, last)]
  | ref :: next :: rest, last => (ref, opensInstance next) :: tagBefore (next :: rest) last

/-- Every node of a preorder list with its liveness. The last node is live. -/
def nodes (refs : List Ref) : List (Ref × Bool) := tagBefore refs true

theorem tagBefore_fst (refs : List Ref) (last : Bool) : (tagBefore refs last).map Prod.fst = refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail => simp only [tagBefore, List.map_cons] at ih ⊢; rw [ih]

theorem tagBefore_cons (ref : Ref) (post : List Ref) (last : Bool) :
    tagBefore (ref :: post) last = (ref, (post.head?.map opensInstance).getD last) :: tagBefore post last := by
  cases post <;> rfl

theorem tagBefore_append (pre : List Ref) (ref : Ref) (post : List Ref) (last : Bool) :
    tagBefore (pre ++ ref :: post) last = tagBefore pre (opensInstance ref) ++ tagBefore (ref :: post) last := by
  induction pre with
  | nil => rfl
  | cons head pre ih =>
    cases pre with
    | nil => simp [tagBefore]
    | cons next rest =>
      simp only [List.cons_append] at ih ⊢
      simp only [tagBefore, ih, List.cons_append]

/-- Attaching a chain whose root opens an instance leaves every liveness tag unchanged. -/
theorem nodes_append_open (pre : List Ref) (ref : Ref) (post : List Ref) (opens : opensInstance ref = true) :
    nodes (pre ++ ref :: post) = nodes pre ++ nodes (ref :: post) := by
  simp only [nodes, tagBefore_append, opens]

def emptyPhysical (inst : Nat) : List Atom := [NotionCorePartition.boundary (inst, .start)]

theorem empty_title_rejects (physical : Nat → List Atom) (bid : Nat) (marker : Address)
    (empty : physical bid = emptyPhysical bid) : contains physical (titleRef bid) marker = false := by
  simp [contains, titleRef, empty, emptyPhysical, NotionCorePartition.extractIds,
    NotionCorePartition.ids, NotionCorePartition.boundary,
    NotionCoreSource.Endpoint.extract, NotionCoreSource.Endpoint.afterStart,
    NotionCoreSource.Endpoint.beforeEnd]

def forestRefs (forest : Forest) : List Ref := forest.flatMap fun block => preorderTree block.title

def forestNodes (forest : Forest) : List (Ref × Bool) :=
  forest.flatMap fun block => nodes (preorderTree block.title)

theorem forestNodes_fst (forest : Forest) : (forestNodes forest).map Prod.fst = forestRefs forest := by
  simp [forestNodes, forestRefs, List.map_flatMap, nodes, tagBefore_fst]

theorem node_ref {forest : Forest} {ref : Ref} {live : Bool} (member : (ref, live) ∈ forestNodes forest) :
    ref ∈ forestRefs forest := by
  rw [← forestNodes_fst]
  exact List.mem_map.mpr ⟨_, member, rfl⟩

theorem root_ref {forest : Forest} {block : Block} (member : block ∈ forest) :
    block.title.slice ∈ forestRefs forest :=
  List.mem_flatMap.mpr ⟨block, member, by rw [preorderTree_eq]; simp⟩

/-- Every block title is a chain rooted at the start of the block's own name. -/
def ChainForest (forest : Forest) : Prop :=
  ∀ block ∈ forest, Chain block.title ∧ block.title.slice.start = (block.id, .start)

/-- No node of the forest lies in the named instance. -/
def FreshName (forest : Forest) (name : Nat) : Prop := ∀ ref ∈ forestRefs forest, ref.start.1 ≠ name

theorem fresh_name_absent {forest : Forest} {name : Nat} (chains : ChainForest forest)
    (fresh : FreshName forest name) : name ∉ forest.map Block.id := by
  intro member
  obtain ⟨block, present, rfl⟩ := List.mem_map.mp member
  exact fresh _ (root_ref present) (by rw [(chains block present).2])

/-- Every dead node is the empty title root of its own instance, and no live
node lies in that instance. -/
def EmptyInactive (physical : Nat → List Atom) (forest : Forest) : Prop :=
  ∀ dead, (dead, false) ∈ forestNodes forest →
    dead = titleRef dead.start.1 ∧ physical dead.start.1 = emptyPhysical dead.start.1 ∧
    ∀ live, (live, true) ∈ forestNodes forest → live.start.1 ≠ dead.start.1

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

theorem detach_fresh_none (marker : Address) (tree : Tree) (fresh : marker ∉ keys tree) :
    detachTree marker tree = none := by
  cases found : detachTree marker tree with
  | none => rfl
  | some result =>
    obtain ⟨before, after, shape, _, start⟩ := detachTree_refs marker tree result.1 result.2 found
    exact False.elim (fresh (by
      rw [keys, shape, preorderTree_eq result.2]
      simp [start]))

/-- The unique element satisfying a predicate fixes the decomposition. -/
private theorem split_unique {α : Type} (P : α → Prop) {l1 l2 p q : List α} {a b : α}
    (equal : l1 ++ a :: l2 = p ++ b :: q) (holds : P a) (others : ∀ y ∈ p ++ q, ¬ P y) :
    l1 = p ∧ a = b ∧ l2 = q := by
  induction l1 generalizing p with
  | nil =>
    cases p with
    | nil => simpa using equal
    | cons c rest =>
      have same := (List.cons.inj equal).1
      exact False.elim (others c (by simp) (same ▸ holds))
  | cons c l1 ih =>
    cases p with
    | nil =>
      have tail := (List.cons.inj equal).2
      exact False.elim (others a (by simp [← tail]) holds)
    | cons d rest =>
      obtain ⟨same, tail⟩ := List.cons.inj equal
      obtain ⟨first, middle, last⟩ := ih tail (fun y member => others y (by
        simp only [List.cons_append, List.mem_cons, List.mem_append] at member ⊢
        tauto))
      exact ⟨by rw [same, first], middle, last⟩

/-- The search splits the first containing node of a chain, and detachment
moves exactly the suffix chain that begins at the new right node. -/
theorem splitForest_detach (physical : Nat → List Atom) (marker : Address) (forest divided : Forest)
    (chains : ∀ block ∈ forest, Chain block.title) (fresh : FreshMarker forest marker)
    (accepted : splitForest physical marker forest = some divided) :
    ∃ before block after pre ref post title moved,
      forest = before ++ block :: after ∧ preorderTree block.title = pre ++ ref :: post ∧
      contains physical ref marker = true ∧
      Chain title ∧ preorderTree title = pre ++ [leftRef ref marker] ∧
      Chain moved ∧ preorderTree moved = rightRef ref marker :: post ∧
      detachForest marker divided = some (before ++ {block with title := title} :: after, moved) := by
  induction forest generalizing divided with
  | nil => simp [splitForest] at accepted
  | cons block rest ih =>
    have headChain := chains block (by simp)
    have headFresh := fresh block (by simp)
    cases selected : splitTree physical marker block.title with
    | some changed =>
      simp only [splitForest, selected, Option.some.injEq] at accepted
      subst divided
      obtain ⟨pre, ref, post, old, found, new⟩ := splitTree_refs physical marker block.title changed selected
      have changedChain := splitTree_chain physical marker headChain selected
      have present : marker ∈ (preorderTree changed).tail.map Ref.start := by
        rw [new]
        cases pre <;> simp [rightRef]
      obtain ⟨title, moved, detached⟩ := detachTree_chain_progress marker changedChain present
      obtain ⟨titleChain, movedChain, joined⟩ := detachTree_chain marker changedChain detached
      obtain ⟨_, _, _, _, start⟩ := detachTree_refs marker changed title moved detached
      have others : ∀ y ∈ (pre ++ [leftRef ref marker]) ++ post, ¬ y.start = marker := by
        intro y member equal
        apply headFresh
        rw [keys, old]
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with (member | rfl) | member
        · exact List.mem_map.mpr ⟨y, by simp [member], equal⟩
        · exact List.mem_map.mpr ⟨ref, by simp, equal⟩
        · exact List.mem_map.mpr ⟨y, by simp [member], equal⟩
      rw [new, preorderTree_eq moved] at joined
      obtain ⟨titleEq, slice, rest'⟩ := split_unique (fun y : Ref => y.start = marker)
        (l1 := preorderTree title) (p := pre ++ [leftRef ref marker])
        (by simpa [List.append_assoc] using joined) start others
      refine ⟨[], block, rest, pre, ref, post, title, moved, rfl, old, found, titleChain, titleEq,
        movedChain, ?_, ?_⟩
      · rw [preorderTree_eq moved, slice, rest']
      · simp [detachForest, detached]
    | none =>
      simp only [splitForest, selected] at accepted
      obtain ⟨tail, step, same⟩ := Option.map_eq_some_iff.mp accepted
      subst divided
      obtain ⟨before, found, after, pre, ref, post, title, moved, shape, old, inside, titleChain,
        titleEq, movedChain, movedEq, detached⟩ :=
        ih tail (fun b hb => chains b (List.mem_cons_of_mem _ hb))
          (fun b hb => fresh b (List.mem_cons_of_mem _ hb)) step
      refine ⟨block :: before, found, after, pre, ref, post, title, moved, by simp [shape], old, inside,
        titleChain, titleEq, movedChain, movedEq, ?_⟩
      simp [detachForest, detach_fresh_none marker block.title headFresh, detached]

theorem splitDetach_chain (physical : Nat → List Atom) (marker : Address)
    (forest remaining : Forest) (moved : Tree)
    (chains : ∀ block ∈ forest, Chain block.title) (fresh : FreshMarker forest marker)
    (accepted : splitDetach physical marker forest = some (remaining, moved)) :
    ∃ before block after pre ref post title,
      forest = before ++ block :: after ∧ preorderTree block.title = pre ++ ref :: post ∧
      contains physical ref marker = true ∧
      Chain title ∧ preorderTree title = pre ++ [leftRef ref marker] ∧
      Chain moved ∧ preorderTree moved = rightRef ref marker :: post ∧
      remaining = before ++ {block with title := title} :: after := by
  cases divided : splitForest physical marker forest with
  | none => simp [splitDetach, divided] at accepted
  | some split =>
    obtain ⟨before, block, after, pre, ref, post, title, moved', shape, old, inside, titleChain,
      titleEq, movedChain, movedEq, detached⟩ :=
      splitForest_detach physical marker forest split chains fresh divided
    simp only [splitDetach, divided, Option.bind_eq_bind, Option.bind_some, detached,
      Option.some.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨before, block, after, pre, ref, post, title, shape, old, inside, titleChain, titleEq,
      movedChain, movedEq, rfl⟩

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

/-- Exact shape of every successful atomic tree split. The containing node and
the moved suffix chain are derived by the forest search and detachment
algorithms; the fresh destination's empty title root receives the suffix. -/
theorem atomicSplit_result (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest result : Forest) (chains : ∀ block ∈ forest, Chain block.title)
    (fresh : FreshMarker forest marker) (freshTarget : target ∉ forest.map Block.id)
    (empty : physical target = emptyPhysical target)
    (accepted : atomicSplit physical marker target forest = some result) :
    ∃ before block after pre ref post title moved,
      forest = before ++ block :: after ∧ preorderTree block.title = pre ++ ref :: post ∧
      contains physical ref marker = true ∧
      Chain title ∧ preorderTree title = pre ++ [leftRef ref marker] ∧
      Chain moved ∧ preorderTree moved = rightRef ref marker :: post ∧
      result = (before ++ {block with title := title} :: after) ++
        [⟨target, .node (titleRef target) (.cons moved .nil)⟩] := by
  rw [atomicSplit_route physical marker target forest empty] at accepted
  obtain ⟨pair, divided, equal⟩ := Option.map_eq_some_iff.mp accepted
  rcases pair with ⟨remaining, moved⟩
  obtain ⟨before, block, after, pre, ref, post, title, shape, old, inside, titleChain, titleEq,
    movedChain, movedEq, remainingEq⟩ :=
    splitDetach_chain physical marker forest remaining moved chains fresh divided
  have sameIds : remaining.map Block.id = forest.map Block.id := by simp [remainingEq, shape]
  have freshRemaining : target ∉ remaining.map Block.id := sameIds ▸ freshTarget
  rw [appendToBlock_fresh remaining target moved freshRemaining] at equal
  refine ⟨before, block, after, pre, ref, post, title, moved, shape, old, inside, titleChain, titleEq,
    movedChain, movedEq, ?_⟩
  rw [← equal, remainingEq]
  rfl

structure State where
  blocks : Forest
  physical : Nat → List Atom

def Invariant (state : State) : Prop :=
  ChainForest state.blocks ∧ (state.blocks.map Block.id).Nodup ∧
    EmptyInactive state.physical state.blocks

def write (physical : Nat → List Atom) (inst : Nat) (items : List Atom) : Nat → List Atom :=
  fun other => if other = inst then items else physical other

def create (state : State) (bid : Nat) : State :=
  ⟨state.blocks ++ [⟨bid, freshTitle bid⟩], write state.physical bid (emptyPhysical bid)⟩

def updateInstance (state : State) (inst : Nat) (items : List Atom) : State :=
  {state with physical := write state.physical inst items}

theorem forestNodes_append (a b : Forest) : forestNodes (a ++ b) = forestNodes a ++ forestNodes b := by
  simp [forestNodes]

theorem forestRefs_append (a b : Forest) : forestRefs (a ++ b) = forestRefs a ++ forestRefs b := by
  simp [forestRefs]

theorem forestNodes_fresh (bid : Nat) : forestNodes [⟨bid, freshTitle bid⟩] = [(titleRef bid, true)] := by
  simp [forestNodes, freshTitle, preorderTree, preorderChildren, nodes, tagBefore]

theorem create_preserves (state : State) (bid : Nat) (invariant : Invariant state)
    (fresh : FreshName state.blocks bid) : Invariant (create state bid) := by
  obtain ⟨chains, unique, empty⟩ := invariant
  have absent := fresh_name_absent chains fresh
  refine ⟨?_, ?_, ?_⟩
  · intro block member
    rcases List.mem_append.mp member with member | member
    · exact chains block member
    · have equal := List.mem_singleton.mp member
      subst block
      exact ⟨.leaf _, rfl⟩
  · simpa [create] using List.nodup_append'.mpr ⟨unique, by simp,
      List.disjoint_left.mpr fun id old new => absent (by rw [List.mem_singleton.mp new] at old; exact old)⟩
  · intro dead member
    simp only [create, forestNodes_append, forestNodes_fresh, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at member
    rcases member with member | ⟨_, contra⟩
    · obtain ⟨form, physicalEq, lives⟩ := empty dead member
      have other : dead.start.1 ≠ bid := fresh dead (node_ref member)
      refine ⟨form, by simpa [create, write, other] using physicalEq, ?_⟩
      intro live liveMember
      simp only [create, forestNodes_append, forestNodes_fresh, List.mem_append,
        List.mem_singleton, Prod.mk.injEq] at liveMember
      rcases liveMember with liveMember | ⟨rfl, _⟩
      · exact lives live liveMember
      · exact fun equal => other (by simpa [titleRef] using equal.symm)
    · simp at contra

/-- RGA insertion/deletion changes one live instance and does not touch the
slice forest. The update's actual contents are abstract here; the frame theorem
uses only the instance addressed by the operation, not a desired text result. -/
theorem updateInstance_preserves (state : State) (inst : Nat) (items : List Atom)
    (invariant : Invariant state)
    (owned : ∃ live, (live, true) ∈ forestNodes state.blocks ∧ live.start.1 = inst) :
    Invariant (updateInstance state inst items) := by
  refine ⟨invariant.1, invariant.2.1, ?_⟩
  obtain ⟨live, member, equal⟩ := owned
  intro dead deadMember
  obtain ⟨form, physicalEq, lives⟩ := invariant.2.2 dead deadMember
  have different : dead.start.1 ≠ inst := fun same => lives live member (equal.trans same.symm)
  exact ⟨form, by simpa [updateInstance, write, different] using physicalEq, lives⟩

/-- Create the fresh title before the actual source tree phases. The physical
marker insertion is an instance update and is supplied before this operation. -/
def split (state : State) (marker : Address) (target : Nat) : Option State :=
  let physical := (create state target).physical
  (atomicSplit physical marker target state.blocks).map fun blocks => ⟨blocks, physical⟩

private theorem slice_of_preorder {a b : Tree} {pre rest rest' : List Ref} {x y : Ref}
    (left : preorderTree a = pre ++ x :: rest) (right : preorderTree b = pre ++ y :: rest')
    (same : x.start = y.start) : a.slice.start = b.slice.start := by
  rw [preorderTree_eq] at left right
  cases pre with
  | nil =>
    have ha := (List.cons.inj left).1
    have hb := (List.cons.inj right).1
    simp [ha, hb, same]
  | cons head tail =>
    rw [(List.cons.inj left).1, (List.cons.inj right).1]

/-- Split keeps every old node's liveness: the containing node, which is
live, is replaced by its two live halves, and the destination's empty title
root is the only new dead node. -/
theorem atomicSplit_nodes (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest result : Forest) (chains : ChainForest forest)
    (fresh : FreshMarker forest marker) (freshTarget : target ∉ forest.map Block.id)
    (empty : physical target = emptyPhysical target) (markerEvent : marker.2 ≠ .start)
    (deadRejects : ∀ dead, (dead, false) ∈ forestNodes forest → contains physical dead marker = false)
    (accepted : atomicSplit physical marker target forest = some result) :
    ∃ ref, (ref, true) ∈ forestNodes forest ∧ contains physical ref marker = true ∧
      (∀ node ∈ forestNodes result, node ∈ forestNodes forest ∨ node = (leftRef ref marker, true) ∨
        node = (titleRef target, false) ∨ node = (rightRef ref marker, true)) ∧
      (∀ node ∈ forestNodes forest, node ∈ forestNodes result ∨ node = (ref, true)) ∧
      (leftRef ref marker, true) ∈ forestNodes result ∧ (titleRef target, false) ∈ forestNodes result ∧
      (rightRef ref marker, true) ∈ forestNodes result ∧ ChainForest result ∧
      result.map Block.id = forest.map Block.id ++ [target] := by
  obtain ⟨before, block, after, pre, ref, post, title, moved, shape, old, inside, titleChain, titleEq,
    movedChain, movedEq, resultEq⟩ :=
    atomicSplit_result physical marker target forest result (fun b hb => (chains b hb).1)
      fresh freshTarget empty accepted
  subst resultEq
  have blockMember : block ∈ forest := by rw [shape]; simp
  have oldNodes : forestNodes forest = forestNodes before ++
      (tagBefore pre (opensInstance ref) ++
        (ref, (post.head?.map opensInstance).getD true) :: tagBefore post true) ++
      forestNodes after := by
    rw [shape]
    simp [forestNodes, old, nodes, tagBefore_append, tagBefore_cons]
  have live : (post.head?.map opensInstance).getD true = true := by
    cases flag : (post.head?.map opensInstance).getD true with
    | true => rfl
    | false =>
      have deadMember : (ref, false) ∈ forestNodes forest := by
        rw [oldNodes]; simp [flag]
      rw [deadRejects ref deadMember] at inside
      contradiction
  have markerOpens : opensInstance (rightRef ref marker) = false := by
    simp [opensInstance, rightRef, markerEvent]
  have leftOpens : opensInstance (leftRef ref marker) = opensInstance ref := rfl
  have newNodes : forestNodes ((before ++ {block with title := title} :: after) ++
      [⟨target, .node (titleRef target) (.cons moved .nil)⟩]) =
      (forestNodes before ++ (tagBefore pre (opensInstance ref) ++ [(leftRef ref marker, true)]) ++
        forestNodes after) ++
      ((titleRef target, false) :: (rightRef ref marker, true) :: tagBefore post true) := by
    have targetPreorder : preorderTree (.node (titleRef target) (.cons moved .nil)) =
        titleRef target :: rightRef ref marker :: post := by
      simp [preorderTree, preorderChildren, movedEq]
    simp only [forestNodes_append, List.append_assoc]
    simp [forestNodes, titleEq, targetPreorder, nodes, tagBefore_append, tagBefore_cons, markerOpens,
      leftOpens, live, tagBefore]
  refine ⟨ref, by rw [oldNodes]; simp [live], inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro node member
    rw [newNodes] at member
    rw [oldNodes]
    simp only [List.mem_append, List.mem_cons] at member ⊢
    tauto
  · intro node member
    rw [newNodes]
    rw [oldNodes, live] at member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    tauto
  · rw [newNodes]; simp
  · rw [newNodes]; simp
  · rw [newNodes]; simp
  · intro found member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | rfl | member) | rfl
    · exact chains found (by rw [shape]; simp [member])
    · refine ⟨titleChain, ?_⟩
      rw [← (chains block blockMember).2]
      exact slice_of_preorder titleEq old rfl
    · exact chains found (by rw [shape]; simp [member])
    · exact ⟨.link _ _ movedChain, rfl⟩
  · simp [shape]

theorem split_preserves (state result : State) (marker : Address) (target : Nat)
    (invariant : Invariant state) (fresh : FreshMarker state.blocks marker)
    (markerEvent : marker.2 ≠ .start)
    (freshTarget : FreshName state.blocks target)
    (accepted : split state marker target = some result) : Invariant result := by
  obtain ⟨chains, unique, empty⟩ := invariant
  let physical := (create state target).physical
  have emptyTarget : physical target = emptyPhysical target := by simp [physical, create, write]
  have absent := fresh_name_absent chains freshTarget
  have physicalOld : ∀ inst, inst ≠ target → physical inst = state.physical inst := by
    intro inst different
    simp [physical, create, write, different]
  have deadRejects : ∀ dead, (dead, false) ∈ forestNodes state.blocks →
      contains physical dead marker = false := by
    intro dead member
    obtain ⟨form, physicalEq, _⟩ := empty dead member
    have other : dead.start.1 ≠ target := freshTarget dead (node_ref member)
    rw [form]
    exact empty_title_rejects physical _ marker ((physicalOld _ other).trans physicalEq)
  obtain ⟨blocks, executed, equal⟩ := Option.map_eq_some_iff.mp accepted
  cases equal
  obtain ⟨ref, refLive, inside, classify, -, -, -, -, chainsNext, ids⟩ :=
    atomicSplit_nodes physical marker target state.blocks blocks chains fresh absent emptyTarget
      markerEvent deadRejects executed
  have refInstance : ref.start.1 ≠ target := freshTarget ref (node_ref refLive)
  have sameInstance : ref.start.1 = marker.1 :=
    (Bool.and_eq_true_iff.mp inside).1 |> of_decide_eq_true
  refine ⟨chainsNext, ?_, ?_⟩
  · change (blocks.map Block.id).Nodup
    rw [ids]
    exact List.nodup_append'.mpr ⟨unique, by simp,
      List.disjoint_left.mpr fun id old new => absent (by rw [List.mem_singleton.mp new] at old; exact old)⟩
  · intro dead deadMember
    have liveSource : ∀ live, (live, true) ∈ forestNodes blocks →
        (live, true) ∈ forestNodes state.blocks ∨ live.start.1 = ref.start.1 := by
      intro live member
      rcases classify _ member with old | equal | equal | equal
      · exact Or.inl old
      · exact Or.inr (by simp [(Prod.mk.inj equal).1, leftRef])
      · simp at equal
      · exact Or.inr (by rw [(Prod.mk.inj equal).1]; exact sameInstance.symm)
    rcases classify _ deadMember with old | equal | equal | equal
    · obtain ⟨form, physicalEq, lives⟩ := empty dead old
      have other : dead.start.1 ≠ target := freshTarget dead (node_ref old)
      refine ⟨form, (physicalOld _ other).trans physicalEq, ?_⟩
      intro live member
      rcases liveSource live member with prior | sameInstance
      · exact lives live prior
      · rw [sameInstance]; exact lives ref refLive
    · simp at equal
    · obtain ⟨rfl, -⟩ := Prod.mk.inj equal
      refine ⟨rfl, emptyTarget, ?_⟩
      intro live member
      rcases liveSource live member with prior | sameInstance
      · exact freshTarget live (node_ref prior)
      · rw [sameInstance]; exact refInstance
    · simp at equal

/-! Merge. The holder of a block name is the block whose chain contains that
name's title root; title roots move with merges, so the holder of a merged
block is the block that absorbed it. -/

def holderOf (forest : Forest) (target : Nat) : Option Block :=
  forest.find? fun block => (preorderTree block.title).any fun ref => ref.start == (target, .start)

/-- Move the source block's whole chain under the last node of the target's
holder and drop the source block. A missing source or holder, or a holder that
is the source itself, leaves the forest unchanged. -/
def mergeForest (forest : Forest) (source target : Nat) : Forest :=
  match forest.find? (fun block => block.id == source), holderOf forest target with
  | some moved, some holder =>
      if holder.id = source then forest
      else (forest.filter fun block => block.id != source).map fun block =>
        if block.id = holder.id then {block with title := appendLast block.title moved.title} else block
  | _, _ => forest

theorem mergeForest_cases (forest : Forest) (source target : Nat) :
    mergeForest forest source target = forest ∨
      ∃ moved holder, moved ∈ forest ∧ holder ∈ forest ∧ moved.id = source ∧ holder.id ≠ source ∧
        holderOf forest target = some holder ∧
        mergeForest forest source target = (forest.filter fun block => block.id != source).map fun block =>
          if block.id = holder.id then {block with title := appendLast block.title moved.title} else block := by
  unfold mergeForest
  cases foundSource : forest.find? (fun block => block.id == source) with
  | none => exact Or.inl rfl
  | some moved =>
    cases foundHolder : holderOf forest target with
    | none => exact Or.inl rfl
    | some holder =>
      by_cases same : holder.id = source
      · exact Or.inl (by simp [same])
      · refine Or.inr ⟨moved, holder, List.mem_of_find?_eq_some foundSource,
          List.mem_of_find?_eq_some foundHolder, by simpa using List.find?_some foundSource, same,
          rfl, by simp [same]⟩

private theorem unique_id {forest : Forest} (unique : (forest.map Block.id).Nodup)
    {a b : Block} (ha : a ∈ forest) (hb : b ∈ forest) (same : a.id = b.id) : a = b := by
  induction forest with
  | nil => simp at ha
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨b, hb, same.symm⟩))
    · exact False.elim (unique.1 (List.mem_map.mpr ⟨a, ha, same⟩))
    · exact ih unique.2 ha hb

private theorem merged_nodes {forest : Forest} {moved holder : Block}
    (chains : ChainForest forest) (movedMember : moved ∈ forest) (block : Block) :
    nodes (preorderTree (if block.id = holder.id then
      {block with title := appendLast block.title moved.title} else block).title) =
      nodes (preorderTree block.title) ++
        (if block.id = holder.id then nodes (preorderTree moved.title) else []) := by
  by_cases selected : block.id = holder.id
  · have opens : opensInstance moved.title.slice = true := by
      simp [opensInstance, (chains moved movedMember).2]
    simp only [selected, ↓reduceIte, preorder_appendLast]
    rw [preorderTree_eq moved.title, nodes_append_open _ _ _ opens]
  · simp [selected]

/-- Merge moves nodes between chains without changing any node's liveness. -/
theorem mergeForest_nodes (forest : Forest) (source target : Nat)
    (chains : ChainForest forest) (unique : (forest.map Block.id).Nodup) (node : Ref × Bool) :
    node ∈ forestNodes (mergeForest forest source target) ↔ node ∈ forestNodes forest := by
  rcases mergeForest_cases forest source target with same | ⟨moved, holder, movedMember, holderMember,
    movedId, distinct, _, merged⟩
  · rw [same]
  · rw [merged]
    simp only [forestNodes, List.flatMap_map, List.mem_flatMap, List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨block, ⟨member, _⟩, inside⟩
      rw [merged_nodes chains movedMember block] at inside
      rcases List.mem_append.mp inside with inside | inside
      · exact ⟨block, member, inside⟩
      · split at inside
        · exact ⟨moved, movedMember, inside⟩
        · simp at inside
    · rintro ⟨block, member, inside⟩
      by_cases isSource : block.id = source
      · have same := unique_id unique member movedMember (isSource.trans movedId.symm)
        subst block
        refine ⟨holder, ⟨holderMember, distinct⟩, ?_⟩
        rw [merged_nodes chains movedMember holder]
        simp [inside]
      · refine ⟨block, ⟨member, by simpa using isSource⟩, ?_⟩
        rw [merged_nodes chains movedMember block]
        exact List.mem_append_left _ inside

private theorem flatMap_append_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left (f x) ((List.Perm.append_left (g x) ih).trans ?_)
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

private theorem flatMap_single {α β : Type} (xs : List α) (key : α → Nat) (k : Nat) (item : α)
    (unique : (xs.map key).Nodup) (member : item ∈ xs) (hit : key item = k) (value : List β) :
    (xs.flatMap fun x => if key x = k then value else []) = value := by
  obtain ⟨left, right, rfl⟩ := List.append_of_mem member
  have absent := List.nodup_middle.mp (by simpa using unique)
  simp only [List.nodup_cons, List.mem_append, not_or] at absent
  have leftNone : ∀ x ∈ left, key x ≠ k := fun x hx equal =>
    absent.1.1 (List.mem_map.mpr ⟨x, hx, equal.trans hit.symm⟩)
  have rightNone : ∀ x ∈ right, key x ≠ k := fun x hx equal =>
    absent.1.2 (List.mem_map.mpr ⟨x, hx, equal.trans hit.symm⟩)
  simp only [List.flatMap_append, List.flatMap_cons, hit, ↓reduceIte]
  rw [List.flatMap_eq_nil_iff.mpr (fun x hx => by simp [leftNone x hx]),
    List.flatMap_eq_nil_iff.mpr (fun x hx => by simp [rightNone x hx])]
  simp

/-- Merge moves the source's nodes into the holder: the multiset of nodes is
unchanged. -/
theorem mergeForest_refs (forest : Forest) (source target : Nat)
    (unique : (forest.map Block.id).Nodup) :
    (forestRefs (mergeForest forest source target)).Perm (forestRefs forest) := by
  rcases mergeForest_cases forest source target with same | ⟨moved, holder, movedMember, holderMember,
    movedId, distinct, _, merged⟩
  · rw [same]
  · rw [merged]
    let kept := forest.filter fun block => block.id != source
    have keptUnique : (kept.map Block.id).Nodup :=
      (List.Sublist.map Block.id List.filter_sublist).nodup unique
    have holderKept : holder ∈ kept := List.mem_filter.mpr ⟨holderMember, by simpa using distinct⟩
    have dropped : (forest.filter fun block => !(block.id != source)) = [moved] := by
      obtain ⟨left, right, shape⟩ := List.append_of_mem movedMember
      have absent := List.nodup_middle.mp (by simpa [shape] using unique)
      simp only [List.nodup_cons, List.mem_append, not_or] at absent
      rw [shape]
      have leftNone : ∀ x ∈ left, x.id ≠ source := fun x hx equal =>
        absent.1.1 (List.mem_map.mpr ⟨x, hx, equal.trans movedId.symm⟩)
      have rightNone : ∀ x ∈ right, x.id ≠ source := fun x hx equal =>
        absent.1.2 (List.mem_map.mpr ⟨x, hx, equal.trans movedId.symm⟩)
      simp only [List.filter_append, List.filter_cons, movedId, bne_self_eq_false, Bool.not_false,
        ↓reduceIte]
      rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [leftNone x hx]),
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [rightNone x hx])]
      rfl
    have newRefs : forestRefs (kept.map fun block =>
        if block.id = holder.id then {block with title := appendLast block.title moved.title} else block) =
        kept.flatMap fun block => preorderTree block.title ++
          (if block.id = holder.id then preorderTree moved.title else []) := by
      simp only [forestRefs, List.flatMap_map]
      congr 1
      funext block
      by_cases selected : block.id = holder.id <;> simp [selected, preorder_appendLast]
    change (forestRefs (kept.map _)).Perm _
    rw [newRefs]
    refine (flatMap_append_perm kept _ _).trans ?_
    rw [flatMap_single kept Block.id holder.id holder keptUnique holderKept rfl]
    have whole : (forestRefs kept ++ forestRefs [moved]).Perm (forestRefs forest) := by
      rw [← dropped, ← forestRefs_append]
      exact (List.filter_append_perm _ forest).flatMap_right _
    simpa [forestRefs] using whole

theorem mergeForest_ids (forest : Forest) (source target : Nat) :
    List.Sublist ((mergeForest forest source target).map Block.id) (forest.map Block.id) := by
  rcases mergeForest_cases forest source target with same | ⟨moved, holder, -, -, -, -, -, merged⟩
  · rw [same]
  · rw [merged, List.map_map]
    have ids : (Block.id ∘ fun block => if block.id = holder.id then
        {block with title := appendLast block.title moved.title} else block) = Block.id := by
      funext block; simp only [Function.comp_apply]; split <;> rfl
    rw [ids]
    exact List.Sublist.map Block.id List.filter_sublist

/-- The holder's chain becomes its old nodes followed by the source's. -/
theorem mergeForest_holder (forest : Forest) (source target : Nat) (moved holder : Block)
    (unique : (forest.map Block.id).Nodup) (movedMember : moved ∈ forest) (movedId : moved.id = source)
    (found : holderOf forest target = some holder) (distinct : holder.id ≠ source) :
    {holder with title := appendLast holder.title moved.title} ∈ mergeForest forest source target ∧
      preorderTree (appendLast holder.title moved.title) =
        preorderTree holder.title ++ preorderTree moved.title ∧
      moved.id ∉ (mergeForest forest source target).map Block.id := by
  have sourceFound : forest.find? (fun block => block.id == source) = some moved := by
    obtain ⟨left, right, shape⟩ := List.append_of_mem movedMember
    have absent := List.nodup_middle.mp (by simpa [shape] using unique)
    simp only [List.nodup_cons, List.mem_append, not_or] at absent
    rw [shape, List.find?_append, List.find?_eq_none.mpr (fun x hx => by
      simpa [← movedId] using fun equal => absent.1.1 (List.mem_map.mpr ⟨x, hx, equal⟩))]
    simp [movedId]
  have holderMember := List.mem_of_find?_eq_some found
  have merged : mergeForest forest source target = (forest.filter fun block => block.id != source).map
      fun block => if block.id = holder.id then
        {block with title := appendLast block.title moved.title} else block := by
    simp [mergeForest, sourceFound, found, distinct]
  refine ⟨?_, preorder_appendLast _ _, ?_⟩
  · rw [merged]
    exact List.mem_map.mpr ⟨holder, List.mem_filter.mpr ⟨holderMember, by simpa using distinct⟩, by simp⟩
  · intro member
    rw [merged, List.map_map] at member
    obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp blockMember).2
    have sameId : block.id = moved.id := by
      simp only [Function.comp_apply] at equal
      split at equal <;> exact equal
    simp [sameId, movedId] at different

theorem merge_preserves (state : State) (source target : Nat) (invariant : Invariant state) :
    Invariant {state with blocks := mergeForest state.blocks source target} := by
  obtain ⟨chains, unique, empty⟩ := invariant
  refine ⟨?_, (mergeForest_ids state.blocks source target).nodup unique, ?_⟩
  · rcases mergeForest_cases state.blocks source target with same | ⟨moved, holder, movedMember,
      holderMember, -, -, -, merged⟩
    · simpa only [same] using chains
    · intro block member
      simp only [merged, List.mem_map, List.mem_filter] at member
      obtain ⟨old, ⟨oldMember, _⟩, rfl⟩ := member
      by_cases selected : old.id = holder.id
      · simp only [selected, ↓reduceIte]
        exact ⟨chain_appendLast (chains old oldMember).1 (chains moved movedMember).1,
          by simpa [appendLast_slice, selected] using (chains old oldMember).2⟩
      · simp only [selected, ↓reduceIte]
        exact chains old oldMember
  · intro dead member
    have nodesEq := mergeForest_nodes state.blocks source target chains unique
    obtain ⟨form, physicalEq, lives⟩ := empty dead ((nodesEq _).mp member)
    exact ⟨form, physicalEq, fun live liveMember => lives live ((nodesEq _).mp liveMember)⟩

def initial : State := ⟨[], emptyPhysical⟩

/-- Guards concern fresh names and the instance addressed by an operation.
No tree-shape, empty-root or expected-observation predicate is an input.
Merge has no guard. -/
inductive Reach : State → Prop where
  | init : Reach initial
  | create {state : State} (bid : Nat) : Reach state →
      FreshName state.blocks bid → Reach (create state bid)
  | update {state : State} (inst : Nat) (items : List Atom) : Reach state →
      (∃ live, (live, true) ∈ forestNodes state.blocks ∧ live.start.1 = inst) →
      Reach (updateInstance state inst items)
  | split {state result : State} (marker : Address) (target : Nat) : Reach state →
      FreshMarker state.blocks marker → marker.2 ≠ .start → FreshName state.blocks target →
      split state marker target = some result → Reach result
  | merge {state : State} (source target : Nat) : Reach state →
      Reach {state with blocks := mergeForest state.blocks source target}

theorem reachable_invariant {state : State} (reachable : Reach state) : Invariant state := by
  induction reachable with
  | init => exact ⟨by simp [initial, ChainForest], by simp [initial],
      by simp [EmptyInactive, initial, forestNodes]⟩
  | create bid _ fresh ih => exact create_preserves _ bid ih fresh
  | update inst items _ owned ih => exact updateInstance_preserves _ inst items ih owned
  | split marker target _ fresh event freshTarget accepted ih =>
      exact split_preserves _ _ marker target ih fresh event freshTarget accepted
  | merge source target _ ih => exact merge_preserves _ source target ih

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
chain shape and empty dead title are consequences of the induction. -/
theorem reachable_shape_control : Reach firstResult ∧
    (firstResult.physical 10 = emptyPhysical 10) ∧
    firstResult.blocks ≠ [⟨0, freshTitle 0⟩, ⟨10, freshTitle 10⟩] := by
  refine ⟨?_, rfl, by decide⟩
  apply Reach.split (itemAddress 3) 10
  · apply Reach.update 0 firstPhysical
    · exact Reach.create 0 .init (by simp [FreshName, forestRefs, initial])
    · exact ⟨titleRef 0, by decide, rfl⟩
  · intro block member
    have same : block = ⟨0, freshTitle 0⟩ := by simpa [readyState, updateInstance, create, initial] using member
    subst block
    decide
  · simp [itemAddress]
  · intro ref member
    simp [updateInstance, create, initial, forestRefs, freshTitle, preorderTree,
      preorderChildren] at member
    simp [member, titleRef]
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

private def mergedBack : Forest :=
  [⟨0, chainOf ⟨(0, .start), some (itemAddress 3)⟩ [titleRef 10, ⟨itemAddress 3, none⟩]⟩]

/-- PASS+FAIL: merging the split destination back moves its whole chain,
dead title root included, under the source's last node. The merged block is
gone; its text is not dropped and the target is not emptied. -/
theorem merge_back_control :
    mergeForest splitBlocks 10 0 = mergedBack ∧
    mergeForest splitBlocks 10 0 ≠ [⟨0, .node ⟨(0, .start), some (itemAddress 3)⟩ .nil⟩] ∧
    mergeForest splitBlocks 10 0 ≠ splitBlocks := by decide

/-- PASS+FAIL: a merge into a merged-away block lands in its absorber, and a
merge whose holder is the source itself is a no-op rather than a removal. -/
theorem merge_absorbed_control :
    let three : Forest := [⟨0, freshTitle 0⟩, ⟨1, freshTitle 1⟩, ⟨2, freshTitle 2⟩]
    let first := mergeForest three 1 0
    mergeForest first 2 1 = [⟨0, chainOf (titleRef 0) [titleRef 1, titleRef 2]⟩] ∧
    mergeForest first 2 1 ≠ first ∧
    mergeForest first 0 1 = first ∧
    mergeForest first 0 1 ≠ [⟨2, freshTitle 2⟩] := by decide

#print axioms splitForest_detach
#print axioms atomicSplit_result
#print axioms atomicSplit_nodes
#print axioms split_preserves
#print axioms mergeForest_nodes
#print axioms mergeForest_refs
#print axioms merge_preserves
#print axioms reachable_invariant

end Sal.MRDTs.Instances.NotionCoreSliceForest
