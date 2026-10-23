import Sal.MRDTs.Instances.NotionCoreParentMap

/-!
Pinned-demo boolean formatting, kept separate from the verified editing core.

Research question: does translating a displayed selection to instance anchors
preserve exact selection? The falsifiers are a reversed selection and a
selection with an intervening character displayed elsewhere. This module keeps
the original interval rule; it does not repair it to selected identities.

Reality oracle: rich-text.js, replica.js contiguousSegments/toggleBold, and
document.js annotationAnchors pinned by experiments/notion-oracle/sources.json.
The model uses typed inputs, finite origin trees, and the existing UTF-16 Lamport IDs.
It does not verify JavaScript parsing, exception behavior, source-to-Lean
translation, or integration with the production transaction/core enums.

Source field mapping: Character.textInstance represents textInstanceId;
Item.id and MarkOp.id use the source counter/session pair. Item.kind retains
text/deleted/split. Nat text values abstract scalar contents. START/END are
Endpoint.start/finish. Anchor.side is the normalized anchor-or-affinity field.
MarkOp.value distinguishes addAnnotation from removeAnnotation for key "b".
Search labels and block pointers route operations to an instance before this
read; this fragment does not formalize that routing or transaction transport.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingSource
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Kind Tree Forest preorder preorderTree)

inductive Endpoint where
  | start
  | finish
  | item (id : Id)
  deriving DecidableEq, Repr

inductive Side where
  | before
  | after
  deriving DecidableEq, Repr

/-- `anchor ?? affinity`, followed by the source's equality test with before.
Typed absence of both fields chooses after, exactly as undefined does. -/
def normalizeSide (anchor affinity : Option Side) : Side :=
  (anchor.orElse (fun _ => affinity)).getD .after

/-- Both source `anchor` and legacy `affinity` normalize to this typed side. -/
structure Anchor where
  endpoint : Endpoint
  side : Side := .before
  deriving DecidableEq, Repr

structure Positioned where
  item : Item
  entry : Nat
  exit : Nat
  deriving DecidableEq, Repr

mutual
/-- Entry precedes the item; exit follows its complete origin subtree, not
just its own character. Tombstones and split markers contribute positions. -/
def walkTree (offset : Nat) : Tree → List Positioned
  | .node item children =>
      ⟨item, offset, offset + (preorder children).length + 1⟩ :: walk (offset + 1) children
def walk (offset : Nat) : Forest → List Positioned
  | .nil => []
  | .cons tree rest => walkTree offset tree ++ walk (offset + (preorderTree tree).length) rest
end

mutual
/-- The computed entries are the actual consecutive physical preorder
indices. This guards against confusing character indices with subtree exits. -/
theorem walkTree_entries (offset : Nat) (tree : Tree) :
    (walkTree offset tree).map Positioned.entry = List.range' offset (preorderTree tree).length := by
  cases tree with
  | node item children => simp [walkTree, preorderTree, walk_entries, List.range'_succ]
theorem walk_entries (offset : Nat) (forest : Forest) :
    (walk offset forest).map Positioned.entry = List.range' offset (preorder forest).length := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
      simp only [walk, preorder, List.map_append, List.length_append, walkTree_entries, walk_entries]
      simpa only [Nat.one_mul] using (List.range'_append (s := offset) (m := (preorderTree tree).length)
        (n := (preorder rest).length) (step := 1))
end

mutual
theorem walkTree_items (offset : Nat) (tree : Tree) :
    (walkTree offset tree).map Positioned.item = preorderTree tree := by
  cases tree with
  | node item children => simp [walkTree, preorderTree, walk_items]
theorem walk_items (offset : Nat) (forest : Forest) :
    (walk offset forest).map Positioned.item = preorder forest := by
  cases forest with
  | nil => rfl
  | cons tree rest => simp [walk, preorder, walkTree_items, walk_items]
end

/-- A unique-ID source origin forest has exactly one entry/exit record per
item. `find?` is lookup in the source traversal maps on that domain. -/
def anchorPosition (forest : Forest) (anchor : Anchor) : Option Nat :=
  match anchor.endpoint with
  | .start => some 0
  | .finish => some (preorder forest).length
  | .item id => ((walk 0 forest).find? (fun p => p.item.id == id)).map fun p =>
      match anchor.side with
      | .before => p.entry
      | .after => p.exit

structure MarkOp where
  id : Id
  start : Anchor
  finish : Anchor
  value : Bool
  deriving DecidableEq, Repr

/-- Missing endpoints, equal endpoints and reversed intervals are no-ops. -/
def covers (forest : Forest) (operation : MarkOp) (index : Nat) : Bool :=
  match anchorPosition forest operation.start, anchorPosition forest operation.finish with
  | some lo, some hi => decide (lo ≤ index ∧ index < hi)
  | _, _ => false

def applyOrdered (forest : Forest) (operations : List MarkOp) (index : Nat)
    (initial : Bool) : Bool :=
  operations.foldl (fun bold operation => if covers forest operation index then operation.value else bold)
    initial

theorem applyOrdered_singleton (forest : Forest) (operation : MarkOp) (index : Nat)
    (initial : Bool) :
    applyOrdered forest [operation] index initial =
      if covers forest operation index then operation.value else initial := rfl

theorem applyOrdered_append (forest : Forest) (left right : List MarkOp) (index : Nat)
    (initial : Bool) :
    applyOrdered forest (left ++ right) index initial =
      applyOrdered forest right index (applyOrdered forest left index initial) := by
  simp [applyOrdered, List.foldl_append]

theorem untouched (forest : Forest) (operations : List MarkOp) (index : Nat) (initial : Bool)
    (outside : ∀ operation ∈ operations, covers forest operation index = false) :
    applyOrdered forest operations index initial = initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      have first := outside operation (by simp)
      have tail : ∀ op ∈ rest, covers forest op index = false :=
        fun op member => outside op (by simp [member])
      simpa [applyOrdered, first] using ih initial tail

/-- An actual final covering assignment determines the value even when
earlier overlapping additions/removals occur. -/
theorem last_covering (forest : Forest) (earlier later : List MarkOp) (operation : MarkOp)
    (index : Nat) (initial : Bool)
    (inside : covers forest operation index = true)
    (laterOutside : ∀ op ∈ later, covers forest op index = false) :
    applyOrdered forest (earlier ++ operation :: later) index initial = operation.value := by
  rw [applyOrdered_append]
  simp only [applyOrdered, List.foldl_cons, inside, ↓reduceIte]
  exact untouched forest later index operation.value laterOutside

def Ascending (left right : MarkOp) : Prop :=
  NotionRunAllocation.Before left.id right.id ∨ left.id = right.id

instance (left right : MarkOp) : Decidable (Ascending left right) :=
  inferInstanceAs (Decidable (NotionRunAllocation.Before left.id right.id ∨ left.id = right.id))

instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy a.id b.id with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)

instance : IsTrans MarkOp Ascending where
  trans a b c ab bc := by
    rcases ab with ab | ab <;> rcases bc with bc | bc
    · exact Or.inl (NotionCoreSourceInvariant.before_trans ab bc)
    · exact Or.inl (bc ▸ ab)
    · exact Or.inl (ab ▸ bc)
    · exact Or.inr (ab.trans bc)

/-- Ascending counter-first, UTF-16-session-second order, as compareOpIds.
Library insertion sort makes this model kernel-reducible. Its sortedness and
permutation contract determines the source order on unique operation IDs;
the JavaScript sorting algorithm is not encoded. Conflicting duplicate
operation IDs are excluded by an additional annotation-issuance assumption,
not by the source archive's transaction-ID duplicate check. -/
def sortOperations (operations : List MarkOp) : List MarkOp :=
  operations.insertionSort Ascending

theorem sorted_pairwise (operations : List MarkOp) :
    (sortOperations operations).Pairwise Ascending := List.pairwise_insertionSort _ _

theorem sorted_perm (operations : List MarkOp) :
    (sortOperations operations).Perm operations := List.perm_insertionSort _ _

def resolveAt (forest : Forest) (operations : List MarkOp) (index : Nat) : Bool :=
  applyOrdered forest (sortOperations operations) index false

theorem resolve_untouched (forest : Forest) (operations : List MarkOp) (index : Nat)
    (outside : ∀ operation ∈ operations, covers forest operation index = false) :
    resolveAt forest operations index = false := by
  apply untouched
  intro operation member
  exact outside operation ((sorted_perm operations).mem_iff.mp member)

theorem preserves_value (forest : Forest) (operations : List MarkOp) (index : Nat) (value : Bool)
    (same : ∀ operation ∈ operations, covers forest operation index = true → operation.value = value) :
    applyOrdered forest operations index value = value := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
      have tail : ∀ op ∈ rest, covers forest op index = true → op.value = value :=
        fun op member covered => same op (by simp [member]) covered
      by_cases covered : covers forest operation index = true
      · simpa [applyOrdered, covered, same operation (by simp) covered] using ih tail
      · simpa [applyOrdered, covered] using ih tail

/-- A greatest covering Lamport operation wins independently of input list
order. The premise excludes conflicting payloads sharing its operation ID,
as an explicit annotation-ID integrity premise. Transaction-ID integrity alone
does not imply this. Repeated identical operations are OK. -/
theorem greatest_covering_wins (forest : Forest) (operations : List MarkOp) (operation : MarkOp)
    (index : Nat) (member : operation ∈ operations) (inside : covers forest operation index = true)
    (greatest : ∀ other ∈ operations, covers forest other index = true →
      NotionRunAllocation.Before other.id operation.id ∨ other = operation) :
    resolveAt forest operations index = operation.value := by
  have permutation := sorted_perm operations
  have sortedMember : operation ∈ sortOperations operations := permutation.mem_iff.mpr member
  obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp sortedMember
  have ordered := sorted_pairwise operations
  rw [decomposition] at ordered
  have after := (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1
  unfold resolveAt
  rw [decomposition, applyOrdered_append]
  simp only [applyOrdered, List.foldl_cons, inside, ↓reduceIte]
  apply preserves_value
  intro other laterMember covered
  have originalMember : other ∈ operations := permutation.mem_iff.mp (by
    rw [decomposition]; simp [laterMember])
  rcases greatest other originalMember covered with older | same
  · have priority := after other laterMember
    rcases priority with newer | equal
    · exact False.elim (NotionCoreSourceInvariant.before_asymm older newer)
    · have impossible : NotionRunAllocation.Before operation.id operation.id := equal ▸ older
      exact False.elim (NotionCoreSourceInvariant.before_irrefl _ impossible)
  · simp [same]

/-- Independent index-interval evaluator. It searches the tail first and
therefore selects the rightmost covering assignment without state mutation. -/
structure Interval where
  lower : Option Nat
  upper : Option Nat
  value : Bool
  deriving DecidableEq, Repr

def Interval.contains (interval : Interval) (index : Nat) : Bool :=
  match interval.lower, interval.upper with
  | some lo, some hi => (lo ≤ index) && (index < hi)
  | _, _ => false

def intervalWinner (intervals : List Interval) (index : Nat) : Option Bool :=
  match intervals with
  | [] => none
  | interval :: rest =>
      match intervalWinner rest index with
      | some value => some value
      | none => if interval.contains index then some interval.value else none

def compileInterval (forest : Forest) (operation : MarkOp) : Interval :=
  ⟨anchorPosition forest operation.start, anchorPosition forest operation.finish, operation.value⟩

theorem compiled_contains (forest : Forest) (operation : MarkOp) (index : Nat) :
    (compileInterval forest operation).contains index = covers forest operation index := by
  simp only [compileInterval, Interval.contains, covers]
  cases anchorPosition forest operation.start <;>
    cases anchorPosition forest operation.finish <;> simp

/-- Exact correspondence to a separate rightmost index-interval evaluator,
for arbitrary mixtures of addition/removal and arbitrary initial mark. -/
theorem interval_correspondence (forest : Forest) (operations : List MarkOp) (index : Nat)
    (initial : Bool) :
    applyOrdered forest operations index initial =
      (intervalWinner (operations.map (compileInterval forest)) index).getD initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      simp only [applyOrdered, List.foldl_cons]
      rw [show List.foldl _ _ rest = applyOrdered forest rest index
        (if covers forest operation index then operation.value else initial) from rfl]
      rw [ih]
      simp only [List.map_cons, intervalWinner]
      cases winner : intervalWinner (rest.map (compileInterval forest)) index with
      | some value => rfl
      | none => simp [compiled_contains]; cases covers forest operation index <;> rfl

theorem resolve_correspondence (forest : Forest) (operations : List MarkOp) (index : Nat) :
    resolveAt forest operations index =
      (intervalWinner ((sortOperations operations).map (compileInterval forest)) index).getD false :=
  interval_correspondence forest _ index false

theorem reversed_noop (forest : Forest) (operation : MarkOp) (lo hi : Nat)
    (startAt : anchorPosition forest operation.start = some lo)
    (finishAt : anchorPosition forest operation.finish = some hi)
    (reversed : hi ≤ lo) (index : Nat) : covers forest operation index = false := by
  simp only [covers, startAt, finishAt]
  simp only [decide_eq_false_iff_not]
  omega

structure Character where
  textInstance : Nat
  item : Item
  bold : Bool
  deriving DecidableEq, Repr

/-- Maximal adjacent runs of equal instance IDs. The original selected order
is retained, including a reversed or noncontiguous instance selection. -/
def contiguousSegments : List Character → List (List Character)
  | [] => []
  | character :: rest =>
      match contiguousSegments rest with
      | [] => [[character]]
      | [] :: segments => [character] :: segments
      | (first :: tail) :: segments =>
          if character.textInstance = first.textInstance then (character :: first :: tail) :: segments
          else [character] :: (first :: tail) :: segments

theorem contiguousSegments_flatten (characters : List Character) :
    (contiguousSegments characters).flatten = characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      cases parts : contiguousSegments rest with
      | nil => simpa [contiguousSegments, parts] using congrArg (character :: ·) ih
      | cons segment segments =>
          cases segment with
          | nil => simpa [contiguousSegments, parts] using congrArg (character :: ·) ih
          | cons first tail =>
              by_cases same : character.textInstance = first.textInstance <;>
                simpa [contiguousSegments, parts, same] using congrArg (character :: ·) ih

def visibleItems (forest : Forest) : List Item := (preorder forest).filter fun item =>
  match item.kind with
  | .text _ false => true
  | _ => false

/-- The source's visible.findIndex(last) + 1, including its missing-last
fallback to the first visible item (JavaScript -1 + 1 = 0). -/
def nextVisible (forest : Forest) (last : Id) : Option Item :=
  let visible := visibleItems forest
  match visible.findIdx? (fun item => item.id == last) with
  | some index => visible[index + 1]?
  | none => visible[0]?

def annotationAnchors (forest : Forest) (first last : Item) : Anchor × Anchor :=
  (⟨.item first.id, .before⟩,
   ⟨match nextVisible forest last.id with
      | some next => .item next.id
      | none => .finish, .before⟩)

/-- One atomic source toggle may emit several independent interval operations.
The operation counter increases once per segment; all segments share the same
add/remove verdict, determined from the complete displayed selection. -/
def prepareSegments (forests : Nat → Forest) (session : NotionRunAllocation.Session)
    (counter : Nat) (value : Bool) : List (List Character) → List (Nat × MarkOp)
  | [] => []
  | [] :: rest => prepareSegments forests session counter value rest
  | (first :: rest) :: segments =>
      let last := rest.getLast?.getD first
      let anchors := annotationAnchors (forests first.textInstance) first.item last.item
      (first.textInstance, ⟨⟨counter, session⟩, anchors.1, anchors.2, value⟩) ::
        prepareSegments forests session (counter + 1) value segments

def toggleBold (forests : Nat → Forest) (session : NotionRunAllocation.Session)
    (firstCounter : Nat) (selection : List Character) : List (Nat × MarkOp) :=
  prepareSegments forests session firstCounter (!(selection.all Character.bold))
    (contiguousSegments selection)

theorem prepareSegments_value (forests : Nat → Forest) (session : NotionRunAllocation.Session)
    (counter : Nat) (value : Bool) (segments : List (List Character))
    (located : Nat × MarkOp) (member : located ∈ prepareSegments forests session counter value segments) :
    located.2.value = value := by
  induction segments generalizing counter with
  | nil => simp [prepareSegments] at member
  | cons segment segments ih =>
      cases segment with
      | nil => exact ih counter member
      | cons first rest =>
          simp only [prepareSegments, List.mem_cons] at member
          rcases member with same | later
          · subst located; rfl
          · exact ih (counter + 1) later

theorem toggleBold_value (forests : Nat → Forest) (session : NotionRunAllocation.Session)
    (counter : Nat) (selection : List Character) (located : Nat × MarkOp)
    (member : located ∈ toggleBold forests session counter selection) :
    located.2.value = !(selection.all Character.bold) :=
  prepareSegments_value forests session counter _ _ located member

structure Formatted where
  item : Item
  bold : Bool
  deriving DecidableEq, Repr

/-- Rich-text resolution retains physical positions while projecting away
markers and tombstones; they still affect anchor boundaries and index tests. -/
def resolveRichText (forest : Forest) (operations : List MarkOp) : List Formatted :=
  (preorder forest).zipIdx |>.filterMap fun (item, index) =>
    match item.kind with
    | .text _ false => some ⟨item, resolveAt forest operations index⟩
    | _ => none

/-- Direct parent-map extraction frontend; no production core enums change. -/
def resolveParentMap (rows : NotionCoreParentMap.Table) (operations : List MarkOp) : List Formatted :=
  resolveRichText (NotionCoreParentMap.extract (NotionCoreParentMap.maximumCounter rows) rows .start)
    operations

/-- The physical items beneath the parent-map frontend agree with its
independent child-enumerating traversal, including hidden items. -/
theorem parentMap_walk_items (rows : NotionCoreParentMap.Table) :
    (walk 0 (NotionCoreParentMap.extract (NotionCoreParentMap.maximumCounter rows) rows .start)).map
      Positioned.item =
      NotionCoreParentMap.traverse (NotionCoreParentMap.maximumCounter rows) rows .start := by
  rw [walk_items, NotionCoreParentMap.extract_preorder]

#print axioms greatest_covering_wins
#print axioms interval_correspondence
#print axioms walk_entries
#print axioms parentMap_walk_items

end Sal.MRDTs.Instances.NotionCoreFormattingSource
