import Mathlib.Data.List.Basic

/-! A restricted executable counterpart of the demo's block-merge transaction.
A merge splits the source block's root text slice, moves the right part after
the target's last slice, and removes the source block. The model keeps the
last two steps. Slices form a forest owned by blocks; a block's text is the
preorder traversal of its slices, and removed blocks keep their slices. The
move appends the slice under its target wherever that target lives, and is a
no-op when the target lies inside the moved subtree, as in the source's cycle
handling. The fixtures are the slice trees dumped from the demo just before
each failing update arrives, after its split step. This does not formalize
JavaScript or prove source correspondence.
-/
namespace Sal.MRDTs.Instances.NotionMergeLossCounterexample

/-! ## Ordinary sequential editing conserves characters -/

abbrev Document := List (List Nat)

/-- Ordinary split of block `i` at position `k`. -/
def ordinarySplit : Document → Nat → Nat → Document
  | [], _, _ => []
  | w :: rest, 0, k => w.take k :: w.drop k :: rest
  | w :: rest, i + 1, k => w :: ordinarySplit rest i k

/-- Ordinary merge of block `i` into its predecessor. -/
def ordinaryMerge : Document → Nat → Document
  | p :: q :: rest, 1 => (p ++ q) :: rest
  | p :: rest, i + 2 => p :: ordinaryMerge rest (i + 1)
  | doc, _ => doc

inductive Request where
  | split (block index : Nat)
  | merge (block : Nat)
  deriving DecidableEq

def ordinaryStep (doc : Document) : Request → Document
  | .split i k => ordinarySplit doc i k
  | .merge i => ordinaryMerge doc i

def run (doc : Document) (requests : List Request) : Document :=
  requests.foldl ordinaryStep doc

theorem flatten_ordinarySplit (doc : Document) (i k : Nat) :
    (ordinarySplit doc i k).flatten = doc.flatten := by
  induction doc generalizing i with
  | nil => cases i <;> rfl
  | cons w rest ih =>
    cases i with
    | zero => simp [ordinarySplit, ← List.append_assoc]
    | succ i => simp [ordinarySplit, ih]

theorem flatten_ordinaryMerge (doc : Document) (i : Nat) :
    (ordinaryMerge doc i).flatten = doc.flatten := by
  fun_induction ordinaryMerge doc i <;> simp_all

/-- Every sequential history of splits and merges keeps the document's
characters in order, whatever positions its requests name. -/
theorem flatten_run (doc : Document) (requests : List Request) :
    (run doc requests).flatten = doc.flatten := by
  induction requests generalizing doc with
  | nil => rfl
  | cons r rs ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases r with
    | split i k => exact flatten_ordinarySplit doc i k
    | merge i => exact flatten_ordinaryMerge doc i

/-- Hence no sequential history of splits and merges explains a display that
has lost a character of the starting document. -/
theorem no_sequential_explanation (doc observed : Document)
    (lost : observed.flatten ≠ doc.flatten) (requests : List Request) :
    run doc requests ≠ observed := by
  intro h
  exact lost (h ▸ flatten_run doc requests)

/-! ## The source's merge transaction -/

/-- A slice belongs directly to a block (its root slice) or to a parent slice. -/
inductive Owner where
  | block (id : Nat)
  | slice (id : Nat)
  deriving DecidableEq

structure Slice where
  id : Nat
  text : List Nat
  owner : Owner
  deriving DecidableEq

/-- Blocks in display order with their liveness, and the slice forest. The
children of a slice are the slices it owns, in list order. -/
structure State where
  blocks : List (Nat × Bool)
  slices : List Slice
  deriving DecidableEq

def children (slices : List Slice) (owner : Owner) : List Slice :=
  slices.filter (·.owner == owner)

/-- Preorder text below an owner; `fuel` bounds the depth. -/
def textBelow (slices : List Slice) : Nat → Owner → List Nat
  | 0, _ => []
  | fuel + 1, owner =>
      (children slices owner).flatMap fun s => s.text ++ textBelow slices fuel (.slice s.id)

def display (st : State) : Document :=
  (st.blocks.filter (·.2)).map fun b => textBelow st.slices st.slices.length (.block b.1)

/-- Every character stored in any slice, visible or not. -/
def stored (st : State) : List Nat := st.slices.flatMap (·.text)

/-- Whether the owner chain upward from `owner` passes through slice `src`. -/
def within (slices : List Slice) (src : Nat) : Nat → Owner → Bool
  | 0, _ => false
  | _, .block _ => false
  | fuel + 1, .slice s =>
      s == src || match slices.find? (·.id == s) with
        | some parent => within slices src fuel parent.owner
        | none => false

/-- Counterpart of `moveTextSlice`: append `src` as the last child of `tgt`,
without checking that `tgt`'s block is alive. A move whose target lies inside
the moved subtree would create a cycle and leaves the forest unchanged. -/
def move (slices : List Slice) (src tgt : Nat) : List Slice :=
  if within slices src slices.length (.slice tgt) then slices
  else match slices.find? (·.id == src) with
    | none => slices
    | some s => slices.filter (·.id != src) ++ [{ s with owner := .slice tgt }]

def removeBlock (blocks : List (Nat × Bool)) (b : Nat) : List (Nat × Bool) :=
  blocks.map fun c => (c.1, c.2 && c.1 != b)

/-- The move and block removal of one merge transaction. -/
def mergeTransaction (st : State) (src tgt sourceBlock : Nat) : State :=
  { blocks := removeBlock st.blocks sourceBlock, slices := move st.slices src tgt }

/-! ## N-004: a merge into a removed block hides the whole document

Characters a, b, c are 0, 1, 2. Blocks 1, 3 and 5 held the seed blocks and are
removed; block 28 shows `abc`. The arriving merge was issued to merge block 28
into block 3. Its split step has created slice 49 holding the old root's
children. Its target, the last slice of block 3, is that removed block's root. -/

def documentLossBefore : State where
  blocks := [(1, false), (3, false), (5, false), (28, true)]
  slices :=
    [ ⟨1, [], .block 1⟩, ⟨3, [], .block 3⟩, ⟨5, [], .block 5⟩, ⟨28, [], .block 28⟩,
      ⟨49, [], .slice 28⟩, ⟨50, [], .slice 49⟩, ⟨51, [0], .slice 50⟩,
      ⟨52, [1], .slice 51⟩, ⟨53, [2], .slice 52⟩ ]

def documentLossAfter : State := mergeTransaction documentLossBefore 49 3 28

/-- PASS+FAIL: before the update the display is `abc`; afterwards no block is
visible, although all three characters are still stored. -/
theorem merge_into_removed_block_hides_document :
    display documentLossBefore = [[0, 1, 2]] ∧
    display documentLossAfter = [] ∧
    display documentLossAfter ≠ [[0, 1, 2]] ∧
    stored documentLossAfter = [0, 1, 2] := by decide

/-- No sequential history of splits and merges from the seed `a · b · c`
produces the observed empty display. -/
theorem document_loss_unexplained (requests : List Request) :
    run [[0], [1], [2]] requests ≠ display documentLossAfter :=
  no_sequential_explanation _ _ (by decide) requests

/-- Nearby positive control: the same transaction with a live target block
keeps `abc` visible, so the move rule does not always hide text. -/
theorem live_target_control :
    display (mergeTransaction { documentLossBefore with
      blocks := [(1, false), (3, true), (5, false), (28, true)] } 49 3 28) = [[0, 1, 2]] ∧
    display (mergeTransaction { documentLossBefore with
      blocks := [(1, false), (3, true), (5, false), (28, true)] } 49 3 28) ≠ [] := by
  decide

/-! ## N-005: a delayed merge hides a character

Character x is 0. Block 1 shows an empty text and block 31 shows `x`; block 30
is removed. The delayed merge removes block 31 after its split step has
created slice 24, which owns the chain down to slice 5 holding x. Its target
slice, identified by its end, is slice 5 itself, inside the moved subtree. -/

def characterLossBefore : State where
  blocks := [(1, true), (30, false), (31, true)]
  slices :=
    [ ⟨1, [], .block 1⟩, ⟨30, [], .block 30⟩, ⟨31, [], .block 31⟩,
      ⟨24, [], .slice 31⟩, ⟨3, [], .slice 24⟩, ⟨4, [], .slice 3⟩, ⟨5, [0], .slice 4⟩ ]

def characterLossAfter : State := mergeTransaction characterLossBefore 24 5 31

/-- PASS+FAIL: the move would create a cycle and is skipped, but the block
holding x is still removed. -/
theorem cyclic_merge_removal_hides_character :
    display characterLossBefore = [[], [0]] ∧
    within characterLossBefore.slices 24 characterLossBefore.slices.length (.slice 5) = true ∧
    characterLossAfter.slices = characterLossBefore.slices ∧
    display characterLossAfter = [[]] ∧
    display characterLossAfter ≠ [[0]] ∧
    stored characterLossAfter = [0] := by decide

/-- No sequential history of splits and merges from the seed `x` produces the
observed display. -/
theorem character_loss_unexplained (requests : List Request) :
    run [[0]] requests ≠ display characterLossAfter :=
  no_sequential_explanation _ _ (by decide) requests

/-- Nearby positive control: moving the same subtree under the live first
block's root performs the ordinary merge and keeps x visible. -/
theorem acyclic_target_control :
    display (mergeTransaction characterLossBefore 24 1 31) = [[0]] ∧
    display (mergeTransaction characterLossBefore 24 1 31) ≠ [[]] := by decide

#print axioms merge_into_removed_block_hides_document
#print axioms document_loss_unexplained
#print axioms cyclic_merge_removal_hides_character
#print axioms character_loss_unexplained
end Sal.MRDTs.Instances.NotionMergeLossCounterexample
