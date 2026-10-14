import Mathlib.Data.List.Basic

/-! Independent fragment specifications for the Notion split investigation.
No transaction replay, transaction order, or implementation identifiers occur.
The identity fragment retains hidden character slots so a prepared split gap
remains meaningful after deletion. This is not yet a demo refinement theorem.
-/
namespace Sal.MRDTs.Instances.NotionSplitSpec

abbrev Text := List Nat
abbrev Document := List Text

/-- Total positional requests on the original (first) block. `take`/`drop`
clamp out-of-range indices; strict validity would only remove serializations. -/
inductive Request where
  | split (index : Nat)
  | delete (start stop : Nat)
  deriving DecidableEq

def step (doc : Document) (request : Request) : Document :=
  match doc with
  | [] => []
  | text :: rest => match request with
    | .split i => text.take i :: text.drop i :: rest
    | .delete lo hi => (text.take lo ++ text.drop hi) :: rest

def run (doc : Document) (requests : List Request) : Document :=
  requests.foldl step doc

def initial : Document := [[0, 1, 2, 3]]
def splitRequest : Request := .split 2
def deleteRequest : Request := .delete 1 3

/-- Hand calculation: split first confines the later positional delete to ab. -/
theorem positional_split_delete :
    run initial [splitRequest, deleteRequest] = [[0], [2, 3]] := by decide

theorem positional_delete_split :
    run initial [deleteRequest, splitRequest] = [[0, 3], []] := by decide

/-- Both serial orders fail to explain the identity-preserving crossing delete.
This refutes this positional request alphabet, not an identity message spec. -/
theorem no_positional_serialization :
    run initial [splitRequest, deleteRequest] ≠ [[0], [3]] ∧
    run initial [deleteRequest, splitRequest] ≠ [[0], [3]] := by decide

/-- A slot has a stable semantic character identity, content, and visibility.
Hidden slots retain a gap's position after the character is deleted. -/
structure Slot where
  id : Nat
  value : Nat
  visible : Bool
  deriving DecidableEq

abbrev IdentityText := List Slot
abbrev IdentityDocument := List IdentityText

def display (doc : IdentityDocument) : Document :=
  doc.map fun text => (text.filter Slot.visible).map Slot.value

/-- An identity-addressed delete affects every block containing a selected
character, including characters moved to a new block by an earlier split. -/
def eraseSlot (targets : List Nat) (slot : Slot) : Slot :=
  { slot with visible := slot.visible && !(targets.contains slot.id) }

def erase (targets : List Nat) (doc : IdentityDocument) : IdentityDocument :=
  doc.map (List.map (eraseSlot targets))

/-- A retained gap in this one-split fragment is a cut between stable slots.
It is independent of visible indices and preserved by `erase`. A complete
spec must replace this fragment's cut by a prepared identity gap. -/
def cut (gap : Nat) (doc : IdentityDocument) : IdentityDocument :=
  match doc with
  | [] => []
  | text :: rest => text.take gap :: text.drop gap :: rest

/-- The key ordinary editing law: deleting stable characters commutes with
splitting their containing block at a retained gap. -/
theorem cut_erase_commute (gap : Nat) (targets : List Nat)
    (doc : IdentityDocument) :
    cut gap (erase targets doc) = erase targets (cut gap doc) := by
  cases doc with
  | nil => rfl
  | cons text rest => simp [cut, erase, List.map_take, List.map_drop]

def identityInitial : IdentityDocument :=
  [[⟨0, 0, true⟩, ⟨1, 1, true⟩, ⟨2, 2, true⟩, ⟨3, 3, true⟩]]

/-- PASS: deleting b,c and splitting between b,c gives a | d in either order. -/
theorem identity_crossing_delete :
    display (erase [1, 2] (cut 2 identityInitial)) = [[0], [3]] ∧
    display (cut 2 (erase [1, 2] identityInitial)) = [[0], [3]] := by decide

/-- FAIL controls: deletion is effective and affects both resulting blocks. -/
theorem identity_crossing_delete_controls :
    display (erase [1, 2] (cut 2 identityInitial)) ≠ [[0, 1], [2, 3]] ∧
    display (erase [1, 2] (cut 2 identityInitial)) ≠ [[0], [2, 3]] := by decide

/-- Local delete preparation for a concrete visible range has its requested
visible effect before any concurrent split. The expectation is hand-derived. -/
theorem local_delete_preparation_control :
    display (erase [1, 2] identityInitial) = [[0, 3]] ∧
    display (erase [1, 2] identityInitial) ≠ [[0, 1, 2, 3]] := by decide

/-- A split names an original character immediately before its gap. This
semantic identity still exists when the character becomes hidden. A missing
anchor yields the unchanged text and an empty suffix; `splitByAnchor` still
creates that empty block. Issuance must establish presence and uniqueness. -/
def splitAfter (anchor : Nat) : IdentityText → IdentityText × IdentityText
  | [] => ([], [])
  | slot :: rest =>
      if slot.id = anchor then ([slot], rest)
      else let (left, right) := splitAfter anchor rest
           (slot :: left, right)

def splitByAnchor (anchor : Nat) (doc : IdentityDocument) : IdentityDocument :=
  match doc with
  | [] => []
  | text :: rest =>
      let (left, right) := splitAfter anchor text
      left :: right :: rest

/-- Identity deletion preserves the semantic cut named by a character. -/
theorem splitAfter_erase (anchor : Nat) (targets : List Nat)
    (text : IdentityText) :
    splitAfter anchor (text.map (eraseSlot targets)) =
      ((splitAfter anchor text).1.map (eraseSlot targets),
       (splitAfter anchor text).2.map (eraseSlot targets)) := by
  induction text with
  | nil => rfl
  | cons slot rest ih =>
      simp only [List.map_cons, splitAfter, eraseSlot]
      split <;> simp_all [eraseSlot]

theorem splitByAnchor_erase_commute (anchor : Nat) (targets : List Nat)
    (doc : IdentityDocument) :
    splitByAnchor anchor (erase targets doc) =
      erase targets (splitByAnchor anchor doc) := by
  cases doc with
  | nil => rfl
  | cons text rest => simp [splitByAnchor, erase, splitAfter_erase]

/-- Ordinary insertion after a retained character. The new identity must be
fresh; this executable fragment leaves issuance as a separate obligation. -/
def insertAfter (anchor : Nat) (fresh : Slot) : IdentityText → IdentityText
  | [] => []
  | slot :: rest =>
      if slot.id = anchor then slot :: fresh :: rest
      else slot :: insertAfter anchor fresh rest

def insertByAnchor (anchor : Nat) (fresh : Slot)
    (doc : IdentityDocument) : IdentityDocument :=
  doc.map (insertAfter anchor fresh)

/-- PASS+FAIL: the two boundary placements are ordinary sequential outcomes
for identity messages, with opposite witness orders. The fresh symbol is 4. -/
theorem boundary_insert_orders :
    display (insertByAnchor 1 ⟨4, 4, true⟩
      (splitByAnchor 1 identityInitial)) = [[0, 1, 4], [2, 3]] ∧
    display (splitByAnchor 1
      (insertByAnchor 1 ⟨4, 4, true⟩ identityInitial)) = [[0, 1], [4, 2, 3]] ∧
    display (insertByAnchor 1 ⟨4, 4, true⟩
      (splitByAnchor 1 identityInitial)) ≠
    display (splitByAnchor 1
      (insertByAnchor 1 ⟨4, 4, true⟩ identityInitial)) := by decide

/-- The identity split handles a deleted anchor, so both witness orders remain
legal at the semantic level when a deletion crosses the prepared gap. -/
theorem identity_anchor_crossing_delete :
    display (erase [1, 2] (splitByAnchor 1 identityInitial)) = [[0], [3]] ∧
    display (splitByAnchor 1 (erase [1, 2] identityInitial)) = [[0], [3]] ∧
    display (splitByAnchor 1 (erase [1, 2] identityInitial)) ≠ [[0, 3], []] := by decide

/-- Ordinary local splitting at zero preserves the full text on the right. -/
theorem local_split_zero (text : Text) (rest : Document) :
    step (text :: rest) (.split 0) = [] :: text :: rest := by
  simp [step]

/-- Conditional semantic counterpart of the measured post-merge split anomaly:
the target block `aX` (0,1) becoming `X | a` cannot satisfy the independent split-at-zero rule.
This theorem does not assert that JavaScript produces the source result. -/
theorem minimized_split_zero_rejects_ordinary_contract :
    step [[0, 1]] (.split 0) = [[], [0, 1]] ∧
    step [[0, 1]] (.split 0) ≠ [[1], [0]] := by decide

#print axioms cut_erase_commute
#print axioms splitByAnchor_erase_commute
#print axioms no_positional_serialization
end Sal.MRDTs.Instances.NotionSplitSpec
