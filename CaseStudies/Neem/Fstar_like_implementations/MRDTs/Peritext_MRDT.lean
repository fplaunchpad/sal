import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide
import Blaster

import CaseStudies.Neem_interfaces.Set_extended
import CaseStudies.Neem_interfaces.Map_extended

@[simp]
abbrev counter := Int

@[simp]
abbrev nodeId := Nat

@[simp]
abbrev opIdType := counter × nodeId

-- Define lexicographic ordering for opIds
-- First compare by counter, then by nodeId if counters are equal
instance : LT opIdType where
  lt a b :=
    let (c1, n1) := a
    let (c2, n2) := b
    c1 < c2 ∨ (c1 = c2 ∧ n1 < n2)

-- Make the ordering decidable
instance : DecidableRel (α := opIdType) (· < ·) := fun a b =>
  let (c1, n1) := a
  let (c2, n2) := b
  if h1 : c1 < c2 then
    isTrue (Or.inl h1)
  else if h2 : c1 = c2 ∧ n1 < n2 then
    isTrue (Or.inr h2)
  else
    isFalse (by
      intro h
      cases h with
      | inl hc => exact h1 hc
      | inr hand =>
        cases hand
        exact h2 (And.intro ‹c1 = c2› ‹n1 < n2›)
    )


structure insert_op where
 opId :  opIdType
 afterId : Option opIdType
 character : Char
deriving DecidableEq

structure remove_op where
  opId : opIdType
  removedId : opIdType
deriving DecidableEq

inductive markType where
| Bold
| Italics
| Link
deriving DecidableEq

inductive BeforeAfterType where
| Before
| After
deriving DecidableEq

structure span_struct where
  type : BeforeAfterType
  opId : opIdType
deriving DecidableEq

inductive spanType where
| ManualSpan : span_struct → spanType
| StartOfText
| EndOfText
deriving DecidableEq

structure addMark_op where
  opId : opIdType
  _start : spanType
  _end : spanType
  mark : markType
deriving DecidableEq

structure removeMark_op where
  opId : opIdType
  _start : spanType
  _end : spanType
  mark : markType
deriving DecidableEq

inductive MarkOp where
| AddMarkOperation : addMark_op → MarkOp
| RemoveMarkOperation : removeMark_op → MarkOp
deriving DecidableEq

structure CharMetaData where
  insert_opId : opIdType
  c : Char
  deleted : Bool
  markOpsBefore? : Option (set MarkOp)
  markOpsAfter? : Option (set MarkOp)


abbrev TextMetaData := Array CharMetaData

-- Equality for CharMetaData: compare all fields, using equal for set fields
def CharMetaData.eq (c1 c2 : CharMetaData) : Prop :=
  c1.insert_opId = c2.insert_opId ∧
  c1.c = c2.c ∧
  c1.deleted = c2.deleted ∧
  match c1.markOpsBefore?, c2.markOpsBefore? with
  | none, none => True
  | some s1, some s2 => equal s1 s2
  | _, _ => False
  ∧
  match c1.markOpsAfter?, c2.markOpsAfter? with
  | none, none => True
  | some s1, some s2 => equal s1 s2
  | _, _ => False

abbrev concrete_st := TextMetaData

-- Equality for texts: same size and all characters equal
@[simp]
def eq (a b : concrete_st) : Prop :=
  a.size = b.size ∧
  ∀ i : Nat, ∀ ha : i < a.size, ∀ hb : i < b.size,
    CharMetaData.eq a[i] b[i]


inductive Op where
| InsertOp : insert_op → Op
| RemoveOp : remove_op → Op
| AddMarkOp : addMark_op → Op
| RemoveMarkOp : removeMark_op → Op
deriving DecidableEq

@[simp]
def init_st : concrete_st := #[]

-- Helper: Find index of character with given opId
def findCharIndex (text: TextMetaData) (id: opIdType) : Option Nat :=
  text.findIdx? (fun char => char.insert_opId = id)

-- Helper: Find insertion position after a given opId
def findInsertPosition (text: TextMetaData) (afterId: Option opIdType) : Nat :=
  match afterId with
  | none => 0  -- Insert at beginning
  | some id =>
      match findCharIndex text id with
      | none => text.size  -- If not found, append at end
      | some idx => idx + 1  -- Insert after the found character

-- Helper: Check if a span includes a character position
def spanIncludes (span_start: spanType) (span_end: spanType) (charId: opIdType) (text: TextMetaData) : Bool :=
  -- Simplified: check if character is within the span range
  -- In full implementation, this would handle Before/After semantics
  match span_start, span_end with
  | .StartOfText, .EndOfText => true  -- Entire document
  | .StartOfText, .ManualSpan endSpan =>
      match findCharIndex text charId with
      | none => false
      | some charIdx =>
          match findCharIndex text endSpan.opId with
          | none => false
          | some endIdx => charIdx < endIdx
  | .ManualSpan startSpan, .EndOfText =>
      match findCharIndex text charId with
      | none => false
      | some charIdx =>
          match findCharIndex text startSpan.opId with
          | none => false
          | some startIdx =>
              if startSpan.type = BeforeAfterType.Before then
                startIdx ≤ charIdx
              else
                startIdx < charIdx
  | .ManualSpan startSpan, .ManualSpan endSpan =>
      match findCharIndex text charId with
      | none => false
      | some charIdx =>
          match findCharIndex text startSpan.opId, findCharIndex text endSpan.opId with
          | some startIdx, some endIdx =>
              let actualStart := if startSpan.type = BeforeAfterType.Before then startIdx else startIdx + 1
              let actualEnd := if endSpan.type = BeforeAfterType.Before then endIdx else endIdx + 1
              actualStart ≤ charIdx ∧ charIdx < actualEnd
          | _, _ => false
  | _, _ => false


-- Helper: Insert element at position in array
def arrayInsertAt {α : Type} (arr : Array α) (pos : Nat) (elem : α) : Array α :=
  let left := arr.extract 0 pos
  let right := arr.extract pos arr.size
  left.push elem ++ right

-- Main do_ function: applies an operation to the state
@[simp]
def do_ (s: concrete_st) (o: Op) : concrete_st :=
  match o with
  | Op.InsertOp insertOp =>
      -- Create new character metadata
      let newChar : CharMetaData := {
        insert_opId := insertOp.opId,
        c := insertOp.character,
        deleted := false,
        markOpsBefore? := none,
        markOpsAfter? := none
      }
      -- Find insertion position and insert
      let pos := findInsertPosition s insertOp.afterId
      arrayInsertAt s pos newChar

  | Op.RemoveOp removeOp =>
      -- Find the character and mark it as deleted
      match findCharIndex s removeOp.removedId with
      | none => s  -- Character not found, no change
      | some idx =>
          s.mapIdx (fun i char =>
            if i = idx then
              { char with deleted := true }
            else
              char
          )

  | Op.AddMarkOp addMarkOp =>
      -- Add mark operation to characters at span boundaries
      let markOp := MarkOp.AddMarkOperation addMarkOp

      -- Helper to check if this is the start anchor and get its type
      let getStartType (charId : opIdType) : Option BeforeAfterType :=
        match addMarkOp._start with
        | .ManualSpan span => if span.opId = charId then some span.type else none
        | _ => none

      -- Helper to check if this is the end anchor and get its type
      let getEndType (charId : opIdType) : Option BeforeAfterType :=
        match addMarkOp._end with
        | .ManualSpan span => if span.opId = charId then some span.type else none
        | _ => none

      -- Apply mark to boundary characters
      s.mapIdx (fun _ char =>
        let startType := getStartType char.insert_opId
        let endType := getEndType char.insert_opId

        match startType, endType with
        | some .Before, none =>
            -- Start with Before: add to markOpsBefore
            let newMarkOpsBefore := match char.markOpsBefore? with
              | none => some (add markOp empty)
              | some curr_set => some (add markOp curr_set)
            { char with markOpsBefore? := newMarkOpsBefore }

        | some .After, none =>
            -- Start with After: add to markOpsAfter
            let newMarkOpsAfter := match char.markOpsAfter? with
              | none => some (add markOp empty)
              | some curr_set => some (add markOp curr_set)
            { char with markOpsAfter? := newMarkOpsAfter }

        | none, some .Before =>
            -- End with Before: add to markOpsBefore
            let newMarkOpsBefore := match char.markOpsBefore? with
              | none => some empty  -- Initialize as empty for end
              | some _ => char.markOpsBefore?  -- Keep as is if already has value
            { char with markOpsBefore? := newMarkOpsBefore }

        | none, some .After =>
            -- End with After: add to markOpsAfter
            let newMarkOpsAfter := match char.markOpsAfter? with
              | none => some empty  -- Initialize as empty for end
              | some _ => char.markOpsAfter?  -- Keep as is if already has value
            { char with markOpsAfter? := newMarkOpsAfter }

        | _, _ => char  -- Not a boundary character or both (shouldn't happen)
      )

  | Op.RemoveMarkOp removeMarkOp =>
      -- Add remove mark operation to characters at span boundaries (same logic as AddMark)
      let markOp := MarkOp.RemoveMarkOperation removeMarkOp

      -- Helper to check if this is the start anchor and get its type
      let getStartType (charId : opIdType) : Option BeforeAfterType :=
        match removeMarkOp._start with
        | .ManualSpan span => if span.opId = charId then some span.type else none
        | _ => none

      -- Helper to check if this is the end anchor and get its type
      let getEndType (charId : opIdType) : Option BeforeAfterType :=
        match removeMarkOp._end with
        | .ManualSpan span => if span.opId = charId then some span.type else none
        | _ => none

      -- Apply mark to boundary characters
      s.mapIdx (fun _ char =>
        let startType := getStartType char.insert_opId
        let endType := getEndType char.insert_opId

        match startType, endType with
        | some .Before, none =>
            -- Start with Before: add to markOpsBefore
            let newMarkOpsBefore := match char.markOpsBefore? with
              | none => some (add markOp empty)
              | some curr_set => some (add markOp curr_set)
            { char with markOpsBefore? := newMarkOpsBefore }

        | some .After, none =>
            -- Start with After: add to markOpsAfter
            let newMarkOpsAfter := match char.markOpsAfter? with
              | none => some (add markOp empty)
              | some curr_set => some (add markOp curr_set)
            { char with markOpsAfter? := newMarkOpsAfter }

        | none, some .Before =>
            -- End with Before: add to markOpsBefore
            let newMarkOpsBefore := match char.markOpsBefore? with
              | none => some empty  -- Initialize as empty for end
              | some _ => char.markOpsBefore?  -- Keep as is if already has value
            { char with markOpsBefore? := newMarkOpsBefore }

        | none, some .After =>
            -- End with After: add to markOpsAfter
            let newMarkOpsAfter := match char.markOpsAfter? with
              | none => some empty  -- Initialize as empty for end
              | some _ => char.markOpsAfter?  -- Keep as is if already has value
            { char with markOpsAfter? := newMarkOpsAfter }

        | _, _ => char  -- Not a boundary character or both (shouldn't happen)
      )

-- ============================================================================
-- Example: User 1 creates "hello", User 2 deletes "h"
-- ============================================================================

-- User 1 (nodeId = 1) creates the word "hello"
def user1_nodeId : nodeId := 1

-- Insert operations for "hello" by User 1
def insert_h : Op := Op.InsertOp {
  opId := (0, user1_nodeId),  -- counter=0, nodeId=1
  afterId := none,             -- Insert at beginning
  character := 'h'
}

def insert_e : Op := Op.InsertOp {
  opId := (1, user1_nodeId),
  afterId := some (0, user1_nodeId),  -- After 'h'
  character := 'e'
}

def insert_l1 : Op := Op.InsertOp {
  opId := (2, user1_nodeId),
  afterId := some (1, user1_nodeId),  -- After 'e'
  character := 'l'
}

def insert_l2 : Op := Op.InsertOp {
  opId := (3, user1_nodeId),
  afterId := some (2, user1_nodeId),  -- After first 'l'
  character := 'l'
}

def insert_o : Op := Op.InsertOp {
  opId := (4, user1_nodeId),
  afterId := some (3, user1_nodeId),  -- After second 'l'
  character := 'o'
}

-- Build the initial state with "hello"
def state_after_hello : concrete_st :=
  let s0 := init_st
  let s1 := do_ s0 insert_h
  let s2 := do_ s1 insert_e
  let s3 := do_ s2 insert_l1
  let s4 := do_ s3 insert_l2
  let s5 := do_ s4 insert_o
  s5

-- User 2 (nodeId = 2) deletes the 'h'
def user2_nodeId : nodeId := 2

def remove_h : Op := Op.RemoveOp {
  opId := (0, user2_nodeId),      -- User 2's first operation
  removedId := (0, user1_nodeId)  -- Remove the 'h' inserted by User 1
}

-- Apply the delete operation
def state_after_delete_h : concrete_st :=
  do_ state_after_hello remove_h

/-
Expected behavior:
1. state_after_hello contains 5 characters: 'h', 'e', 'l', 'l', 'o'
   - All characters have deleted = false
   - opIds are (0,1), (1,1), (2,1), (3,1), (4,1) respectively

2. state_after_delete_h contains the same 5 characters, but:
   - Character 'h' at position 0 now has deleted = true
   - Other characters remain unchanged
   - When rendering, filter out deleted characters to show "ello"

3. The CRDT property: If these operations arrive in any order at different
   replicas, they will converge to the same state (tombstone for 'h')
-/

-- Extract info from a single character
def extractCharInfo (char : CharMetaData) : opIdType × Char × Bool :=
  (char.insert_opId, char.c, char.deleted)

-- Map over all characters in state_after_hello
def allCharsInfo : Array (opIdType × Char × Bool) :=
  state_after_hello.map extractCharInfo

#eval allCharsInfo
-- Expected output: #[((0, 1), 'h', false), ((1, 1), 'e', false), ((2, 1), 'l', false), ((3, 1), 'l', false), ((4, 1), 'o', false)]

-- Same for state_after_delete_h
def allCharsInfoAfterDelete : Array (opIdType × Char × Bool) :=
  state_after_delete_h.map extractCharInfo

#eval allCharsInfoAfterDelete
-- Expected: #[((0, 1), 'h', true), ((1, 1), 'e', false), ((2, 1), 'l', false), ((3, 1), 'l', false), ((4, 1), 'o', false)]
-- Notice: 'h' now has deleted = true

-- Helper: Get visible text (filter out deleted characters)
def getVisibleText (state : concrete_st) : String :=
  let visibleChars := state.filter (fun char => !char.deleted)
  String.ofList (visibleChars.map (fun char => char.c)).toList

#eval getVisibleText state_after_hello
-- Expected output: "hello"

#eval getVisibleText state_after_delete_h
-- Expected output: "ello"

-- ============================================================================
-- Example 2: User writes "Hello World" and bolds "Hello"
-- ============================================================================

-- User 3 (nodeId = 3) writes "Hello World"
def user3_nodeId : nodeId := 3

-- Insert operations for "Hello World"
def insert_H : Op := Op.InsertOp {
  opId := (0, user3_nodeId),
  afterId := none,
  character := 'H'
}

def insert_e2 : Op := Op.InsertOp {
  opId := (1, user3_nodeId),
  afterId := some (0, user3_nodeId),
  character := 'e'
}

def insert_l3 : Op := Op.InsertOp {
  opId := (2, user3_nodeId),
  afterId := some (1, user3_nodeId),
  character := 'l'
}

def insert_l4 : Op := Op.InsertOp {
  opId := (3, user3_nodeId),
  afterId := some (2, user3_nodeId),
  character := 'l'
}

def insert_o2 : Op := Op.InsertOp {
  opId := (4, user3_nodeId),
  afterId := some (3, user3_nodeId),
  character := 'o'
}

def insert_space : Op := Op.InsertOp {
  opId := (5, user3_nodeId),
  afterId := some (4, user3_nodeId),
  character := ' '
}

def insert_W : Op := Op.InsertOp {
  opId := (6, user3_nodeId),
  afterId := some (5, user3_nodeId),
  character := 'W'
}

def insert_o3 : Op := Op.InsertOp {
  opId := (7, user3_nodeId),
  afterId := some (6, user3_nodeId),
  character := 'o'
}

def insert_r : Op := Op.InsertOp {
  opId := (8, user3_nodeId),
  afterId := some (7, user3_nodeId),
  character := 'r'
}

def insert_l5 : Op := Op.InsertOp {
  opId := (9, user3_nodeId),
  afterId := some (8, user3_nodeId),
  character := 'l'
}

def insert_d : Op := Op.InsertOp {
  opId := (10, user3_nodeId),
  afterId := some (9, user3_nodeId),
  character := 'd'
}

-- Build state with "Hello World"
def state_hello_world : concrete_st :=
  let s0 := init_st
  let s1 := do_ s0 insert_H
  let s2 := do_ s1 insert_e2
  let s3 := do_ s2 insert_l3
  let s4 := do_ s3 insert_l4
  let s5 := do_ s4 insert_o2
  let s6 := do_ s5 insert_space
  let s7 := do_ s6 insert_W
  let s8 := do_ s7 insert_o3
  let s9 := do_ s8 insert_r
  let s10 := do_ s9 insert_l5
  let s11 := do_ s10 insert_d
  s11

#eval getVisibleText state_hello_world
-- Expected: "Hello World"

-- Now apply Bold formatting to "Hello" (characters at positions 0-4)
-- Bold starts after 'H' and ends before the space
def add_bold_hello : Op := Op.AddMarkOp {
  opId := (11, user3_nodeId),
  _start := .ManualSpan { type := .After, opId := (0, user3_nodeId) },  -- After 'H'
  _end := .ManualSpan { type := .After, opId := (5, user3_nodeId) },   -- Before space
  mark := .Bold
}

def state_with_bold : concrete_st :=
  do_ state_hello_world add_bold_hello

-- Helper: Check if a mark operation is in a character's mark set
def hasBoldInMarkOps (markSet : Option (set MarkOp)) (pos : Bool) : Bool :=
  match markSet with
  | none => false
  | some s =>
      -- Check if there's an AddMarkOperation with Bold in the set
      if pos = true then
      mem (MarkOp.AddMarkOperation {
        opId := (11, user3_nodeId),
        _start := .ManualSpan { type := .After, opId := (0, user3_nodeId) },
        _end := .ManualSpan { type := .After, opId := (5, user3_nodeId) },
        mark := .Bold
      }) s
      else true

-- Extract character at index with mark info
def getCharWithMarks (state : concrete_st) (idx : Nat) (pos: Bool) : Option (Char × Bool × Bool) :=
  if h : idx < state.size then
    let char := state[idx]
    some (char.c,
          hasBoldInMarkOps char.markOpsBefore? pos,
          hasBoldInMarkOps char.markOpsAfter? pos)
  else
    none

-- Check 'H' (index 0) - Bold should be in markOpsAfter
def h_marks := getCharWithMarks state_with_bold 0
#eval! h_marks true
-- Output: some ('H', false, true) - Bold is in markOpsAfter

-- Check space (index 5) - Bold should be in markOpsBefore
def space_marks := getCharWithMarks state_with_bold 5
#eval! space_marks false
-- output : some (' ', false, true) - markOpsAfter should be an empty set indicating that the operation ends here.
