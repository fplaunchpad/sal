import Sal.Interfaces.Set_Extended
import Sal.MRDTs.Peritext_with_tombstones.Peritext_MRDT
import Sal.MRDTs.Peritext_with_tombstones.Peritext_ReadSide
import Mathlib.Tactic.IntervalCases

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 800000

open Classical

/-! # Peritext (MRDT) Test DSL

MRDT-side counterpart of `Sal/CRDTs/Peritext/Peritext_DSL.lean`.
Same `Scenario` API, ported to the MRDT's flat-set substrate. -/

namespace Peritext_MRDT_DSL

structure Scenario where
  state : concrete_st
  positions : List (OpId × Char)
  next_ts : Nat

@[simp]
def Scenario.empty : Scenario := ⟨init_st, [], 1⟩

@[simp]
def lastOpId : List (OpId × Char) → OpId
  | [] => (0, 0)
  | [(oid, _)] => oid
  | _ :: rest => lastOpId rest

@[simp]
def Scenario.insertChar (sc : Scenario) (rid : Nat) (c : Char) : Scenario :=
  let after := lastOpId sc.positions
  let opId : OpId := (sc.next_ts, rid)
  let op : op_t := (sc.next_ts, rid, app_op_t.Insert c.toNat after)
  { state := do_ sc.state op
    positions := sc.positions ++ [(opId, c)]
    next_ts := sc.next_ts + 1 }

@[simp]
def Scenario.insertChars (sc : Scenario) (rid : Nat) (cs : List Char) : Scenario :=
  cs.foldl (fun acc c => acc.insertChar rid c) sc

@[simp]
def Scenario.insertCharAfter (sc : Scenario) (rid : Nat) (afterId : OpId)
    (c : Char) : Scenario :=
  let opId : OpId := (sc.next_ts, rid)
  let op : op_t := (sc.next_ts, rid, app_op_t.Insert c.toNat afterId)
  { state := do_ sc.state op
    positions := sc.positions ++ [(opId, c)]
    next_ts := sc.next_ts + 1 }

@[simp]
def matchPrefix : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: cs, t :: ts => decide (c = t) && matchPrefix cs ts

@[simp]
def nthOpId : List (OpId × Char) → Nat → OpId
  | [], _ => (0, 0)
  | (oid, _) :: _, 0 => oid
  | _ :: rest, n + 1 => nthOpId rest n

@[simp]
def findRangeAux : List (OpId × Char) → List Char → Option (OpId × OpId)
  | _, [] => none
  | [], _ :: _ => none
  | (oid, c) :: rest, t :: ts =>
    if matchPrefix (c :: rest.map Prod.snd) (t :: ts) then
      let len := ts.length
      some (oid, nthOpId ((oid, c) :: rest) len)
    else findRangeAux rest (t :: ts)

@[simp]
def Scenario.findRange (sc : Scenario) (target : List Char) :
    Option (OpId × OpId) :=
  findRangeAux sc.positions target

@[simp]
def Scenario.addMark (sc : Scenario) (rid markType : Nat)
    (target : List Char) : Scenario :=
  match sc.findRange target with
  | none => sc
  | some (startId, endId) =>
    let op : op_t :=
      (sc.next_ts, rid, app_op_t.AddMark startId false endId true markType)
    { state := do_ sc.state op
      positions := sc.positions
      next_ts := sc.next_ts + 1 }

@[simp]
def Scenario.removeMark (sc : Scenario) (rid markType : Nat)
    (target : List Char) : Scenario :=
  match sc.findRange target with
  | none => sc
  | some (startId, endId) =>
    let op : op_t :=
      (sc.next_ts, rid, app_op_t.RemoveMark startId false endId true markType)
    { state := do_ sc.state op
      positions := sc.positions
      next_ts := sc.next_ts + 1 }

@[simp]
def Scenario.bold (sc : Scenario) (rid : Nat) (target : List Char) : Scenario :=
  sc.addMark rid 0 target

@[simp]
def Scenario.unbold (sc : Scenario) (rid : Nat) (target : List Char) : Scenario :=
  sc.removeMark rid 0 target

@[simp]
def Scenario.removeAt (sc : Scenario) (rid pos : Nat) : Scenario :=
  let target := nthOpId sc.positions pos
  let op : op_t := (sc.next_ts, rid, app_op_t.Remove target)
  { state := do_ sc.state op
    positions := sc.positions
    next_ts := sc.next_ts + 1 }

theorem chain_reach (s : concrete_st) (i j : Nat) (h_i_le_j : i ≤ j)
    (h_after : ∀ k, i ≤ k → k < j → after_of s (k + 1, 0) (k, 0) = true) :
    afters_reach s (j, 0) (i, 0) := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp h_i_le_j
    subst this
    exact afters_reach.refl _
  | succ k ih =>
    by_cases h_eq : i = k + 1
    · subst h_eq; exact afters_reach.refl _
    · have h_i_le_k : i ≤ k := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h_i_le_j h_eq)
      exact afters_reach.step
        (h_after k h_i_le_k (Nat.lt_succ_self k))
        (ih h_i_le_k (fun n h1 h2 => h_after n h1 (Nat.lt_succ_of_lt h2)))

theorem afters_reach_to_visible_lt (s : concrete_st) (c anc : OpId) :
    afters_reach s c anc → c ≠ anc → visible_lt s anc c := by
  intro h_reach h_ne
  induction h_reach with
  | refl c => exact absurd rfl h_ne
  | @step c mid anc h_after _ ih =>
    by_cases h_eq : mid = anc
    · subst h_eq
      exact visible_lt.parent_child h_after
    · exact visible_lt.trans (ih h_eq) (visible_lt.parent_child h_after)

/-! ## Anchor positions and named mark constructors

A mark boundary lies *between* two characters: relative to its
anchor OpId, it can sit either `before` that character or `after`
it. See the CRDT-side `Peritext_DSL.lean` for the full description.
The MRDT's `MarkOp` is a `structure` with named fields, so the
underlying boolean storage is wrapped behind `Anchor`-taking
constructors below. -/

inductive Anchor where
  | before
  | after
deriving DecidableEq, Repr

@[simp] def Anchor.toBool : Anchor → Bool
  | .before => false
  | .after => true

namespace Mark

/-- Generic mark constructor with named fields. -/
@[simp] def mk
    (opId startId endId : OpId) (startSide endSide : Anchor)
    (markType : Nat) (isAdd : Bool) : MarkOp :=
  ⟨opId, startId, startSide.toBool, endId, endSide.toBool, markType, isAdd⟩

@[simp] def bold (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 0 true

@[simp] def unbold (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 0 false

@[simp] def italic (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .after 1 true

@[simp] def link (opId startId endId : OpId) : MarkOp :=
  mk opId startId endId .before .before 1 true

end Mark

@[simp]
def Scenario.opIdAt (sc : Scenario) (pos : Nat) : OpId :=
  nthOpId sc.positions pos

@[simp]
noncomputable def Scenario.formattedAt (sc : Scenario) (pos mt : Nat) : Bool :=
  formatted_visible sc.state (sc.opIdAt pos) mt

@[simp]
noncomputable def Scenario.boldAt (sc : Scenario) (pos : Nat) : Bool :=
  sc.formattedAt pos 0

@[simp]
noncomputable def Scenario.visibleAt (sc : Scenario) (pos : Nat) : Bool :=
  visible sc.state (sc.opIdAt pos)

end Peritext_MRDT_DSL
