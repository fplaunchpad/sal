import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

/-!
# Peritext (rich text) as a state-based MRDT

MRDT companion to `Sal/CRDTs/Peritext_CRDT.lean`, following the CSCW 2022
Peritext paper (Litt, van Hardenberg, et al.) via the op-based
specification and adapting the pattern used by `Replicated_Growable_Array_MRDT`.

The Peritext CRDT keeps four grow-only components:

  chars    : map OpId ℕ         -- character payloads
  afters   : map OpId OpId      -- RGA after-pointers
  deleted  : map OpId Bool      -- tombstone bits
  marks    : set AnchorAttachment -- formatting mark attachments

RGA's tombstones are structurally load-bearing (later inserts reference
earlier character ids via `after_id`), so the MRDT cannot strip them the
way the OR-Set or Add-Win PQ MRDTs can. Following the precedent of
`Replicated_Growable_Array_MRDT`, this MRDT keeps all four components as
grow-only sets and uses pointwise-union for merge; it does not rely on
the LCA at all. This makes the translation mechanical and keeps the 24
VCs in the same shape as the Peritext CRDT and RGA MRDT.

State as three sets (afters folded into the char record):

  chars : set (OpId × OpId × ℕ)    -- (id, after_id, ch)
  dels  : set OpId                 -- tombstoned character ids
  marks : set AnchorAttachment

## Rich-text read-side theorems

A section at the end of the file mirrors the read-side additions in
`Peritext_CRDT.lean`: `readRichText`, `formatted`, and the anchor-
side-sensitive coverage predicate `in_span_boundary`, plus
characterization theorems for the paper's headline merge semantics
(expand/contract via anchor sides, Add-beats-Remove priority rule,
and anchors-survive-tombstones). See the CRDT file's module docstring
for scope and caveats.
-/

@[simp] abbrev OpId := ℕ × ℕ

/-- Mark op payload — see `Peritext_CRDT` for field meaning. -/
structure MarkOp where
  opId : OpId
  startId : OpId
  startSide : Bool
  endId : OpId
  endSide : Bool
  markType : ℕ
  isAdd : Bool
deriving DecidableEq

/-- A single mark op anchored at one of its two endpoints. -/
structure AnchorAttachment where
  charId : OpId
  side : Bool
  markOp : MarkOp
deriving DecidableEq

/-- Char record: `(id, after_id, ch)`. -/
abbrev CharRec := OpId × OpId × ℕ

/-- Σ = (chars, removed, marks). Three grow-only components:
  * `chars`   : `set CharRec` — every `Insert` stakes a `(id, after, ch)`.
  * `removed` : `set OpId`    — tombstones on char ids.
  * `marks`   : `set AnchorAttachment` — one entry per (mark op, anchor
                side); flat-set representation per the CRDT refactor. -/
@[simp] abbrev concrete_st :=
  set CharRec × set OpId × set AnchorAttachment

/-- Initial state: all three components empty. -/
@[simp]
def init_st : concrete_st := (empty, empty, empty)

/-- Pointwise set equality on all three components. -/
@[simp]
def eq (a b : concrete_st) :=
  equal (Prod.fst a) (Prod.fst b) ∧
  equal (Prod.fst (Prod.snd a)) (Prod.fst (Prod.snd b)) ∧
  equal (Prod.snd (Prod.snd a)) (Prod.snd (Prod.snd b))

/-- Four ops:
  * `Insert ch after`           — add char `ch` right after `after`.
  * `Remove target`             — tombstone char `target`.
  * `AddMark s sSd e eSd mt`    — mark range `(s, sSd)…(e, eSd)` as `mt`.
  * `RemoveMark s sSd e eSd mt` — unmark the same range. -/
inductive app_op_t : Type where
| Insert (ch : ℕ) (after : OpId)
| Remove (target : OpId)
| AddMark (startId : OpId) (startSide : Bool) (endId : OpId) (endSide : Bool) (markType : ℕ)
| RemoveMark (startId : OpId) (startSide : Bool) (endId : OpId) (endSide : Bool) (markType : ℕ)

abbrev op_t := ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

/-- Effect:
  * `Insert`     adds a CharRec with this op's `(ts, rid)` as its OpId.
  * `Remove`     adds `target` to the tombstone set.
  * `AddMark`    stakes two AnchorAttachments (start and end anchors),
                 each carrying the same MarkOp with `isAdd = true`.
  * `RemoveMark` same, but with `isAdd = false`. -/
@[simp]
def do_ (s : concrete_st) (o : op_t) : concrete_st :=
match o with
| (ts, (rid, .Insert ch after)) =>
    (add ((ts, rid), after, ch) (Prod.fst s),
     Prod.fst (Prod.snd s),
     Prod.snd (Prod.snd s))
| (_, (_, .Remove target)) =>
    (Prod.fst s,
     add target (Prod.fst (Prod.snd s)),
     Prod.snd (Prod.snd s))
| (ts, (rid, .AddMark sId sSd eId eSd mt)) =>
    let mark : MarkOp := ⟨(ts, rid), sId, sSd, eId, eSd, mt, true⟩
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     add ⟨eId, eSd, mark⟩
         (add ⟨sId, sSd, mark⟩ (Prod.snd (Prod.snd s))))
| (ts, (rid, .RemoveMark sId sSd eId eSd mt)) =>
    let mark : MarkOp := ⟨(ts, rid), sId, sSd, eId, eSd, mt, false⟩
    (Prod.fst s,
     Prod.fst (Prod.snd s),
     add ⟨eId, eSd, mark⟩
         (add ⟨sId, sSd, mark⟩ (Prod.snd (Prod.snd s))))

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc := Either`: every op writes to a unique OpId slot (via
`distinct_ops` on ts), so ops from distinct replicas commute. -/
@[simp]
def rc (_o1 _o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-- Merge: pointwise three-way union on each of the three components.
All three are grow-only, so the MRDT's LCA argument is vestigial here
(just like `Replicated_Growable_Array_MRDT`). -/
@[simp]
def merge (l a b : concrete_st) : concrete_st :=
  (union (Prod.fst l) (union (Prod.fst a) (Prod.fst b)),
   union (Prod.fst (Prod.snd l)) (union (Prod.fst (Prod.snd a)) (Prod.fst (Prod.snd b))),
   union (Prod.snd (Prod.snd l)) (union (Prod.snd (Prod.snd a)) (Prod.snd (Prod.snd b))))


set_option maxHeartbeats 2000000

theorem rc_non_comm (o1: op_t) (o2: op_t):
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2
→
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  intro h
  refine ⟨fun _ s => ?_, fun _ => rfl⟩
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _ | _ | _⟩ <;> simp +decide [*] at *
  all_goals grind

theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3) := by sal

theorem  merge_comm (l: concrete_st) (a: concrete_st) (b: concrete_st) :
eq (merge l a b) (merge l b a) := by sal

theorem merge_idem (s: concrete_st):
eq (merge s s s) s := by sal

theorem base_2op (o1: op_t) (o2: op_t):
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2
→
eq (merge init_st (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st init_st (do_ init_st o2)) o1) := by sal

theorem ind_lca_2op (l: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧ eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) ∧ eq (merge l (do_ l o1) (do_ l o2)) (do_ (merge l l (do_ l o2)) o1)
→
eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ (do_ l ol) o2)) (do_ (merge (do_ l ol) (do_ l ol) (do_ (do_ l ol) o2)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind


theorem inter_right_base_2op  (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
(rc o2 o1 = rc_res.Fst_then_snd ∨ rc o2 o1 = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ rc ob o1 = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1) ∧
                    eq (merge l (do_ a o1) (do_ (do_ b ob) o2)) (do_ (merge l a (do_ (do_ b ob) o2)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    := by sal

theorem inter_left_base_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o2 ob ∧ distinct_ops o2 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1)
                    →
                  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
:= by sal


theorem inter_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b ob) ol) o2)) o1)
                    →
 eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ (do_ b o) ob) ol) o2)) o1)
:= by sal


theorem inter_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ob: op_t) (ol: op_t) :
 (rc o2 o1) = rc_res.Fst_then_snd ∧ (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid o2 != get_rid o1 ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops o2 ob ∧
                    distinct_ops o2 ol ∧ distinct_ops o2 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ (do_ b ol) o2)) o1)
                    →
   eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ (do_ b ol) o2)) o1)
   := by sal

theorem inter_lca_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (ol: op_t) :
((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 ol ∧ distinct_ops o2 ol ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1) ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
  →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ol) o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ol) o2)) o1) := by sal

theorem ind_right_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o2': op_t) :
(rc o2 o1) = rc_res.Fst_then_snd ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o2' ∧ distinct_ops o2 o2' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →  eq (merge l (do_ a o1) (do_ (do_ b o2') o2)) (do_ (merge l a (do_ (do_ b o2') o2)) o1) := by sal

theorem ind_left_2op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o2: op_t) (o1': op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2 ∧ distinct_ops o1 o1' ∧ distinct_ops o2 o1' ∧
                    eq (merge l (do_ a o1) (do_ b o2)) (do_ (merge l a (do_ b o2)) o1)
                    →
 eq (merge l (do_ (do_ a o1') o1) (do_ b o2)) (do_ (merge l (do_ a o1') (do_ b o2)) o1)
 := by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases o1' with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem base_1op (o1: op_t) :
eq (merge init_st (do_ init_st o1) init_st) (do_ (merge init_st init_st init_st) o1) := by sal

theorem  ind_lca_1op (l: concrete_st) (o1: op_t) (ol: op_t) :
 distinct_ops o1 ol ∧
                    (get_rid o1 != get_rid ol ∨ Prod.fst ol < Prod.fst o1) ∧
                    eq (merge l (do_ l o1) l) (do_ (merge l l l) o1)
  → eq (merge (do_ l ol) (do_ (do_ l ol) o1) (do_ l ol)) (do_ (merge (do_ l ol) (do_ l ol) (do_ l ol)) o1) := by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem inter_right_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t)  :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    ((rc ob o1) = rc_res.Fst_then_snd → eq (merge l (do_ a o1) (do_ b ob)) (do_ (merge l a (do_ b ob)) o1)) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
  := by sal

theorem inter_left_base_1op (l : concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops ob ol ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
  eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
  := by sal

theorem inter_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
rc ob ol =  rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧ (¬(rc o ob = rc_res.Either) ∨ (rc o ol = rc_res.Fst_then_snd)) ∧ distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧ get_rid o != get_rid ol ∧ eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ b ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ b ob) ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ (do_ (do_ b o) ob) ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ (do_ (do_ b o) ob) ol)) o1)
:= by sal

theorem inter_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ob: op_t) (ol: op_t) (o: op_t) :
 (rc ob ol) = rc_res.Fst_then_snd ∧ get_rid ob != get_rid ol ∧
                    (¬ ((rc o ob) = rc_res.Either) ∨ (rc o ol) = rc_res.Fst_then_snd) ∧
                    distinct_ops o1 ob ∧ distinct_ops o1 ol ∧ distinct_ops o1 o ∧ distinct_ops ob ol ∧ distinct_ops ob o ∧ distinct_ops ol o ∧
                    get_rid o != get_rid ol ∧
                    eq (merge (do_ l ol) (do_ (do_ (do_ a ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ a ob) ol) (do_ b ol)) o1)
                    →
                     eq (merge (do_ l ol) (do_ (do_ (do_ (do_ a o) ob) ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ (do_ (do_ a o) ob) ol) (do_ b ol)) o1)
        := by sal

theorem inter_lca_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (ol: op_t) (oi: op_t) :
distinct_ops o1 ol ∧ distinct_ops o1 oi ∧ distinct_ops ol oi ∧
                    (exists o, (rc o ol) = rc_res.Fst_then_snd) ∧
                    (exists o, (rc o oi) = rc_res.Fst_then_snd) ∧
                    eq (merge (do_ l oi) (do_ (do_ a oi) o1) (do_ b oi)) (do_ (merge (do_ l oi) (do_ a oi) (do_ b oi)) o1) ∧
                    eq (merge (do_ l ol) (do_ (do_ a ol) o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b ol)) o1)
                    →
                  eq (merge (do_ (do_ l oi) ol) (do_ (do_ (do_ a oi) ol) o1) (do_ (do_ b oi) ol))
                      (do_ (merge (do_ (do_ l oi) ol) (do_ (do_ a oi) ol) (do_ (do_ b oi) ol)) o1)
:= by sal

theorem ind_left_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o1: op_t) (o1': op_t) (ol: op_t) :
distinct_ops o1 o1' ∧ distinct_ops o1 ol ∧ distinct_ops o1' ol ∧
                    eq (merge (do_ l ol) (do_ a o1) (do_ b ol)) (do_ (merge (do_ l ol) a (do_ b ol)) o1)
→
eq (merge (do_ l ol) (do_ (do_ a o1') o1) (do_ b ol)) (do_ (merge (do_ l ol) (do_ a o1') (do_ b ol)) o1)
:= by
  intro h
  rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o1' with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem ind_right_1op (l: concrete_st) (a: concrete_st) (b: concrete_st) (o2: op_t) (o2': op_t) (ol: op_t)  :
distinct_ops o2 o2' ∧ distinct_ops o2 ol ∧ distinct_ops o2' ol ∧
                    eq (merge (do_ l ol) (do_ a ol) (do_ b o2)) (do_ (merge (do_ l ol) (do_ a ol) b) o2)
→
eq (merge (do_ l ol) (do_ a ol) (do_ (do_ b o2') o2)) (do_ (merge (do_ l ol) (do_ a ol) (do_ b o2')) o2)
:= by
  intro h
  rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2' with ⟨_, _, _ | _ | _ | _⟩ <;>
    rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*] at h ⊢
  all_goals grind

theorem  lem_0op (l: concrete_st) (a: concrete_st) (b: concrete_st) (ol: op_t) :
eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol)
:= by
  rcases ol with ⟨_, _, _ | _ | _ | _⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro k <;>
    simp +decide [*]
  all_goals grind


/-! ## Read-side projection and rich-text merge-semantic characterizations

Mirror of the CRDT additions — see `Sal/CRDTs/Peritext_CRDT.lean` for
the full scope, caveats, and semantic motivation. The MRDT's state
shape differs (chars as a flat `set CharRec` of `(id, after, ch)`
triples, a `set OpId` tombstone set, and the `set AnchorAttachment`
component), so the concrete definitions adapt; the theorems carry
the same content.

Tiers covered:
1. `readRichText_convergent` — pointwise-`eq` implies identical rich-text read.
2. `expand_contract_{end,start}_{after,before}` — anchor sides decide
   whether concurrent boundary inserts fall inside the mark.
3. `add_beats_remove` — concurrent `AddMark` wins over concurrent
   `RemoveMark` for every covered character (state-based form).
4. `anchors_survive_tombstones` — tombstoning any interior character
   leaves the formatting of the other visible characters unchanged.
-/

open Classical

/-- Lexicographic max on `OpId` (MRDT-local copy; used by the priority rule). -/
def opid_max (a b : OpId) : OpId :=
  if a.1 > b.1 then a
  else if b.1 > a.1 then b
  else if a.2 ≥ b.2 then a
  else b

@[simp] def chars_of   (s : concrete_st) : set CharRec         := Prod.fst s
@[simp] def removed_of (s : concrete_st) : set OpId            := Prod.fst (Prod.snd s)
@[simp] def marks_of   (s : concrete_st) : set AnchorAttachment := Prod.snd (Prod.snd s)

/-- Is mark op `m` present in state `s`?  Present iff either of its
two canonical anchor attachments appears in the marks set. -/
@[simp]
def mark_present (s : concrete_st) (m : MarkOp) : Bool :=
  marks_of s ⟨m.startId, m.startSide, m⟩ ||
  marks_of s ⟨m.endId, m.endSide, m⟩

/-- Is `c` visible in `s`: some `CharRec` has id `c` and `c` is not
tombstoned.  Noncomputable: the existential requires Classical. -/
noncomputable def visible (s : concrete_st) (c : OpId) : Bool :=
  decide (∃ after ch, chars_of s (c, after, ch) = true) && !(removed_of s c)

/-- Was `c` inserted with `after = target`? -/
noncomputable def after_of (s : concrete_st) (c target : OpId) : Bool :=
  decide (∃ ch, chars_of s (c, target, ch) = true)

/-- Boundary-case covering predicate — same content as the CRDT's
version (see its docstring for the anchor-side semantics). -/
noncomputable def in_span_boundary (s : concrete_st) (m : MarkOp) (c : OpId) : Bool :=
  if c = m.startId then !m.startSide
  else if c = m.endId then m.endSide
  else if after_of s c m.startId = true then m.startSide
  else if after_of s c m.endId = true then m.endSide
  else false

/-- Priority: Add beats Remove, else LWW by opId. -/
def mark_beats (a b : MarkOp) : Bool :=
  if a.isAdd && !b.isAdd then true
  else if !a.isAdd && b.isAdd then false
  else decide (opid_max a.opId b.opId = a.opId)

/-- Is `m` the winning covering mark for `(c, mt)` in state `s`? -/
noncomputable def mark_wins (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_boundary s m c = true ∧
  m.markType = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_boundary s m' c = true →
        m'.markType = mt →
        m' ≠ m →
        mark_beats m m' = true

/-- Is visible char `c` formatted with mark type `mt` in state `s`? -/
noncomputable def formatted (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins s m c mt ∧ m.isAdd = true)
  else false

/-- Per-character rich-text read: `some formatting` if visible, else
`none`. The list-valued form would require an RGA traversal
formalization that's out of scope; this per-char function is the
abstraction the convergence theorem is stated against. -/
noncomputable def readRichText (s : concrete_st) : OpId → Option (ℕ → Bool) :=
  fun c => if visible s c = true then some (fun mt => formatted s c mt) else none

set_option maxHeartbeats 0

/-- **Tier 1 — Convergence.** Pointwise `eq` implies identical
rich-text read at every character id.

Proof: the MRDT's `eq` is `∀ x, s₁.i x == s₂.i x` componentwise,
which lifts via `funext` to full functional equality on each set
component, and then to `s₁ = s₂` via `Prod.ext`. `readRichText` is
a pure function of state, so the result follows by `rw`. -/
theorem readRichText_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readRichText s₁ = readRichText s₂ := by
  intro h
  rcases h with ⟨hch, hrm, hmk⟩
  have hch'' : Prod.fst s₁ = Prod.fst s₂ := by
    funext x; have := hch x; simpa using this
  have hrm'' : Prod.fst (Prod.snd s₁) = Prod.fst (Prod.snd s₂) := by
    funext x; have := hrm x; simpa using this
  have hmk'' : Prod.snd (Prod.snd s₁) = Prod.snd (Prod.snd s₂) := by
    funext x; have := hmk x; simpa using this
  have h_eq : s₁ = s₂ := Prod.ext hch'' (Prod.ext hrm'' hmk'')
  rw [h_eq]

/-- **Tier 4 — Anchors survive tombstones.**

Tombstoning any character `c_rm` does not change the formatting of
any other visible character `c ≠ c_rm`.  Parameterized over all
states, all mark types, and all replica ids.  The MRDT's `Remove`
op extends the `removed` set with `c_rm`; `chars` and `marks` are
untouched, and the `removed` lookup at `c` is invariant because
`c ≠ c_rm`. -/
theorem anchors_survive_tombstones
    (s : concrete_st) (c c_rm : OpId) (mt : ℕ) (ts rid : ℕ) :
    c ≠ c_rm →
    formatted s c mt = formatted (do_ s (ts, rid, app_op_t.Remove c_rm)) c mt := by
  intro hne
  -- Removing `c_rm` only adds `c_rm` to the `removed` set; `chars` and
  -- `marks` are untouched. For `c ≠ c_rm`, `removed` lookup at `c`
  -- is invariant: `add c_rm rm c = rm c || (c = c_rm) = rm c`.
  have h_rm_inv : add c_rm (Prod.fst (Prod.snd s)) c = Prod.fst (Prod.snd s) c := by
    simp [add, union, _root_.singleton, hne]
  simp only [formatted, visible, do_, mark_present, marks_of, chars_of,
             removed_of, in_span_boundary, after_of, mark_wins, h_rm_inv]

/-- **Tier 3 — Concurrent Add beats concurrent Remove.**

Same semantic content as the CRDT theorem — see
`Peritext_CRDT.add_beats_remove` for the state-based-vs-op-based
caveat on "concurrent."  If an `AddMark` is present and beats every
other same-type covering mark, the covered character is formatted. -/
theorem add_beats_remove
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp : MarkOp) :
    addOp.isAdd = true →
    addOp.markType = mt →
    mark_present s addOp = true →
    in_span_boundary s addOp c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt_a h_pres_a h_cov_a h_vis h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩

/-- **Tier 2 — Expand/contract at the `endId` boundary (expand case).**

With `endSide = true`, a character inserted immediately after `endId`
is covered — the mark *expands* to include the concurrent boundary
insert. -/
theorem expand_contract_end_after
    (s : concrete_st) (c_new : OpId) (mt : ℕ) (m : MarkOp) :
    m.isAdd = true →
    m.endSide = true →
    m.markType = mt →
    mark_present s m = true →
    visible s c_new = true →
    after_of s c_new m.endId = true →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    ¬ after_of s c_new m.startId = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c_new = true →
           m'.markType = mt →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c_new mt = true := by
  intro h_add h_eSd h_mt h_pres h_vis h_after h_ne_s h_ne_e h_ns_after h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, ?_, h_mt, h_beats⟩, h_add⟩
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Contract at the `endId` boundary.**

With `endSide = false`, the same boundary insert is *not* covered —
the mark *contracts* away from the concurrent boundary insert. -/
theorem expand_contract_end_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.endSide = false →
    m.endId ≠ c_new →
    c_new ≠ m.startId →
    after_of s c_new m.endId = true →
    ¬ after_of s c_new m.startId = true →
    in_span_boundary s m c_new = false := by
  intro h_eSd h_ne h_ne_s h_after h_ns_after
  have h_ne' : c_new ≠ m.endId := fun h => h_ne h.symm
  simp only [in_span_boundary, h_ne_s, h_ne', h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Start-side expansion.** -/
theorem expand_contract_start_after
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.startSide = true →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    after_of s c_new m.startId = true →
    in_span_boundary s m c_new = true := by
  intro h_sSd h_ne_s h_ne_e h_after
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd]
  grind

/-- **Tier 2 (symmetric) — Start-side contraction.** -/
theorem expand_contract_start_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.startSide = false →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    after_of s c_new m.startId = true →
    ¬ after_of s c_new m.endId = true →
    in_span_boundary s m c_new = false := by
  intro h_sSd h_ne_s h_ne_e h_after h_not_after_end
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd, h_not_after_end]
  grind

/-- **Paper Ex 2 — Partially overlapping Adds of the same type.**

If no Remove of type `mt` covers `c`, and some `AddMark` `m` covers
`c` and beats every other covering Add by LWW, then `c` is formatted.
Captures the "union of overlapping bolds is bold" semantics. -/
theorem partial_overlap_all_adds_formatted
    (s : concrete_st) (c : OpId) (mt : ℕ) (m : MarkOp) :
    m.isAdd = true →
    m.markType = mt →
    mark_present s m = true →
    in_span_boundary s m c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m'.isAdd = false →
           False) →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m'.isAdd = true →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt h_pres h_cov h_vis h_no_rem h_beats_adds
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, h_cov, h_mt, ?_⟩, h_add⟩
  intro m' h_pres' h_cov' h_mt' h_ne
  match h_isAdd : m'.isAdd with
  | true  => exact h_beats_adds m' h_pres' h_cov' h_mt' h_isAdd h_ne
  | false => exact absurd (h_no_rem m' h_pres' h_cov' h_mt' h_isAdd) id

/-- **Paper Ex 3 — Different-type Adds coexist.**

Two Adds with distinct `markType` at the same character both apply:
the character is formatted as both. Captures the paper's independence
of mark types. -/
theorem different_type_adds_coexist
    (s : concrete_st) (c : OpId) (mB mI : MarkOp) :
    mB.isAdd = true →
    mI.isAdd = true →
    mB.markType ≠ mI.markType →
    mark_present s mB = true →
    mark_present s mI = true →
    in_span_boundary s mB c = true →
    in_span_boundary s mI c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           m'.markType = mB.markType → m' ≠ mB →
           mark_beats mB m' = true) →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           m'.markType = mI.markType → m' ≠ mI →
           mark_beats mI m' = true) →
    formatted s c mB.markType = true ∧ formatted s c mI.markType = true := by
  intro h_addB h_addI _ h_presB h_presI h_covB h_covI h_vis h_beatsB h_beatsI
  refine ⟨?_, ?_⟩
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mB ⟨⟨h_presB, h_covB, rfl, h_beatsB⟩, h_addB⟩)
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mI ⟨⟨h_presI, h_covI, rfl, h_beatsI⟩, h_addI⟩)

/-- **Paper Ex 5 (negative case) — No covering Add → unformatted.**

If no `AddMark` of type `mt` covers `c` at the boundary, then `c` is
not formatted with `mt`. Holds regardless of priority rule — depends
only on the definition of `formatted`. -/
theorem no_add_cover_implies_unformatted
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    (∀ m, mark_present s m = true →
          in_span_boundary s m c = true →
          m.markType = mt →
          m.isAdd = false) →
    formatted s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins s m c mt ∧ m.isAdd = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : w.isAdd = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl
