import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal

open Classical

/-!
# Why tombstone-free RGA needs the path: a `cond_comm_base` counterexample

This is the salvaged negative result that motivates `RGA_Tombstone_Free_MRDT.lean`.
It encodes the *plain* tombstone-free splice RGA, where operations carry only an
immediate anchor (no ancestor path), and proves that this design **fails** one of
the 24 RA-linearizability VCs, `cond_comm_base`. The path-carrying design in the
sibling file exists precisely to repair this failure.

## What is encoded

State is `map ℕ (ℕ × ℕ)` (`id ↦ (element, anchor)`), with `0` the root. `Ins e a`
records `(t, (e, a))`; `Del x` is `splice`: physically drop `x` and rehome its
children onto `anc σ x`. There is no path argument and no tombstone.

## The obstruction

Physical splice destroys `x`'s parent pointer, so `Ins`-after-`x` and `Del`-`x`
do not commute: whether the insert was applied before the splice decides whether
it is rehomed onto `anc(x)` or left dangling. `rc` must therefore order that pair
`Fst_then_snd`, which makes `cond_comm_base` non-vacuous, and then false on the
trace `Ins-after-5 ; Del-5 ; Ins-after-5`. In `o1; o2` the inserted record is
rehomed onto `anc(5) = 0` and survives; in `o2; o1` it dangles off the deleted
`5`. The two states differ at identity `10`. `cond_comm_base_violated` proves it.

`native_decide` evaluates the concrete finite trace, so the axiom trail includes
`Lean.ofReduceBool`; that is appropriate for a ground-data counterexample.

The definitions are namespaced because they intentionally mirror, and differ
from, the path-carrying ones in the sibling module.
-/

namespace SpliceCounterexample

/-- State: `id ↦ (element, anchor)`; `0` is the root. -/
abbrev concrete_st := map ℕ (ℕ × ℕ)

@[simp] def el (s : concrete_st) (t : ℕ) : ℕ := (sel s t).1
@[simp] def anc (s : concrete_st) (t : ℕ) : ℕ := (sel s t).2
@[simp] def init_st : concrete_st := const_on empty (0, 0)

/-- `splice σ x`: drop `x` and rehome every child of `x` onto `anc σ x`.
Tombstone-free deletion (no path argument). -/
@[simp] def splice (s : concrete_st) (x : ℕ) : concrete_st :=
  let ax := anc s x
  del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, ax) else ea) s) x

inductive app_op_t : Type where
| Ins : ℕ → ℕ → app_op_t      -- element, anchor
| Del : ℕ → app_op_t          -- target identity
deriving DecidableEq

abbrev op_t := ℕ × ℕ × app_op_t

@[simp] def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2
@[simp] def get_rid (o : op_t) := match o with | (_, (rid, _)) => rid

/-- Effect: `Ins e a` records `(t, (e, a))`; `Del x` splices `x`. -/
@[simp] def do_ (s : concrete_st) (o : op_t) : concrete_st :=
  match o with
  | (t, _, app_op_t.Ins e a) => upd s t (e, a)
  | (_, _, app_op_t.Del x)   => splice s x

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either
deriving DecidableEq

/-- `Ins e a` (id `t`) and `Del x` conflict iff `a = x` or `t = x`; the insert is
sequenced first. Everything else commutes (`Either`). This is the relation forced
by `rc_non_comm`, and it is exactly what makes `cond_comm_base` non-vacuous. -/
@[simp] def rc (o1 o2 : op_t) : rc_res :=
  match o1, o2 with
  | (t1, _, app_op_t.Ins _ a1), (_, _, app_op_t.Del x) =>
      if a1 = x ∨ t1 = x then rc_res.Fst_then_snd else rc_res.Either
  | (_, _, app_op_t.Del x), (t2, _, app_op_t.Ins _ a2) =>
      if a2 = x ∨ t2 = x then rc_res.Snd_then_fst else rc_res.Either
  | _, _ => rc_res.Either

/-- Domain-relative state equality. -/
@[simp] def eq (a b : concrete_st) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

def mk (recs : List (ℕ × ℕ × ℕ)) : concrete_st :=
  recs.foldl (fun s r => upd s r.1 (r.2.1, r.2.2)) init_st

def dump (s : concrete_st) (ids : List ℕ) : List (ℕ × ℕ × ℕ) :=
  ids.filterMap (fun t => if contains s t then some (t, el s t, anc s t) else none)

/-- `o1 = Ins after 5`, `o2 = Del 5`, `o3 = Ins after 5`, on a state with `5`. -/
def s0 : concrete_st := mk [(5,83,0)]
def o1 : op_t := (10, 1, app_op_t.Ins 65 5)
def o2 : op_t := (11, 2, app_op_t.Del 5)
def o3 : op_t := (12, 3, app_op_t.Ins 90 5)

-- The two orders diverge at id 10 (anchor 0 rehomed vs 5 dangling):
#eval dump (do_ (do_ (do_ s0 o1) o2) o3) [5,10,12]   -- Ins;Del;Ins → [(10,65,0),(12,90,5)]
#eval dump (do_ (do_ (do_ s0 o2) o1) o3) [5,10,12]   -- Del;Ins;Ins → [(10,65,5),(12,90,5)]

set_option maxHeartbeats 1000000

/-- **`cond_comm_base` is violated.** The hypothesis holds (`rc o1 o2 =
Fst_then_snd`, `rc o2 o3 ≠ Either`, ops pairwise distinct) but the two do_-orders
are not `eq`: they differ at identity `10` (anchor `0`, rehomed, versus `5`,
dangling). So the plain tombstone-free splice does not satisfy RA-linearizability;
the path-carrying `RGA_Tombstone_Free_MRDT` is what repairs it. -/
theorem cond_comm_base_violated :
    (distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
      ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
    ∧ ¬ eq (do_ (do_ (do_ s0 o1) o2) o3) (do_ (do_ (do_ s0 o2) o1) o3) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  intro h
  have h10 := (h 10).2
  revert h10
  native_decide

end SpliceCounterexample
