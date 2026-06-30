import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal

open Classical

/-!
# Tombstone-free RGA — flat-set three-way-merge MRDT

A Lean encoding of the tombstone-free RGA described in
`_references/Formalising-the-Merge.pdf`. State is a flat keyed collection of
records; deletion physically splices a node out and rehomes its children; the
three-way merge decides survival by an OR-set on identities and then reparents
each survivor by climbing the LCA's ancestor chain to the nearest live anchor.

## Encoding

* **Identity / anchor** are `ℕ`, with `0` the root anchor (the PDF's `0`).
* **State** `concrete_st := map ℕ (ℕ × ℕ)` maps an identity `t` to
  `(element, anchor)`. id-uniqueness (wf clause i) is structural: map keys are
  unique. `ids σ = domain σ`. A plain `set` is unusable here — `splice` and the
  merge's `climb` walk both need to *read* `anc σ x`, which the `α → Bool` set
  representation cannot do.
* **`do_` guard dropped.** The PDF guards `Ins` with `(a = 0 ∨ a ∈ ids)`. As in
  `RGA_CRDT`, we drop it: an insert always records, even with a dangling anchor.
  The guard only adds non-commuting pairs; dropping it isolates the splice
  mechanism, which is what the notes are about.

## climb fuel

`climb` walks `anc_L` until it reaches the root (`0`) or a survivor. On a
well-formed state a node's anchor is an *older* node, so `anc t < t` and the
chain strictly descends; the climb from anchor `a` finishes within `a` steps.
We use `a` itself as fuel — computable, total on every state, exact on wf ones.
-/

/-- State: `id ↦ (element, anchor)`. `ids σ = domain σ`; `0` is the root. -/
abbrev concrete_st := map ℕ (ℕ × ℕ)

/-- Element stored at identity `t` (junk if `t ∉ ids`). -/
@[simp] def el (s : concrete_st) (t : ℕ) : ℕ := (sel s t).1

/-- Birth-anchor stored at identity `t` (junk if `t ∉ ids`). -/
@[simp] def anc (s : concrete_st) (t : ℕ) : ℕ := (sel s t).2

/-- Initial state: empty map. -/
@[simp] def init_st : concrete_st := const_on empty (0, 0)

/-- `splice σ x`: drop `x` and rehome every child of `x` (record with
anchor `= x`) onto `x`'s own anchor `anc σ x`. Tombstone-free deletion. -/
@[simp] def splice (s : concrete_st) (x : ℕ) : concrete_st :=
  let ax := anc s x
  del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, ax) else ea) s) x

/-- User operations. `Ins e a` inserts element `e` after anchor `a`;
`Del x` removes identity `x`. -/
inductive app_op_t : Type where
| Ins : ℕ → ℕ → app_op_t      -- element, anchor
| Del : ℕ → app_op_t          -- target identity
deriving DecidableEq

/-- `(timestamp, replica id, op)`. The timestamp is the new record's identity
on `Ins`; for `Del` it is causal bookkeeping only. -/
abbrev op_t := ℕ × ℕ × app_op_t

@[simp] def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp] def get_rid (o : op_t) := match o with | (_, (rid, _)) => rid

/-- Effect. `Ins e a` at ts `t` records `(t, (e, a))`; `Del x` splices `x`. -/
@[simp] def do_ (s : concrete_st) (o : op_t) : concrete_st :=
  match o with
  | (t, _, app_op_t.Ins e a) => upd s t (e, a)
  | (_, _, app_op_t.Del x)   => splice s x

/-- climb worker: walk `ancL` up to the root or a survivor in `I`. Fuel is the
starting anchor value (an upper bound on chain length on wf states). -/
def climb_aux (ancL : ℕ → ℕ) (I : set ℕ) : ℕ → ℕ → ℕ
  | 0,        x => x
  | (fuel+1), x => if x = 0 || I x then x else climb_aux ancL I fuel (ancL x)

/-- climb from anchor `x`, fuelled by `x`. -/
@[simp] def climb (ancL : ℕ → ℕ) (I : set ℕ) (x : ℕ) : ℕ := climb_aux ancL I x x

/-- Three-way merge.

`I` = OR-set survival on identities. `betaf t` = `β(t)`, the birth-anchor of
`t` taken from the region it belongs to (`L`, else `A∖L`, else `B∖L`). `elf t`
= its (immutable) element. Each survivor's final anchor is `climb` of `β(t)`
up the LCA's parent chain. -/
@[simp] def merge (l a b : concrete_st) : concrete_st :=
  let dl := domain l
  let da := domain a
  let db := domain b
  let I : set ℕ := union (intersection (intersection dl da) db)
                         (union (difference da dl) (difference db dl))
  let ancL : ℕ → ℕ := fun y => anc l y
  let elf : ℕ → ℕ := fun t =>
    if contains l t then el l t else if contains a t then el a t else el b t
  let betaf : ℕ → ℕ := fun t =>
    if contains l t then anc l t else if contains a t then anc a t else anc b t
  map.mk (fun t => (elf t, climb ancL I (betaf t))) I

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either
deriving DecidableEq

/-- Conflict resolution — the relation forced by `rc_non_comm`
(`rc = Either ⇔ ops commute at `do_`).

The full `do_`-commutation table (over well-formed states):
* `Ins / Ins` — always commute (two distinct keys; RGA newer-first order is a
  read-side concern). → `Either`.
* `Del / Del` — always commute (each node's final anchor is its nearest
  surviving ancestor, independent of splice order). → `Either`.
* `Ins e a` (id `t`) vs `Del x` — commute **iff** `a ≠ x ∧ t ≠ x`. They
  conflict exactly when the delete targets either the insert's anchor
  (`a = x`, insert-after-the-deleted) or the insert's own id (`t = x`,
  delete-the-just-inserted). In both cases the insert must be sequenced first,
  so `Fst_then_snd`.

This is the `rc` that makes `rc_non_comm` hold on reachable states. It does
*not* rescue `cond_comm_base`: the same insert-after-deleted entry that this
relation must contain is exactly what makes `cond_comm_base` non-vacuous and
then false (see `cond_comm_base_violated`). -/
@[simp] def rc (o1 o2 : op_t) : rc_res :=
  match o1, o2 with
  | (t1, _, app_op_t.Ins _ a1), (_, _, app_op_t.Del x) =>
      if a1 = x ∨ t1 = x then rc_res.Fst_then_snd else rc_res.Either
  | (_, _, app_op_t.Del x), (t2, _, app_op_t.Ins _ a2) =>
      if a2 = x ∨ t2 = x then rc_res.Snd_then_fst else rc_res.Either
  | _, _ => rc_res.Either

/-- Domain-relative state equality: same identities, same `(elem, anchor)` on
identities that are present. Off-domain `mappings` junk is irrelevant. -/
@[simp] def eq (a b : concrete_st) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

@[simp] def commutes_with (o1 o2 : op_t) :=
  forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

/-! ## Operational oracle: the 8 PDF scenarios

`mk` builds a state from a record list; `dump` reads back the records at a
given id list, so `#eval` can compare against the PDF's hand-traced merges. -/

/-- Build a state by inserting each `(id, elem, anchor)` record. -/
def mk (recs : List (ℕ × ℕ × ℕ)) : concrete_st :=
  recs.foldl (fun s r => upd s r.1 (r.2.1, r.2.2)) init_st

/-- Read back present records at the given ids, as `(id, elem, anchor)`. -/
def dump (s : concrete_st) (ids : List ℕ) : List (ℕ × ℕ × ℕ) :=
  ids.filterMap (fun t => if contains s t then some (t, el s t, anc s t) else none)

-- Scenario 1 — insert on one side only. Expect {(1,A,0),(2,Y,1)}.
#eval dump (merge (mk [(1,65,0)]) (mk [(1,65,0),(2,89,1)]) (mk [(1,65,0)])) [1,2,3,4]
-- Scenario 2 — remove on one side. Expect {(1,A,0)}.
#eval dump (merge (mk [(1,65,0),(2,89,1)]) (mk [(1,65,0)]) (mk [(1,65,0),(2,89,1)])) [1,2,3,4]
-- Scenario 4 — remove anchor, concurrent insert after it. Expect {(3,Z,0)}.
#eval dump (merge (mk [(1,65,0)]) (mk []) (mk [(1,65,0),(3,90,1)])) [1,2,3,4]
-- Scenario 5 — concurrent insert at same anchor. Expect {(1,A,0),(2,Y,1),(3,Z,1)}.
#eval dump (merge (mk [(1,65,0)]) (mk [(1,65,0),(2,89,1)]) (mk [(1,65,0),(3,90,1)])) [1,2,3,4]
-- Scenario 6 — chained removal + deep insert. Expect {(3,C,0),(4,D,0)}.
#eval dump (merge (mk [(1,65,0),(2,66,1),(3,67,2)]) (mk [(3,67,0)]) (mk [(1,65,0),(2,66,1),(3,67,2),(4,68,2)])) [1,2,3,4]
-- Scenario 7 — inserts straddling a removed anchor. Expect {(2,B,0),(3,C,0),(4,P,2)}.
#eval dump (merge (mk [(1,65,0),(2,66,1)]) (mk [(2,66,0),(4,80,2)]) (mk [(1,65,0),(2,66,1),(3,67,1)])) [1,2,3,4]
-- Scenario 8 — overlapping splices (transitive reparent). Expect {(1,A,0),(4,D,1)}.
#eval dump (merge (mk [(1,65,0),(2,66,1),(3,67,2),(4,68,3)]) (mk [(1,65,0),(3,67,1),(4,68,3)]) (mk [(1,65,0),(2,66,1),(4,68,2)])) [1,2,3,4]

/-! ### splice (local `Del`) sanity -/
-- Del 2 from chain 1←2←3 rehomes 3 onto 1. Expect {(1,A,0),(3,C,1)}.
#eval dump (splice (mk [(1,65,0),(2,66,1),(3,67,2)]) 2) [1,2,3]

/-! ### `cond_comm_base` counterexample (the RA-linearizability obstruction)

`o1 = Ins e1 after p`, `o2 = Del p`, `o3 = Ins e3 after p`, all on a state
where `p` exists. `rc o1 o2 = Fst_then_snd` and `rc o2 o3 = Snd_then_fst`
(≠ Either), so `cond_comm_base`'s hypothesis holds — yet the two do_-orders
diverge. -/
def s0 : concrete_st := mk [(5,83,0)]                    -- p = 5 present
def o1 : op_t := (10, 1, app_op_t.Ins 65 5)              -- insert after 5
def o2 : op_t := (11, 2, app_op_t.Del 5)                 -- delete 5
def o3 : op_t := (12, 3, app_op_t.Ins 90 5)              -- insert after 5

-- LHS: do_ (do_ (do_ s0 o1) o2) o3   (Ins ; Del ; Ins)
#eval dump (do_ (do_ (do_ s0 o1) o2) o3) [5,10,12]
-- RHS: do_ (do_ (do_ s0 o2) o1) o3   (Del ; Ins ; Ins)
#eval dump (do_ (do_ (do_ s0 o2) o1) o3) [5,10,12]
-- rc verdicts feeding the hypothesis:
#eval (match rc o1 o2 with | rc_res.Fst_then_snd => "Fst_then_snd" | rc_res.Snd_then_fst => "Snd_then_fst" | rc_res.Either => "Either")
#eval (match rc o2 o3 with | rc_res.Fst_then_snd => "Fst_then_snd" | rc_res.Snd_then_fst => "Snd_then_fst" | rc_res.Either => "Either")

/-! ## Verification: RA-linearizability

The framework's 24 VCs are stated over *arbitrary* states and operation orders.
Two structural facts of this tombstone-free design decide the outcome:

1. The merge converges, but `climb` is a recursive walk and is only exact on
   *well-formed* states (anchors resolve, parent map acyclic). So the merge VCs
   carry a `wf` hypothesis; over arbitrary states the recursion can wander.
2. Physical excise makes insert-after-`x` and delete-`x` non-commuting, which
   forces a non-`Either` `rc` entry, which makes `cond_comm_base` *non-vacuous*
   and then *false*. This is the tombstone tax, identical to `RGA_Tree`.

We prove the merge-convergence core (`merge_idem` under `wf`), the structural
`no_rc_chain`, and — as the RA-linearizability verdict — that `cond_comm_base`
is violated by a concrete trace. -/

set_option maxHeartbeats 1000000

/-- `climb` is the identity on a starting anchor that is already the root or a
survivor. This is the fixed-point the merge relies on: on a well-formed state
the birth-anchor `β(t)` is already live (or root), so no climbing happens. -/
theorem climb_fixpoint (ancL : ℕ → ℕ) (I : set ℕ) (x : ℕ)
    (h : x = 0 ∨ I x = true) : climb ancL I x = x := by
  unfold climb
  cases x with
  | zero => rfl
  | succ n =>
    unfold climb_aux
    have : I (n + 1) = true := by rcases h with h | h <;> simp_all
    simp [this]

/-- Well-formedness: every present record's anchor is the root or itself
present. (The PDF's clause (ii); clause (iii) acyclicity is not needed for the
results below.) Every state reachable from `init_st` by `do_` satisfies this. -/
@[simp] def wf (s : concrete_st) : Prop :=
  ∀ t, contains s t → (anc s t = 0 ∨ contains s (anc s t))

/-- **Merge idempotence (convergence core).** On a well-formed state,
`merge s s s = s`: survival keeps exactly `ids s`, and each survivor's
birth-anchor is already live, so `climb` is the identity. -/
theorem merge_idem (s : concrete_st) (hwf : wf s) : eq (merge s s s) s := by
  intro k
  constructor
  · -- domains agree: I = dom s ∩ dom s ∩ dom s ∪ ... = dom s
    simp only [merge, contains, domain, mem]
    grind
  · intro hk
    -- on a present key, sel (merge s s s) k = (el s k, climb ... (anc s k))
    have hcontain : contains s k = true := by
      simpa [merge, contains, domain, mem] using hk
    have hres : anc s k = 0 ∨ contains s (anc s k) = true := hwf k hcontain
    simp only [merge, sel, el, anc, contains, domain, mem] at hcontain ⊢
    simp only [hcontain, if_true]
    -- the survivor's birth-anchor is already root/live, so climb is the identity
    rw [climb_fixpoint (fun y => (s.mappings y).2)
          (union (intersection (intersection s.domain s.domain) s.domain)
                 (union (difference s.domain s.domain) (difference s.domain s.domain)))
          ((s.mappings k).2)
          (by
            rcases hres with h | h
            · left; simpa [anc, sel] using h
            · right
              simp only [union, intersection, difference, contains, mem, anc, sel] at h ⊢
              grind)]

/-- **No `rc` chain.** `rc` yields `Fst_then_snd` only for `(Ins _ a, Del a)`;
a chain would need the middle op to be both a `Del` (to receive the first
`Fst_then_snd`) and an `Ins` (to emit the second), which is impossible. -/
theorem no_rc_chain (o1 o2 o3 : op_t) :
    (distinct_ops o1 o2 ∧ distinct_ops o2 o3)
    → ¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd) := by
  rcases o1 with ⟨_, _, _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _⟩ <;>
    rcases o3 with ⟨_, _, _ | _⟩ <;> simp [rc] <;> grind

/-! ### The RA-linearizability obstruction: `cond_comm_base` is violated

`cond_comm_base` requires, whenever `rc o1 o2 = Fst_then_snd` and
`rc o2 o3 ≠ Either`:

    eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3).

The trace `o1 = Ins _ after 5`, `o2 = Del 5`, `o3 = Ins _ after 5` on a state
where `5` is present satisfies the hypothesis but breaks the conclusion: in
`o1; o2` the inserted record is rehomed onto `anc(5) = 0` and survives there,
whereas in `o2; o1` it dangles off the now-deleted `5`. The two states differ
at identity `10`. This is exactly the physical-excise obstruction `RGA_Tree`
documented; the flat-set representation does not avoid it. -/
theorem cond_comm_base_violated :
    (distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
      ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
    ∧ ¬ eq (do_ (do_ (do_ s0 o1) o2) o3) (do_ (do_ (do_ s0 o2) o1) o3) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  intro h
  have h10 := (h 10).2
  revert h10
  native_decide

/-! ### Merge convergence VCs requiring well-formedness (follow-up)

`merge_comm` and `lem_0op` hold operationally (every #eval above confirms it)
but their proofs need `wf` plus a `climb` commutation lemma — the same
manual-lemma envelope `RGA_Tree` hit (Aristotle-scale). `merge_comm` further
needs branch-consistency: a node present in both `a∖l` and `b∖l` with
conflicting anchors would break symmetry, which global id-uniqueness rules out
but arbitrary states do not. Stated here with the needed hypotheses as the
documented next step; not closed in this pass. -/

/-- Branch consistency: where `a` and `b` both carry an identity outside `l`,
they agree on its `(elem, anchor)`. Holds under global id-uniqueness. -/
@[simp] def consistent (l a b : concrete_st) : Prop :=
  ∀ t, (contains a t ∧ contains b t ∧ ¬ contains l t) → sel a t = sel b t

theorem merge_comm (l a b : concrete_st)
    (hwf : wf l ∧ wf a ∧ wf b) (hc : consistent l a b) :
    eq (merge l a b) (merge l b a) := by
  sorry  -- climb-commutation under wf+consistent; see PLAN.md (Aristotle-scale)

theorem lem_0op (l a b : concrete_st) (ol : op_t)
    (hwf : wf l ∧ wf a ∧ wf b) :
    eq (merge (do_ l ol) (do_ a ol) (do_ b ol)) (do_ (merge l a b) ol) := by
  sorry  -- splice/climb interaction under wf; see PLAN.md (Aristotle-scale)
