import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# The efficient OR-set: its implementation tuple

The Efficient OR-set row of Table 1. The state holds at most one record per
replica per element, `(r, t, x)`, instead of one record per `add`. A second
`add x` at replica `r` replaces the first, so the state stays bounded by the
number of replicas, and a `remove x` drops every record for `x` with no
tombstone left behind.

`rc` is the OR-set's: `remove x` is ordered before `add x`.

The replacement is what sets this row apart. Two `add x` events issued by
one replica do **not** commute, and they carry the **same operation**, so no
`rc` can relate them: an edge `add x --rc--> add x` is a chain of two `rc`
edges, which NO-RC-CHAIN forbids. The paper's RC-NON-COMM exempts exactly
this pair, because one replica's events are always causally ordered and
`lo^C_E` never consults `rc` about them. The SPOT block below pins that the
unguarded reading is false here, which is why the row takes the route of
`Interface/PaperRoute.lean`.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`: add and remove an element. -/
inductive AppOp (α : Type) where
  | add (element : α)
  | remove (element : α)
  deriving DecidableEq

/-- A stored record: the replica that added the element, the timestamp of
the `add`, and the element. -/
abbrev Record (α : Type) := Replica × Timestamp × α

/-- `Sigma`: a finite set of records, at most one per replica per element. -/
abbrev State (α : Type) := Finset (Record α)

/-- An event: an operation with its timestamp and replica. -/
abbrev Event (α : Type) := Op (AppOp α)

variable {α : Type} [DecidableEq α]

/-- `do(sigma, t, r, o)`. An `add` replaces its own replica's record for the
element; a `remove` drops every record for the element. -/
def update (s : State α) (e : Event α) : State α :=
  match e.2.2 with
  | .add x => insert (e.2.1, e.1, x)
      (s.filter fun p => ¬ (p.1 = e.2.1 ∧ p.2.2 = x))
  | .remove x => s.filter fun p => p.2.2 ≠ x

/-- `merge(l,a,b)`, the usual three-way shape. -/
def merge (l a b : State α) : State α :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The elements the client sees: every record's element. -/
def elements (s : State α) : Finset α := s.image fun p => p.2.2

/-- `rc`: `remove x` is ordered before `add x`, and nothing else. -/
def rcOps : AppOp α → AppOp α → OrderResult
  | .remove x, .add y => if x = y then OrderResult.Fst_then_snd else OrderResult.Either
  | .add x, .remove y => if x = y then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (α)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def itype : MRDTType where
  OType := AppOp α
  decOType := inferInstance
  QType := α
  ValType := Bool


/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
@[reducible] def D : Impl (itype α) where
  Sigma := State α
  decSigma := inferInstance
  sigma0 := ∅
  do_ := update
  merge := merge
  query s x := decide (x ∈ elements s)
  rc := rcOps

variable {α}

/-! ## Membership in a single step

Every proof about this row is a membership computation, and these two
definitions are what it runs on. `kills r x e` says the effect of `e`
removes the record `(r, t, x)` whatever `t` is: a `remove x`, or an `add x`
issued by `r` itself. -/

/-- The effects that drop a record for the pair `(r, x)`. -/
def kills (r : Replica) (x : α) (e : Event α) : Prop :=
  match e.2.2 with
  | .add y => e.2.1 = r ∧ y = x
  | .remove y => y = x

/-- The event that contributes `p`, which exists whether or not it occurred. -/
def birth (p : Record α) : Event α := (p.2.1, p.1, AppOp.add p.2.2)

omit [DecidableEq α] in
@[simp] theorem birth_time (p : Record α) : (birth p).1 = p.2.1 := rfl

omit [DecidableEq α] in
@[simp] theorem birth_rep (p : Record α) : (birth p).2.1 = p.1 := rfl

omit [DecidableEq α] in
@[simp] theorem birth_op (p : Record α) : (birth p).2.2 = AppOp.add p.2.2 := rfl

/-- `p` survives `e` unless `e` kills its pair, and `e` itself contributes
the record whose birth it is. -/
theorem mem_update_iff (p : Record α) (s : State α) (e : Event α) :
    p ∈ update s e ↔ e = birth p ∨ (p ∈ s ∧ ¬ kills p.1 p.2.2 e) := by
  rcases p with ⟨r, t, x⟩
  rcases e with ⟨et, er, op⟩
  cases op <;>
    simp [update, kills, birth, Prod.mk.injEq, eq_comm, and_comm, and_left_comm,
      and_assoc]

@[simp] theorem merge_comm (l a b : State α) : merge l a b = merge l b a := by
  ext p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem merge_init (s : State α) : merge ∅ ∅ s = s := by simp [merge]

/-! ## At most one timestamp per replica per element

The invariant the replacement buys. It is not needed by any obligation
below, and is kept because the SPOT block uses it to show that merging
unrelated replays is not a fold of anything. -/

/-- At most one timestamp is stored for each replica/element pair. -/
def KeyUnique (s : State α) : Prop :=
  ∀ r t u x, (r,t,x) ∈ s → (r,u,x) ∈ s → t = u

omit [DecidableEq α] in
theorem keyUnique_empty : KeyUnique (∅ : State α) := by simp [KeyUnique]

theorem keyUnique_update {s : State α} (h : KeyUnique s) (e : Event α) :
    KeyUnique (update s e) := by
  rcases e with ⟨et, er, op⟩
  intro r t u x ht hu
  cases op with
  | add y =>
    simp only [update, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq] at ht hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact ht.2.1.trans hu.2.1.symm
    · exact False.elim (hu.2 ⟨ht.1, ht.2.2⟩)
    · exact False.elim (ht.2 ⟨hu.1, hu.2.2⟩)
    · exact h r t u x ht.1 hu.1
  | remove y =>
    simp only [update, Finset.mem_filter] at ht hu
    exact h r t u x ht.1 hu.1

theorem keyUnique_fold (ops : List (Event α)) {s : State α}
    (h : KeyUnique s) : KeyUnique (ops.foldl update s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons e ops ih => exact ih (keyUnique_update h e)

/-! ## SPOT -/

namespace SPOT

def a : Event Nat := (1, 0, .add 7)
def a' : Event Nat := (2, 0, .add 7)
def b : Event Nat := (3, 1, .add 7)
def rem : Event Nat := (4, 2, .remove 7)

theorem local_add_replaces : update (update ∅ a) a' = {(0,2,7)} := by decide
theorem replicas_keep_distinct_records :
    update (update ∅ a') b = {(0,2,7), (1,3,7)} := by decide
theorem remove_keeps_no_tombstones : update (update ∅ a) rem = ∅ := by decide
theorem observed_remove_not_union :
    merge (update ∅ a) (update (update ∅ a) rem) (update ∅ a) = ∅ := by decide
theorem concurrent_add_wins :
    merge (update ∅ a) (update (update ∅ a) rem) (update (update ∅ a) b)
      = {(1,3,7)} := by decide
theorem union_would_resurrect :
    (update (update ∅ a) rem ∪ update ∅ a) ≠
      merge (update ∅ a) (update (update ∅ a) rem) (update ∅ a) := by decide

/-- Two `add 7` events from replica `0` do not commute. -/
theorem same_replica_adds_not_commuting : ¬ (D Nat).Commutes a a' := by
  intro h
  have bad := h (∅ : State Nat)
  change update (update ∅ a) a' = update (update ∅ a') a at bad
  have ne : update (update ∅ a) a' ≠ update (update ∅ a') a := by decide
  exact ne bad

/-- **No `rc` edge covers that pair.** With the theorem above this refutes
the unguarded reading of RC-NON-COMM: the pair does not commute, carries one
operation, and no edge relates it. The guarded reading exempts it, and that
is the whole reason the row states its conditions at `lo^C_E` rather than at
`rc`. -/
theorem no_rc_edge_for_same_replica_adds :
    ¬ ((D Nat).EventRcBefore a a' ∨ (D Nat).EventRcBefore a' a) := by
  rintro (hr | hr) <;>
    simp [Impl.EventRcBefore, Impl.RcBefore, rcOps, Op.op, a, a'] at hr

/-- Arbitrary independent replay choices cannot be used as merge premises.
All three singleton states are folds of permutations of the same three adds,
but their merge is not the fold of any sequential execution. -/
def a'' : Event Nat := (3, 0, .add 7)

theorem three_replay_choices :
    [a', a'', a].foldl update ∅ = {(0,1,7)} ∧
    [a, a'', a'].foldl update ∅ = {(0,2,7)} ∧
    [a, a', a''].foldl update ∅ = {(0,3,7)} := by decide

theorem incompatible_replays_merge_not_a_fold :
    ∀ ops : List (Event Nat),
      ops.foldl update ∅ ≠ merge {(0,1,7)} {(0,2,7)} {(0,3,7)} := by
  intro ops heq
  have h := keyUnique_fold ops keyUnique_empty
  rw [heq] at h
  have bad := h 0 2 3 7 (by decide) (by decide)
  exact (by decide : (2 : Nat) ≠ 3) bad

end SPOT

#print axioms keyUnique_fold
#print axioms SPOT.no_rc_edge_for_same_replica_adds
#print axioms SPOT.incompatible_replays_merge_not_a_fold

end LeanProofs.Implementations.EfficientORSet
