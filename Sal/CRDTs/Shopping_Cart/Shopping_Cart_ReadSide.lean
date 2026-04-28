import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Shopping_Cart.Shopping_Cart_CRDT
import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # Shopping_Cart (CRDT) — read-side projection

The 24 VCs prove the `(adds, removes)` map pair converges under
per-key max. The headline reads are **per-replica per-product
adds and removes**:

* `add_count s rid pid`    — times replica `rid` has added `pid`.
* `remove_count s rid pid` — times replica `rid` has removed `pid`.

The total quantity for a product (sum across replicas) is the
client-side projection
`Σ_rid (add_count s rid pid − remove_count s rid pid)`. -/

def add_count (s : concrete_st) (rid pid : ℕ) : Int :=
  mysel (Prod.fst s) (rid, pid)

def remove_count (s : concrete_st) (rid pid : ℕ) : Int :=
  mysel (Prod.snd s) (rid, pid)

/-- Per-replica per-product net contribution: `adds − removes`. -/
def per_replica_qty (s : concrete_st) (rid pid : ℕ) : Int :=
  add_count s rid pid - remove_count s rid pid

theorem add_count_convergent (s₁ s₂ : concrete_st) (rid pid : ℕ) :
    eq s₁ s₂ → add_count s₁ rid pid = add_count s₂ rid pid := by
  intro ⟨h_a, _⟩
  unfold add_count
  exact (h_a (rid, pid)).2

theorem remove_count_convergent (s₁ s₂ : concrete_st) (rid pid : ℕ) :
    eq s₁ s₂ → remove_count s₁ rid pid = remove_count s₂ rid pid := by
  intro ⟨_, h_r⟩
  unfold remove_count
  exact (h_r (rid, pid)).2

theorem per_replica_qty_convergent (s₁ s₂ : concrete_st) (rid pid : ℕ) :
    eq s₁ s₂ → per_replica_qty s₁ rid pid = per_replica_qty s₂ rid pid := by
  intro h_eq
  unfold per_replica_qty
  rw [add_count_convergent _ _ _ _ h_eq, remove_count_convergent _ _ _ _ h_eq]

/-- **Add raises the per-replica add count by 1.** -/
theorem add_count_after_add (s : concrete_st) (ts rid pid : ℕ) :
    add_count (do_ s (ts, rid, app_op_t.Add pid)) rid pid =
      add_count s rid pid + 1 := by
  simp [add_count, do_, mysel]

/-- **Remove raises the per-replica remove count by 1.** -/
theorem remove_count_after_remove (s : concrete_st) (ts rid pid : ℕ) :
    remove_count (do_ s (ts, rid, app_op_t.Remove pid)) rid pid =
      remove_count s rid pid + 1 := by
  simp [remove_count, do_, mysel]
