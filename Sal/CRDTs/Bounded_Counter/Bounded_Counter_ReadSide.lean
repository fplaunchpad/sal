import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.Bounded_Counter.Bounded_Counter_CRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped Classical
set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Classical

/-! # Bounded_Counter (CRDT): read-side projection

The 24 VCs prove the three components `(incs, decs, transfers)`
converge under per-key max. The headline reads are:

* `inc_count s rid`: Inc operations issued by replica `rid`.
* `dec_count s rid`: Dec operations issued by replica `rid`.
* `transfer_count s s r`: Transfer operations from `s` to `r`.

The full per-replica `quota(rid)` requires summing transfers in
and out across all replicas; we leave that as a derived
client-side computation and pin the per-slot reads here. -/

def inc_count (s : concrete_st) (rid : ℕ) : Int :=
  mysel (Prod.fst s) rid

def dec_count (s : concrete_st) (rid : ℕ) : Int :=
  mysel (Prod.fst (Prod.snd s)) rid

def transfer_count (s : concrete_st) (sender receiver : ℕ) : Int :=
  mysel_t (Prod.snd (Prod.snd s)) (sender, receiver)

theorem inc_count_convergent (s₁ s₂ : concrete_st) (rid : ℕ) :
    eq s₁ s₂ → inc_count s₁ rid = inc_count s₂ rid := by
  intro ⟨h_inc, _, _⟩
  unfold inc_count
  exact (h_inc rid).2

theorem dec_count_convergent (s₁ s₂ : concrete_st) (rid : ℕ) :
    eq s₁ s₂ → dec_count s₁ rid = dec_count s₂ rid := by
  intro ⟨_, h_dec, _⟩
  unfold dec_count
  exact (h_dec rid).2

theorem transfer_count_convergent
    (s₁ s₂ : concrete_st) (sender receiver : ℕ) :
    eq s₁ s₂ → transfer_count s₁ sender receiver =
               transfer_count s₂ sender receiver := by
  intro ⟨_, _, h_t⟩
  unfold transfer_count
  exact (h_t (sender, receiver)).2

/-- **Inc raises the inc count at the same replica by 1.** -/
theorem inc_count_after_inc (s : concrete_st) (ts rid : ℕ) :
    inc_count (do_ s (ts, rid, app_op_t.Inc)) rid = inc_count s rid + 1 := by
  simp [inc_count, do_, mysel]

/-- **Dec raises the dec count at the same replica by 1.** -/
theorem dec_count_after_dec (s : concrete_st) (ts rid : ℕ) :
    dec_count (do_ s (ts, rid, app_op_t.Dec)) rid = dec_count s rid + 1 := by
  simp [dec_count, do_, mysel]

/-- **Transfer raises the per-pair transfer count by 1.** -/
theorem transfer_count_after_transfer
    (s : concrete_st) (ts rid recv : ℕ) :
    transfer_count (do_ s (ts, rid, app_op_t.Transfer recv)) rid recv =
      transfer_count s rid recv + 1 := by
  simp [transfer_count, do_, mysel_t]
