import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.Multi_Valued_Register.Multi_Valued_Register_MRDT
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! # Multi-Valued Register (MRDT, classical): read-side projection

MRDT counterpart to `Sal/CRDTs/Multi_Valued_Register/Multi_Valued_Register_ReadSide.lean`.
Same two-component state `(writes, removed)` and same headline
classical-MVR claims. The MRDT's `eq` is plain `=` so convergence
proofs are trivial; the substantive theorems are unchanged.

Reference: Shapiro et al. INRIA RR-7506 §3.2.2 Spec 14. -/

/-- Value `v` is visible iff some `(ts, v)` write-record exists
that has not been superseded. -/
def is_visible_value (s : concrete_st) (v : ℕ) : Prop :=
  ∃ ts : ℕ,
    mem (ts, v) (Prod.fst s) = true ∧
    mem ts (Prod.snd s) = false

theorem is_visible_value_convergent (s₁ s₂ : concrete_st) (v : ℕ) :
    eq s₁ s₂ → (is_visible_value s₁ v ↔ is_visible_value s₂ v) := by
  intro h_eq; unfold eq at h_eq; subst h_eq; rfl

/-- **Lookup after Write.** Applying `Write v O` makes `v` visible
provided the new ts is fresh (not in `O`, not in pre-state's
removed). -/
theorem visible_after_write
    (s : concrete_st) (v ts rid : ℕ) (O : set ℕ)
    (h_fresh_O : mem ts O = false)
    (h_fresh_removed : mem ts (Prod.snd s) = false) :
    is_visible_value (do_ s (ts, rid, app_op_t.Write v O)) v := by
  refine ⟨ts, ?_, ?_⟩
  · simp [do_]
  · simp only [mem] at h_fresh_O h_fresh_removed
    simp [do_, h_fresh_O, h_fresh_removed]

/-- **Concurrent writes both survive (headline).** Two replicas
each apply a `Write` whose snapshot does not include the other's
fresh ts (true by `distinct_ops` for any well-formed execution).
After standard three-way merge, both values are visible. -/
theorem concurrent_writes_both_visible
    (l : concrete_st) (v₁ v₂ ts₁ ts₂ rid₁ rid₂ : ℕ) (O₁ O₂ : set ℕ)
    (h_fresh_t1_O1 : mem ts₁ O₁ = false)
    (h_fresh_t2_O1 : mem ts₂ O₁ = false)
    (h_fresh_t1_O2 : mem ts₁ O₂ = false)
    (h_fresh_t2_O2 : mem ts₂ O₂ = false)
    (h_fresh_t1_R  : mem ts₁ (Prod.snd l) = false)
    (h_fresh_t2_R  : mem ts₂ (Prod.snd l) = false)
    (h_fresh_t1_W  : mem (ts₁, v₁) (Prod.fst l) = false)
    (h_fresh_t2_W  : mem (ts₂, v₂) (Prod.fst l) = false) :
    is_visible_value
      (merge l
        (do_ l (ts₁, rid₁, app_op_t.Write v₁ O₁))
        (do_ l (ts₂, rid₂, app_op_t.Write v₂ O₂))) v₁ ∧
    is_visible_value
      (merge l
        (do_ l (ts₁, rid₁, app_op_t.Write v₁ O₁))
        (do_ l (ts₂, rid₂, app_op_t.Write v₂ O₂))) v₂ := by
  simp only [mem] at *
  refine ⟨⟨ts₁, ?_, ?_⟩, ⟨ts₂, ?_, ?_⟩⟩
  · simp [merge, do_, h_fresh_t1_W]
  · simp [merge, do_, h_fresh_t1_O1, h_fresh_t1_O2, h_fresh_t1_R]
  · simp [merge, do_, h_fresh_t2_W]
  · simp [merge, do_, h_fresh_t2_O1, h_fresh_t2_O2, h_fresh_t2_R]

/-- **Sequential write supersedes prior (witness level).** Building-
block fact: if `O₂` includes `ts₁`, then `ts₁` is in the post-state's
`removed`, so the specific `(ts₁, v₁)` witness is no longer visible. -/
theorem sequential_write_supersedes_witness
    (s : concrete_st) (v₂ ts₁ ts₂ rid : ℕ) (O₂ : set ℕ)
    (h_t1_in_O2 : mem ts₁ O₂ = true) :
    mem ts₁ (Prod.snd (do_ s (ts₂, rid, app_op_t.Write v₂ O₂))) = true := by
  simp only [mem] at h_t1_in_O2
  simp [do_, h_t1_in_O2]

/-- **Sequential write supersedes prior (value level).** Headline
classical-MVR claim, stated plainly via `is_visible_value`: after a
new `Write v₂` whose snapshot `O₂` covers every prior visible
witness for `v₁`, `v₁` is no longer visible.

Premises:
* `h_v2_ne_v1`: the new write does not coincidentally rewrite `v₁`.
* `h_covered`: every currently-visible witness `(ts, v₁)` in `s`
  has `ts ∈ O₂`. In a well-formed sequential execution the
  prepare-time snapshot includes every visible record. -/
theorem sequential_write_supersedes_value
    (s : concrete_st) (v₁ v₂ ts₂ rid : ℕ) (O₂ : set ℕ)
    (h_v2_ne_v1 : v₂ ≠ v₁)
    (h_covered : ∀ ts,
        mem (ts, v₁) (Prod.fst s) = true →
        mem ts (Prod.snd s) = false →
        mem ts O₂ = true) :
    ¬ is_visible_value (do_ s (ts₂, rid, app_op_t.Write v₂ O₂)) v₁ := by
  rintro ⟨ts, h_in_writes, h_not_removed⟩
  simp [do_, add, _root_.singleton, union] at h_in_writes h_not_removed
  obtain ⟨h_not_rem, h_not_O2⟩ := h_not_removed
  rcases h_in_writes with h_in_old | h_eq
  · have h_in_O2 : mem ts O₂ = true :=
      h_covered ts h_in_old (by simp [mem, h_not_rem])
    simp [mem, h_not_O2] at h_in_O2
  · exact h_v2_ne_v1 h_eq.2.symm
