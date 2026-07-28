import Std.Tactic.BVDecide
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Sal.CRDTs.LWW_Element_Set.LWW_Element_Set_CRDT
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

/-! # LWW-Element-Set (CRDT): read-side projection

The 24 RA-linearizability VCs in `LWW_Element_Set_CRDT.lean` prove
that the per-element `(addTs, remTs)` map pair converges under
per-key max merge, both maps are grow-only ℕ-valued lattices. They
say nothing about the headline LWW-Element-Set claim: that an
element is live iff its latest `Add` strictly post-dates its latest
`Remove` (with ties favouring `Remove`, the conservative
"remove-wins-on-tie" convention encoded in `LWW_Element_Set_CRDT`'s
docstring).

This file lifts the headline:

1. `lookup s id`: element `id` is live iff its add-ts strictly
   exceeds its remove-ts.
2. **Convergence at the read.**
3. **Two intent theorems** (independent, they constrain `do_`'s effect on
   liveness, so they would catch a wrong update):
   - `lookup_after_add_with_fresh_ts`: `Add` at a ts strictly larger
     than the current rem-ts makes `id` live.
   - `remove_at_higher_ts_extinguishes`: a `Remove` at ts > current
     add-ts strips the element from the live set.
4. `lookup_def`: the definitional unfolding of `lookup` (liveness is the
   add-ts/rem-ts comparison). This is NOT an independent guarantee: it
   restates how `lookup` is defined and holds for whatever that definition
   is, so it catches no bug. The genuine "latest write wins" behavioural
   content is convergence together with the two intent theorems above; a
   `rfl` unfolding is not it. (Renamed from `latest_write_wins`, which
   overstated a definitional restatement as the headline guarantee.) -/

/-! ## Read-side primitives -/

/-- Element `id` is live iff its latest add-ts strictly exceeds its
latest remove-ts. Ties favour the remove (conservative LWW-Set
convention). -/
def lookup (s : concrete_st) (id : ℕ) : Prop :=
  mysel (Prod.fst s) id > mysel (Prod.snd s) id

/-! ## Convergence at the read -/

theorem lookup_convergent (s₁ s₂ : concrete_st) (id : ℕ) :
    eq s₁ s₂ → (lookup s₁ id ↔ lookup s₂ id) := by
  rintro ⟨h_a, h_r⟩
  unfold lookup
  rw [(h_a id).2, (h_r id).2]

/-! ## Intent-preservation theorems -/

/-- **Lookup after Add with a fresh, larger ts.** Applying `Add id`
at ts strictly greater than the element's current latest remove-ts
makes the element live, the new add-ts becomes the per-element
maximum, and it strictly exceeds the unchanged remove-ts. -/
theorem lookup_after_add_with_fresh_ts
    (s : concrete_st) (id ts rid : ℕ)
    (h_ts_gt_rem : ts > mysel (Prod.snd s) id) :
    lookup (do_ s (ts, rid, app_op_t.Add id)) id := by
  simp only [mysel] at h_ts_gt_rem
  unfold lookup
  simp [do_, mysel]
  exact Or.inr h_ts_gt_rem

/-- **Remove at higher ts extinguishes.** Applying `Remove id` at ts
strictly greater than the element's current latest add-ts pushes the
remove-ts above the add-ts, making the element no longer live. -/
theorem remove_at_higher_ts_extinguishes
    (s : concrete_st) (id ts rid : ℕ)
    (h_ts_ge_add : ts ≥ mysel (Prod.fst s) id) :
    ¬ lookup (do_ s (ts, rid, app_op_t.Remove id)) id := by
  simp only [mysel] at h_ts_ge_add
  unfold lookup
  simp [do_, mysel]
  intro _
  exact h_ts_ge_add

/-- **`lookup` unfolded (definitional).** Liveness is the add-ts/rem-ts
comparison, because that is how `lookup` is *defined* (`by rfl`). Useful as
a rewrite lemma; it is NOT an independent intent theorem and does not certify
any behaviour: it would hold for any definition of `lookup`. The behavioural
"latest write wins" property is carried by convergence and the two
ts-conditioned theorems (`lookup_after_add_with_fresh_ts`,
`remove_at_higher_ts_extinguishes`). -/
theorem lookup_def
    (s : concrete_st) (id : ℕ) :
    lookup s id ↔ mysel (Prod.fst s) id > mysel (Prod.snd s) id := by
  rfl

/-- **Add wins on equal-ts tiebreak (sanity).** Under the
conservative tie-favours-remove convention, equal add-ts and rem-ts
means the element is **not** live (lookup uses strict `>`). -/
theorem equal_ts_remove_wins
    (s : concrete_st) (id : ℕ)
    (h_eq : mysel (Prod.fst s) id = mysel (Prod.snd s) id) :
    ¬ lookup s id := by
  unfold lookup
  rw [h_eq]
  exact lt_irrefl _
