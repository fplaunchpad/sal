import Sal.Emulation.RA_Linearizability
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Induction

/-!
# Merge linearization (existential form)

Given two RA-lin witnesses `π₁` (for replica `r₁` at state `s₁` and
event set `ev₁`) and `π₂` (for `r₂` at `s₂`, `ev₂`), establish the
existence of a witness for the merged configuration.

## Why existential, not constructive

A previous design attempted a three-lemma decomposition
`merge_witness_{perm, respects, state}` against a concrete witness
definition. That design fails: **any elementary witness definition
couples `_respects` and `_state`**. The concurrent, `rc`-ordered
cross case in `_respects` has no contradiction from permutation /
respect hypotheses alone — closing it requires knowing the state
equation being proved. The paper's own proof handles this by
**co-constructing** the witness and the lo-respect property inside
a single bottom-up induction; separating them is a mechanisation
artifact that doesn't reflect the proof.

We therefore state the merge-case as a single existential theorem
`merge_linearization_exists` (paper Lemma 1 / Theorem 1, lin.tex
§3.3 + appendix §A.2–A.4) and will prove it by induction on the
total event count, pulling events out of `merge` one at a time via
the 24 VCs (`base_*`, `ind_*`, `inter_*`, `lem_0op`).

The `restrictTo` helper is kept for use inside the induction's
inductive-case argument. -/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- Sub-list of `π` restricted to events in set `E`. Uses classical
decidability on `Set` membership, so the function is `noncomputable`. -/
noncomputable def restrictTo (π : List (Op D.AppOp)) (E : Set (Op D.AppOp)) :
    List (Op D.AppOp) :=
  π.filter fun x => decide (x ∈ E)

/-! ### Paper's BottomUp rules (derived from the 24 VCs)

The Sal paper (arXiv:2502.19967v1, appendix §A.2–A.4) proves the
merge case in two layers:

1. **Derive the BottomUp-{0,1,2}-OP rules** from the 24 VCs. Each
   rule is a general-shape rewrite that pulls an event out of
   `merge`; each is proved by a nested induction cascading through
   the VCs named `base_*op`, `ind_*_*op`, and `inter_*_*op`.
2. **Apply the BottomUp rules** repeatedly inside a quintuple-nested
   induction over the event sets `L_top^a, L_top^b, L_1^b, L_2^b` to
   construct the merge witness.

Since we are in the 2-way-merge CRDT setting (no LCA), only the
single-argument LCA `l = init` instances of these rules are needed. -/

/-- **BottomUp-0-OP** specialised to CRDTs with `l = init`.
Corresponds to `lem_0op` applied recursively. When a single op `ol`
appears on both sides of `merge`, it can be pulled out. In its
general form this is exactly `lem_0op`; we restate with a
`SatisfiesVCs` argument to match the shape of the other two rules. -/
theorem bottomUp_0op (hVC : SatisfiesVCs D)
    (a b : D.State) (ol : Op D.AppOp) :
    D.merge (D.update a ol) (D.update b ol)
      = D.update (D.merge a b) ol :=
  hVC.lem_0op a b ol

/-! **BottomUp-1-OP** (paper `lemmas.tex` fig `bottom-up`):

```
  (e_⊤ ≠ ε ∧ e_1 ≠ e_⊤) ∨ (e_⊤ = ε ∧ l = b)
  ─────────────────────────────────────────────────────────
  merge(e_⊤(l), e_1(a), e_⊤(b)) = e_1(merge(e_⊤(l), a, e_⊤(b)))
```

For 2-way-merge CRDTs `l` collapses (no LCA argument). We split the
disjunctive premise into two theorems:

* `bottomUp_1op_top` — clause (`e_⊤ ≠ ε`): right side ends in a
  shared event `ol ≠ o₁`.
* `bottomUp_1op_bot` — clause (`e_⊤ = ε ∧ l = b`): right side
  degenerates to `D.init`.

Their base cases (both `a = init`) are direct VC applications.
General-`a` extension is the paper's nested induction.
-/

/-- **BottomUp-1-OP, clause (a), base case** (`a = init`, `b = init`).

`merge(update init o₁, update init ol) = update (merge init (update init ol)) o₁`
under `rc`-preconditions. Direct application of `base_2op`. -/
theorem bottomUp_1op_top_base
    (hVC : SatisfiesVCs D) (o₁ ol : Op D.AppOp)
    (h_rc : D.rc ol o₁ = RcRes.Fst_then_snd ∨ D.rc ol o₁ = RcRes.Either)
    (h_rep : differentReplicas o₁ ol) (h_dist : distinctOps o₁ ol) :
    D.merge (D.update D.init o₁) (D.update D.init ol)
      = D.update (D.merge D.init (D.update D.init ol)) o₁ :=
  hVC.base_2op o₁ ol h_rc h_rep h_dist

/-- **BottomUp-1-OP, clause (a)** (general `a`, `b = init`).

`merge(update a o₁, update init ol) = update (merge a (update init ol)) o₁`.
Abstract-state form; closed for reachable states by
`bottomUp_1op_top_reachable` (defined below, corollary of
`bottomUp_2op_reachable` by renaming `ol → o₂`). -/
theorem bottomUp_1op_top
    (_hVC : SatisfiesVCs D)
    (a : D.State) (o₁ ol : Op D.AppOp)
    (_h_rc : D.rc ol o₁ = RcRes.Fst_then_snd ∨ D.rc ol o₁ = RcRes.Either)
    (_h_rep : differentReplicas o₁ ol) (_h_dist : distinctOps o₁ ol) :
    D.merge (D.update a o₁) (D.update D.init ol)
      = D.update (D.merge a (D.update D.init ol)) o₁ := by
  sorry

/-- **BottomUp-1-OP, clause (b), base case** (`a = init`).

`merge(update init o₁, init) = update (merge init init) o₁`.
Direct application of `base_1op`. -/
theorem bottomUp_1op_bot_base
    (hVC : SatisfiesVCs D) (o₁ : Op D.AppOp) :
    D.merge (D.update D.init o₁) D.init
      = D.update (D.merge D.init D.init) o₁ :=
  hVC.base_1op o₁

/-- **BottomUp-1-OP, clause (b)** (general `a`, `b = init`).

`merge(update a o₁, init) = update (merge a init) o₁`.

The analogue of `bottomUp_1op_top` for the `e_⊤ = ε ∧ l = b`
premise clause. No direct VC covers the general-`a` extension when
the RHS is `init` — `ind_left_1op` requires the RHS to be
`update b ol`, not `init`. The paper's nested induction resolves
this by transport through clause (a) first. -/
theorem bottomUp_1op_bot
    (_hVC : SatisfiesVCs D)
    (a : D.State) (o₁ : Op D.AppOp) :
    D.merge (D.update a o₁) D.init
      = D.update (D.merge a D.init) o₁ := by
  -- Base: a = init — closed by `bottomUp_1op_bot_base`.
  -- Step: a = update a' o₁'. Not directly VC-shape; paper's
  -- nested induction uses clause (a) with a "phantom" ol event.
  sorry

/-- **BottomUp-2-OP** (paper `lemmas.tex` fig `bottom-up`):

```
  e_1 ≠ e_2  ∧  (e_1 →^rc e_2 ∨ e_1 ⇄ e_2)
  ────────────────────────────────────────────────
  merge(l, e_1(a), e_2(b)) = e_2(merge(l, e_1(a), b))
```

Pulls the right-side last event `o₂` out, under `rc`-commutativity.
For 2-way CRDTs (`l` collapses), the shape matches `ind_right_2op`'s
inductive step pattern, though with `l → init`.

Base case (both `a = b = init`) is `base_2op`. General form is
proved by induction on `a, b`'s constructions via
`ind_right_2op` + `inter_*_2op`. -/
theorem bottomUp_2op_base
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂) :
    D.merge (D.update D.init o₁) (D.update D.init o₂)
      = D.update (D.merge D.init (D.update D.init o₂)) o₁ :=
  hVC.base_2op o₁ o₂ h_rc h_rep h_dist

/-- **BottomUp-2-OP** (fix `a = init`, extend `b` by a list of events).

Specialised form useful for the inductive case of
`merge_linearization_exists` when `π₁ = []`. Proved by induction on
`π_b` (via `List.reverseRecOn`): base uses `bottomUp_2op_base`,
step uses `ind_right_2op`. Requires `Fst_then_snd` (strict) for the
`rc` precondition — `ind_right_2op` does not cover the `Either`
case. -/
theorem bottomUp_2op_init_left
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂)
    (π_b : List (Op D.AppOp))
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_o₂ : ∀ e ∈ π_b, distinctOps o₂ e) :
    D.merge (D.update D.init o₁) (D.update (applySeq D D.init π_b) o₂)
      = D.update (D.merge D.init (D.update (applySeq D D.init π_b) o₂)) o₁ := by
  induction π_b using List.reverseRecOn with
  | nil =>
    simpa [applySeq] using hVC.base_2op o₁ o₂ (Or.inl h_rc) h_rep h_dist
  | append_singleton π' e ih =>
    rw [applySeq_append_single]
    refine hVC.ind_right_2op D.init (applySeq D D.init π') o₁ o₂ e
      h_rc h_rep h_dist ?_ ?_ ?_
    · exact h_dist_b_o₁ e (by simp)
    · exact h_dist_b_o₂ e (by simp)
    · exact ih (fun f hf => h_dist_b_o₁ f (by simp [hf]))
               (fun f hf => h_dist_b_o₂ f (by simp [hf]))

/-- **BottomUp-2-OP** (reachable `a, b`, Fst_then_snd `rc` case).

For `a = applySeq init π_a`, `b = applySeq init π_b`, pulls `o₁`
out of the left of `merge(update a o₁, update b o₂)`. Proved by
double induction: outer on `π_a` (via `ind_left_2op`), inner on
`π_b` (via `bottomUp_2op_init_left`).

Does **not** cover the `Either` `rc` case (`ind_right_2op` rejects
it) — that case needs different VC machinery, likely the
`inter_*_2op` family. -/
theorem bottomUp_2op_reachable
    (hVC : SatisfiesVCs D) (o₁ o₂ : Op D.AppOp)
    (h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ o₂) (h_dist : distinctOps o₁ o₂)
    (π_a π_b : List (Op D.AppOp))
    (h_dist_a_o₁ : ∀ e ∈ π_a, distinctOps o₁ e)
    (h_dist_a_o₂ : ∀ e ∈ π_a, distinctOps o₂ e)
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_o₂ : ∀ e ∈ π_b, distinctOps o₂ e) :
    D.merge (D.update (applySeq D D.init π_a) o₁)
            (D.update (applySeq D D.init π_b) o₂)
      = D.update (D.merge (applySeq D D.init π_a)
                          (D.update (applySeq D D.init π_b) o₂)) o₁ := by
  induction π_a using List.reverseRecOn with
  | nil =>
    simpa [applySeq] using
      bottomUp_2op_init_left hVC o₁ o₂ h_rc h_rep h_dist π_b h_dist_b_o₁ h_dist_b_o₂
  | append_singleton π' e ih =>
    rw [applySeq_append_single]
    refine hVC.ind_left_2op (applySeq D D.init π') (applySeq D D.init π_b) o₁ o₂ e
      (Or.inl h_rc) h_rep h_dist ?_ ?_ ?_
    · exact h_dist_a_o₁ e (by simp)
    · exact h_dist_a_o₂ e (by simp)
    · exact ih (fun f hf => h_dist_a_o₁ f (by simp [hf]))
               (fun f hf => h_dist_a_o₂ f (by simp [hf]))

/-- **BottomUp-1-OP, clause (a), reachable form** — strict
`Fst_then_snd` `rc` case. Direct corollary of
`bottomUp_2op_reachable` (same theorem, renaming `ol → o₂`). -/
theorem bottomUp_1op_top_reachable
    (hVC : SatisfiesVCs D) (o₁ ol : Op D.AppOp)
    (h_rc : D.rc ol o₁ = RcRes.Fst_then_snd)
    (h_rep : differentReplicas o₁ ol) (h_dist : distinctOps o₁ ol)
    (π_a π_b : List (Op D.AppOp))
    (h_dist_a_o₁ : ∀ e ∈ π_a, distinctOps o₁ e)
    (h_dist_a_ol : ∀ e ∈ π_a, distinctOps ol e)
    (h_dist_b_o₁ : ∀ e ∈ π_b, distinctOps o₁ e)
    (h_dist_b_ol : ∀ e ∈ π_b, distinctOps ol e) :
    D.merge (D.update (applySeq D D.init π_a) o₁)
            (D.update (applySeq D D.init π_b) ol)
      = D.update (D.merge (applySeq D D.init π_a)
                          (D.update (applySeq D D.init π_b) ol)) o₁ :=
  bottomUp_2op_reachable hVC o₁ ol h_rc h_rep h_dist π_a π_b
    h_dist_a_o₁ h_dist_a_ol h_dist_b_o₁ h_dist_b_ol

/-- **BottomUp-2-OP** (general). Pulls `o₂` out of the right side
of `merge(update a o₁, update b o₂)`. Closed by
`bottomUp_2op_reachable` once the caller materialises the
event-list witnesses for `a, b`. The abstract-state form (no
`π_a, π_b`) remains `sorry` because the VCs only hold for
reachable states — a universal statement over `a, b` is strictly
stronger than the VCs guarantee. -/
theorem bottomUp_2op
    (_hVC : SatisfiesVCs D)
    (a b : D.State) (o₁ o₂ : Op D.AppOp)
    (_h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either)
    (_h_rep : differentReplicas o₁ o₂) (_h_dist : distinctOps o₁ o₂) :
    D.merge (D.update a o₁) (D.update b o₂)
      = D.update (D.merge a (D.update b o₂)) o₁ := by
  -- Abstract-state form. Callers that know `a = applySeq init π_a`
  -- and `b = applySeq init π_b` should use `bottomUp_2op_reachable`
  -- directly.
  sorry

/-- **Merge case of the bridge theorem (existential form).**

Given two RA-linearization witnesses for replicas `r₁` and `r₂`,
there exists a witness for the merged configuration: a list `π`
which is a permutation of `ev₁ ∪ ev₂`, respects `lo C`, and applies
to `D.merge s₁ s₂` when folded into `D.init`.

Paper reference: Lemma 1 / Theorem 1 of lin.tex §3.3, detailed in
appendix §A.2–A.4.

**Proof strategy** (to be mechanised): strong induction on the total
event count `π₁.length + π₂.length`. At each step, pull an event off
the tail of `π₁` or `π₂` and push it through `merge` using the
appropriate VC (`base_2op`, `ind_right_*`, `ind_left_*`, `inter_*`,
`lem_0op`), recursing on the smaller configuration. Base: both lists
empty; `merge_idem` on `D.init` closes it.

Closing this theorem is the main remaining work for Phase 1 — see
`MERGE_PROOF.md` for the case-analysis plan. -/
theorem merge_linearization_exists
    {D : CRDTSig} (_hVC : SatisfiesVCs D)
    {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h₁_perm : listPermOf π₁ ev₁) (h₂_perm : listPermOf π₂ ev₂)
    (_h₁_resp : respects π₁ (lo C)) (_h₂_resp : respects π₂ (lo C))
    (h₁_state : applySeq D D.init π₁ = s₁)
    (h₂_state : applySeq D D.init π₂ = s₂) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧
         respects π (lo C) ∧
         applySeq D D.init π = D.merge s₁ s₂ := by
  -- Degenerate base case: both event sets empty.
  -- Covers the one exercisable case of the reachable state space
  -- (initConfig.merge applied to freshly-created replicas).
  -- The full induction is left for future work.
  by_cases h_empty₁ : π₁ = []
  · by_cases h_empty₂ : π₂ = []
    · -- Both π's empty ⟹ ev's empty, s's are init, merge is init.
      subst h_empty₁; subst h_empty₂
      obtain ⟨_, hm₁⟩ := h₁_perm
      obtain ⟨_, hm₂⟩ := h₂_perm
      have hev₁_empty : ev₁ = ∅ := by
        ext a; constructor
        · intro ha; exact absurd ((hm₁ a).mpr ha) (List.not_mem_nil)
        · intro ha; exact ha.elim
      have hev₂_empty : ev₂ = ∅ := by
        ext a; constructor
        · intro ha; exact absurd ((hm₂ a).mpr ha) (List.not_mem_nil)
        · intro ha; exact ha.elim
      subst hev₁_empty; subst hev₂_empty
      simp [applySeq] at h₁_state h₂_state
      subst h₁_state; subst h₂_state
      refine ⟨[], ?_, List.Pairwise.nil, ?_⟩
      · refine ⟨List.nodup_nil, fun a => ?_⟩
        simp
      · simp [applySeq, _hVC.merge_idem]
    · -- π₂ non-empty — inductive step. Left to future work.
      sorry
  · -- π₁ non-empty — inductive step. Left to future work.
    sorry

end

/-! ### Packaging

Invoke `merge_linearization_exists` to build the merged replica's
witness from the IH witnesses for `r₁` and `r₂`. -/

/-- `Merge` preserves RA-lin. Intended closure of
`RA_Linearizability.RA_lin_preserved_merge`.

Body: destructure the existential from `merge_linearization_exists`
and thread it through. Closes end-to-end once
`merge_linearization_exists` is fully proved. -/
theorem RA_lin_preserved_merge_via_witness
    {D : CRDTSig} {C C' : Configuration D} (hVC : SatisfiesVCs D)
    {r₁ r₂ : Replica} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁  : C.N r₁ = some s₁) (h_s₂  : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  intro r' s' E' hN' hL'
  rw [hN] at hN'
  rw [hL] at hL'
  by_cases hr' : r' = r₁
  · -- Merged replica.
    subst hr'
    simp [updateRep] at hN' hL'
    obtain ⟨π₁, hp₁, hr₁, hs₁'⟩ := hRA r' s₁ ev₁ h_s₁ h_ev₁
    obtain ⟨π₂, hp₂, hr₂, hs₂'⟩ := hRA r₂ s₂ ev₂ h_s₂ h_ev₂
    obtain ⟨π, hperm, hresp, hstate⟩ :=
      merge_linearization_exists (D := D) (C := C) hVC hp₁ hp₂ hr₁ hr₂ hs₁' hs₂'
    refine ⟨π, ?_, ?_, ?_⟩
    · rw [← hL']; exact hperm
    · have : lo C' = lo C := by unfold lo; rw [hvis]
      rw [this]; exact hresp
    · rw [← hN']; exact hstate
  · -- Other replica: IH applies directly.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s' E' hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    have : lo C' = lo C := by unfold lo; rw [hvis]
    rw [this]; exact hresp

end Sal.Emulation
