import Sal.Emulation.RA_Linearizability
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic

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

/-! ### Convergence

Two `lo`-respecting permutations of the same event set yield the
same state when folded into `D.init`.

This is the Sal paper's **convergence theorem** (lin.tex §3.2,
Lemma `convergence`). It underpins several sub-cases of
`merge_linearization_exists`:

* `π₁ = []`, `π₂ ≠ []`: we need `merge D.init s₂ = s₂` for
  reachable `s₂`. Convergence gives us that any `lo`-respecting
  permutation of `ev₂` yields `s₂`; combined with `base_1op` +
  induction, this collapses the `merge init` to the right-side
  state.
* The mirror `π₁ ≠ []`, `π₂ = []` symmetrically.

Convergence is provable from the 24 VCs via a bubble-sort argument:
any two `lo`-respecting permutations differ by adjacent
transpositions of lo-unordered pairs; each transposition preserves
state via `rc_non_comm` (unordered ⟹ commuting) or `cond_comm` +
the presence of an overwriter. -/

/-- **Convergence.** Two `lo`-respecting permutations of the same
event set yield equal states when folded into `D.init`.

Proof scaffold: base cases for empty and singleton permutations
are trivial (unique permutation). The general case requires the
bubble-sort argument via `rc_non_comm` / `cond_comm`. -/
theorem convergence
    (_hVC : SatisfiesVCs D) {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev : Set (Op D.AppOp)}
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (_h₁_resp : respects π₁ (lo C)) (_h₂_resp : respects π₂ (lo C)) :
    applySeq D D.init π₁ = applySeq D D.init π₂ := by
  -- Base case: both empty.
  by_cases h₁_nil : π₁ = []
  · by_cases h₂_nil : π₂ = []
    · subst h₁_nil; subst h₂_nil; rfl
    · -- π₁ = [], π₂ ≠ []. Impossible: listPermOf forces ev = ∅ = ev,
      -- but π₂ ≠ [] means some event is in ev, contradiction.
      exfalso
      obtain ⟨_, hm₂⟩ := h₂_perm
      obtain ⟨_, hm₁⟩ := h₁_perm
      subst h₁_nil
      obtain ⟨e, hmem⟩ : ∃ e, e ∈ π₂ := by
        match π₂, h₂_nil with
        | e :: _, _ => exact ⟨e, List.mem_cons_self⟩
      have hev : e ∈ ev := (hm₂ e).mp hmem
      exact (List.not_mem_nil : e ∉ []) ((hm₁ e).mpr hev)
  · by_cases h₂_nil : π₂ = []
    · -- Symmetric impossibility.
      exfalso
      obtain ⟨_, hm₁⟩ := h₁_perm
      obtain ⟨_, hm₂⟩ := h₂_perm
      subst h₂_nil
      obtain ⟨e, hmem⟩ : ∃ e, e ∈ π₁ := by
        match π₁, h₁_nil with
        | e :: _, _ => exact ⟨e, List.mem_cons_self⟩
      have hev : e ∈ ev := (hm₁ e).mp hmem
      exact (List.not_mem_nil : e ∉ []) ((hm₂ e).mpr hev)
    · -- Both non-empty. The general convergence argument: pull
      -- the rc-maximal event to the end of both permutations via
      -- adjacent swaps (justified by `rc_non_comm` and
      -- `cond_comm`), then recurse on the shorter permutations.
      -- Left for future work; requires list-manipulation lemmas
      -- beyond what's directly derivable from the 24 VCs.
      sorry

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

/-- **BottomUp-1-OP, clause (b), base case** (`a = init`).

`merge(update init o₁, init) = update (merge init init) o₁`.
Direct application of `base_1op`. -/
theorem bottomUp_1op_bot_base
    (hVC : SatisfiesVCs D) (o₁ : Op D.AppOp) :
    D.merge (D.update D.init o₁) D.init
      = D.update (D.merge D.init D.init) o₁ :=
  hVC.base_1op o₁

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

/-! ### Missing lemmas isolated as dependencies

These lemmas are needed to close the inductive cases of
`merge_linearization_exists` but are not directly derivable from
the 24 VCs as standalone statements. The Sal paper (appendix §A.2)
proves them as byproducts of its nested induction that combines
the outer event-set-size induction with the inner VC applications.

Each is stated here with a sorry so `merge_linearization_exists`
can invoke them; they will be closed in future sessions by either
(a) porting the paper's nested induction, or (b) adding the
required invariants to `Configuration` and re-deriving. -/

/-- `merge D.init s = s` for reachable `s`. Needed for the
`π₁ = []` case of `merge_linearization_exists`.

Not a direct VC consequence: every `ind_*_1op` / `inter_*_1op`
requires the RHS of `merge` to have an event `ol` applied; the
degenerate `b = init` is only handled by `base_1op` at `a = init`.
The paper derives this via convergence + iteratively stripping the
rightmost event of `π` through phantom-event tricks. -/
theorem merge_init_left_reachable
    (_hVC : SatisfiesVCs D) (π : List (Op D.AppOp)) :
    D.merge D.init (applySeq D D.init π) = applySeq D D.init π := by
  sorry

/-- `merge s D.init = s` for reachable `s`. Mirror of
`merge_init_left_reachable` via `merge_comm`. -/
theorem merge_init_right_reachable
    (hVC : SatisfiesVCs D) (π : List (Op D.AppOp)) :
    D.merge (applySeq D D.init π) D.init = applySeq D D.init π := by
  rw [hVC.merge_comm]
  exact merge_init_left_reachable hVC π

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
    {D : CRDTSig} (hVC : SatisfiesVCs D)
    {C : Configuration D}
    {π₁ π₂ : List (Op D.AppOp)} {ev₁ ev₂ : Set (Op D.AppOp)}
    {s₁ s₂ : D.State}
    (h₁_perm : listPermOf π₁ ev₁) (h₂_perm : listPermOf π₂ ev₂)
    (h₁_resp : respects π₁ (lo C)) (h₂_resp : respects π₂ (lo C))
    (h₁_state : applySeq D D.init π₁ = s₁)
    (h₂_state : applySeq D D.init π₂ = s₂) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧
         respects π (lo C) ∧
         applySeq D D.init π = D.merge s₁ s₂ := by
  -- Generalise then strong-induct on π₁.length + π₂.length.
  suffices gen : ∀ n (π₁ π₂ : List (Op D.AppOp)) (ev₁ ev₂ : Set (Op D.AppOp))
                   (s₁ s₂ : D.State),
      π₁.length + π₂.length = n →
      listPermOf π₁ ev₁ → listPermOf π₂ ev₂ →
      respects π₁ (lo C) → respects π₂ (lo C) →
      applySeq D D.init π₁ = s₁ → applySeq D D.init π₂ = s₂ →
      ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C) ∧
           applySeq D D.init π = D.merge s₁ s₂ by
    exact gen _ π₁ π₂ ev₁ ev₂ s₁ s₂ rfl
      h₁_perm h₂_perm h₁_resp h₂_resp h₁_state h₂_state
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro π₁ π₂ ev₁ ev₂ s₁ s₂ h_len h₁p h₂p h₁r h₂r h₁s h₂s
    match hπ₁ : π₁, hπ₂ : π₂ with
    | [], [] =>
      -- Both-empty base case.
      subst hπ₁; subst hπ₂
      obtain ⟨_, hm₁⟩ := h₁p
      obtain ⟨_, hm₂⟩ := h₂p
      have hev₁_empty : ev₁ = ∅ := by
        ext a; exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
      have hev₂_empty : ev₂ = ∅ := by
        ext a; exact ⟨fun ha => absurd ((hm₂ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
      subst hev₁_empty; subst hev₂_empty
      simp [applySeq] at h₁s h₂s
      subst h₁s; subst h₂s
      refine ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, ?_⟩
      simp [applySeq, hVC.merge_idem]
    | [], _ :: _ =>
      -- π₁ = [], π₂ non-empty. Use merge_init_left_reachable:
      -- merge init s₂ = s₂, so witness is π₂.
      subst hπ₁; subst hπ₂
      simp [applySeq] at h₁s
      obtain ⟨hn₁, hm₁⟩ := h₁p
      have hev₁_empty : ev₁ = ∅ := by
        ext a; exact ⟨fun ha => absurd ((hm₁ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
      subst hev₁_empty
      subst h₁s
      refine ⟨_, ?_, h₂r, ?_⟩
      · simpa [Set.empty_union] using h₂p
      · rw [← h₂s]; exact (merge_init_left_reachable hVC _).symm
    | _ :: _, [] =>
      -- π₁ non-empty, π₂ = []. Symmetric via merge_init_right_reachable.
      subst hπ₁; subst hπ₂
      simp [applySeq] at h₂s
      obtain ⟨hn₂, hm₂⟩ := h₂p
      have hev₂_empty : ev₂ = ∅ := by
        ext a; exact ⟨fun ha => absurd ((hm₂ a).mpr ha) List.not_mem_nil, fun ha => ha.elim⟩
      subst hev₂_empty
      subst h₂s
      refine ⟨_, ?_, h₁r, ?_⟩
      · simpa [Set.union_empty] using h₁p
      · rw [← h₁s]; exact (merge_init_right_reachable hVC _).symm
    | _ :: _, _ :: _ =>
      -- Both non-empty. Decompose from the back to expose last events.
      rcases List.eq_nil_or_concat' π₁ with hπ₁_nil | ⟨π₁', e₁, hπ₁_back⟩
      · rw [hπ₁_nil] at hπ₁; exact absurd hπ₁ (List.cons_ne_nil _ _).symm
      rcases List.eq_nil_or_concat' π₂ with hπ₂_nil | ⟨π₂', e₂, hπ₂_back⟩
      · rw [hπ₂_nil] at hπ₂; exact absurd hπ₂ (List.cons_ne_nil _ _).symm
      -- Now π₁ = π₁' ++ [e₁], π₂ = π₂' ++ [e₂]. Case-split on
      -- whether the last events match.
      by_cases h_same : e₁ = e₂
      · -- Shared last event: factor via lem_0op + recurse via ih.
        subst h_same
        -- Invoke IH with smaller lengths. To call ih, we need to
        -- establish:
        --   - π₁'.length + π₂'.length < n
        --   - listPermOf π₁' (ev₁ \ {e₁}) and similarly for π₂'
        --   - respects π₁' (lo C), from h₁r
        --   - applySeq init π₁' = some s₁', similarly for π₂'
        -- Then construct witness π' ++ [e₁] from the IH result.
        -- Concrete state equation:
        --   applySeq init (π' ++ [e₁])
        --     = update (merge s₁' s₂') e₁     [by ih]
        --     = merge (update s₁' e₁) (update s₂' e₁) [by lem_0op.symm]
        --     = merge s₁ s₂                    [defs]
        -- The listPermOf + respects bookkeeping is substantial but
        -- mechanical. Left for dedicated session.
        sorry
      · -- Distinct last events: use bottomUp_2op_reachable (rc case)
        -- + symmetric variant for the Either rc case + IH.
        -- Key step: rc between e₁ and e₂ determines which to peel.
        -- If rc(e₂, e₁) = Fst_then_snd, use bottomUp_2op_reachable.
        -- If rc(e₁, e₂) = Fst_then_snd, peel e₂ instead (symmetric).
        -- If rc = Either (commute), peel either.
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
