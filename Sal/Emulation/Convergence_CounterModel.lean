import Sal.Emulation.Merge_Linearization_Set

/-!
# Counter-model: convergence over backward-closed replica sets is FALSE

This file machine-checks finding **A1** of
`Sal/Metatheory/FINDINGS.md`: the lemma that `FINDINGS.md` §5
identified as the sole remaining blocker of the merge-linearization
induction —

> *convergence over merely backward-closed reachable replica event
> sets* (w.r.t. the configuration-global `lo C`)

— is **false**, even for a `D` that satisfies every property the
`convergence` proof machinery consumes (`rc_non_comm` +
`rc_non_comm_directional` + `no_rc_chain` + `cond_comm_base` +
`cond_comm_lift` + `merge_comm/idem/init` + `lem_0op`).

## The model

`AWSet` — a two-op add-wins set skeleton over one implicit key:

* `State := (added, dead) : Set Timestamp × Set Timestamp`;
  the live set is `added \ dead`.
* `add` inserts its timestamp into `added`.
* `rem` kills everything currently added: `dead := added ∪ dead`
  (state-dependent — this is what makes `add`/`rem` non-commuting).
* `merge` is the pairwise union (a join-semilattice).
* `rc rem add = Fst_then_snd` (add wins over a concurrent remove),
  the paper's OR-set resolution.

## The configuration

* replica 0: `e = add` (t=0) then `e₃ = rem` (t=1), so `vis e e₃`;
* replica 1: `y = rem` (t=2), concurrent with both; its event set is
  `ev = {y, e}` — it merged replica 0's state *between* `e` and `e₃`.

In the full configuration, `lo C` orders **neither** `y, e`: the
rc-edge `y →lo e` is cancelled because `e` has the absorber `e₃ ∈
C.events` (`lo`'s overwriter existential is configuration-global).
So `[y, e]` and `[e, y]` both respect `lo C`, yet

    fold [y, e] = ({0}, ∅)   ≠   fold [e, y] = ({0}, {0}).

`ev` is backward-closed (even unconditionally: the only `vis`-edge
points out of `ev`). Hence no convergence statement over
backward-closed sub-sets w.r.t. `lo C` is provable.

The set-relative relation of `Merge_Linearization_Set.lean` repairs
this: `loOn C ev` *keeps* the edge `y → e` (no absorber inside
`ev`), so only the fold-correct `[y, e]` respects it —
`loOn_keeps_the_edge` below.

## Bonus finding (A3 corollary)

`SatisfiesVCs.shared_peel_1op` — the "missing VC" added to the
bundle as a crutch for the shared-event peel — is **false for
`AWSet`** (`AWSet_shared_peel_1op_false`): the current bundle
excludes exactly the state-dependent RDTs (the paper's own OR-set
among them) whose non-trivial `rc` the metatheorem is about.
-/

namespace Sal.Emulation

open Classical

/-- The two abstract ops of the add-wins skeleton. -/
inductive AWOp : Type where
  | add
  | rem
  deriving DecidableEq, Repr

/-- The state: `(added, dead)`. -/
abbrev AWState : Type := Set Timestamp × Set Timestamp

/-- `add` inserts its timestamp; `rem` kills everything added. -/
def awUpdate (σ : AWState) (e : Op AWOp) : AWState :=
  match e.2.2 with
  | .add => (insert e.1 σ.1, σ.2)
  | .rem => (σ.1, σ.1 ∪ σ.2)

/-- Pairwise union — a join-semilattice. -/
def awMerge (σ τ : AWState) : AWState := (σ.1 ∪ τ.1, σ.2 ∪ τ.2)

/-- `rc rem add = Fst_then_snd`: add wins over a concurrent remove. -/
def awRc (e₁ e₂ : Op AWOp) : RcRes :=
  match e₁.2.2, e₂.2.2 with
  | .rem, .add => RcRes.Fst_then_snd
  | .add, .rem => RcRes.Snd_then_fst
  | _, _ => RcRes.Either

/-- Add-wins set skeleton over one implicit key. See file header. -/
noncomputable def AWSet : CRDTSig where
  State := AWState
  dec_state := Classical.decEq _
  init := (∅, ∅)
  AppOp := AWOp
  dec_op := inferInstance
  Query := Unit
  Value := Set Timestamp
  update := awUpdate
  merge := awMerge
  query := fun σ _ => σ.1 \ σ.2
  rc := awRc

@[simp] theorem AWSet_update : AWSet.update = awUpdate := rfl
@[simp] theorem AWSet_merge : AWSet.merge = awMerge := rfl
@[simp] theorem AWSet_rc : AWSet.rc = awRc := rfl
@[simp] theorem AWSet_init : AWSet.init = ((∅ : Set Timestamp), (∅ : Set Timestamp)) := rfl

theorem awUpdate_add {e : Op AWOp} (h : e.2.2 = AWOp.add) (σ : AWState) :
    awUpdate σ e = (insert e.1 σ.1, σ.2) := by
  unfold awUpdate; rw [h]

theorem awUpdate_rem {e : Op AWOp} (h : e.2.2 = AWOp.rem) (σ : AWState) :
    awUpdate σ e = (σ.1, σ.1 ∪ σ.2) := by
  unfold awUpdate; rw [h]

theorem awRc_eq {e₁ e₂ : Op AWOp} :
    awRc e₁ e₂ =
      match e₁.2.2, e₂.2.2 with
      | .rem, .add => RcRes.Fst_then_snd
      | .add, .rem => RcRes.Snd_then_fst
      | _, _ => RcRes.Either := rfl

/-! ### Basic op algebra -/

theorem AWSet_comm_add_add {e₁ e₂ : Op AWSet.AppOp}
    (h₁ : e₁.2.2 = AWOp.add) (h₂ : e₂.2.2 = AWOp.add) :
    AWSet.commutes e₁ e₂ := by
  intro s
  simp only [AWSet_update, awUpdate_add h₁, awUpdate_add h₂]
  refine Prod.ext ?_ rfl
  ext x
  simp only [Set.mem_insert_iff]
  tauto

theorem AWSet_comm_rem_rem {e₁ e₂ : Op AWSet.AppOp}
    (h₁ : e₁.2.2 = AWOp.rem) (h₂ : e₂.2.2 = AWOp.rem) :
    AWSet.commutes e₁ e₂ := by
  intro s
  simp only [AWSet_update, awUpdate_rem h₁, awUpdate_rem h₂]

/-- add/rem never commute: from `(∅, ∅)`, add-then-rem kills the new
timestamp, rem-then-add leaves it alive. -/
theorem AWSet_not_comm_add_rem {e₁ e₂ : Op AWSet.AppOp}
    (h₁ : e₁.2.2 = AWOp.add) (h₂ : e₂.2.2 = AWOp.rem) :
    ¬ AWSet.commutes e₁ e₂ := by
  intro h
  have h0 := h (∅, ∅)
  simp only [AWSet_update, awUpdate_add h₁, awUpdate_rem h₂] at h0
  have h_dead := congrArg Prod.snd h0
  simp only [] at h_dead
  have h_mem : e₁.1 ∈ (insert e₁.1 (∅ : Set Timestamp) ∪ ∅) := by simp
  rw [h_dead] at h_mem
  simp at h_mem

theorem AWSet_not_comm_rem_add {e₁ e₂ : Op AWSet.AppOp}
    (h₁ : e₁.2.2 = AWOp.rem) (h₂ : e₂.2.2 = AWOp.add) :
    ¬ AWSet.commutes e₁ e₂ :=
  fun h => AWSet_not_comm_add_rem h₂ h₁ (fun s => (h s).symm)

/-! ### The `convergence`-toolkit properties hold for `AWSet` -/

theorem AWSet_rc_non_comm :
    ∀ o₁ o₂ : Op AWSet.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (AWSet.rc o₁ o₂ = RcRes.Either ↔ AWSet.commutes o₁ o₂) := by
  intro o₁ o₂ _ _
  rcases h₁ : o₁.2.2 <;> rcases h₂ : o₂.2.2 <;>
    simp only [AWSet_rc, awRc_eq, h₁, h₂]
  · exact ⟨fun _ => AWSet_comm_add_add h₁ h₂, fun _ => by trivial⟩
  · constructor
    · intro h; exact absurd h (by first | exact fun h' => nomatch h' | decide)
    · intro h; exact absurd h (AWSet_not_comm_add_rem h₁ h₂)
  · constructor
    · intro h; exact absurd h (by first | exact fun h' => nomatch h' | decide)
    · intro h; exact absurd h (AWSet_not_comm_rem_add h₁ h₂)
  · exact ⟨fun _ => AWSet_comm_rem_rem h₁ h₂, fun _ => by trivial⟩

theorem AWSet_rc_non_comm_directional :
    ∀ o₁ o₂ : Op AWSet.AppOp,
      distinctOps o₁ o₂ →
      (¬ AWSet.commutes o₁ o₂ ↔
       (AWSet.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        AWSet.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _
  rcases h₁ : o₁.2.2 <;> rcases h₂ : o₂.2.2 <;>
    simp only [AWSet_rc, awRc_eq, h₁, h₂]
  · constructor
    · intro h; exact absurd (AWSet_comm_add_add h₁ h₂) h
    · rintro (h | h) <;>
        exact absurd h (by first | exact fun h' => nomatch h' | decide)
  · constructor
    · intro _; exact Or.inr (by trivial)
    · intro _; exact AWSet_not_comm_add_rem h₁ h₂
  · constructor
    · intro _; exact Or.inl (by trivial)
    · intro _; exact AWSet_not_comm_rem_add h₁ h₂
  · constructor
    · intro h; exact absurd (AWSet_comm_rem_rem h₁ h₂) h
    · rintro (h | h) <;>
        exact absurd h (by first | exact fun h' => nomatch h' | decide)

theorem AWSet_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op AWSet.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (AWSet.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         AWSet.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro o₁ o₂ o₃ _ _ ⟨h₁₂, h₂₃⟩
  rcases ha : o₁.2.2 <;> rcases hb : o₂.2.2 <;> rcases hc : o₃.2.2 <;>
    simp only [AWSet_rc, awRc_eq, ha, hb, hc] at h₁₂ h₂₃ <;>
    first
      | exact absurd h₁₂ (by decide)
      | exact absurd h₂₃ (by decide)

theorem AWSet_merge_comm :
    ∀ a b : AWSet.State, AWSet.merge a b = AWSet.merge b a := by
  intro a b
  simp only [AWSet_merge, awMerge]
  exact Prod.ext (Set.union_comm _ _) (Set.union_comm _ _)

theorem AWSet_merge_idem : ∀ s : AWSet.State, AWSet.merge s s = s := by
  intro s
  simp only [AWSet_merge, awMerge]
  exact Prod.ext (Set.union_self _) (Set.union_self _)

theorem AWSet_merge_init :
    ∀ s : AWSet.State, AWSet.merge AWSet.init s = s := by
  intro s
  simp only [AWSet_merge, AWSet_init, awMerge]
  exact Prod.ext (Set.empty_union _) (Set.empty_union _)

theorem AWSet_lem_0op :
    ∀ (a b : AWSet.State) (ol : Op AWSet.AppOp),
      AWSet.merge (AWSet.update a ol) (AWSet.update b ol)
        = AWSet.update (AWSet.merge a b) ol := by
  intro a b ol
  rcases h : ol.2.2
  · simp only [AWSet_update, AWSet_merge, awUpdate_add h, awMerge]
    refine Prod.ext ?_ rfl
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto
  · simp only [AWSet_update, AWSet_merge, awUpdate_rem h, awMerge]
    refine Prod.ext rfl ?_
    ext x
    simp only [Set.mem_union]
    tauto

/-- `cond_comm_base`: `rc o₁ o₂ = Fst` forces `(o₁, o₂) = (rem, add)`;
`rc o₂ o₃ ≠ Either` with `o₂ = add` forces `o₃ = rem`, which re-kills
the timestamp on which the two sides differ. -/
theorem AWSet_cond_comm_base :
    ∀ (s : AWSet.State) (o₁ o₂ o₃ : Op AWSet.AppOp),
      distinctOps o₁ o₂ → distinctOps o₂ o₃ → distinctOps o₁ o₃ →
      AWSet.rc o₁ o₂ = RcRes.Fst_then_snd →
      AWSet.rc o₂ o₃ ≠ RcRes.Either →
      AWSet.update (AWSet.update (AWSet.update s o₁) o₂) o₃
        = AWSet.update (AWSet.update (AWSet.update s o₂) o₁) o₃ := by
  intro s o₁ o₂ o₃ _ _ _ h_rc h_ne
  -- every branch except (o₁, o₂) = (rem, add) is killed by h_rc
  rcases ha : o₁.2.2 <;> rcases hb : o₂.2.2 <;>
    simp only [AWSet_rc, awRc_eq, ha, hb] at h_rc <;>
    try exact absurd h_rc (by decide)
  rcases hc : o₃.2.2
  · exact absurd (by simp only [AWSet_rc, awRc_eq, hb, hc]) h_ne
  · simp only [AWSet_update, awUpdate_rem ha, awUpdate_add hb,
      awUpdate_rem hc]
    refine Prod.ext rfl ?_
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto

/-- The invariant threaded through `cond_comm_lift`'s intervening
sequence: equal `added` components containing the pivot timestamp,
`dead` components equal or differing exactly by the pivot. -/
private theorem AWSet_lift_invariant (t : Timestamp)
    (π : List (Op AWSet.AppOp)) :
    ∀ L R : AWState,
      L.1 = R.1 → t ∈ L.1 →
      (L.2 = R.2 ∨ L.2 = insert t R.2) →
      (applySeq AWSet L π).1 = (applySeq AWSet R π).1 ∧
      t ∈ (applySeq AWSet L π).1 ∧
      ((applySeq AWSet L π).2 = (applySeq AWSet R π).2 ∨
       (applySeq AWSet L π).2 = insert t (applySeq AWSet R π).2) := by
  induction π with
  | nil =>
    intro L R h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  | cons o π' ih =>
    intro L R h₁ h₂ h₃
    have h_step : applySeq AWSet L (o :: π')
        = applySeq AWSet (awUpdate L o) π' := rfl
    have h_step' : applySeq AWSet R (o :: π')
        = applySeq AWSet (awUpdate R o) π' := rfl
    rw [h_step, h_step']
    rcases ho : o.2.2
    · -- add: dead unchanged, added grows equally on both sides.
      refine ih (awUpdate L o) (awUpdate R o) ?_ ?_ ?_
      · simp only [awUpdate_add ho]; rw [h₁]
      · simp only [awUpdate_add ho]
        exact Set.mem_insert_of_mem _ h₂
      · simp only [awUpdate_add ho]
        rcases h₃ with h₃ | h₃
        · left; rw [h₃]
        · right; rw [h₃]
    · -- rem: dead := added ∪ dead; the pivot inside `added`
      -- collapses the `insert t` difference.
      refine ih (awUpdate L o) (awUpdate R o) ?_ ?_ ?_
      · simp only [awUpdate_rem ho]; exact h₁
      · simp only [awUpdate_rem ho]; exact h₂
      · simp only [awUpdate_rem ho]
        left
        rw [← h₁]
        rcases h₃ with h₃ | h₃
        · rw [h₃]
        · rw [h₃]
          ext x
          simp only [Set.mem_union, Set.mem_insert_iff]
          constructor
          · rintro (hx | hx | hx)
            · exact Or.inl hx
            · subst hx; exact Or.inl h₂
            · exact Or.inr hx
          · rintro (hx | hx)
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)

/-- `cond_comm_lift` holds for `AWSet`. -/
theorem AWSet_cond_comm_lift :
    ∀ (s : AWSet.State) (e e' e'' : Op AWSet.AppOp)
      (π : List (Op AWSet.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      AWSet.rc e e' = RcRes.Fst_then_snd →
      ¬ AWSet.commutes e' e'' →
      AWSet.update (applySeq AWSet (AWSet.update (AWSet.update s e') e) π) e''
        = AWSet.update (applySeq AWSet (AWSet.update (AWSet.update s e) e') π) e'' := by
  intro s e e' e'' π _ _ _ h_rc h_nc
  -- rc e e' = Fst forces e = rem, e' = add.
  rcases ha : e.2.2 <;> rcases hb : e'.2.2 <;>
    simp only [AWSet_rc, awRc_eq, ha, hb] at h_rc <;>
    try exact absurd h_rc (by decide)
  -- e'' cannot be add (add/add commute), so e'' = rem.
  rcases hc : e''.2.2
  · exact absurd (AWSet_comm_add_add hb hc) h_nc
  -- L := (s; e'=add; e=rem) carries the extra dead pivot e'.1;
  -- R := (s; e=rem; e'=add).
  have h_inv := AWSet_lift_invariant e'.1 π
    (awUpdate (awUpdate s e') e)
    (awUpdate (awUpdate s e) e')
    (by simp only [awUpdate_add hb, awUpdate_rem ha])
    (by simp only [awUpdate_add hb, awUpdate_rem ha]
        exact Set.mem_insert _ _)
    (by
      simp only [awUpdate_add hb, awUpdate_rem ha]
      right
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff]
      tauto)
  obtain ⟨h_added, h_t, h_dead⟩ := h_inv
  -- Final rem: dead := added ∪ dead absorbs the pivot difference.
  show awUpdate (applySeq AWSet (awUpdate (awUpdate s e') e) π) e''
      = awUpdate (applySeq AWSet (awUpdate (awUpdate s e) e') π) e''
  simp only [awUpdate_rem hc]
  refine Prod.ext h_added ?_
  rcases h_dead with h_dead | h_dead
  · rw [h_added, h_dead]
  · rw [h_added, h_dead]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inl hx
      · subst hx; exact Or.inl (h_added ▸ h_t)
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)

/-! ### The three events and the configuration -/

/-- `e = add` at replica 0, timestamp 0. -/
def evAdd : Op AWSet.AppOp := (0, 0, AWOp.add)
/-- `e₃ = rem` at replica 0, timestamp 1 — the absorber
(`vis evAdd evRem0`). -/
def evRem0 : Op AWSet.AppOp := (1, 0, AWOp.rem)
/-- `y = rem` at replica 1, timestamp 2, concurrent with both. -/
def evRem1 : Op AWSet.AppOp := (2, 1, AWOp.rem)

/-- Every event of any replica set of the counter-configuration is
one of the three literals. -/
private theorem counter_L_cases (r₀ : Replica)
    (s₀ : Set (Op AWSet.AppOp))
    (hL₀ : (if r₀ = 0 then some {evAdd, evRem0}
            else if r₀ = 1 then some {evRem1, evAdd}
            else none) = some s₀) :
    ∀ x ∈ s₀, x = evAdd ∨ x = evRem0 ∨ x = evRem1 := by
  intro x hx
  by_cases h0 : r₀ = 0
  · rw [if_pos h0, Option.some.injEq] at hL₀
    rw [← hL₀] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases h1 : r₀ = 1
    · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL₀
      rw [← hL₀] at hx
      rcases hx with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rw [if_neg h0, if_neg h1] at hL₀
      exact absurd hL₀ (by simp)

/-- The counter-configuration. Replica 0 holds `{evAdd, evRem0}`;
replica 1 holds `{evRem1, evAdd}` (it merged replica 0's state
between `evAdd` and `evRem0`). The single `vis`-edge is
`evAdd → evRem0`. Visibly reachable in 5 transition-system steps. -/
noncomputable def counterConfig : Configuration AWSet where
  N := fun r =>
    if r = 0 then some (applySeq AWSet AWSet.init [evAdd, evRem0])
    else if r = 1 then some (applySeq AWSet AWSet.init [evRem1, evAdd])
    else none
  L := fun r =>
    if r = 0 then some {evAdd, evRem0}
    else if r = 1 then some {evRem1, evAdd}
    else none
  vis := fun a b => a = evAdd ∧ b = evRem0
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [h0]
    · by_cases h1 : r = 1 <;> simp [h0, h1]
  vis_src := by
    rintro a b ⟨rfl, rfl⟩
    exact ⟨0, {evAdd, evRem0}, by simp, Or.inl rfl⟩
  vis_tgt := by
    rintro a b ⟨rfl, rfl⟩
    exact ⟨0, {evAdd, evRem0}, by simp, Or.inr rfl⟩
  vis_causal := by
    rintro a b r s ⟨rfl, rfl⟩ hL hs
    by_cases h0 : r = 0
    · rw [if_pos h0, Option.some.injEq] at hL
      rw [← hL]
      exact Or.inl rfl
    · by_cases h1 : r = 1
      · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL
        rw [← hL] at hs
        rcases hs with h | h <;> simp [evRem0, evRem1, evAdd] at h
      · rw [if_neg h0, if_neg h1] at hL
        exact absurd hL (by simp)
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rcases counter_L_cases r s hL a hs with rfl | rfl | rfl <;>
      rcases counter_L_cases r' s' hL' b hs' with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [evAdd, evRem0, evRem1]
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne hrep
    rcases counter_L_cases r s hL a hs with rfl | rfl | rfl <;>
      rcases counter_L_cases r' s' hL' b hs' with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩
        | (exfalso; simp [evAdd, evRem0, evRem1] at hrep)

/-! ### The refutation -/

/-- The replica set of replica 1. -/
def counterEv : Set (Op AWSet.AppOp) := {evRem1, evAdd}

theorem counterEv_in_C : ∀ a ∈ counterEv, a ∈ counterConfig.events := by
  intro a ha
  exact ⟨1, {evRem1, evAdd}, by simp [counterConfig], ha⟩

/-- `counterEv` is backward-closed under `vis` — unconditionally, not
just under `vis ∧ ¬commutes`: the only `vis` edge targets `evRem0`,
which is outside the set. -/
theorem counterEv_closed :
    ∀ a b, counterConfig.vis a b → b ∈ counterEv → a ∈ counterEv := by
  rintro a b ⟨rfl, rfl⟩ hb
  rcases hb with h | h <;> simp [evRem0, evRem1, evAdd] at h

/-- `[y, e]` respects `lo C`: there is no `lo`-edge `evAdd → evRem1`
(`rc add rem = Snd_then_fst`, no vis). -/
theorem respects_ye :
    respects [evRem1, evAdd] (lo counterConfig) := by
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro b hb
  rw [List.mem_singleton] at hb; subst hb
  rintro (⟨h, _⟩ | ⟨_, _, h_rc, _⟩)
  · exact absurd h.2 (by simp [counterConfig, evAdd, evRem0, evRem1])
  · rw [AWSet_rc] at h_rc
    exact absurd h_rc (by simp [awRc_eq, evAdd, evRem1])

/-- **The absorber cancellation**: `[e, y]` also respects `lo C`.
The rc-edge `evRem1 → evAdd` (`rc rem add = Fst`) is cancelled by the
configuration-global overwriter `evRem0` (`vis evAdd evRem0`,
`¬commutes`). -/
theorem respects_ey :
    respects [evAdd, evRem1] (lo counterConfig) := by
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro b hb
  rw [List.mem_singleton] at hb; subst hb
  rintro (⟨h, _⟩ | ⟨_, _, _, h_no_ow⟩)
  · exact absurd h.1 (by simp [counterConfig, evAdd, evRem0, evRem1])
  · exact h_no_ow ⟨evRem0, ⟨rfl, rfl⟩,
      AWSet_not_comm_add_rem (by rfl) (by rfl)⟩

/-- The two folds differ: `[y, e]` leaves timestamp 0 alive,
`[e, y]` kills it. -/
theorem folds_differ :
    applySeq AWSet AWSet.init [evRem1, evAdd]
      ≠ applySeq AWSet AWSet.init [evAdd, evRem1] := by
  intro h
  have h_dead := congrArg Prod.snd h
  have h_lhs : applySeq AWSet AWSet.init [evRem1, evAdd]
      = (insert (0 : Timestamp) ∅, (∅ : Set Timestamp)) := by
    show awUpdate (awUpdate AWSet.init evRem1) evAdd = _
    simp only [AWSet_init,
      awUpdate_rem (show evRem1.2.2 = AWOp.rem from rfl),
      awUpdate_add (show evAdd.2.2 = AWOp.add from rfl)]
    refine Prod.ext rfl ?_
    simp
  have h_rhs : applySeq AWSet AWSet.init [evAdd, evRem1]
      = (insert (0 : Timestamp) ∅,
         insert (0 : Timestamp) (∅ : Set Timestamp) ∪ ∅) := by
    show awUpdate (awUpdate AWSet.init evAdd) evRem1 = _
    simp only [AWSet_init,
      awUpdate_add (show evAdd.2.2 = AWOp.add from rfl),
      awUpdate_rem (show evRem1.2.2 = AWOp.rem from rfl)]
    rfl
  rw [h_lhs, h_rhs] at h_dead
  have h0 := Set.ext_iff.mp h_dead 0
  simp at h0

theorem perm_ye : listPermOf [evRem1, evAdd] counterEv := by
  constructor
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro b hb
    rw [List.mem_singleton] at hb; subst hb
    simp [evRem1, evAdd]
  · intro a
    constructor
    · intro ha
      rcases List.mem_cons.mp ha with h | h
      · exact Or.inl h
      · rw [List.mem_singleton] at h; exact Or.inr h
    · rintro (h | h)
      · rw [h]; exact List.mem_cons_self
      · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem perm_ey : listPermOf [evAdd, evRem1] counterEv := by
  constructor
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro b hb
    rw [List.mem_singleton] at hb; subst hb
    simp [evRem1, evAdd]
  · intro a
    constructor
    · intro ha
      rcases List.mem_cons.mp ha with h | h
      · exact Or.inr h
      · rw [List.mem_singleton] at h; exact Or.inl h
    · rintro (h | h)
      · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [h]; exact List.mem_cons_self

/-- **The headline refutation.** There is a CRDT signature satisfying
the entire toolkit the `convergence` proof machinery consumes,
together with a configuration, a backward-closed sub-set `ev` of its
events, and two `lo C`-respecting enumerations of `ev` whose folds
differ. Hence "convergence over backward-closed (replica) event sets
w.r.t. `lo C`" — the blocker lemma proposed by `FINDINGS.md` §5 — is
false, and no weakening of `convergence`'s overwriter-closure
hypothesis to backward closure can be proved. -/
theorem convergence_over_backward_closed_subsets_false :
    ∃ (D : CRDTSig) (C : Configuration D) (ev : Set (Op D.AppOp))
      (π₁ π₂ : List (Op D.AppOp)),
      -- the convergence toolkit holds for D
      (∀ o₁ o₂ : Op D.AppOp, distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
        (D.rc o₁ o₂ = RcRes.Either ↔ D.commutes o₁ o₂)) ∧
      (∀ o₁ o₂ : Op D.AppOp, distinctOps o₁ o₂ →
        (¬ D.commutes o₁ o₂ ↔
         (D.rc o₁ o₂ = RcRes.Fst_then_snd ∨
          D.rc o₂ o₁ = RcRes.Fst_then_snd))) ∧
      (∀ o₁ o₂ o₃ : Op D.AppOp, distinctOps o₁ o₂ → distinctOps o₂ o₃ →
        ¬ (D.rc o₁ o₂ = RcRes.Fst_then_snd ∧
           D.rc o₂ o₃ = RcRes.Fst_then_snd)) ∧
      (∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
        distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
        D.rc e e' = RcRes.Fst_then_snd →
        ¬ D.commutes e' e'' →
        D.update (applySeq D (D.update (D.update s e') e) π) e''
          = D.update (applySeq D (D.update (D.update s e) e') π) e'') ∧
      (∀ a b : D.State, D.merge a b = D.merge b a) ∧
      (∀ s : D.State, D.merge s s = s) ∧
      (∀ s : D.State, D.merge D.init s = s) ∧
      (∀ (a b : D.State) (ol : Op D.AppOp),
        D.merge (D.update a ol) (D.update b ol)
          = D.update (D.merge a b) ol) ∧
      -- the counter-instance
      (∀ a ∈ ev, a ∈ C.events) ∧
      (∀ a b, C.vis a b → b ∈ ev → a ∈ ev) ∧
      listPermOf π₁ ev ∧ listPermOf π₂ ev ∧
      respects π₁ (lo C) ∧ respects π₂ (lo C) ∧
      applySeq D D.init π₁ ≠ applySeq D D.init π₂ :=
  ⟨AWSet, counterConfig, counterEv, [evRem1, evAdd], [evAdd, evRem1],
    AWSet_rc_non_comm, AWSet_rc_non_comm_directional, AWSet_no_rc_chain,
    AWSet_cond_comm_lift, AWSet_merge_comm, AWSet_merge_idem,
    AWSet_merge_init, AWSet_lem_0op,
    counterEv_in_C, counterEv_closed, perm_ye, perm_ey,
    respects_ye, respects_ey, folds_differ⟩

/-- **The repair, on the same instance**: the set-relative `loOn`
keeps the edge `evRem1 → evAdd` (there is no absorber of `evAdd`
*inside* `counterEv`), so the fold-wrong enumeration `[e, y]` does
NOT respect `loOn C counterEv` — exactly the discrimination
`convergence_on` needs. -/
theorem loOn_keeps_the_edge :
    loOn counterConfig counterEv evRem1 evAdd ∧
    ¬ respects [evAdd, evRem1] (loOn counterConfig counterEv) := by
  have h_edge : loOn counterConfig counterEv evRem1 evAdd := by
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨h, _⟩; simp [evRem1, evAdd] at h
    · rintro ⟨_, h⟩; simp [evRem0, evRem1] at h
    · rw [AWSet_rc]; rfl
    · rintro ⟨e₃, h_mem, h_vis, _⟩
      obtain ⟨_, rfl⟩ := h_vis
      rcases h_mem with h | h <;> simp [evRem0, evRem1, evAdd] at h
  refine ⟨h_edge, fun h_resp => ?_⟩
  have := (List.pairwise_cons.mp h_resp).1 evRem1 List.mem_cons_self
  exact this h_edge

/-! ### Bonus: the `shared_peel_1op` crutch VC is false for `AWSet`

`SatisfiesVCs.shared_peel_1op` quantifies over **all** states. For
state-dependent removes it fails: with `a = (∅,∅)`, `b = ({2},∅)`,
`ol = add₁`, `o₁ = rem₀`, the left `rem` cannot see `b`'s live
timestamp 2, but the right-hand side's `rem` (applied after the
merge) kills it. Since `AWSet` is the two-op skeleton of the paper's
own OR-set, the current `SatisfiesVCs` bundle is unsatisfiable for
precisely the RDTs with non-trivial `rc` — the bundle is *stronger*
than the paper's 24 VCs, and `distinct_last_case`'s reliance on
`shared_peel_1op` needs to be re-examined. -/
theorem AWSet_shared_peel_1op_false :
    ¬ (∀ (o₁ ol : Op AWSet.AppOp), distinctOps o₁ ol →
        ∀ (a b : AWSet.State),
          AWSet.merge (AWSet.update (AWSet.update a ol) o₁)
              (AWSet.update b ol)
            = AWSet.update (AWSet.merge (AWSet.update a ol)
                (AWSet.update b ol)) o₁) := by
  intro h
  have h_inst := h (0, 0, AWOp.rem) (1, 0, AWOp.add)
    (by simp [distinctOps, Op.time]) (∅, ∅) ({2}, ∅)
  simp only [AWSet_update, AWSet_merge,
    awUpdate_add (show ((1 : Timestamp), (0 : Replica), AWOp.add).2.2 = AWOp.add from rfl),
    awUpdate_rem (show ((0 : Timestamp), (0 : Replica), AWOp.rem).2.2 = AWOp.rem from rfl),
    awMerge] at h_inst
  have h_dead := congrArg Prod.snd h_inst
  -- LHS dead misses timestamp 2; RHS dead contains it.
  have h2 := Set.ext_iff.mp h_dead 2
  simp at h2

end Sal.Emulation
