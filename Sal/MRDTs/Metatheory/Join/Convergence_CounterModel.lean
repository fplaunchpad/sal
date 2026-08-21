import Sal.MRDTs.Metatheory.Join.Merge_Linearization_Set

/-!
# Counter-model: convergence over backward-closed replica sets is FALSE

This file machine-checks that convergence over merely backward-closed
reachable replica event sets (w.r.t. the configuration-global `lo C`)
is **false**, even for a `D` that satisfies every property the
`convergence` proof machinery consumes (`rc_non_comm` +
`rc_non_comm_directional` + `no_rc_chain` + `cond_comm_base` +
`cond_comm_lift` + `merge_comm/idem/init` + `lem_0op`).

## The model

`AWSet`, a two-op add-wins set skeleton over one implicit key:

* `State := (added, dead) : Set Timestamp × Set Timestamp`;
  the live set is `added \ dead`.
* `add` inserts its timestamp into `added`.
* `rem` kills everything currently added: `dead := added ∪ dead`
  (state-dependent: this is what makes `add`/`rem` non-commuting).
* `merge` is the pairwise union (a join-semilattice).
* `rc rem add = Fst_then_snd` (add wins over a concurrent remove),
  the paper's OR-set resolution.

## The configuration

* replica 0: `e = add` (t=0) then `e₃ = rem` (t=1), so `vis e e₃`;
* replica 1: `y = rem` (t=2), concurrent with both; its event set is
  `ev = {y, e}`, it merged replica 0's state *between* `e` and `e₃`.

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
`ev`), so only the fold-correct `[y, e]` respects it,
`loOn_keeps_the_edge` below.

## Bonus finding

`SatisfiesVCs.shared_peel_1op`, the "missing VC" added to the
bundle as a crutch for the shared-event peel, is **false for
`AWSet`** (`AWSet_shared_peel_1op_false`): the current bundle
excludes exactly the state-dependent RDTs (the paper's own OR-set
among them) whose non-trivial `rc` the metatheorem is about.
-/

namespace Sal.MRDTs.Foundation

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

/-- Pairwise union, a join-semilattice. -/
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
/-- `e₃ = rem` at replica 0, timestamp 1, the absorber
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

/-- `counterEv` is backward-closed under `vis`, unconditionally, not
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
w.r.t. `lo C`" is false, and no weakening of `convergence`'s
overwriter-closure hypothesis to backward closure can be proved. -/
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
NOT respect `loOn C counterEv`, exactly the discrimination
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
precisely the RDTs with non-trivial `rc`, the bundle is *stronger*
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

/-! ### Discharging `JoinPeelVCs` for `AWSet`

`AWSet` cannot satisfy the full `SatisfiesVCs`
(`AWSet_shared_peel_1op_false`), but it satisfies the `CoreVCs`
fragment the Join-Lemma machinery consumes, and (the point of this
section) the two contextual peel identities. The engine is a
**characterization of canonical states**:

    σ(ev) = (awAdds ev, awKilled C ev)

added = timestamps of `ev`'s add events; dead = timestamps of `ev`'s
add events that are `vis`-before some rem event *inside `ev`*. The
proof threads a sandwich invariant along any `loOn C ev`-respecting
enumeration: adds absorbed within the processed prefix are already
dead (the vis-edge to the absorber is mandatory), and everything
dead is absorbed within `ev` (a rem cannot precede an unabsorbed
concurrent add, the rc-edge `rem → add` would be mandatory).

The peel identities then reduce to set algebra plus the
trichotomy (`awAdds_killed_of_rem_max`): under union-maximality of a
rem `e` and backward closure, *every* add of `ev₁ ∪ ev₂` is absorbed
on the side that owns it. This yields `AWSet_joinLemma`, the Join
Lemma, hence the full merge case, for a CRDT with non-trivial `rc`,
on exactly the class of instances where the paper's own proof
breaks. -/

/-- All-rem lists leave `added` empty. -/
private theorem AWSet_fold_rems_added {π : List (Op AWSet.AppOp)}
    (h : ∀ x ∈ π, x.2.2 = AWOp.rem) :
    (applySeq AWSet AWSet.init π).1 = ∅ := by
  induction π using List.reverseRecOn with
  | nil => rfl
  | append_singleton π' x ih =>
    rw [applySeq_append_single]
    have hx := h x (by simp)
    rw [AWSet_update, awUpdate_rem hx]
    exact ih (fun y hy => h y (by simp [hy]))

/-- `merge_peel_comm` for `AWSet`: an add peels unconditionally; a
rem commutes only with rems, whose fold adds nothing. -/
theorem AWSet_merge_peel_comm :
    ∀ (a : AWSet.State) (e : Op AWSet.AppOp)
      (π : List (Op AWSet.AppOp)),
      (∀ x ∈ π, AWSet.commutes e x) →
      AWSet.merge (AWSet.update a e) (applySeq AWSet AWSet.init π)
        = AWSet.update (AWSet.merge a (applySeq AWSet AWSet.init π)) e := by
  intro a e π h_comm
  rcases he : e.2.2
  · simp only [AWSet_update, AWSet_merge, awUpdate_add he, awMerge]
    refine Prod.ext ?_ rfl
    ext u
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto
  · have h_all_rem : ∀ x ∈ π, x.2.2 = AWOp.rem := by
      intro x hx
      rcases hx_op : x.2.2
      · exact absurd (h_comm x hx) (AWSet_not_comm_rem_add he hx_op)
      · rfl
    have hB : (applySeq AWSet AWSet.init π).1 = ∅ :=
      AWSet_fold_rems_added h_all_rem
    simp only [AWSet_update, AWSet_merge, awUpdate_rem he, awMerge]
    refine Prod.ext rfl ?_
    rw [hB]
    ext u
    simp only [Set.mem_union, Set.mem_empty_iff_false]
    tauto

/-- `AWSet` satisfies the core bundle (though not the full one). -/
theorem AWSet_coreVCs : CoreVCs AWSet :=
  ⟨AWSet_rc_non_comm_directional, AWSet_no_rc_chain,
   AWSet_cond_comm_lift, AWSet_merge_comm, AWSet_merge_init,
   AWSet_lem_0op, AWSet_merge_peel_comm⟩

/-- Timestamps of the add events of `ev`. -/
def awAdds (ev : Set (Op AWSet.AppOp)) : Set Timestamp :=
  {t | ∃ a, a ∈ ev ∧ a.2.2 = AWOp.add ∧ a.1 = t}

/-- Timestamps of `ev`'s add events absorbed inside `ev` (some rem of
`ev` observed them). -/
def awKilled (C : Configuration AWSet) (ev : Set (Op AWSet.AppOp)) :
    Set Timestamp :=
  {t | ∃ a, a ∈ ev ∧ a.2.2 = AWOp.add ∧ a.1 = t ∧
       ∃ z, z ∈ ev ∧ C.vis a z ∧ z.2.2 = AWOp.rem}

/-- The sandwich invariant along a `loOn C ev`-respecting list. -/
private theorem AWSet_char_aux {C : Configuration AWSet}
    {ev : Set (Op AWSet.AppOp)} :
    ∀ ρ : List (Op AWSet.AppOp),
      (∀ a ∈ ρ, a ∈ ev) →
      respects ρ (loOn C ev) →
      ((applySeq AWSet AWSet.init ρ).1
          = {t | ∃ a, a ∈ ρ ∧ a.2.2 = AWOp.add ∧ a.1 = t}) ∧
      (∀ a z : Op AWSet.AppOp, a ∈ ρ → z ∈ ρ →
          a.2.2 = AWOp.add → C.vis a z → z.2.2 = AWOp.rem →
          a.1 ∈ (applySeq AWSet AWSet.init ρ).2) ∧
      (∀ t, t ∈ (applySeq AWSet AWSet.init ρ).2 →
          ∃ a, a ∈ ρ ∧ a.2.2 = AWOp.add ∧ a.1 = t ∧
            ∃ z, z ∈ ev ∧ C.vis a z ∧ z.2.2 = AWOp.rem) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · ext t
      simp [applySeq]
    · intro a _ ha _ _ _ _
      exact absurd ha List.not_mem_nil
    · intro t ht
      simp [applySeq] at ht
  | append_singleton ρ' x ih =>
    intro h_sub h_resp
    have h_split := List.pairwise_append.mp h_resp
    have h_resp' : respects ρ' (loOn C ev) := h_split.1
    have h_cross : ∀ a ∈ ρ', ¬ loOn C ev x a := fun a ha =>
      h_split.2.2 a ha x (by simp)
    have h_sub' : ∀ a ∈ ρ', a ∈ ev := fun a ha =>
      h_sub a (List.mem_append.mpr (Or.inl ha))
    have hx_ev : x ∈ ev := h_sub x (by simp)
    obtain ⟨ih_add, ih_low, ih_up⟩ := ih h_sub' h_resp'
    rw [applySeq_append_single]
    rcases hx_op : x.2.2
    · -- x = add: dead unchanged, added gains x.1.
      rw [AWSet_update, awUpdate_add hx_op]
      refine ⟨?_, ?_, ?_⟩
      · ext t
        simp only [Set.mem_insert_iff, ih_add, Set.mem_setOf_eq,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro (rfl | ⟨a, ha, hadd, ht⟩)
          · exact ⟨x, Or.inr rfl, hx_op, rfl⟩
          · exact ⟨a, Or.inl ha, hadd, ht⟩
        · rintro ⟨a, ha | rfl, hadd, ht⟩
          · exact Or.inr ⟨a, ha, hadd, ht⟩
          · exact Or.inl ht.symm
      · intro a z ha hz hadd hvis hrem
        rcases List.mem_append.mp hz with hz' | hz'
        · rcases List.mem_append.mp ha with ha' | ha'
          · exact ih_low a z ha' hz' hadd hvis hrem
          · -- a = x with vis x z into the prefix: the mandatory edge
            -- x → z contradicts x being last.
            rw [List.mem_singleton] at ha'; subst ha'
            exact absurd (Or.inl ⟨hvis,
              AWSet_not_comm_add_rem hadd hrem⟩) (h_cross z hz')
        · rw [List.mem_singleton] at hz'; subst hz'
          rw [hx_op] at hrem
          exact absurd hrem (fun h' => nomatch h')
      · intro t ht
        obtain ⟨a, ha, hadd, ht', hz⟩ := ih_up t ht
        exact ⟨a, List.mem_append.mpr (Or.inl ha), hadd, ht', hz⟩
    · -- x = rem: dead absorbs the whole current added set.
      rw [AWSet_update, awUpdate_rem hx_op]
      refine ⟨?_, ?_, ?_⟩
      · ext t
        simp only [ih_add, Set.mem_setOf_eq, List.mem_append,
          List.mem_singleton]
        constructor
        · rintro ⟨a, ha, hadd, ht⟩
          exact ⟨a, Or.inl ha, hadd, ht⟩
        · rintro ⟨a, ha | rfl, hadd, ht⟩
          · exact ⟨a, ha, hadd, ht⟩
          · rw [hx_op] at hadd
            exact absurd hadd (fun h' => nomatch h')
      · intro a z ha hz hadd hvis hrem
        have ha' : a ∈ ρ' := by
          rcases List.mem_append.mp ha with h | h
          · exact h
          · rw [List.mem_singleton] at h; subst h
            rw [hx_op] at hadd
            exact absurd hadd (fun h' => nomatch h')
        rcases List.mem_append.mp hz with hz' | hz'
        · exact Or.inr (ih_low a z ha' hz' hadd hvis hrem)
        · -- z = x: the victim sits in the prefix's added set.
          left
          rw [ih_add]
          exact ⟨a, ha', hadd, rfl⟩
      · intro t ht
        rcases ht with ht | ht
        · -- t was alive in the prefix: the trichotomy argument produces
          -- an absorber of its add inside ev.
          rw [ih_add] at ht
          obtain ⟨a, ha, hadd, ht'⟩ := ht
          have h_nc : ¬ AWSet.commutes x a :=
            AWSet_not_comm_rem_add hx_op hadd
          have h_noedge := h_cross a ha
          have h1 : ¬ C.vis x a := fun hv =>
            h_noedge (Or.inl ⟨hv, h_nc⟩)
          have h_rc : AWSet.rc x a = RcRes.Fst_then_snd := by
            simp only [AWSet_rc, awRc_eq, hx_op, hadd]
          by_cases h2 : C.vis a x
          · exact ⟨a, List.mem_append.mpr (Or.inl ha), hadd, ht',
              x, hx_ev, h2, hx_op⟩
          · have h_abs : ∃ z ∈ ev,
                C.vis a z ∧ ¬ AWSet.commutes a z := by
              by_contra h_no
              exact h_noedge (Or.inr ⟨h1, h2, h_rc, h_no⟩)
            obtain ⟨z, hz_ev, hz_vis, hz_nc⟩ := h_abs
            rcases hz_op : z.2.2
            · exact absurd (AWSet_comm_add_add hadd hz_op) hz_nc
            · exact ⟨a, List.mem_append.mpr (Or.inl ha), hadd, ht',
                z, hz_ev, hz_vis, hz_op⟩
        · obtain ⟨a, ha, hadd, ht', hz⟩ := ih_up t ht
          exact ⟨a, List.mem_append.mpr (Or.inl ha), hadd, ht', hz⟩

/-- **Canonical states of `AWSet`, characterized.** -/
theorem AWSet_canonical_eq {C : Configuration AWSet}
    {ev : Set (Op AWSet.AppOp)} {s : AWSet.State}
    (h : IsCanonicalState C ev s) :
    s = (awAdds ev, awKilled C ev) := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  obtain ⟨h_add, h_low, h_up⟩ :=
    AWSet_char_aux ρ (fun a ha => (hp.2 a).mp ha) hr
  subst hf
  refine Prod.ext ?_ ?_
  · rw [h_add]
    ext t
    simp only [Set.mem_setOf_eq, awAdds]
    constructor
    · rintro ⟨a, ha, hadd, ht⟩
      exact ⟨a, (hp.2 a).mp ha, hadd, ht⟩
    · rintro ⟨a, ha, hadd, ht⟩
      exact ⟨a, (hp.2 a).mpr ha, hadd, ht⟩
  · ext t
    simp only [awKilled, Set.mem_setOf_eq]
    constructor
    · intro ht
      obtain ⟨a, ha, hadd, ht', z, hz_ev, hvis, hrem⟩ := h_up t ht
      exact ⟨a, (hp.2 a).mp ha, hadd, ht', z, hz_ev, hvis, hrem⟩
    · rintro ⟨a, ha, hadd, ht', z, hz_ev, hvis, hrem⟩
      subst ht'
      exact h_low a z ((hp.2 a).mpr ha) ((hp.2 z).mpr hz_ev)
        hadd hvis hrem

/-! #### Set algebra for `awAdds` / `awKilled` -/

theorem awAdds_diff_rem {ev : Set (Op AWSet.AppOp)}
    {e : Op AWSet.AppOp} (he : e.2.2 = AWOp.rem) :
    awAdds (ev \ {e}) = awAdds ev := by
  ext t
  simp only [awAdds, Set.mem_setOf_eq, Set.mem_diff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨ha, _⟩, hadd, ht⟩
    exact ⟨a, ha, hadd, ht⟩
  · rintro ⟨a, ha, hadd, ht⟩
    refine ⟨a, ⟨ha, ?_⟩, hadd, ht⟩
    rintro rfl
    rw [he] at hadd
    exact absurd hadd (fun h' => nomatch h')

theorem awAdds_insert_add {ev : Set (Op AWSet.AppOp)}
    {e : Op AWSet.AppOp} (he : e.2.2 = AWOp.add) (he_in : e ∈ ev) :
    awAdds ev = insert e.1 (awAdds (ev \ {e})) := by
  ext t
  simp only [awAdds, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, hadd, ht⟩
    by_cases hae : a = e
    · subst hae
      exact Or.inl ht.symm
    · exact Or.inr ⟨a, ⟨ha, hae⟩, hadd, ht⟩
  · rintro (rfl | ⟨a, ⟨ha, _⟩, hadd, ht⟩)
    · exact ⟨e, he_in, he, rfl⟩
    · exact ⟨a, ha, hadd, ht⟩

theorem awKilled_mono {C : Configuration AWSet}
    {ev ev' : Set (Op AWSet.AppOp)} (h : ev ⊆ ev') :
    awKilled C ev ⊆ awKilled C ev' := by
  rintro t ⟨a, ha, hadd, ht, z, hz, hvis, hrem⟩
  exact ⟨a, h ha, hadd, ht, z, h hz, hvis, hrem⟩

theorem awKilled_sub_adds {C : Configuration AWSet}
    {ev : Set (Op AWSet.AppOp)} :
    awKilled C ev ⊆ awAdds ev := by
  rintro t ⟨a, ha, hadd, ht, _⟩
  exact ⟨a, ha, hadd, ht⟩

/-- A union-maximal add has no absorber anywhere in the union. -/
theorem no_absorber_of_max {C : Configuration AWSet}
    {evU ev : Set (Op AWSet.AppOp)} {e : Op AWSet.AppOp}
    (h_sub : ev ⊆ evU) (he_add : e.2.2 = AWOp.add)
    (h_max : ∀ x ∈ evU, x ≠ e → ¬ loOn C evU e x) :
    ¬ ∃ z, z ∈ ev ∧ C.vis e z ∧ z.2.2 = AWOp.rem := by
  rintro ⟨z, hz, hvis, hrem⟩
  have hz_ne : z ≠ e := by
    rintro rfl
    rw [he_add] at hrem
    exact absurd hrem (fun h' => nomatch h')
  exact h_max z (h_sub hz) hz_ne
    (Or.inl ⟨hvis, AWSet_not_comm_add_rem he_add hrem⟩)

/-- Removing an unabsorbed add leaves `awKilled` unchanged. -/
theorem awKilled_diff_add {C : Configuration AWSet}
    {ev : Set (Op AWSet.AppOp)} {e : Op AWSet.AppOp}
    (he : e.2.2 = AWOp.add)
    (h_no_abs : ¬ ∃ z, z ∈ ev ∧ C.vis e z ∧ z.2.2 = AWOp.rem) :
    awKilled C (ev \ {e}) = awKilled C ev := by
  apply Set.Subset.antisymm (awKilled_mono (fun a ha => ha.1))
  rintro t ⟨a, ha, hadd, ht, z, hz, hvis, hrem⟩
  have ha_ne : a ≠ e := by
    rintro rfl
    exact h_no_abs ⟨z, hz, hvis, hrem⟩
  have hz_ne : z ≠ e := by
    rintro rfl
    rw [he] at hrem
    exact absurd hrem (fun h' => nomatch h')
  exact ⟨a, ⟨ha, ha_ne⟩, hadd, ht, z, ⟨hz, hz_ne⟩, hvis, hrem⟩

/-- **The trichotomy**: with a union-maximal rem `e ∈ ev₁` and
backward-closed sides, every add of the union is absorbed on a side
that owns it. -/
theorem awAdds_killed_of_rem_max {C : Configuration AWSet}
    {ev₁ ev₂ : Set (Op AWSet.AppOp)} {e : Op AWSet.AppOp}
    (h_cl₁ : ∀ a b, C.vis a b → ¬ AWSet.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (h_cl₂ : ∀ a b, C.vis a b → ¬ AWSet.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    (he_rem : e.2.2 = AWOp.rem) (he₁ : e ∈ ev₁)
    (h_max : ∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) :
    awAdds ev₁ ∪ awAdds ev₂ ⊆ awKilled C ev₁ ∪ awKilled C ev₂ := by
  intro t ht
  have h_wit : ∃ a, a ∈ ev₁ ∪ ev₂ ∧ a.2.2 = AWOp.add ∧ a.1 = t := by
    rcases ht with ⟨a, ha, hadd, ht'⟩ | ⟨a, ha, hadd, ht'⟩
    · exact ⟨a, Or.inl ha, hadd, ht'⟩
    · exact ⟨a, Or.inr ha, hadd, ht'⟩
  obtain ⟨a, ha_U, hadd, ht'⟩ := h_wit
  have ha_ne : a ≠ e := by
    rintro rfl
    rw [he_rem] at hadd
    exact absurd hadd (fun h' => nomatch h')
  have h_nc : ¬ AWSet.commutes e a :=
    AWSet_not_comm_rem_add he_rem hadd
  have h_noedge := h_max a ha_U ha_ne
  have h1 : ¬ C.vis e a := fun hv => h_noedge (Or.inl ⟨hv, h_nc⟩)
  have h_rc : AWSet.rc e a = RcRes.Fst_then_snd := by
    simp only [AWSet_rc, awRc_eq, he_rem, hadd]
  by_cases h2 : C.vis a e
  · have ha₁ : a ∈ ev₁ :=
      h_cl₁ a e h2 (fun hc => h_nc (commutes_symm hc)) he₁
    exact Or.inl ⟨a, ha₁, hadd, ht', e, he₁, h2, he_rem⟩
  · have h_abs : ∃ z ∈ ev₁ ∪ ev₂,
        C.vis a z ∧ ¬ AWSet.commutes a z := by
      by_contra h_no
      exact h_noedge (Or.inr ⟨h1, h2, h_rc, h_no⟩)
    obtain ⟨z, hz_U, hz_vis, hz_nc⟩ := h_abs
    have hz_rem : z.2.2 = AWOp.rem := by
      rcases hz_op : z.2.2
      · exact absurd (AWSet_comm_add_add hadd hz_op) hz_nc
      · rfl
    rcases hz_U with hz₁ | hz₂
    · exact Or.inl ⟨a, h_cl₁ a z hz_vis hz_nc hz₁, hadd, ht',
        z, hz₁, hz_vis, hz_rem⟩
    · exact Or.inr ⟨a, h_cl₂ a z hz_vis hz_nc hz₂, hadd, ht',
        z, hz₂, hz_vis, hz_rem⟩

/-- **`AWSet` discharges the peel identities.** -/
theorem AWSet_joinPeelVCs : JoinPeelVCs AWSet := by
  constructor
  · -- peel_local
    intro C ev₁ ev₂ s₁ s₂ t₁ e h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₁ hc₂ hct₁
    have hs₁ := AWSet_canonical_eq hc₁
    have hs₂ := AWSet_canonical_eq hc₂
    have hu₁ := AWSet_canonical_eq hct₁
    subst hs₁; subst hs₂; subst hu₁
    rcases he_op : e.2.2
    · have h_no_abs₁ :=
        no_absorber_of_max Set.subset_union_left he_op h_max
      simp only [AWSet_merge, AWSet_update, awMerge, awUpdate_add he_op]
      refine Prod.ext ?_ ?_
      · rw [awAdds_insert_add he_op he₁, Set.insert_union]
      · rw [awKilled_diff_add he_op h_no_abs₁]
    · simp only [AWSet_merge, AWSet_update, awMerge, awUpdate_rem he_op]
      refine Prod.ext ?_ ?_
      · rw [awAdds_diff_rem he_op]
      · rw [awAdds_diff_rem he_op]
        apply Set.Subset.antisymm
        · rintro t (h | h)
          · exact Or.inl (Or.inl (awKilled_sub_adds h))
          · exact Or.inl (Or.inr (awKilled_sub_adds h))
        · rintro t ((h | h) | (h | h))
          · exact awAdds_killed_of_rem_max h_cl₁ h_cl₂ he_op he₁
              h_max (Or.inl h)
          · exact awAdds_killed_of_rem_max h_cl₁ h_cl₂ he_op he₁
              h_max (Or.inr h)
          · exact Or.inl (awKilled_mono (fun a ha => ha.1) h)
          · exact Or.inr h
  · -- peel_shared
    intro C ev₁ ev₂ s₁ s₂ t₁ t₂ e h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂
      h_max hc₁ hc₂ hct₁ hct₂
    have hs₁ := AWSet_canonical_eq hc₁
    have hs₂ := AWSet_canonical_eq hc₂
    have hu₁ := AWSet_canonical_eq hct₁
    have hu₂ := AWSet_canonical_eq hct₂
    subst hs₁; subst hs₂; subst hu₁; subst hu₂
    rcases he_op : e.2.2
    · have h_no_abs₁ :=
        no_absorber_of_max Set.subset_union_left he_op h_max
      have h_no_abs₂ :=
        no_absorber_of_max Set.subset_union_right he_op h_max
      simp only [AWSet_merge, AWSet_update, awMerge, awUpdate_add he_op]
      refine Prod.ext ?_ ?_
      · rw [awAdds_insert_add he_op he₁]
        rw [awAdds_insert_add (ev := ev₂) he_op he₂]
        ext u
        simp only [Set.mem_union, Set.mem_insert_iff]
        tauto
      · rw [awKilled_diff_add he_op h_no_abs₁,
          awKilled_diff_add he_op h_no_abs₂]
    · simp only [AWSet_merge, AWSet_update, awMerge, awUpdate_rem he_op]
      refine Prod.ext ?_ ?_
      · rw [awAdds_diff_rem he_op, awAdds_diff_rem he_op]
      · rw [awAdds_diff_rem he_op, awAdds_diff_rem he_op]
        apply Set.Subset.antisymm
        · rintro t (h | h)
          · exact Or.inl (Or.inl (awKilled_sub_adds h))
          · exact Or.inl (Or.inr (awKilled_sub_adds h))
        · rintro t ((h | h) | (h | h))
          · exact awAdds_killed_of_rem_max h_cl₁ h_cl₂ he_op he₁
              h_max (Or.inl h)
          · exact awAdds_killed_of_rem_max h_cl₁ h_cl₂ he_op he₁
              h_max (Or.inr h)
          · exact Or.inl (awKilled_mono (fun a ha => ha.1) h)
          · exact Or.inr (awKilled_mono (fun a ha => ha.1) h)

/-- **The Join Lemma holds for `AWSet`**, a CRDT with non-trivial
`rc`, state-dependent updates, and instances (the defeater shape)
on which the paper's own bottom-up proof breaks. -/
theorem AWSet_joinLemma : JoinLemma AWSet :=
  join_lemma_of_peel AWSet_coreVCs AWSet_joinPeelVCs

end Sal.MRDTs.Foundation
