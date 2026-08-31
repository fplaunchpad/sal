import Sal.MRDTs.Metatheory.Join.Convergence_CounterModel

/-!
# Counter-model: `BinaryMergeLaws` + merge associativity + idempotence do NOT
# imply `BinaryPeelLaws`

The phantom-conflict merge `AWSetX`, whose merge is *not associative*,
establishes `∃ D, BinaryMergeLaws D ∧ ¬ BinaryPeelLaws D`. The natural conjecture
is that adding associativity (+ idempotence) to `BinaryMergeLaws` would force
the peel identities generically. This file refutes that conjecture:
there is a `D` whose merge is a **bona fide bounded join-semilattice**
(commutative, associative, idempotent, `init`-unital) satisfying every
field of `BinaryMergeLaws`, for which `peel_local` (and the Join Lemma itself)
fails on a two-event, visibly-reachable configuration.

## The model: `AWSetF` = `AWSet` × a last-op flag

State = `AWState × Bool`. The base component is exactly `AWSet`
(add-wins set skeleton: `add` inserts its timestamp, `rem` kills
everything currently added, merge is pairwise union, `rc rem add =
Fst`). The extra component is a Boolean **flag written by every
update**: `add` sets it `true`, `rem` sets it `false`; merge is `∨`;
`init` is `false`. `(Bool, ∨, false)` is a semilattice with unit, so
the full merge is ACI-1. Crucially the flag after any nonempty
history is just *the kind of the last op*. It has no memory.

## Why every `BinaryMergeLaws` field survives

The update-level fields (`rc_non_comm_directional`, `no_rc_chain`,
`cond_comm_lift`) compare states produced by update sequences **ending
in the same event**, so the flags agree trivially; the base components
are `AWSet`'s, proved in `Convergence_CounterModel.lean`. (The flag
does not disturb `commutes` either: it makes add/rem non-commuting
(they already were) and leaves add/add, rem/rem commuting.)

The merge-level fields constrain only *synchronized* or *commuting*
situations, where the flag is again invisible:

* `lem_0op`: both sides end in the same `ol`, flags
  `awFlag ol ∨ awFlag ol = awFlag ol`;
* `merge_peel_comm`: for `e = add` the joined flag is
  `true ∨ _ = true = awFlag e`; for `e = rem` the other side is a fold
  of *commuting* (hence all-`rem`) events from `init`, whose flag is
  `false`;
* `merge_comm/init` and the new `merge_assoc`, `merge_idem`: `∨` is
  ACI with unit `false`.

## Why the peel dies

`peel_local`'s two sides end **differently**: the left is a *merge*
(flag = join of flags), the right ends in `update e`. Take the
canonical two-replica scenario, replica 0 does `a = add` then
`e = rem` (`vis a e`); replica 1 merged replica 0's state in between,
so its set is `{a}`. With `ev₁ = {a, e}`, `ev₂ = {a}`, `e` is
`loOn(∪)`-maximal (its only potential rc-edge target `a` is
`vis`-before it) and both sides are backward-closed. Then

    merge σ(ev₁) σ(ev₂)              has flag  false ∨ true = true
    update (merge σ(ev₁∖e) σ(ev₂)) e has flag  awFlag rem   = false.

`peel_local` fails; so does the Join Lemma (`merge σ(ev₁) σ(ev₂)` is
not the canonical state of the union, the only `loOn`-respecting
enumeration `[a, e]` folds to flag `false`).

## The boundary, relocated

`AWSetF`'s update is **not inflationary** w.r.t. the merge order
(`rem` strictly *decreases* the flag: `s ⊔ update s rem ≠ update s
rem`, `AWSetF_update_not_inflationary`). Every genuine state-based
CRDT has inflationary updates, the other half of the
convergent-replication contract, alongside the ACI merge. The
sharpened question is therefore

> **does `BinaryMergeLaws D` + merge ACI + update-inflationarity
> (`∀ s e, merge s (update s e) = update s e`) imply `BinaryPeelLaws D`?**

This model shows the question is tight from below:
drop inflationarity and it is false, *even with the full semilattice
laws*. (The non-associative separator shows the same for associativity.)
-/

namespace Sal.MRDTs.Foundation

open Classical

/-! ### 0. The lattice VC bundle -/

/-- The lattice laws conjectured to close the gap between
`BinaryMergeLaws` and `BinaryPeelLaws` (`merge_comm` and `merge_init` are already
in `BinaryMergeLaws`; together these make `merge` a bounded join-semilattice).
This file refutes the conjecture: `AWSetF` below satisfies
`BinaryMergeLaws + BinaryLatticeLaws` and violates `BinaryPeelLaws`. -/
structure BinaryLatticeLaws (D : UpdateSig) [HistoricalBinaryMerge D] : Prop where
  merge_assoc :
    ∀ a b c : D.State, D.historicalMerge (D.historicalMerge a b) c = D.historicalMerge a (D.historicalMerge b c)
  merge_idem : ∀ s : D.State, D.historicalMerge s s = s

/-! ### 1. The model -/

/-- The flag an update writes: the kind of the op. -/
def awFlag (e : Op AWOp) : Bool :=
  match e.2.2 with
  | .add => true
  | .rem => false

theorem awFlag_add {e : Op AWOp} (h : e.2.2 = AWOp.add) :
    awFlag e = true := by
  unfold awFlag; rw [h]

theorem awFlag_rem {e : Op AWOp} (h : e.2.2 = AWOp.rem) :
    awFlag e = false := by
  unfold awFlag; rw [h]

/-- State: `AWSet`'s state × the last-op flag. -/
abbrev AWFState : Type := AWState × Bool

/-- Update: the base `AWSet` update, and the flag records the kind of
this (the most recent) op. -/
def awfUpdate (σ : AWFState) (e : Op AWOp) : AWFState :=
  (awUpdate σ.1 e, awFlag e)

/-- Merge: base union-merge, `∨` on the flag, a bounded
join-semilattice (ACI with unit `((∅,∅), false)`). -/
def awfMerge (σ τ : AWFState) : AWFState :=
  (awMerge σ.1 τ.1, σ.2 || τ.2)

/-- `AWSet` enriched with the last-op flag. Same ops, same `rc`, same
base semantics; the merge is a genuine lattice join. -/
noncomputable def AWSetF : UpdateSig where
  State := AWFState
  dec_state := Classical.decEq _
  init := ((∅, ∅), false)
  AppOp := AWOp
  dec_op := inferInstance
  update := awfUpdate

noncomputable instance AWSetFHistoricalBinaryMerge : HistoricalBinaryMerge AWSetF where
  binaryMerge := awfMerge

local instance : ReplayPolicy AWSetF where
  order := awRc

@[simp] theorem AWSetF_update : AWSetF.update = awfUpdate := rfl
@[simp] theorem AWSetF_merge : AWSetF.historicalMerge = awfMerge := rfl
@[simp] theorem AWSetF_rc : AWSetF.replayOrder = awRc := rfl
@[simp] theorem AWSetF_init :
    AWSetF.init = ((((∅ : Set Timestamp), (∅ : Set Timestamp))), false) := rfl

/-- Base-component projection of a fold: the flag never feeds back
into the `AWSet` component. -/
theorem awf_applySeq_fst (σ : AWSetF.State) (π : List (Op AWSetF.AppOp)) :
    (applySeq AWSetF σ π).1 = applySeq AWSet σ.1 π := by
  induction π generalizing σ with
  | nil => rfl
  | cons x π' ih => exact ih (AWSetF.update σ x)

/-- The flag of a fold of removes from `init` is `false`. -/
theorem awf_fold_rems_flag (π : List (Op AWSetF.AppOp))
    (h : ∀ x ∈ π, x.2.2 = AWOp.rem) :
    (applySeq AWSetF AWSetF.init π).2 = false := by
  induction π using List.reverseRecOn with
  | nil => rfl
  | append_singleton π' x _ =>
    rw [applySeq_append_single]
    exact awFlag_rem (h x (by simp))

/-! ### 2. Op algebra: `commutes` is unchanged from `AWSet` -/

theorem AWSetF_comm_add_add {e₁ e₂ : Op AWSetF.AppOp}
    (h₁ : e₁.2.2 = AWOp.add) (h₂ : e₂.2.2 = AWOp.add) :
    AWSetF.commutes e₁ e₂ := by
  intro s
  refine Prod.ext ?_ ?_
  · exact AWSet_comm_add_add h₁ h₂ s.1
  · show awFlag e₂ = awFlag e₁
    rw [awFlag_add h₁, awFlag_add h₂]

theorem AWSetF_comm_rem_rem {e₁ e₂ : Op AWSetF.AppOp}
    (h₁ : e₁.2.2 = AWOp.rem) (h₂ : e₂.2.2 = AWOp.rem) :
    AWSetF.commutes e₁ e₂ := by
  intro s
  refine Prod.ext ?_ ?_
  · exact AWSet_comm_rem_rem h₁ h₂ s.1
  · show awFlag e₂ = awFlag e₁
    rw [awFlag_rem h₁, awFlag_rem h₂]

/-- add/rem never commute, visible on the flag alone. -/
theorem AWSetF_not_comm_add_rem {e₁ e₂ : Op AWSetF.AppOp}
    (h₁ : e₁.2.2 = AWOp.add) (h₂ : e₂.2.2 = AWOp.rem) :
    ¬ AWSetF.commutes e₁ e₂ := by
  intro h
  have h0 : awFlag e₂ = awFlag e₁ := congrArg Prod.snd (h AWSetF.init)
  rw [awFlag_add h₁, awFlag_rem h₂] at h0
  exact Bool.noConfusion h0

theorem AWSetF_not_comm_rem_add {e₁ e₂ : Op AWSetF.AppOp}
    (h₁ : e₁.2.2 = AWOp.rem) (h₂ : e₂.2.2 = AWOp.add) :
    ¬ AWSetF.commutes e₁ e₂ :=
  fun h => AWSetF_not_comm_add_rem h₂ h₁ (fun s => (h s).symm)

/-! ### 3. `BinaryMergeLaws` holds for `AWSetF` -/

theorem AWSetF_rc_non_comm_directional :
    ∀ o₁ o₂ : Op AWSetF.AppOp,
      distinctOps o₁ o₂ →
      (¬ AWSetF.commutes o₁ o₂ ↔
       (AWSetF.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∨
        AWSetF.replayOrder o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _
  rcases h₁ : o₁.2.2 <;> rcases h₂ : o₂.2.2 <;>
    simp only [AWSetF_rc, awRc_eq, h₁, h₂]
  · constructor
    · intro h; exact absurd (AWSetF_comm_add_add h₁ h₂) h
    · rintro (h | h) <;>
        exact absurd h (by first | exact fun h' => nomatch h' | decide)
  · constructor
    · intro _; exact Or.inr (by trivial)
    · intro _; exact AWSetF_not_comm_add_rem h₁ h₂
  · constructor
    · intro _; exact Or.inl (by trivial)
    · intro _; exact AWSetF_not_comm_rem_add h₁ h₂
  · constructor
    · intro h; exact absurd (AWSetF_comm_rem_rem h₁ h₂) h
    · rintro (h | h) <;>
        exact absurd h (by first | exact fun h' => nomatch h' | decide)

theorem AWSetF_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op AWSetF.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (AWSetF.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∧
         AWSetF.replayOrder o₂ o₃ = RcRes.Fst_then_snd) := by
  rintro o₁ o₂ o₃ _ _ ⟨h₁₂, h₂₃⟩
  rcases ha : o₁.2.2 <;> rcases hb : o₂.2.2 <;> rcases hc : o₃.2.2 <;>
    simp only [AWSetF_rc, awRc_eq, ha, hb, hc] at h₁₂ h₂₃ <;>
    first
      | exact absurd h₁₂ (by decide)
      | exact absurd h₂₃ (by decide)

/-- `cond_comm_lift`: both sides end in the same `e''`, so the flags
agree definitionally; the base components are `AWSet`'s lemma. -/
theorem AWSetF_cond_comm_lift :
    ∀ (s : AWSetF.State) (e e' e'' : Op AWSetF.AppOp)
      (π : List (Op AWSetF.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      AWSetF.replayOrder e e' = RcRes.Fst_then_snd →
      ¬ AWSetF.commutes e' e'' →
      AWSetF.update (applySeq AWSetF (AWSetF.update (AWSetF.update s e') e) π) e''
        = AWSetF.update (applySeq AWSetF (AWSetF.update (AWSetF.update s e) e') π) e'' := by
  intro s e e' e'' π hd1 hd2 hd3 h_rc h_nc
  -- rc e e' = Fst forces e = rem, e' = add.
  rcases ha : e.2.2 <;> rcases hb : e'.2.2 <;>
    simp only [AWSetF_rc, awRc_eq, ha, hb] at h_rc <;>
    try exact absurd h_rc (by decide)
  -- e'' cannot be add (add/add commute), so e'' = rem.
  rcases hc : e''.2.2
  · exact absurd (AWSetF_comm_add_add hb hc) h_nc
  · refine Prod.ext ?_ ?_
    · have hbase := AWSet_cond_comm_lift s.1 e e' e'' π hd1 hd2 hd3
        (by simp only [AWSet_rc, awRc_eq, ha, hb])
        (AWSet_not_comm_add_rem hb hc)
      show awUpdate (applySeq AWSetF (AWSetF.update (AWSetF.update s e') e) π).1 e''
          = awUpdate (applySeq AWSetF (AWSetF.update (AWSetF.update s e) e') π).1 e''
      rw [awf_applySeq_fst, awf_applySeq_fst]
      exact hbase
    · rfl

theorem AWSetF_merge_comm :
    ∀ a b : AWSetF.State, AWSetF.historicalMerge a b = AWSetF.historicalMerge b a := by
  intro a b
  refine Prod.ext ?_ ?_
  · exact AWSet_merge_comm a.1 b.1
  · exact Bool.or_comm _ _

theorem AWSetF_merge_init :
    ∀ s : AWSetF.State, AWSetF.historicalMerge AWSetF.init s = s := by
  intro s
  refine Prod.ext ?_ ?_
  · exact AWSet_merge_init s.1
  · exact Bool.false_or _

theorem AWSetF_lem_0op :
    ∀ (a b : AWSetF.State) (ol : Op AWSetF.AppOp),
      AWSetF.historicalMerge (AWSetF.update a ol) (AWSetF.update b ol)
        = AWSetF.update (AWSetF.historicalMerge a b) ol := by
  intro a b ol
  refine Prod.ext ?_ ?_
  · exact AWSet_lem_0op a.1 b.1 ol
  · exact Bool.or_self _

/-- `merge_peel_comm`: an add commutes only with adds, its flag
absorbs the join; a rem commutes only with rems, whose fold from
`init` has flag `false`. -/
theorem AWSetF_merge_peel_comm :
    ∀ (a : AWSetF.State) (e : Op AWSetF.AppOp)
      (π : List (Op AWSetF.AppOp)),
      (∀ x ∈ π, AWSetF.commutes e x) →
      AWSetF.historicalMerge (AWSetF.update a e) (applySeq AWSetF AWSetF.init π)
        = AWSetF.update (AWSetF.historicalMerge a (applySeq AWSetF AWSetF.init π)) e := by
  intro a e π h_comm
  rcases he : e.2.2
  · -- e = add: everything in π is an add.
    have h_kinds : ∀ x ∈ π, x.2.2 = AWOp.add := by
      intro x hx
      rcases hx_op : x.2.2
      · rfl
      · exact absurd (h_comm x hx) (AWSetF_not_comm_add_rem he hx_op)
    have h_base : ∀ x ∈ π, AWSet.commutes e x :=
      fun x hx => AWSet_comm_add_add he (h_kinds x hx)
    refine Prod.ext ?_ ?_
    · show awMerge (awUpdate a.1 e) (applySeq AWSetF AWSetF.init π).1
          = awUpdate (awMerge a.1 (applySeq AWSetF AWSetF.init π).1) e
      rw [awf_applySeq_fst]
      exact AWSet_merge_peel_comm a.1 e π h_base
    · show (awFlag e || (applySeq AWSetF AWSetF.init π).2) = awFlag e
      rw [awFlag_add he]
      exact Bool.true_or _
  · -- e = rem: everything in π is a rem; the fold's flag is false.
    have h_kinds : ∀ x ∈ π, x.2.2 = AWOp.rem := by
      intro x hx
      rcases hx_op : x.2.2
      · exact absurd (h_comm x hx) (AWSetF_not_comm_rem_add he hx_op)
      · rfl
    have h_base : ∀ x ∈ π, AWSet.commutes e x :=
      fun x hx => AWSet_comm_rem_rem he (h_kinds x hx)
    refine Prod.ext ?_ ?_
    · show awMerge (awUpdate a.1 e) (applySeq AWSetF AWSetF.init π).1
          = awUpdate (awMerge a.1 (applySeq AWSetF AWSetF.init π).1) e
      rw [awf_applySeq_fst]
      exact AWSet_merge_peel_comm a.1 e π h_base
    · show (awFlag e || (applySeq AWSetF AWSetF.init π).2) = awFlag e
      rw [awFlag_rem he, awf_fold_rems_flag π h_kinds]
      rfl

/-- **`AWSetF` satisfies the full core bundle.** -/
theorem AWSetF_binaryMergeLaws : BinaryMergeLaws AWSetF :=
  ⟨AWSetF_rc_non_comm_directional, AWSetF_no_rc_chain,
   AWSetF_cond_comm_lift, AWSetF_merge_comm, AWSetF_merge_init,
   AWSetF_lem_0op, AWSetF_merge_peel_comm⟩

/-! ### 4. `AWSetF`'s merge is a bounded join-semilattice -/

theorem AWSetF_merge_assoc :
    ∀ a b c : AWSetF.State,
      AWSetF.historicalMerge (AWSetF.historicalMerge a b) c
        = AWSetF.historicalMerge a (AWSetF.historicalMerge b c) := by
  intro a b c
  refine Prod.ext ?_ ?_
  · exact Prod.ext (Set.union_assoc _ _ _) (Set.union_assoc _ _ _)
  · exact Bool.or_assoc _ _ _

theorem AWSetF_merge_idem : ∀ s : AWSetF.State, AWSetF.historicalMerge s s = s := by
  intro s
  refine Prod.ext ?_ ?_
  · exact Prod.ext (Set.union_self _) (Set.union_self _)
  · exact Bool.or_self _

/-- **`AWSetF` satisfies the lattice bundle.** -/
theorem AWSetF_binaryLatticeLaws : BinaryLatticeLaws AWSetF :=
  ⟨AWSetF_merge_assoc, AWSetF_merge_idem⟩

/-! ### 5. The two events and the configuration

Replica 0 executes `aF = add` (t = 0) then `eF = rem` (t = 1), so
`vis aF eF`. Replica 1 merged replica 0's state in between, so its
event set is `{aF}`. Reachable in 5 transition-system steps
(create r1; apply aF at r0; merge r1 ← r0; apply eF at r0; the final
merge below is the Merge step the Join Lemma is about). -/

/-- `aF = add` at replica 0, timestamp 0. -/
def aF : Op AWSetF.AppOp := (0, 0, AWOp.add)
/-- `eF = rem` at replica 0, timestamp 1 (`vis aF eF`). -/
def eF : Op AWSetF.AppOp := (1, 0, AWOp.rem)

/-- Every event of any replica set of the configuration is one of the
two literals. -/
private theorem flag_L_cases (r₀ : Replica)
    (s₀ : Set (Op AWSetF.AppOp))
    (hL₀ : (if r₀ = 0 then some {aF, eF}
            else if r₀ = 1 then some {aF} else none) = some s₀) :
    ∀ x ∈ s₀, x = aF ∨ x = eF := by
  intro x hx
  by_cases h0 : r₀ = 0
  · rw [if_pos h0, Option.some.injEq] at hL₀
    rw [← hL₀] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  · by_cases h1 : r₀ = 1
    · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL₀
      rw [← hL₀] at hx
      exact Or.inl hx
    · rw [if_neg h0, if_neg h1] at hL₀
      exact absurd hL₀ (by simp)

/-- The refuting configuration. Replica 0 holds `{aF, eF}`; replica 1
holds `{aF}`. The single `vis`-edge is `aF → eF`. -/
noncomputable def flagConfig : ReplayContext AWSetF where
  L := fun r =>
    if r = 0 then some {aF, eF}
    else if r = 1 then some {aF}
    else none
  vis := fun x y => x = aF ∧ y = eF
  timestamps_distinct := by
    intro x y r s r' s' hL hs hL' hs' hne
    rcases flag_L_cases r s hL x hs with rfl | rfl <;>
      rcases flag_L_cases r' s' hL' y hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [aF, eF]
  vis_total_same_replica := by
    intro x y r s r' s' hL hs hL' hs' hne _
    rcases flag_L_cases r s hL x hs with rfl | rfl <;>
      rcases flag_L_cases r' s' hL' y hs' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩

/-! ### 6. The instance data for the peel -/

/-- Replica 0's event set. -/
def evF₁ : Set (Op AWSetF.AppOp) := {aF, eF}
/-- Replica 1's event set. -/
def evF₂ : Set (Op AWSetF.AppOp) := {aF}

private theorem hF_in₁ : ∀ x ∈ evF₁, x ∈ flagConfig.events :=
  fun x hx => ⟨0, {aF, eF}, by simp [flagConfig], hx⟩

private theorem hF_in₂ : ∀ x ∈ evF₂, x ∈ flagConfig.events :=
  fun x hx => ⟨1, {aF}, by simp [flagConfig], hx⟩

private theorem hF_cl₁ :
    ∀ x y, flagConfig.vis x y → ¬ AWSetF.commutes x y →
      y ∈ evF₁ → x ∈ evF₁ := by
  rintro x y ⟨rfl, rfl⟩ _ _
  exact Or.inl rfl

private theorem hF_cl₂ :
    ∀ x y, flagConfig.vis x y → ¬ AWSetF.commutes x y →
      y ∈ evF₂ → x ∈ evF₂ := by
  rintro x y ⟨rfl, rfl⟩ _ hy
  exact absurd hy (by simp [evF₂, aF, eF])

/-- `eF` is `loOn(ev₁ ∪ ev₂)`-maximal: its only potential target is
`aF`, which is `vis`-before it (so neither `loOn` disjunct fires). -/
private theorem hF_max :
    ∀ x ∈ evF₁ ∪ evF₂, x ≠ eF →
      ¬ loOn flagConfig (evF₁ ∪ evF₂) eF x := by
  intro x hx hne
  rintro (⟨hv, _⟩ | ⟨_, hnv, _, _⟩)
  · obtain ⟨h1, _⟩ := hv
    exact absurd h1 (by simp [aF, eF])
  · have hxa : x = aF := by
      rcases hx with hx | hx
      · rcases hx with h | h
        · exact h
        · exact absurd h hne
      · exact hx
    subst hxa
    exact hnv ⟨rfl, rfl⟩

private theorem hF_vis_trans :
    ∀ {x y z : Op AWSetF.AppOp},
      flagConfig.vis x y → flagConfig.vis y z → flagConfig.vis x z := by
  rintro x y z ⟨rfl, rfl⟩ ⟨h1, _⟩
  exact absurd h1 (by simp [aF, eF])

private theorem hF_vis_irrefl :
    ∀ x : Op AWSetF.AppOp, ¬ flagConfig.vis x x := by
  rintro x ⟨rfl, h⟩
  exact absurd h (by simp [aF, eF])

/-- Canonical state of `ev₁ = {aF, eF}`: the fold of `[aF, eF]`. -/
noncomputable def sF₁ : AWSetF.State := applySeq AWSetF AWSetF.init [aF, eF]
/-- Canonical state of `ev₂ = {aF}` (also of `ev₁ ∖ {eF}`). -/
noncomputable def sF₂ : AWSetF.State := applySeq AWSetF AWSetF.init [aF]

private theorem hF_perm₁ : listPermOf [aF, eF] evF₁ := by
  constructor
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro b hb
    rw [List.mem_singleton] at hb; subst hb
    simp [aF, eF]
  · intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with h | h
      · exact Or.inl h
      · rw [List.mem_singleton] at h
        exact Or.inr h
    · rintro (h | h)
      · rw [h]; exact List.mem_cons_self
      · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- `[aF, eF]` respects `loOn C ev₁`: there is no `loOn`-edge
`eF → aF` (`vis aF eF` kills both disjuncts). -/
private theorem hF_resp₁ : respects [aF, eF] (loOn flagConfig evF₁) := by
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro b hb
  rw [List.mem_singleton] at hb; subst hb
  rintro (⟨hv, _⟩ | ⟨_, hnv, _, _⟩)
  · obtain ⟨h1, _⟩ := hv
    exact absurd h1 (by simp [aF, eF])
  · exact hnv ⟨rfl, rfl⟩

private theorem hF_can₁ : IsCanonicalState flagConfig evF₁ sF₁ :=
  ⟨[aF, eF], hF_perm₁, hF_resp₁, rfl⟩

private theorem hF_can₂ : IsCanonicalState flagConfig evF₂ sF₂ := by
  refine ⟨[aF], ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, rfl⟩
  constructor
  · intro hx
    rw [List.mem_singleton] at hx
    exact hx
  · intro hx
    rw [List.mem_singleton]
    exact hx

private theorem hF_can_t₁ :
    IsCanonicalState flagConfig (evF₁ \ {eF}) sF₂ := by
  refine ⟨[aF], ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, rfl⟩
  constructor
  · intro hx
    rw [List.mem_singleton] at hx; subst hx
    exact ⟨Or.inl rfl, fun h => absurd h (by simp [aF, eF])⟩
  · rintro ⟨hx, hne⟩
    rcases hx with h | h
    · rw [List.mem_singleton]; exact h
    · exact absurd h hne

/-! ### 7. The refutation -/

/-- **`peel_local` fails for `AWSetF`**: hence `BinaryPeelLaws` fails.
The left side is a merge (flag `false ∨ true = true`); the right side
ends in `update eF` (flag `false`). -/
theorem AWSetF_not_binaryPeelLaws : ¬ BinaryPeelLaws AWSetF := by
  intro hPeel
  have h := hPeel.peel_local flagConfig evF₁ evF₂ sF₁ sF₂ sF₂ eF
    hF_in₁ hF_in₂ hF_cl₁ hF_cl₂ (Or.inr rfl)
    (fun h => absurd h (by simp [evF₂, aF, eF]))
    hF_max hF_can₁ hF_can₂ hF_can_t₁
  have hsnd := congrArg Prod.snd h
  exact Bool.noConfusion (show (true : Bool) = false from hsnd)

/-- **The Join Lemma itself fails for `AWSetF`** on the same instance:
`merge σ(ev₁) σ(ev₂)` (flag `true`) is not the canonical state of the
union, the only `loOn`-respecting enumeration is `[aF, eF]`, whose
fold has flag `false`. So the failure is not an artifact of the
`BinaryPeelLaws` packaging. -/
theorem AWSetF_not_binaryJoin : ¬ BinaryJoin AWSetF := by
  intro hJoin
  have h := hJoin flagConfig evF₁ evF₂ sF₁ sF₂
    hF_vis_trans hF_vis_irrefl hF_in₁ hF_in₂ hF_cl₁ hF_cl₂
    hF_can₁ hF_can₂
  obtain ⟨ρ, hp, hr, hf⟩ := h
  -- ρ enumerates the two-element union, so it is [aF,eF] or [eF,aF].
  have hperm_pair : listPermOf [aF, eF] (evF₁ ∪ evF₂) := by
    constructor
    · exact hF_perm₁.1
    · intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with h' | h'
        · exact Or.inl (Or.inl h')
        · rw [List.mem_singleton] at h'
          exact Or.inl (Or.inr h')
      · rintro ((h' | h') | h')
        · rw [h']; exact List.mem_cons_self
        · rw [h']; exact List.mem_cons_of_mem _ List.mem_cons_self
        · rw [h']; exact List.mem_cons_self
  have hlen := listPermOf_length_eq hp hperm_pair
  obtain ⟨x, y, rfl⟩ : ∃ x y, ρ = [x, y] := by
    rcases ρ with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · exact absurd hlen (by simp)
    · exact absurd hlen (by simp)
    · exact ⟨x, y, rfl⟩
    · exact absurd hlen (by simp)
  have hcases : ∀ z, z ∈ evF₁ ∪ evF₂ → z = aF ∨ z = eF := by
    rintro z ((h' | h') | h')
    · exact Or.inl h'
    · exact Or.inr h'
    · exact Or.inl h'
  have hx_mem := (hp.2 x).mp List.mem_cons_self
  have hy_mem := (hp.2 y).mp (List.mem_cons_of_mem _ List.mem_cons_self)
  have hxy : x ≠ y := by
    intro hEq
    have hnd := hp.1
    rw [hEq, List.nodup_cons] at hnd
    exact hnd.1 List.mem_cons_self
  rcases hcases x hx_mem with rfl | rfl
  · rcases hcases y hy_mem with rfl | rfl
    · exact absurd rfl hxy
    · -- ρ = [aF, eF]: fold has flag false, but merge sF₁ sF₂ has true.
      have hsnd := congrArg Prod.snd hf
      exact Bool.noConfusion (show (false : Bool) = true from hsnd)
  · rcases hcases y hy_mem with rfl | rfl
    · -- ρ = [eF, aF]: violates the mandatory loOn-edge aF → eF.
      have hedge : loOn flagConfig (evF₁ ∪ evF₂) aF eF :=
        Or.inl ⟨⟨rfl, rfl⟩, AWSetF_not_comm_add_rem rfl rfl⟩
      exact (List.pairwise_cons.mp hr).1 aF List.mem_cons_self hedge
    · exact absurd rfl hxy

/-- **Where the lattice laws stop short**: `AWSetF`'s update is not
inflationary w.r.t. the merge order, `rem` strictly *decreases* the
flag. Every genuine state-based CRDT satisfies
`merge s (update s e) = update s e`; this is the axiom the lattice
bundle is missing, and this model shows it is not derivable from
`BinaryMergeLaws` + ACI. -/
theorem AWSetF_update_not_inflationary :
    ¬ ∀ (s : AWSetF.State) (e : Op AWSetF.AppOp),
        AWSetF.historicalMerge s (AWSetF.update s e) = AWSetF.update s e := by
  intro h
  have h0 := congrArg Prod.snd (h (AWSetF.update AWSetF.init aF) eF)
  exact Bool.noConfusion (show (true : Bool) = false from h0)

/-- `BinaryMergeLaws` together with a bounded-join-semilattice merge do not
imply `BinaryPeelLaws`. There is a replay algebra whose merge is a
bounded join-semilattice (commutative, associative, idempotent,
`init`-unital) satisfying every field of
`BinaryMergeLaws`, for which both the peel identities and the Join Lemma fail.
Associativity + idempotence do **not** close the gap between
`BinaryMergeLaws` and `BinaryPeelLaws`; the missing ingredient is
update-inflationarity (`AWSetF_update_not_inflationary`). -/
theorem binaryLaws_insufficient :
    BinaryMergeLaws AWSetF ∧ BinaryLatticeLaws AWSetF ∧
      ¬ BinaryPeelLaws AWSetF ∧ ¬ BinaryJoin AWSetF :=
  ⟨AWSetF_binaryMergeLaws, AWSetF_binaryLatticeLaws,
   AWSetF_not_binaryPeelLaws, AWSetF_not_binaryJoin⟩

end Sal.MRDTs.Foundation
