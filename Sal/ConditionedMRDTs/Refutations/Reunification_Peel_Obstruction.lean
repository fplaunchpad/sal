import Sal.CRDTs.Metatheory.Merge_Linearization_Set
import Mathlib.Data.Fintype.Prod

/-!
# Gate G1 kill-test: the full-closure peel does NOT exist

Machine-checks the **Gate G1 refutation** of
`Development/CONDITIONED_METATHEORY_PLAN.md`: the naive OQ3 reunification
route — re-running the `JoinLemma3` induction with the *full-closure*
hypotheses of `JoinLemma3F` (`Sal/MRDTs/Metatheory/VC_Set.lean:191`, the
closure `GoodConfig3.ver_causal` supplies) — needs to peel an event `e`
from a fully causally closed union `U` such that

1. `e` is `loOn C U`-maximal (it may be placed last in the witness), AND
2. `e` is **vis-maximal** in `U` (so `U ∖ {e}` stays *fully* closed: full
   closure is about all vis-predecessors, so the peeled event must have no
   vis-successor at all — commuting or not; `loOn`-maximality only excludes
   the non-commuting ones).

This file exhibits a concrete configuration and a fully closed 4-event `U`
in which **no such event exists** (`no_peelable_event`): the
`loOn(U)`-maximal events are exactly the two adds (`Ax_loOn_maximal`,
`Ay_loOn_maximal`), the vis-maximal events are exactly the two removes
(`Rx_vis_maximal`, `Ry_vis_maximal`), and the union graph closes into the
cycle

    A_y →vis R_x →rc A_x →vis R_y →rc A_y        (`the_cycle`)

## The construction (2-key add-wins skeleton)

Keys `x, y`; ops `addX/remX/addY/remY`. Same-key `rem/add` do **not**
commute; cross-key ops commute; `rc remX addX = rc remY addY =
Fst_then_snd` (add wins over a concurrent same-key remove), everything
else `Either`. The state is the minimal one exhibiting this commutation
structure: a last-writer flag per key (`Bool × Bool`); the add-wins
conflict resolution lives entirely in `rc`, which is all the peel
obligation reads.

Replica `p = 0` runs `A_y` (t=0) then `R_x` (t=1) — program order gives
`vis A_y R_x`. Replica `q = 1` runs `A_x` (t=2) then `R_y` (t=3) — `vis
A_x R_y`. No communication. `U = {A_y, R_x, A_x, R_y}` is fully causally
closed (`U_fully_closed`). The rc-edge `R_x →loOn(U) A_x` survives because
`A_x`'s only vis-successor `R_y` *commutes* with it (cross-key), so the
absorber clause of `loOn` cannot cancel it (`rc_edge_survives_x`);
symmetrically `R_y →loOn(U) A_y` (`rc_edge_survives_y`).

## Scope notes

* The kill-test is at the **configuration level** — a concrete
  `Configuration` with transitive, irreflexive `vis`
  (`peelConfig_vis_trans`, `peelConfig_vis_irrefl`) and a fully closed
  `U ⊆ C.events` — exactly the shape the generic full-closure induction
  would have to quantify over. Reachability in the Step transition system
  is NOT required and not proved: `peelConfig` is the evident 6-step
  execution (two creates, four applies), and `U` is the event set the
  final merge's version would hold.
* The **weak-closure route is untouched**: both vis-edges are cross-key,
  hence commuting, so *every* subset of events is `vis ∧ ¬commutes`-closed
  (`weak_closure_trivial`) and a `loOn(U)`-maximal peel event exists
  (`weak_peel_exists` — e.g. `A_x`). This configuration is handled by
  today's `JoinLemma3`; the obstruction is only against the
  *strengthened* closure, i.e. against the naive reunification of the
  weak-closure route with the `JoinLemma3F` (EWFlag) route.
* `K2` genuinely inhabits the order-theoretic class the `loOn` machinery
  operates on: `rc_non_comm_directional` and `no_rc_chain` hold
  (`K2_rc_non_comm_directional`, `K2_no_rc_chain`), so the obstruction is
  not an artifact of a pathological signature. Merge-layer VCs are
  irrelevant here — the peel obligation mentions only `vis`, `rc`, and
  `commutes`.

Consequence (plan doc): reunification must change the *induction* (block
peel / wider induction class / disjunctive contract), not merely the
closure hypotheses.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-! ## §1. The 2-key add-wins skeleton `K2` -/

/-- The four abstract ops: add/remove per key. -/
inductive K2Op : Type where
  | addX
  | remX
  | addY
  | remY
  deriving DecidableEq, Repr

/-- The state: a last-writer live-flag per key `(x-flag, y-flag)` — the
minimal state making same-key `add/rem` non-commuting and cross-key ops
commuting. -/
abbrev K2State : Type := Bool × Bool

/-- Effect of an abstract op on the state (depends only on the op
component, which keeps everything `decide`-able). -/
def k2Eff : K2Op → K2State → K2State
  | .addX, σ => (true, σ.2)
  | .remX, σ => (false, σ.2)
  | .addY, σ => (σ.1, true)
  | .remY, σ => (σ.1, false)

/-- `update` dispatches on the op component of the event. -/
def k2Update (σ : K2State) (e : Op K2Op) : K2State := k2Eff e.2.2 σ

/-- `rc` on op components: add wins over a concurrent same-key remove;
everything else is order-irrelevant. -/
def k2RcOp : K2Op → K2Op → RcRes
  | .remX, .addX => RcRes.Fst_then_snd
  | .addX, .remX => RcRes.Snd_then_fst
  | .remY, .addY => RcRes.Fst_then_snd
  | .addY, .remY => RcRes.Snd_then_fst
  | _, _ => RcRes.Either

def k2Rc (e₁ e₂ : Op K2Op) : RcRes := k2RcOp e₁.2.2 e₂.2.2

/-- The 2-key add-wins skeleton. `merge`/`query` are inert for this
kill-test (the peel obligation reads only `vis`/`rc`/`commutes`). -/
def K2 : CRDTSig where
  State := K2State
  dec_state := inferInstance
  init := (false, false)
  AppOp := K2Op
  dec_op := inferInstance
  Query := Unit
  Value := K2State
  update := k2Update
  merge := fun σ τ => (σ.1 || τ.1, σ.2 || τ.2)
  query := fun σ _ => σ
  rc := k2Rc

@[simp] theorem K2_update : K2.update = k2Update := rfl
@[simp] theorem K2_rc : K2.rc = k2Rc := rfl

/-! ## §2. Op algebra: commutation structure and the order-theoretic VCs -/

/-- Commutation of events reduces to commutation of op-component effects
(definitional — `update` ignores timestamp and replica). -/
theorem K2_commutes_iff_eff (e₁ e₂ : Op K2Op) :
    K2.commutes e₁ e₂ ↔
      ∀ σ : K2State,
        k2Eff e₂.2.2 (k2Eff e₁.2.2 σ) = k2Eff e₁.2.2 (k2Eff e₂.2.2 σ) :=
  Iff.rfl

/-! ### The four events

Distinct timestamps `0,1,2,3`; replicas `p = 0`, `q = 1`. -/

/-- `A_y`: add key `y` at replica `p = 0`, timestamp 0. -/
def eAy : Op K2.AppOp := (0, 0, K2Op.addY)
/-- `R_x`: remove key `x` at replica `p = 0`, timestamp 1
(program order: `vis eAy eRx`). -/
def eRx : Op K2.AppOp := (1, 0, K2Op.remX)
/-- `A_x`: add key `x` at replica `q = 1`, timestamp 2. -/
def eAx : Op K2.AppOp := (2, 1, K2Op.addX)
/-- `R_y`: remove key `y` at replica `q = 1`, timestamp 3
(program order: `vis eAx eRy`). -/
def eRy : Op K2.AppOp := (3, 1, K2Op.remY)

/-- Cross-key: `A_x` commutes with its only vis-successor `R_y`. This is
what defuses the absorber clause for the rc-edge `R_x → A_x`. -/
theorem K2_comm_Ax_Ry : K2.commutes eAx eRy := fun _ => rfl

/-- Cross-key: `A_y` commutes with its only vis-successor `R_x`. -/
theorem K2_comm_Ay_Rx : K2.commutes eAy eRx := fun _ => rfl

/-- Same-key `rem/add` genuinely do not commute (`R_x` vs `A_x`): the
rc-edge `R_x → A_x` is between a non-commuting pair. -/
theorem K2_not_comm_Rx_Ax : ¬ K2.commutes eRx eAx := by
  rw [K2_commutes_iff_eff]; decide

/-- Same-key `rem/add` genuinely do not commute (`R_y` vs `A_y`). -/
theorem K2_not_comm_Ry_Ay : ¬ K2.commutes eRy eAy := by
  rw [K2_commutes_iff_eff]; decide

/-- `rc_non_comm_directional` holds for `K2`: non-commutation coincides
with same-key `rem/add`, which is `rc`-ordered; every other pair commutes
and is `Either` both ways. `K2` therefore sits inside the class on which
the `loOn` acyclicity/maximality theory operates. -/
theorem K2_rc_non_comm_directional :
    ∀ o₁ o₂ : Op K2.AppOp,
      distinctOps o₁ o₂ →
      (¬ K2.commutes o₁ o₂ ↔
       (K2.rc o₁ o₂ = RcRes.Fst_then_snd ∨
        K2.rc o₂ o₁ = RcRes.Fst_then_snd)) := by
  intro o₁ o₂ _
  rcases h₁ : o₁.2.2 <;> rcases h₂ : o₂.2.2 <;>
    simp only [K2_commutes_iff_eff, K2_rc, k2Rc, h₁, h₂] <;> decide

/-- `no_rc_chain` holds for `K2`: an `rc = Fst_then_snd` edge always ends
at an add, and no `rc`-edge starts at an add. -/
theorem K2_no_rc_chain :
    ∀ o₁ o₂ o₃ : Op K2.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (K2.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         K2.rc o₂ o₃ = RcRes.Fst_then_snd) := by
  intro o₁ o₂ o₃ _ _
  rcases h₁ : o₁.2.2 <;> rcases h₂ : o₂.2.2 <;> rcases h₃ : o₃.2.2 <;>
    simp only [K2_rc, k2Rc, h₁, h₂, h₃] <;> decide

/-! ## §3. The configuration

Replica `p = 0` holds `{A_y, R_x}`, replica `q = 1` holds `{A_x, R_y}`;
the only vis-edges are the two program-order pairs. This is the evident
6-step execution (two creates, four applies); no communication happened,
so the two vis-pairs are disjoint. -/

/-- Every event of any replica set of the peel configuration is one of
the four literals. -/
private theorem peel_L_cases (r₀ : Replica) (s₀ : Set (Op K2.AppOp))
    (hL₀ : (if r₀ = 0 then some {eAy, eRx}
            else if r₀ = 1 then some {eAx, eRy}
            else none) = some s₀) :
    ∀ x ∈ s₀, x = eAy ∨ x = eRx ∨ x = eAx ∨ x = eRy := by
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
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rw [if_neg h0, if_neg h1] at hL₀
      exact absurd hL₀ (by simp)

/-- The peel configuration: two replicas, no communication, the two
program-order vis-edges. -/
noncomputable def peelConfig : Configuration K2 where
  N := fun r =>
    if r = 0 then some (applySeq K2 K2.init [eAy, eRx])
    else if r = 1 then some (applySeq K2 K2.init [eAx, eRy])
    else none
  L := fun r =>
    if r = 0 then some {eAy, eRx}
    else if r = 1 then some {eAx, eRy}
    else none
  vis := fun a b => (a = eAy ∧ b = eRx) ∨ (a = eAx ∧ b = eRy)
  dom_eq := by
    intro r
    by_cases h0 : r = 0
    · simp [h0]
    · by_cases h1 : r = 1 <;> simp [h0, h1]
  vis_src := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨0, {eAy, eRx}, by simp, Or.inl rfl⟩
    · exact ⟨1, {eAx, eRy}, by simp, Or.inl rfl⟩
  vis_tgt := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨0, {eAy, eRx}, by simp, Or.inr rfl⟩
    · exact ⟨1, {eAx, eRy}, by simp, Or.inr rfl⟩
  vis_causal := by
    rintro a b r s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) hL hs
    · by_cases h0 : r = 0
      · rw [if_pos h0, Option.some.injEq] at hL
        rw [← hL]
        exact Or.inl rfl
      · by_cases h1 : r = 1
        · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL
          rw [← hL] at hs
          rcases hs with h | h <;> simp [eRx, eAx, eRy] at h
        · rw [if_neg h0, if_neg h1] at hL
          exact absurd hL (by simp)
    · by_cases h0 : r = 0
      · rw [if_pos h0, Option.some.injEq] at hL
        rw [← hL] at hs
        rcases hs with h | h <;> simp [eAy, eRx, eRy] at h
      · by_cases h1 : r = 1
        · rw [if_neg h0, if_pos h1, Option.some.injEq] at hL
          rw [← hL]
          exact Or.inl rfl
        · rw [if_neg h0, if_neg h1] at hL
          exact absurd hL (by simp)
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    rcases peel_L_cases r s hL a hs with rfl | rfl | rfl | rfl <;>
      rcases peel_L_cases r' s' hL' b hs' with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [eAy, eRx, eAx, eRy]
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne hrep
    rcases peel_L_cases r s hL a hs with rfl | rfl | rfl | rfl <;>
      rcases peel_L_cases r' s' hL' b hs' with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        | exact Or.inl (Or.inr ⟨rfl, rfl⟩)
        | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        | (exfalso; simp [eAy, eRx, eAx, eRy] at hrep)

/-! ## §4. `U` and its full closure -/

/-- `U`: the merged version's event set — all four events. -/
def peelU : Set (Op K2.AppOp) := {eAy, eRx, eAx, eRy}

theorem eAy_mem_U : eAy ∈ peelU := Or.inl rfl
theorem eRx_mem_U : eRx ∈ peelU := Or.inr (Or.inl rfl)
theorem eAx_mem_U : eAx ∈ peelU := Or.inr (Or.inr (Or.inl rfl))
theorem eRy_mem_U : eRy ∈ peelU := Or.inr (Or.inr (Or.inr rfl))

/-- `U ⊆ C.events`. -/
theorem peelU_in_C : ∀ a ∈ peelU, a ∈ peelConfig.events := by
  intro a ha
  have hcases : a = eAy ∨ a = eRx ∨ a = eAx ∨ a = eRy := ha
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ⟨0, {eAy, eRx}, by simp [peelConfig], Or.inl rfl⟩
  · exact ⟨0, {eAy, eRx}, by simp [peelConfig], Or.inr rfl⟩
  · exact ⟨1, {eAx, eRy}, by simp [peelConfig], Or.inl rfl⟩
  · exact ⟨1, {eAx, eRy}, by simp [peelConfig], Or.inr rfl⟩

/-- **(1) `U` is fully causally closed** — unconditionally: every
vis-edge has its source in `U`. -/
theorem U_fully_closed :
    ∀ a b, peelConfig.vis a b → b ∈ peelU → a ∈ peelU := by
  rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _
  · exact eAy_mem_U
  · exact eAx_mem_U

/-- `vis` of the peel configuration is transitive (vacuously: no target of
a vis-edge is a source). Full-closure inductions quantify over
configurations with transitive `vis`; the obstruction is not an artifact
of intransitivity. -/
theorem peelConfig_vis_trans :
    ∀ {a b c : Op K2.AppOp},
      peelConfig.vis a b → peelConfig.vis b c → peelConfig.vis a c := by
  rintro a b c (⟨-, rfl⟩ | ⟨-, rfl⟩) (⟨h, -⟩ | ⟨h, -⟩) <;>
    simp [eAy, eRx, eAx, eRy] at h

/-- `vis` of the peel configuration is irreflexive. -/
theorem peelConfig_vis_irrefl : ∀ a : Op K2.AppOp, ¬ peelConfig.vis a a := by
  rintro a (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp [eAy, eRx, eAx, eRy] at h

/-! ## §5. The vis-edges and the surviving rc-edges -/

/-- **(3a)** `vis A_y R_x` (program order at replica `p`). -/
theorem vis_Ay_Rx : peelConfig.vis eAy eRx := Or.inl ⟨rfl, rfl⟩

/-- **(3b)** `vis A_x R_y` (program order at replica `q`). -/
theorem vis_Ax_Ry : peelConfig.vis eAx eRy := Or.inr ⟨rfl, rfl⟩

/-- **(3) The two vis-edges** of the plan doc, packaged. -/
theorem vis_edges : peelConfig.vis eAy eRx ∧ peelConfig.vis eAx eRy :=
  ⟨vis_Ay_Rx, vis_Ax_Ry⟩

/-- `R_x` is vis-maximal (globally: it is not the source of any
vis-edge) — so it *fails* `loOn(U)`-maximality below, not vis-maximality. -/
theorem Rx_vis_maximal : ∀ e' : Op K2.AppOp, ¬ peelConfig.vis eRx e' := by
  rintro e' (⟨h, -⟩ | ⟨h, -⟩) <;> simp [eAy, eRx, eAx] at h

/-- `R_y` is vis-maximal. -/
theorem Ry_vis_maximal : ∀ e' : Op K2.AppOp, ¬ peelConfig.vis eRy e' := by
  rintro e' (⟨h, -⟩ | ⟨h, -⟩) <;> simp [eAy, eRy, eAx] at h

theorem not_vis_Ax_Rx : ¬ peelConfig.vis eAx eRx := by
  rintro (⟨h, -⟩ | ⟨-, h⟩) <;> simp [eAy, eRx, eAx, eRy] at h

theorem not_vis_Ay_Ry : ¬ peelConfig.vis eAy eRy := by
  rintro (⟨-, h⟩ | ⟨h, -⟩) <;> simp [eAy, eRx, eAx, eRy] at h

/-- **(2a) The rc-edge `R_x → A_x` survives in `loOn(U)`**: the pair is
concurrent and `rc`-ordered, and the absorber clause cannot fire — `A_x`'s
only vis-successor is `R_y`, which *commutes* with `A_x` (cross-key). -/
theorem rc_edge_survives_x : loOn peelConfig peelU eRx eAx := by
  refine Or.inr ⟨Rx_vis_maximal eAx, not_vis_Ax_Rx, rfl, ?_⟩
  rintro ⟨e₃, -, hvis, hnc⟩
  rcases hvis with ⟨h, -⟩ | ⟨-, rfl⟩
  · simp [eAy, eAx] at h
  · exact hnc K2_comm_Ax_Ry

/-- **(2b) The rc-edge `R_y → A_y` survives in `loOn(U)`** — symmetric. -/
theorem rc_edge_survives_y : loOn peelConfig peelU eRy eAy := by
  refine Or.inr ⟨Ry_vis_maximal eAy, not_vis_Ay_Ry, rfl, ?_⟩
  rintro ⟨e₃, -, hvis, hnc⟩
  rcases hvis with ⟨-, rfl⟩ | ⟨h, -⟩
  · exact hnc K2_comm_Ay_Rx
  · simp [eAy, eAx] at h

/-- `A_x` is `loOn(U)`-maximal: no vis-flavored edge out of it (its only
vis-successor commutes), and no rc-flavored edge starts at an add. So the
*weak*-closure peel can take `A_x` — it fails only vis-maximality. -/
theorem Ax_loOn_maximal :
    ∀ e' ∈ peelU, ¬ loOn peelConfig peelU eAx e' := by
  rintro e' he' (⟨hvis, hnc⟩ | ⟨-, -, hrc, -⟩)
  · rcases hvis with ⟨h, -⟩ | ⟨-, rfl⟩
    · simp [eAy, eAx] at h
    · exact hnc K2_comm_Ax_Ry
  · have hcases : e' = eAy ∨ e' = eRx ∨ e' = eAx ∨ e' = eRy := he'
    rcases hcases with rfl | rfl | rfl | rfl <;>
      exact absurd hrc (by decide)

/-- `A_y` is `loOn(U)`-maximal. -/
theorem Ay_loOn_maximal :
    ∀ e' ∈ peelU, ¬ loOn peelConfig peelU eAy e' := by
  rintro e' he' (⟨hvis, hnc⟩ | ⟨-, -, hrc, -⟩)
  · rcases hvis with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hnc K2_comm_Ay_Rx
    · simp [eAy, eAx] at h
  · have hcases : e' = eAy ∨ e' = eRx ∨ e' = eAx ∨ e' = eRy := he'
    rcases hcases with rfl | rfl | rfl | rfl <;>
      exact absurd hrc (by decide)

/-! ## §6. The cycle and the headline -/

/-- **The cycle** `A_y →vis R_x →rc A_x →vis R_y →rc A_y` (plan doc,
Gate G1): vis-flavored and surviving rc-flavored `loOn(U)`-edges
alternate around all four events, so vis-maximality and
`loOn(U)`-maximality can never coincide. -/
theorem the_cycle :
    peelConfig.vis eAy eRx ∧ loOn peelConfig peelU eRx eAx ∧
    peelConfig.vis eAx eRy ∧ loOn peelConfig peelU eRy eAy :=
  ⟨vis_Ay_Rx, rc_edge_survives_x, vis_Ax_Ry, rc_edge_survives_y⟩

/-- **(4) HEADLINE — no full-closure-preserving peel exists.** No event of
the fully closed `U` is simultaneously `loOn(U)`-maximal (placeable last)
and vis-maximal (removable without breaking full closure): the adds
`A_y, A_x` fail vis-maximality (each has a program-order successor), and
the removes `R_x, R_y` fail `loOn(U)`-maximality (each has a surviving
rc-edge to the other key's add). The peel step of the naive `JoinLemma3F`
re-run is therefore impossible. -/
theorem no_peelable_event :
    ¬ ∃ e ∈ peelU,
        (∀ e' ∈ peelU, ¬ loOn peelConfig peelU e e') ∧
        (∀ e' ∈ peelU, ¬ peelConfig.vis e e') := by
  rintro ⟨e, he, hloMax, hvisMax⟩
  have hcases : e = eAy ∨ e = eRx ∨ e = eAx ∨ e = eRy := he
  rcases hcases with rfl | rfl | rfl | rfl
  · exact hvisMax eRx eRx_mem_U vis_Ay_Rx
  · exact hloMax eAx eAx_mem_U rc_edge_survives_x
  · exact hvisMax eRy eRy_mem_U vis_Ax_Ry
  · exact hloMax eAy eAy_mem_U rc_edge_survives_y

/-! ## §7. The weak-closure route is untouched -/

/-- Both vis-edges are cross-key, hence between commuting events. -/
theorem vis_implies_commutes :
    ∀ a b, peelConfig.vis a b → K2.commutes a b := by
  rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact K2_comm_Ay_Rx
  · exact K2_comm_Ax_Ry

/-- Every subset of events is `vis ∧ ¬commutes`-closed — the weak-closure
hypotheses of `JoinLemma3` hold for *any* peel here. -/
theorem weak_closure_trivial (V : Set (Op K2.AppOp)) :
    ∀ a b, peelConfig.vis a b → ¬ K2.commutes a b → b ∈ V → a ∈ V :=
  fun a b hvis hnc _ => absurd (vis_implies_commutes a b hvis) hnc

/-- A `loOn(U)`-maximal peel event exists (`A_x`): the weak route handles
this configuration today. Only the *full-closure* peel is obstructed. -/
theorem weak_peel_exists :
    ∃ e ∈ peelU, ∀ e' ∈ peelU, ¬ loOn peelConfig peelU e e' :=
  ⟨eAx, eAx_mem_U, Ax_loOn_maximal⟩

/-! ## §8. The packaged refutation -/

/-- **Gate G1, packaged.** There is a CRDT signature, a configuration with
transitive and irreflexive `vis`, and a nonempty *fully causally closed*
`U ⊆ C.events` containing no event that is both `loOn(U)`-maximal and
vis-maximal. Hence no single-event peel can drive an induction that
maintains full causal closure of the event set: the naive OQ3
reunification route (re-running the Join induction with `JoinLemma3F`'s
closure hypotheses) is dead as stated, and reunification must change the
induction itself. -/
theorem reunification_peel_obstruction :
    ∃ (D : CRDTSig) (C : Configuration D) (U : Set (Op D.AppOp)),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) ∧
      (∀ a : Op D.AppOp, ¬ C.vis a a) ∧
      (∀ a ∈ U, a ∈ C.events) ∧
      (∀ a b, C.vis a b → b ∈ U → a ∈ U) ∧
      U.Nonempty ∧
      ¬ ∃ e ∈ U,
          (∀ e' ∈ U, ¬ loOn C U e e') ∧
          (∀ e' ∈ U, ¬ C.vis e e') :=
  ⟨K2, peelConfig, peelU, peelConfig_vis_trans, peelConfig_vis_irrefl,
    peelU_in_C, U_fully_closed, ⟨eAy, eAy_mem_U⟩, no_peelable_event⟩

end Sal.ConditionedMRDTs
