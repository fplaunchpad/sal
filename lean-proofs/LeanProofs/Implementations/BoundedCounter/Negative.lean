import LeanProofs_no_spec_non_comm.Implementations.BoundedCounter.VCs

/-!
# The bounded counter needs a larger dependency set and a stronger maximality

`Laws(D_type)` holds for this row, and so do VC1 and VC2. **VC4 does not**,
at either reading of `VCRoute.lean`, and this file proves it twice. The
appendix says why: the cumulative single-writer cells need an event's
dependencies to be its **full causal past**, while Section 5 fixes them to
`downset`, the backward closure of `vis` at non-commuting pairs.

Every pair of this row's events commutes, since each effector adds an amount
to one cell. So `downset C e` is `{e}` for every `e`, and CAUSAL-DELTA is
asked with `B = can(empty) = sigma0`. For two increments of one replica that
reads

```
  merge(sigma0, e1(sigma0), e2(sigma0)) = e2(e1(sigma0))
```

and the diagonal cell is `max 1 1 = 1` on the left against `1 + 1 = 2` on
the right. Componentwise maximum recovers a cumulative cell only from a
state that already holds the earlier writes, and `sigma0` does not.

## Enlarging the dependency set is not enough on its own

`lo^C_E` relates only non-commuting pairs, so for this row it is **empty**
and `PaperMaximalOn` is vacuously true of every event of `E`. VC4 is then
asked about the **first** increment as readily as about the last, and the
first increment's causal past is empty under every reading of
dependencies. `vc4_fails_at_e1` is that refutation, and it survives any
enlargement of `downset`.

What rescues the row is the other half of the change: maximality read at
`vis` as well, which `e1` fails. `not_causalMaximal_e1` records that, and
`VCs.lean` proves all five conditions once both halves move together.

This is not the obstruction the optional register has, where a law is false
of the datatype. Here the datatype is fine and Section 5's reading of
dependencies and maximality is too weak. `Interface/CausalRoute.lean` is the
generalisation the appendix refers to.
-/
namespace LeanProofs.NoSpecNonComm.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {n : Nat} {K : Int}

/-! ## The witness: two increments of one replica -/

/-- The first increment, at timestamp 1. -/
def e1 : Op AppOp := (1, 0, .increment 1)
/-- The second increment, at timestamp 2. Both are issued by replica `0`
and carry the same operation. -/
def e2 : Op AppOp := (2, 0, .increment 1)

theorem e1_ne_e2 : e1 ≠ e2 := by simp [e1, e2]

/-- The two events, observed by replica `0`. -/
def U : Set (Op AppOp) := {e1, e2}

/-- Causal order: the first increment precedes the second. -/
def visRel : Op AppOp → Op AppOp → Prop := fun a b => a = e1 ∧ b = e2

/-- The context. -/
def ctx : Ctx (D n K) where
  L := fun r => if r = 0 then some U else none
  vis := visRel
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    by_cases hr : r = 0 <;> by_cases hr' : r' = 0
    · subst hr; subst hr'
      simp only [if_true, Option.some.injEq] at hL hL'
      rw [← hL] at hs; rw [← hL'] at hs'
      rcases hs with h | h <;> rcases hs' with h' | h' <;> subst h <;> subst h' <;>
        first | (exact absurd rfl hne) | (simp [e1, e2])
    · simp [hr'] at hL'
    · simp [hr] at hL
    · simp [hr] at hL
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    by_cases hr : r = 0 <;> by_cases hr' : r' = 0
    · subst hr; subst hr'
      simp only [if_true, Option.some.injEq] at hL hL'
      rw [← hL] at hs; rw [← hL'] at hs'
      rcases hs with h | h <;> rcases hs' with h' | h' <;> subst h <;> subst h' <;>
        first
          | exact absurd rfl hne
          | (left; exact ⟨rfl, rfl⟩)
          | (right; exact ⟨rfl, rfl⟩)
    · simp [hr'] at hL'
    · simp [hr] at hL
    · simp [hr] at hL

theorem visStrict : VisStrict (D n K) (ctx (n := n) (K := K)) := by
  constructor
  · rintro a b c ⟨rfl, rfl⟩ ⟨h, -⟩
    exact absurd h (by simp [e1, e2])
  · rintro a ⟨rfl, h⟩
    exact absurd h (by simp [e1, e2])

theorem mem_events {e : Op AppOp} (h : e ∈ U) :
    e ∈ (ctx (n := n) (K := K)).events :=
  ⟨0, U, by simp [ctx], h⟩

theorem hsup : SupportedOn (D n K) (ctx (n := n) (K := K)) U :=
  fun _ h => mem_events h

/-! ## The dependency set collapses

`downset` keeps only the non-commuting visible predecessors, and this row
has none, so it never reaches past the event itself. -/

theorem downset_eq (C : Ctx (D n K)) (e : (D n K).Event) :
    downset C e \ {e} = (∅ : Set (D n K).Event) := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' => exact h'.2 (all_commute _ _)
    | tail _ h' => exact h'.2 (all_commute _ _)

/-! ## The canonical states -/

theorem diff_eq : U \ {e2} = {e1} := by
  ext x
  simp only [U, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hne⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨Or.inl rfl, e1_ne_e2⟩

theorem can_A : IsPaperCan (D n K) (ctx (n := n) (K := K)) (U \ {e2})
    ((D n K).do_ (D n K).sigma0 e1) := by
  refine ⟨[e1], ⟨by simp, fun a => ?_⟩, by simp [respects], rfl⟩
  rw [diff_eq]; simp

theorem can_B : IsPaperCan (D n K) (ctx (n := n) (K := K))
    (downset (ctx (n := n) (K := K)) e2 \ {e2}) (D n K).sigma0 := by
  rw [downset_eq]
  exact ⟨[], ⟨by simp, by simp⟩, by simp [respects], rfl⟩

theorem maximal : PaperMaximalOn (D n K) (ctx (n := n) (K := K)) U e2 := by
  intro x _ _
  rintro (⟨-, hnc⟩ | ⟨-, -, hrc, -⟩)
  · exact hnc (all_commute _ _)
  · exact no_rc_edge e2 x hrc

/-! ## The result -/

/-- **VC4 fails.** The diagonal cell is `max 1 1 = 1` on one side and
`1 + 1 = 2` on the other. -/
theorem vc4_fails :
    (D n K).merge (D n K).sigma0 ((D n K).do_ (D n K).sigma0 e1)
        ((D n K).do_ (D n K).sigma0 e2)
      ≠ (D n K).do_ ((D n K).do_ (D n K).sigma0 e1) e2 := by
  have hL : ((D n K).merge (D n K).sigma0 ((D n K).do_ (D n K).sigma0 e1)
      ((D n K).do_ (D n K).sigma0 e2)).R 0 0 = 1 := by
    simp [merge_eq, mergeState, do_eq, step, sigma0_eq, initial, e1, e2,
      bumpMatrix, Op.op, Op.rep]
  have hR : ((D n K).do_ ((D n K).do_ (D n K).sigma0 e1) e2).R 0 0 = 2 := by
    simp [do_eq, step, sigma0_eq, initial, e1, e2, bumpMatrix, Op.op, Op.rep]
  intro h
  have hcell : ((D n K).merge (D n K).sigma0 ((D n K).do_ (D n K).sigma0 e1)
      ((D n K).do_ (D n K).sigma0 e2)).R 0 0
      = ((D n K).do_ ((D n K).do_ (D n K).sigma0 e1) e2).R 0 0 := by rw [h]
  rw [hL, hR] at hcell
  exact absurd hcell (by decide)

/-- **So the five conditions do not all hold at `lo^C_E`.** -/
theorem vcs_fail : ¬ PaperJoinLawsOn (D n K) (fun _ => True) := by
  intro vcs
  exact vc4_fails (vcs.vc4_causal_delta (ctx (n := n) (K := K)) U
    ((D n K).do_ (D n K).sigma0 e1) (D n K).sigma0 e2
    trivial visStrict hsup
    (fun a b _ hnc _ => absurd (all_commute a b) hnc)
    (Or.inr rfl) maximal can_A can_B)

/-- And therefore this row has no obligation bundle at Section 5's reading,
so it does not reach Definition 4 through `PaperJoinLawsOn`. It reaches it
through `CausalJoinLawsOn` instead, which `VCs.lean` proves. -/
theorem no_obligations : ¬ Obligations (D n K) := fun h => vcs_fail h.joinLaws

/-! ## Enlarging the dependency set alone leaves VC4 refutable

The same witness, read at `e1` rather than at `e2`. Nothing below mentions
`downset`, so nothing below is affected by replacing it. -/

/-- **Maximality is vacuous for this row.** `e1` counts as maximal in `U`
although `e2` is visible after it, by the very proof that works for `e2`. -/
theorem maximal_e1 : PaperMaximalOn (D n K) (ctx (n := n) (K := K)) U e1 := by
  intro x _ _
  rintro (⟨-, hnc⟩ | ⟨-, -, hrc, -⟩)
  · exact hnc (all_commute _ _)
  · exact no_rc_edge e1 x hrc

/-- **Maximality at `vis` is not.** This is the half that excludes the
witness, and it is exactly the half Section 5 does not ask for. -/
theorem not_causalMaximal_e1 :
    ¬ CausalMaximalOn (D n K) (ctx (n := n) (K := K)) U e1 := by
  intro h
  exact h e2 (Or.inr rfl) (fun hx => e1_ne_e2 hx.symm) ⟨rfl, rfl⟩

/-- `e1` has no visible predecessors, so its **full causal past** is empty
too and `B` is `sigma0` however dependencies are read. -/
theorem causalPast_e1 :
    CausalPast (D n K) (ctx (n := n) (K := K)) e1 \ {e1}
      = (∅ : Set (D n K).Event) := by
  ext x
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro (hx | hx)
  · exact fun hne => hne hx
  · intro _
    exfalso
    cases hx with
    | single h' => exact absurd h'.2 (by simp [e1, e2])
    | tail _ h' => exact absurd h'.2 (by simp [e1, e2])

theorem diff_e1 : U \ {e1} = {e2} := by
  ext x
  simp only [U, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hne⟩
    · exact absurd rfl hne
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, fun h => e1_ne_e2 h.symm⟩

/-- `A = can(U \ {e1})`. -/
theorem can_A_e1 : IsPaperCan (D n K) (ctx (n := n) (K := K)) (U \ {e1})
    ((D n K).do_ (D n K).sigma0 e2) := by
  refine ⟨[e2], ⟨by simp, fun a => ?_⟩, by simp [respects], rfl⟩
  rw [diff_e1]; simp

/-- **VC4 fails at `e1` with `B = sigma0`**, and `sigma0` is canonical for
`e1`'s full causal past, so no enlargement of the dependency set repairs
this instance. Only the maximality half does, by excluding it. -/
theorem vc4_fails_at_e1 :
    (D n K).merge (D n K).sigma0 ((D n K).do_ (D n K).sigma0 e2)
        ((D n K).do_ (D n K).sigma0 e1)
      ≠ (D n K).do_ ((D n K).do_ (D n K).sigma0 e2) e1 := by
  have hL : ((D n K).merge (D n K).sigma0 ((D n K).do_ (D n K).sigma0 e2)
      ((D n K).do_ (D n K).sigma0 e1)).R 0 0 = 1 := by
    simp [merge_eq, mergeState, do_eq, step, sigma0_eq, initial, e1, e2,
      bumpMatrix, Op.op, Op.rep]
  have hR : ((D n K).do_ ((D n K).do_ (D n K).sigma0 e2) e1).R 0 0 = 2 := by
    simp [do_eq, step, sigma0_eq, initial, e1, e2, bumpMatrix, Op.op, Op.rep]
  intro h
  have hcell := congrArg (fun s => St.R s 0 0) h
  simp only at hcell
  rw [hL, hR] at hcell
  exact absurd hcell (by decide)

end LeanProofs.NoSpecNonComm.Implementations.BoundedCounter
