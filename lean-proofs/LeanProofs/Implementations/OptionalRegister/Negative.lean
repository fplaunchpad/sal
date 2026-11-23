import LeanProofs1.Implementations.OptionalRegister.VCs

/-!
# The optional register fails the join lemma

This row is the one of Table 1 that does **not** satisfy the conditions of
Section 5, and the failure is not an artefact of how they are stated. The
implementation resolves a merged payload by **timestamp**

```
  mergePayload _ a b = if a.1 = b.1 then average
                       else if a.1 > b.1 then a else b
```

while `can(E)` resolves it by **causal order**: the cell holds the write
that is last in `lo^C_E`. Nothing ties the two together. A context
guarantees only that distinct observed events carry distinct timestamps and
that one replica's events are `vis`-comparable. It does not say that `vis`
increases the timestamp, and no `Good` derivable from `MintHonest` can
supply that, because `Issuance.CanIssue` reads only the state of the
issuer's causal past and this state keeps no record of a cleared cell's
timestamp.

The witness below is one replica issuing three events in causal order with
decreasing timestamps.

```
  w1 = set v1  at time 10
  u  = unset   at time 7
  w2 = set v2  at time 5
```

With `E1 = {w1, u, w2}` and `E2 = {w1}`, both causally closed, `can(E1)`
holds `w2`'s payload because `w2` is causally last, while the merge keeps
`w1`'s because `10 > 5`.

`paperJoin_of_vcs` derives the join lemma from `Laws(D_type)` and VC1 to
VC5. `Laws(D_type)` is proved in `VCs.lean`, and so are VC1 and VC2, so the
theorem below says that VC3, VC4 and VC5 cannot all hold. Which of the three
is false is not settled here: the refutation is of the join lemma, and it
does not say which condition the counterexample breaks.
-/

namespace LeanProofs1.Implementations.OptionalRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-! ## The witness -/

/-- The first write, at timestamp 10. -/
def w1 : D.Event := (10, 0, .set 1)
/-- The clear, at timestamp 7. -/
def u : D.Event := (7, 0, .unset)
/-- The second write, at timestamp 5. -/
def w2 : D.Event := (5, 0, .set 2)

theorem w1_ne_u : w1 ≠ u := by decide
theorem w1_ne_w2 : w1 ≠ w2 := by decide
theorem u_ne_w2 : u ≠ w2 := by decide

/-- The whole event set. -/
def E1 : Set D.Event := {w1, u, w2}
/-- The first write alone. -/
def E2 : Set D.Event := {w1}

/-- Causal order: `w1` before `u` before `w2`. -/
def visRel : D.Event → D.Event → Prop := fun a b =>
  (a = w1 ∧ (b = u ∨ b = w2)) ∨ (a = u ∧ b = w2)

instance : DecidablePred (fun p : D.Event × D.Event => visRel p.1 p.2) :=
  fun p => by unfold visRel; infer_instance

/-- The context: one replica, observing all three events. -/
def ctx : Ctx D where
  L := fun r => if r = 0 then some E1 else none
  vis := visRel
  timestamps_distinct := by
    intro a b r s r' s' hL hs hL' hs' hne
    by_cases hr : r = 0 <;> by_cases hr' : r' = 0
    · subst hr; subst hr'
      simp only [if_true, Option.some.injEq] at hL hL'
      rw [← hL] at hs; rw [← hL'] at hs'
      rcases hs with h | h | h <;> rcases hs' with h' | h' | h' <;>
        subst h <;> subst h' <;> first | (exact absurd rfl hne) | decide
    · simp [hr'] at hL'
    · simp [hr] at hL
    · simp [hr] at hL
  vis_total_same_replica := by
    intro a b r s r' s' hL hs hL' hs' hne _
    by_cases hr : r = 0 <;> by_cases hr' : r' = 0
    · subst hr; subst hr'
      simp only [if_true, Option.some.injEq] at hL hL'
      rw [← hL] at hs; rw [← hL'] at hs'
      rcases hs with h | h | h <;> rcases hs' with h' | h' | h' <;>
        subst h <;> subst h' <;>
        first
          | exact absurd rfl hne
          | (left; unfold visRel; tauto)
          | (right; unfold visRel; tauto)
    · simp [hr'] at hL'
    · simp [hr] at hL
    · simp [hr] at hL

/-! ## The context's shape -/

theorem vis_w1_u : ctx.vis w1 u := Or.inl ⟨rfl, Or.inl rfl⟩
theorem vis_w1_w2 : ctx.vis w1 w2 := Or.inl ⟨rfl, Or.inr rfl⟩
theorem vis_u_w2 : ctx.vis u w2 := Or.inr ⟨rfl, rfl⟩

/-- Nothing observes `w1`, and `w2` observes nothing. -/
theorem not_vis_to_w1 (a : D.Event) : ¬ ctx.vis a w1 := by
  rintro (⟨-, h | h⟩ | ⟨-, h⟩) <;> exact absurd h.symm (by decide)

theorem not_vis_from_w2 (b : D.Event) : ¬ ctx.vis w2 b := by
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem not_vis_u_w1 : ¬ ctx.vis u w1 := not_vis_to_w1 u
theorem not_vis_w2_w1 : ¬ ctx.vis w2 w1 := not_vis_to_w1 w2
theorem not_vis_w2_u : ¬ ctx.vis w2 u := not_vis_from_w2 u

theorem visStrict : VisStrict D ctx := by
  constructor
  · intro a b c hab hbc
    rcases hab with ⟨rfl, hb | hb⟩ | ⟨rfl, hb⟩
    · subst hb
      rcases hbc with ⟨h, -⟩ | ⟨-, rfl⟩
      · exact absurd h (by decide)
      · exact vis_w1_w2
    · subst hb; exact absurd hbc (not_vis_from_w2 c)
    · subst hb; exact absurd hbc (not_vis_from_w2 c)
  · rintro a (⟨rfl, h | h⟩ | ⟨rfl, h⟩) <;> exact absurd h (by decide)

theorem mem_events {e : D.Event} (h : e ∈ E1) : e ∈ ctx.events :=
  ⟨0, E1, by simp [ctx], h⟩

theorem hsup1 : SupportedOn D ctx E1 := fun _ h => mem_events h

theorem subset_E2_E1 : E2 ⊆ E1 := by
  rintro e (rfl : e = w1); exact Or.inl rfl

theorem hsup2 : SupportedOn D ctx E2 := fun _ h => mem_events (subset_E2_E1 h)

theorem closed1 : ∀ e f : D.Event, ctx.vis e f → f ∈ E1 → e ∈ E1 := by
  rintro e f (⟨rfl, -⟩ | ⟨rfl, -⟩) -
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem closed2 : ∀ e f : D.Event, ctx.vis e f → f ∈ E2 → e ∈ E2 := by
  rintro e f hv (rfl : f = w1)
  exact absurd hv (not_vis_to_w1 e)

/-! ## The canonical states -/

/-- `can(E1)`: the replay in causal order. -/
noncomputable def s1 : D.Sigma := D.applyList D.sigma0 [w1, u, w2]
/-- `can(E2)`, which is also `can(E1 ∩ E2)`. -/
noncomputable def s2 : D.Sigma := D.applyList D.sigma0 [w1]

theorem mem_E1_iff (a : D.Event) : a ∈ [w1, u, w2] ↔ a ∈ E1 := by
  simp [E1, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem respects_E1 : respects [w1, u, w2] (paperOrder (policy D) ctx E1) := by
  have h1 : ¬ paperOrder (policy D) ctx E1 u w1 := by
    rintro (⟨hv, -⟩ | ⟨-, hnv, -, -⟩)
    · exact not_vis_u_w1 hv
    · exact hnv vis_w1_u
  have h2 : ¬ paperOrder (policy D) ctx E1 w2 w1 := by
    rintro (⟨hv, -⟩ | ⟨-, hnv, -, -⟩)
    · exact not_vis_w2_w1 hv
    · exact hnv vis_w1_w2
  have h3 : ¬ paperOrder (policy D) ctx E1 w2 u := by
    rintro (⟨hv, -⟩ | ⟨-, hnv, -, -⟩)
    · exact not_vis_w2_u hv
    · exact hnv vis_u_w2
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
  · rintro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1
    · rw [List.mem_singleton.mp hb]; exact h2
  · rintro b hb
    rw [List.mem_singleton.mp hb]; exact h3
  · rintro b hb
    exact absurd hb (by simp)

theorem can_E1 : IsPaperCan D ctx E1 s1 :=
  ⟨[w1, u, w2], ⟨by decide, mem_E1_iff⟩, respects_E1, rfl⟩

theorem can_E2 : IsPaperCan D ctx E2 s2 :=
  ⟨[w1], ⟨by decide, fun a => by simp [E2]⟩, by simp [respects], rfl⟩

theorem inter_eq : E1 ∩ E2 = E2 := Set.inter_eq_right.mpr subset_E2_E1
theorem union_eq : E1 ∪ E2 = E1 := Set.union_eq_left.mpr subset_E2_E1

theorem can_inter : IsPaperCan D ctx (E1 ∩ E2) s2 := by
  rw [inter_eq]; exact can_E2

/-! ## The two answers disagree -/

/-- `w2` is the last event of `E1` to write cell `0`, so `can(E1)` holds its
payload. -/
theorem survives_w2 : Survives ctx E1 0 w2 := by
  rintro ⟨x, -, -, hv⟩
  exact not_vis_from_w2 x hv

/-- The merge keeps `w1`'s payload, because `10 > 5`. -/
theorem merge_payload : ((D.merge s2 s1 s2).cells 0).2 = (10, 1) := by
  show (mergeCell (s2.cells 0) (s1.cells 0) (s2.cells 0)).2 = (10, 1)
  rfl

/-! ## The result -/

/-- **The optional register has no join lemma.** Merging the canonical states
of `E1` and `E2` over their intersection does not give the canonical state of
their union: the merge keeps `w1`'s payload because its timestamp is the
greater, while `can(E1 ∪ E2) = can(E1)` keeps `w2`'s because it is the one
that is causally last. -/
theorem join_fails : ¬ PaperJoinOn D (fun _ => True) := by
  intro hjoin
  have hcan : IsPaperCan D ctx (E1 ∪ E2) (D.merge s2 s1 s2) :=
    hjoin ctx E1 E2 s2 s1 s2 trivial visStrict hsup1 hsup2 closed1 closed2
      can_inter can_E1 can_E2
  rw [union_eq] at hcan
  have hpay := (canonical_cell_live visStrict hsup1 hcan
    (w := w2) (v := 2) (Or.inr (Or.inr rfl)) rfl rfl survives_w2).2
  have hr : (w2 : D.Event).rep = 0 := rfl
  rw [hr, merge_payload] at hpay
  exact absurd hpay (by decide)

/-- **So VC1 to VC5 cannot all hold for this row.** `Laws(D_type)` is proved
in `VCs.lean`, and with it the five conditions would give the join lemma.
VC1 and VC2 are proved there too, so the failure is among VC3, VC4 and VC5,
each of which equates a merge of canonical states with another and so is
sensitive to which of two payloads the merge keeps. Which one breaks is not
determined by this refutation. -/
theorem vcs_fail : ¬ PaperJoinLawsOn D (fun _ => True) := fun vcs =>
  join_fails (Metatheory.paperJoin_of_vcs laws equal_op_commutes
    same_rep_cond_comm vcs)

/-- And therefore no **unguarded** obligation bundle. -/
theorem no_obligations : ¬ Obligations D := fun h => vcs_fail h.joinLaws

/-! ## How far this reaches

`Obligations D` is `ObligationsOn D (fun _ => True)`, the bundle asked of
**every** replay context. The witness above is such a context, so the
unguarded bundle is refuted. It is **not** a context any configuration
produces, and that matters: a `Configuration` carries

```
  causal_mono : vis a b -> a.time < b.time
```

so visibility increases the timestamp, while the witness has `w1` visible to
`u` with timestamps `10` and `7`. The two orders the row confuses, timestamp
and causal, therefore agree inside a configuration and may well disagree
only outside one.

So this refutation says the row needs a **guarded** bundle
`ObligationsOn D Good` at a `Good` that records causal monotonicity. It does
not say the row fails Definition 4. -/

/-- Visibility increases the timestamp in every configuration. -/
theorem configs_monotone (C : Configuration D.toMRDTSig) (a b : D.Event)
    (h : C.replayContext.vis a b) : a.time < b.time := C.causal_mono h

/-- The witness context is not one of those. -/
theorem witness_not_monotone :
    ¬ (∀ a b : D.Event, ctx.vis a b → a.time < b.time) := by
  intro h
  exact absurd (h w1 u vis_w1_u) (by decide)

end LeanProofs1.Implementations.OptionalRegister
