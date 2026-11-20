import LeanProofs.Implementations.FlatCounter.Definition
import LeanProofs.Metatheory.Adequacy

/-!
# The counter: discharging the obligations

Each obligation is an integer identity closed by `omega`.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma. The counter proves equations; the metatheory proves the theorem.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- Every pair of events commutes, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro z
  change Int at z
  change (z + delta e₁.op) + delta e₂.op = (z + delta e₂.op) + delta e₁.op
  omega

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names every
other row uses.

`rc` is `Either` at every pair for this datatype, so `no_rc_edge` is
immediate from the tuple and needs no lemma of its own. `all_commute` above
supplies the other half of each proof. The fourth law, SPEC-NON-COMM, needs
`Spec` and is in `SequentialSpec.lean`. -/

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all, so there is none to
chain. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. Both sides are false:
the left by `all_commute`, the right because `rc` is empty. -/
theorem rc_non_comm : UniformRcNonComm D := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. The absorber clause is
reached only behind an `rc` edge, and there is none. -/
theorem cond_comm : UniformCondComm D := fun _ e e' _ _ hb _ =>
  (no_rc_edge e e' hb).elim

/-- **`Laws(D_type)`.** RC-NON-COMM carries the paper's `o1 /= o2` conjunct,
which NO-RC-CHAIN supplies through `rcNonComm_of_exact`. -/
theorem laws : Laws D :=
  ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
   no_rc_chain,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge e e' hb).elim⟩

/-! ## VC1 to VC5

Stated as Section 5 states them and proved here. A `merge` that never
inspects its delta lets each proof abstract `e(m)` in one step and close by
arithmetic, but the theorem proved is the condition, not a stronger
equation that the condition is read off from. -/

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : D.Sigma) :
    D.merge l a b = D.merge l b a := by
  change Int at l a b
  change a + b - l = b + a - l
  omega

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s →
      D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  change Int at s
  change (0 : Int) + s - 0 = s
  omega

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change Int at l m x c y
  change (x + c - m) + y - l = x + y - l + c - m
  omega

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change Int at m x₀ x₁ x₂ c
  change (x₁ + c - m) + (x₂ + c - m) - (x₀ + c - m) = x₁ + x₂ - x₀ + c - m
  omega

/-- The peel law. Not one of the paper's conditions: it is what
`Metatheory.causalDelta_of_commuting` runs on to discharge **VC4**. -/
theorem commuting_peel (a : D.Sigma) (e : D.Event) (pi₀ pi₂ : List D.Event)
    (_ : ∀ x ∈ pi₀, D.Commutes e x) (_ : ∀ x ∈ pi₂, D.Commutes e x) :
    D.merge (D.applyList D.sigma0 pi₀) (D.do_ a e) (D.applyList D.sigma0 pi₂)
      = D.do_ (D.merge (D.applyList D.sigma0 pi₀) a
          (D.applyList D.sigma0 pi₂)) e := by
  change Int at a
  change (a + delta e.op)
      + (show Int from D.applyList D.sigma0 pi₂)
      - (show Int from D.applyList D.sigma0 pi₀)
    = a + (show Int from D.applyList D.sigma0 pi₂)
      - (show Int from D.applyList D.sigma0 pi₀) + delta e.op
  omega

/-- **VC4** CAUSAL-DELTA. Every pair of events commutes, so `down(e)` is
`{e}` and the base is `sigma0`; the peel law then moves `e` outside the
merge and VC2 applies at the canonical state it is left with. -/
theorem vc4_causal_delta :
    @CausalDeltaLaw D.toMRDTSig (Interface.rcOrder D) :=
  Metatheory.causalDelta_of_commuting vc1_merge_comm vc2_merge_init
    commuting_peel all_commute

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLaws D :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute, vc4_causal_delta,
   vc5_redistribute⟩

/-- Everything the metatheory consumes. `laws` is this row's own, not
something the metatheory reconstructs; the unguarded forms of RC-NON-COMM
and COND-COMM follow from it and `all_commute`. -/
theorem obligations : Obligations D :=
  ⟨laws, rc_non_comm, cond_comm, joinLaws⟩

end LeanProofs.Implementations.FlatCounter
