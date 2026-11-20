import LeanProofs.Implementations.FlatGrowOnlyMap.Definition
import LeanProofs.Metatheory.Adequacy

/-!
# The flat grow-only map: discharging the obligations

Both `do` and `merge` are pointwise Boolean disjunctions, so every obligation
reduces to associativity, commutativity and idempotence of `or` at each point.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- Two insertions commute, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : (D A).Event) : (D A).Commutes e₁ e₂ := by
  intro S
  change (fun x => (S x || decide (x = e₁.op)) || decide (x = e₂.op))
    = (fun x => (S x || decide (x = e₂.op)) || decide (x = e₁.op))
  funext x
  cases S x <;> cases decide (x = e₁.op) <;> cases decide (x = e₂.op) <;> rfl

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names every
other row uses.

`rc` is `Either` at every pair for this datatype, so `no_rc_edge` is
immediate from the tuple and needs no lemma of its own. `all_commute` above
supplies the other half of each proof. The fourth law, SPEC-NON-COMM, needs
`Spec` and is in `SequentialSpec.lean`. -/

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : (D A).Event) : ¬ (D A).EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all, so there is none to
chain. -/
theorem no_rc_chain (o₁ o₂ o₃ : (type A).OType) :
    ¬ ((D A).RcBefore o₁ o₂ ∧ (D A).RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. Both sides are false:
the left by `all_commute`, the right because `rc` is empty. -/
theorem rc_non_comm : UniformRcNonComm (D A) := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. The absorber clause is
reached only behind an `rc` edge, and there is none. -/
theorem cond_comm : UniformCondComm (D A) := fun _ e e' _ _ hb _ =>
  (no_rc_edge e e' hb).elim

/-- **`Laws(D_type)`.** RC-NON-COMM carries the paper's `o1 /= o2` conjunct,
which NO-RC-CHAIN supplies through `rcNonComm_of_exact`. -/
theorem laws : Laws (D A) :=
  ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
   no_rc_chain,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge e e' hb).elim⟩

/-! ## VC1 to VC5

Stated as Section 5 states them and proved here. A `merge` that never
inspects its delta lets each proof abstract `e(m)` in one step and close by
arithmetic, but the theorem proved is the condition, not a stronger
equation that the condition is read off from. -/

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : (D A).Sigma) :
    (D A).merge l a b = (D A).merge l b a := by
  change (fun x => l x || a x || b x) = (fun x => l x || b x || a x)
  funext x; cases l x <;> cases a x <;> cases b x <;> rfl

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx (D A)) (E : Set (D A).Event) (s : (D A).Sigma),
      SupportedOn (D A) C E → IsCanOn (D A) C E s →
      (D A).merge (D A).sigma0 (D A).sigma0 s = s := by
  intro _ _ s _ _
  change (fun x => (false || false) || s x) = s
  funext x; cases s x <;> rfl

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx (D A)) (E₁ E₂ : Set (D A).Event) (l m x y : (D A).Sigma)
      (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C E₁ → SupportedOn (D A) C E₂ →
      WeaklyClosed (D A) C E₁ → WeaklyClosed (D A) C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn (D A) C (E₁ ∪ E₂) e →
      IsCanOn (D A) C (E₁ ∩ E₂) l →
      IsCanOn (D A) C (downset C e \ {e}) m →
      IsCanOn (D A) C (E₁ \ {e}) x →
      IsCanOn (D A) C E₂ y →
      (D A).merge l ((D A).merge m x ((D A).do_ m e)) y
        = (D A).merge m ((D A).merge l x y) ((D A).do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  generalize (D A).do_ m e = c
  change (fun z => l z || (m z || x z || c z) || y z)
    = (fun z => m z || (l z || x z || y z) || c z)
  funext z
  cases l z <;> cases m z <;> cases x z <;> cases c z <;> cases y z <;> rfl

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx (D A)) (E₁ E₂ : Set (D A).Event) (x₀ x₁ x₂ m : (D A).Sigma)
      (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C E₁ → SupportedOn (D A) C E₂ →
      WeaklyClosed (D A) C E₁ → WeaklyClosed (D A) C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn (D A) C (E₁ ∪ E₂) e →
      IsCanOn (D A) C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn (D A) C (downset C e \ {e}) m →
      IsCanOn (D A) C (E₁ \ {e}) x₁ →
      IsCanOn (D A) C (E₂ \ {e}) x₂ →
      (D A).merge ((D A).merge m x₀ ((D A).do_ m e)) ((D A).merge m x₁ ((D A).do_ m e))
          ((D A).merge m x₂ ((D A).do_ m e))
        = (D A).merge m ((D A).merge x₀ x₁ x₂) ((D A).do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  generalize (D A).do_ m e = c
  change (fun z => (m z || x₀ z || c z) || (m z || x₁ z || c z) || (m z || x₂ z || c z))
    = (fun z => m z || (x₀ z || x₁ z || x₂ z) || c z)
  funext z
  cases m z <;> cases x₀ z <;> cases x₁ z <;> cases x₂ z <;> cases c z <;> rfl

/-- The peel law. Not one of the paper's conditions: it is what
`Metatheory.causalDelta_of_commuting` runs on to discharge **VC4**. -/
theorem commuting_peel (a : (D A).Sigma) (e : (D A).Event)
    (pi₀ pi₂ : List (D A).Event)
    (_ : ∀ x ∈ pi₀, (D A).Commutes e x) (_ : ∀ x ∈ pi₂, (D A).Commutes e x) :
    (D A).merge ((D A).applyList (D A).sigma0 pi₀) ((D A).do_ a e)
        ((D A).applyList (D A).sigma0 pi₂)
      = (D A).do_ ((D A).merge ((D A).applyList (D A).sigma0 pi₀) a
          ((D A).applyList (D A).sigma0 pi₂)) e := by
  set P₀ := (D A).applyList (D A).sigma0 pi₀ with hP₀
  set P₂ := (D A).applyList (D A).sigma0 pi₂ with hP₂
  change (fun x => P₀ x || (a x || decide (x = e.op)) || P₂ x)
    = (fun x => (P₀ x || a x || P₂ x) || decide (x = e.op))
  funext x
  cases P₀ x <;> cases a x <;> cases P₂ x <;> cases decide (x = e.op) <;> rfl

/-- **VC4** CAUSAL-DELTA. Every pair of events commutes, so `down(e)` is
`{e}` and the base is `sigma0`; the peel law then moves `e` outside the
merge and VC2 applies at the canonical state it is left with. -/
theorem vc4_causal_delta :
    @CausalDeltaLaw (D A).toMRDTSig (Interface.rcOrder (D A)) :=
  Metatheory.causalDelta_of_commuting vc1_merge_comm vc2_merge_init
    commuting_peel all_commute

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLaws (D A) :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute, vc4_causal_delta,
   vc5_redistribute⟩

/-- Everything the metatheory consumes. `laws` is this row's own, not
something the metatheory reconstructs; the unguarded forms of RC-NON-COMM
and COND-COMM follow from it and `all_commute`. -/
theorem obligations : Obligations (D A) :=
  ⟨laws, rc_non_comm, cond_comm, joinLaws⟩

end LeanProofs.Implementations.FlatGrowOnlyMap
