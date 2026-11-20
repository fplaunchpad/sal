import LeanProofs.Implementations.GrowOnlySet.Definition
import LeanProofs.Metatheory.Adequacy

/-!
# The grow-only set: discharging the obligations

Each obligation is a set identity. Because `merge(l,a,b) = a union b` ignores
its base and `do` only inserts, every one reduces to commutativity,
associativity and idempotence of union.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- Two insertions commute, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : (D A).Event) : (D A).Commutes e₁ e₂ := by
  intro S
  change Set A at S
  change insert e₂.op (insert e₁.op S) = insert e₁.op (insert e₂.op S)
  exact Set.insert_comm _ _ _

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names the
direct-route rows use.

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
  change Set A at l a b
  change a ∪ b = b ∪ a
  exact Set.union_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx (D A)) (E : Set (D A).Event) (s : (D A).Sigma),
      SupportedOn (D A) C E → IsCanOn (D A) C E s →
      (D A).merge (D A).sigma0 (D A).sigma0 s = s := by
  intro _ _ s _ _
  change Set A at s
  change (∅ : Set A) ∪ s = s
  exact Set.empty_union _

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
  change Set A at l m x c y
  change (x ∪ c) ∪ y = (x ∪ y) ∪ c
  ext z; simp only [Set.mem_union]; tauto

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
  change Set A at m x₀ x₁ x₂ c
  change (x₁ ∪ c) ∪ (x₂ ∪ c) = (x₁ ∪ x₂) ∪ c
  ext z; simp only [Set.mem_union]; tauto

/-- The peel law. Not one of the paper's conditions: it is what
`Metatheory.causalDelta_of_commuting` runs on to discharge **VC4**. -/
theorem commuting_peel (a : (D A).Sigma) (e : (D A).Event)
    (pi₀ pi₂ : List (D A).Event)
    (_ : ∀ x ∈ pi₀, (D A).Commutes e x) (_ : ∀ x ∈ pi₂, (D A).Commutes e x) :
    (D A).merge ((D A).applyList (D A).sigma0 pi₀) ((D A).do_ a e)
        ((D A).applyList (D A).sigma0 pi₂)
      = (D A).do_ ((D A).merge ((D A).applyList (D A).sigma0 pi₀) a
          ((D A).applyList (D A).sigma0 pi₂)) e := by
  change Set A at a
  change insert e.op a ∪ (D A).applyList (D A).sigma0 pi₂
    = insert e.op (a ∪ (D A).applyList (D A).sigma0 pi₂)
  ext z; simp only [Set.mem_union, Set.mem_insert_iff]; tauto

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

end LeanProofs.Implementations.GrowOnlySet
