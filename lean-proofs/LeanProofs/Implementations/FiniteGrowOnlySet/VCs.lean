import LeanProofs1.Implementations.FiniteGrowOnlySet.Definition
import LeanProofs1.Interface.VCRoute

/-!
# The finite grow-only set: every obligation

`Laws(D_type, Spec)` of Section 4 and VC1 to VC5 of Section 5, all four laws
and all five conditions, for the tuple of `Definition.lean`. `obligations`
bundles what the metatheory consumes; `spec_non_comm` and `specSound` are the
two further premises `Soundness.certifiedSpecRA` asks for.
-/

namespace LeanProofs1.Implementations.FiniteGrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {A : Type} [DecidableEq A]

/-- Two insertions commute, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : (D A).Event) : (D A).Commutes e₁ e₂ := by
  intro S
  change Finset A at S
  change insert e₂.op (insert e₁.op S) = insert e₁.op (insert e₂.op S)
  exact Finset.insert_comm _ _ _

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names every
other row uses.

`rc` is `Either` at every pair for this datatype, so `no_rc_edge` is
immediate from the tuple and needs no lemma of its own. `all_commute` above
supplies the other half of each proof. The fourth law, SPEC-NON-COMM, needs
`Spec` and is at the end of this file. -/

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
  change Finset A at l a b
  change a ∪ b = b ∪ a
  exact Finset.union_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx (D A)) (E : Set (D A).Event) (s : (D A).Sigma),
      SupportedOn (D A) C E → IsCanOn (D A) C E s →
      (D A).merge (D A).sigma0 (D A).sigma0 s = s := by
  intro _ _ s _ _
  change Finset A at s
  change (∅ : Finset A) ∪ s = s
  exact Finset.empty_union _

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
  change Finset A at l m x c y
  change (x ∪ c) ∪ y = (x ∪ y) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

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
  change Finset A at m x₀ x₁ x₂ c
  change (x₁ ∪ c) ∪ (x₂ ∪ c) = (x₁ ∪ x₂) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx (D A)) (U : Set (D A).Event) (A' B : (D A).Sigma) (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C U → WeaklyClosed (D A) C U →
      e ∈ U → MaximalOn (D A) C U e →
      IsCanOn (D A) C (U \ {e}) A' →
      IsCanOn (D A) C (downset C e \ {e}) B →
      (D A).merge B A' ((D A).do_ B e) = (D A).do_ A' e := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  intro C U A' B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting all_commute C e) hB]
  change Finset A at A'
  change A' ∪ insert e.op (∅ : Finset A) = insert e.op A'
  ext z; simp

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn (D A) (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A' B e _ => vc4_causal_delta C U A' B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

variable (A : Type) [DecidableEq A]
variable {A}

/-! ## RA-linearizability -/

variable (A)

variable {A}

/-- The sequential premise. -/
theorem specSound : Soundness.SpecSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  show (D A).applyList (D A).sigma0 pi
    = (pi.map Op.op).foldl (fun S o => insert o S) (∅ : Finset A)
  simp [Impl.applyList, List.foldl_map]
  rfl

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`. The specification inserts, so its two updates commute for the same reason
the implementation's do. -/

/-- Every pair of operations commutes in `Spec`. -/
theorem spec_commutes (o₁ o₂ : (type A).OType) :
    Interface.spec_commutes (historySpec A) o₁ o₂ :=
  (specMachine A).language_commutes o₁ o₂ (fun _ => Finset.insert_comm _ _ _)

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict, because `Spec` has no conflict to erase. -/
theorem spec_non_comm : Interface.spec_non_comm (D A) (historySpec A) :=
  Interface.spec_non_comm_of_spec_commutes spec_commutes

/-- **The bundle the specification route consumes**: the obligations of
Section 5 together with SPEC-NON-COMM, the one law of Section 4 that
mentions `Spec`. -/
theorem specObligations : SpecObligations (D A) (historySpec A) :=
  SpecObligations.ofCommuting laws all_commute joinLaws spec_non_comm

end LeanProofs1.Implementations.FiniteGrowOnlySet
