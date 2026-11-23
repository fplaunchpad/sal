import LeanProofs1.Implementations.NotionCore.Definition
import LeanProofs1.Interface.VCRoute

/-!
# Notion core: every verification condition

Section 4's `Laws(D_type)` and Section 5's VC1 to VC5, for the tuple of
`Definition.lean`. `obligations` bundles what the metatheory consumes.

`do` unions the decoded fact set into the state and `merge` unions the two
branches, so the appendix's equation `e2(e1(F)) = e1(e2(F))` holds at every
state. `Laws` then forces `rc` to be empty, and VC1 to VC5 are union
identities. The independent document commands of `SequentialSpec.lean` do
**not** commute; what commutes is the union of decoded facts.

Clause 2 of Definition 4 is not proved here, so this row has no
`Certificate.lean` yet. The query of `Definition.lean` reconstructs the
displayed document from the facts by a fuel-bounded traversal, a boundary
scan and a creation-link fold, and relating that to the ordered block list
of the same file's `Spec` is a separate development.
-/

namespace LeanProofs1.Implementations.NotionCore

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable (nm : Names)

/-- **Receipt commutes**: this is the appendix's `e2(e1(F)) = e1(e2(F))`. -/
theorem all_commute (e₁ e₂ : (D nm).Event) : (D nm).Commutes e₁ e₂ := by
  intro S
  change (S ∪ delta e₁.op.id e₁.op.payload) ∪ delta e₂.op.id e₂.op.payload
    = (S ∪ delta e₂.op.id e₂.op.payload) ∪ delta e₁.op.id e₁.op.payload
  ext z; simp only [Finset.mem_union]; tauto

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : (D nm).Event) : ¬ (D nm).EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ ((D nm).RcBefore o₁ o₂ ∧ (D nm).RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. -/
theorem rc_non_comm : UniformRcNonComm (D nm) := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute nm e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge nm _ _) (no_rc_edge nm _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. -/
theorem cond_comm : UniformCondComm (D nm) := fun _ e e' _ _ hb _ =>
  (no_rc_edge nm e e' hb).elim

/-- **`Laws(D_type)`.** -/
theorem laws : Laws (D nm) :=
  ⟨rcNonComm_of_exact (no_rc_chain nm) (fun e₁ e₂ _ _ => rc_non_comm nm e₁ e₂),
   no_rc_chain nm,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge nm e e' hb).elim⟩

/-! ## VC1 and VC2 -/

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : (D nm).Sigma) :
    (D nm).merge l a b = (D nm).merge l b a := by
  change a ∪ b = b ∪ a
  exact Finset.union_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init : ∀ (C : Ctx (D nm)) (E : Set (D nm).Event) (s : (D nm).Sigma),
    SupportedOn (D nm) C E → IsCanOn (D nm) C E s →
    (D nm).merge (D nm).sigma0 (D nm).sigma0 s = s := by
  intro _ _ s _ _
  change (∅ : St) ∪ s = s
  exact Finset.empty_union _

/-! ## The three canonical conditions -/

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx (D nm)) (E₁ E₂ : Set (D nm).Event) (l m x y : (D nm).Sigma)
      (e : (D nm).Event),
      VisStrict (D nm) C →
      SupportedOn (D nm) C E₁ → SupportedOn (D nm) C E₂ →
      WeaklyClosed (D nm) C E₁ → WeaklyClosed (D nm) C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn (D nm) C (E₁ ∪ E₂) e →
      IsCanOn (D nm) C (E₁ ∩ E₂) l →
      IsCanOn (D nm) C (downset C e \ {e}) m →
      IsCanOn (D nm) C (E₁ \ {e}) x →
      IsCanOn (D nm) C E₂ y →
      (D nm).merge l ((D nm).merge m x ((D nm).do_ m e)) y
        = (D nm).merge m ((D nm).merge l x y) ((D nm).do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  generalize (D nm).do_ m e = c
  change (x ∪ c) ∪ y = (x ∪ y) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx (D nm)) (E₁ E₂ : Set (D nm).Event)
      (x₀ x₁ x₂ m : (D nm).Sigma) (e : (D nm).Event),
      VisStrict (D nm) C →
      SupportedOn (D nm) C E₁ → SupportedOn (D nm) C E₂ →
      WeaklyClosed (D nm) C E₁ → WeaklyClosed (D nm) C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn (D nm) C (E₁ ∪ E₂) e →
      IsCanOn (D nm) C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn (D nm) C (downset C e \ {e}) m →
      IsCanOn (D nm) C (E₁ \ {e}) x₁ →
      IsCanOn (D nm) C (E₂ \ {e}) x₂ →
      (D nm).merge ((D nm).merge m x₀ ((D nm).do_ m e))
          ((D nm).merge m x₁ ((D nm).do_ m e))
          ((D nm).merge m x₂ ((D nm).do_ m e))
        = (D nm).merge m ((D nm).merge x₀ x₁ x₂) ((D nm).do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  generalize (D nm).do_ m e = c
  change (x₁ ∪ c) ∪ (x₂ ∪ c) = (x₁ ∪ x₂) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx (D nm)) (U : Set (D nm).Event) (A B : (D nm).Sigma) (e : (D nm).Event),
      VisStrict (D nm) C →
      SupportedOn (D nm) C U → WeaklyClosed (D nm) C U →
      e ∈ U → MaximalOn (D nm) C U e →
      IsCanOn (D nm) C (U \ {e}) A →
      IsCanOn (D nm) C (downset C e \ {e}) B →
      (D nm).merge B A ((D nm).do_ B e) = (D nm).do_ A e := by
  letI : EventOrder (D nm).toMRDTSig.toUpdateSig := Interface.rcOrder (D nm)
  intro C U A B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting (all_commute nm) C e) hB]
  change A ∪ ((∅ : St) ∪ delta e.op.id e.op.payload)
    = A ∪ delta e.op.id e.op.payload
  ext z; simp

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn (D nm) (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm nm
  vc2_merge_init := fun C E s _ => vc2_merge_init nm C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute nm C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta nm C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute nm C E₁ E₂ x₀ x₁ x₂ m e

/-- **Everything the metatheory consumes.** -/
theorem obligations : Obligations (D nm) :=
  Obligations.ofCommuting (laws nm) (all_commute nm) (joinLaws nm)

end LeanProofs1.Implementations.NotionCore
