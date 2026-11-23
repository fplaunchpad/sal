import LeanProofs1.Implementations.AegisSheet.Definition
import LeanProofs1.Interface.VCRoute

/-!
# AegisSheet: every verification condition

Section 4's `Laws(D_type)` and Section 5's VC1 to VC5, for the tuple of
`Definition.lean`. `obligations` bundles what the metatheory consumes.

The state is the event set, `do` inserts one event into it, and `merge`
unions the two branches and ignores the ancestor. So every pair of events
commutes **at every state**, with none of the qualifications the embedded
RGA family needs, and `Laws` forces `rc` to be empty. VC1 to VC5 are then
the same set identities the grow-only set proves.

What is **not** proved here is clause 2 of Definition 4, so this row has no
`Certificate.lean` yet. The declarative query of `Definition.lean` has six
components, and showing that it agrees with `specView` on every legal
history is a separate development. The premise it would need is
`HistorySound` rather than `SpecSound`, since `Legal` admits only histories
with increasing timestamps.
-/

namespace LeanProofs1.Implementations.AegisSheet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `do` is a set insertion, so any two events commute at any state. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro S
  change insert e₂.op (insert e₁.op S) = insert e₁.op (insert e₂.op S)
  exact Finset.insert_comm _ _ _

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. -/
theorem rc_non_comm : UniformRcNonComm D := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. -/
theorem cond_comm : UniformCondComm D := fun _ e e' _ _ hb _ =>
  (no_rc_edge e e' hb).elim

/-- **`Laws(D_type)`.** -/
theorem laws : Laws D :=
  ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
   no_rc_chain,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge e e' hb).elim⟩

/-! ## VC1 and VC2

`merge l a b = a ∪ b` ignores the ancestor, so each condition reduces to a
union identity over the event sets. -/

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  change a ∪ b = b ∪ a
  exact Finset.union_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    SupportedOn D C E → IsCanOn D C E s →
    D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  change (∅ : Finset AppOp) ∪ s = s
  exact Finset.empty_union _

/-! ## The three canonical conditions -/

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma) (e : D.Event),
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
  change (x ∪ c) ∪ y = (x ∪ y) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
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
  change (x₁ ∪ c) ∪ (x₂ ∪ c) = (x₁ ∪ x₂) ∪ c
  ext z; simp only [Finset.mem_union]; tauto

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  intro C U A B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting all_commute C e) hB]
  change A ∪ insert e.op (∅ : St) = insert e.op A
  ext z; simp

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-- **Everything the metatheory consumes**: `Laws(D_type)`, the two
unguarded readings it leaves open, VC1 to VC5, and an execution order. -/
theorem obligations : Obligations D :=
  Obligations.ofCommuting laws all_commute joinLaws

end LeanProofs1.Implementations.AegisSheet
