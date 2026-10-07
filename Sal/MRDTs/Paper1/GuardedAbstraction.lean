import Sal.MRDTs.Paper1.AbstractFormalism
import Sal.MRDTs.Paper1.GuardedConvergence
import Sal.MRDTs.Paper1.GuardedOrder

/-! Guarded observational replay laws and canonicality, stated directly with
semantic paper order. The earlier uniform certificates remain separate. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.Guarded
open Foundation
variable {D : MRDTSig}

structure Laws (A : Model D) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b : Op D.AppOp,
    distinctOps (D := D.toUpdateSig) a b → a.rep ≠ b.rep →
    (¬ Commutes A a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c : Op D.AppOp,
    distinctOps (D := D.toUpdateSig) a b → distinctOps (D := D.toUpdateSig) b c →
    ¬ (P.before a.op b.op ∧ P.before b.op c.op)
  conditional_commutation : ∀ s a b c between,
    distinctOps (D := D.toUpdateSig) a b → distinctOps (D := D.toUpdateSig) a c → distinctOps (D := D.toUpdateSig) b c →
    P.before a.op b.op → ¬ Commutes A b c →
    Equivalent A
      (D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) between) c)
      (D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) between) c)

/-- Uniform observational laws are stronger than the guarded requirements. -/
def Laws.ofUniform {A : Model D} {P : OperationPolicy D.AppOp}
    (h : AbstractMRDT.Laws A P) : Laws A P where
  noncomm_exact a b _ _ := h.noncomm_exact a b
  no_chain a b c _ _ := h.no_chain a.op b.op c.op
  conditional_commutation s a b c between _ _ _ :=
    h.conditional_commutation s a b c between

/-- Transport observational laws to equality on the quotient replay algebra. -/
theorem Laws.toReplay {A : Model D} {P : OperationPolicy D.AppOp}
    (h : Laws A P) : GuardedReplay.Laws (algebra A) P := by
  refine ⟨?_, h.no_chain, ?_⟩
  · intro a b distinct different
    rw [commutes_iff]
    exact h.noncomm_exact a b distinct different
  · intro s a b c between hab hac hbc before conflict
    induction s using Quotient.inductionOn with
    | _ s =>
      have hc : ¬ Commutes A b c := fun commute =>
        conflict ((commutes_iff A b c).mpr commute)
      change update A (applySeq (algebra A)
          (observe A (D.update (D.update s b) a)) between) c =
        update A (applySeq (algebra A)
          (observe A (D.update (D.update s a) b)) between) c
      rw [fold_observe, fold_observe, update_observe, update_observe]
      exact Quotient.sound
        (h.conditional_commutation s a b c between hab hac hbc before hc)

/-- A semantic replay witness uses the displayed order directly. -/
def Canonical (A : Model D) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ π : List (Op D.AppOp), listPermOf π E ∧ respects π (order A P C E) ∧
    Equivalent A (applySeq D.toUpdateSig D.init π) s

theorem canonical_congr {A : Model D} {P : OperationPolicy D.AppOp}
    {C : ReplayContext D.toUpdateSig} {E : Set (Op D.AppOp)} {s t : D.State}
    (h : Canonical A P C E s) (same : Equivalent A s t) :
    Canonical A P C E t := by
  obtain ⟨π, hp, hr, hf⟩ := h
  exact ⟨π, hp, hr, equivalent_trans hf same⟩

/-- Two order-respecting replays agree observationally from every initial state. -/
theorem replay_equivalent {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) (s : D.State)
    {π₁ π₂ : List (Op D.AppOp)}
    (hp₁ : listPermOf π₁ E) (hp₂ : listPermOf π₂ E)
    (hr₁ : respects π₁ (order A P C E))
    (hr₂ : respects π₂ (order A P C E)) :
    Equivalent A (applySeq D.toUpdateSig s π₁) (applySeq D.toUpdateSig s π₂) := by
  have resp₁ : respects π₁ (paperOrder P (context A C) E) :=
    hr₁.imp (fun {a b} h edge => h ((order_eq A P C E b a).mpr edge))
  have resp₂ : respects π₂ (paperOrder P (context A C) E) :=
    hr₂.imp (fun {a b} h edge => h ((order_eq A P C E b a).mpr edge))
  have eq := convergence_on_guarded laws.toReplay (C := context A C)
    (observe A s) supported hp₁ hp₂ resp₁ resp₂
  rw [fold_observe, fold_observe] at eq
  exact Quotient.exact eq

/-- Canonicality determines an abstract state even when concrete metadata differs. -/
theorem canonical_equivalent {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) {s t : D.State}
    (hs : Canonical A P C E s) (ht : Canonical A P C E t) : Equivalent A s t := by
  obtain ⟨π₁, hp₁, hr₁, hf₁⟩ := hs
  obtain ⟨π₂, hp₂, hr₂, hf₂⟩ := ht
  exact equivalent_trans (equivalent_symm hf₁)
    (equivalent_trans (replay_equivalent laws C E supported D.init hp₁ hp₂ hr₁ hr₂) hf₂)

theorem canonical_query_unique {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : ∀ e ∈ E, e ∈ C.events) {s t : D.State}
    (hs : Canonical A P C E s) (ht : Canonical A P C E t) (q : D.Query) :
    D.query s q = D.query t q :=
  equivalent_query (canonical_equivalent laws C E supported hs ht) q


/-- Finite supported event sets have a semantic canonical representative. -/
theorem canonical_exists {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (finite : E.Finite) (supported : E ⊆ C.events)
    (trans : ∀ {a b c}, C.vis a b → C.vis b c → C.vis a c)
    (irrefl : ∀ a, ¬ C.vis a a) : ∃ s, Canonical A P C E s := by
  classical
  have hp : listPermOf finite.toFinset.toList E := by
    refine ⟨Finset.nodup_toList _, ?_⟩
    intro a
    simp
  obtain ⟨π, hp, hr⟩ := GuardedReplay.exists_paperOrder_enumeration
    laws.toReplay (C := context A C) trans irrefl supported hp
  refine ⟨applySeq D.toUpdateSig D.init π, π, hp, ?_, equivalent_refl A _⟩
  exact hr.imp (fun {a b} h edge => h ((order_eq A P C E b a).mp edge))

/-- Explicit compatibility with the earlier uniform canonical certificate. -/
theorem canonical_iff_uniform {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : AbstractMRDT.Laws A P) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) (s : D.State) :
    Canonical A P C E s ↔ AbstractMRDT.Canonical A P C E s := by
  exact (AbstractMRDT.canonical_iff laws C E s).symm

end Sal.MRDTs.Paper1.AbstractMRDT.Guarded
