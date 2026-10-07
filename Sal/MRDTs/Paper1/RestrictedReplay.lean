import Sal.MRDTs.Framework.MergeLaws

/-!
# Uniform-law adapter for an operation-level conflict policy

This earlier adapter assumes uniform event exactness to reuse the existing
replay and Join proofs. Under that assumption its `loOn` agrees with concrete
noncommutation, including in the absorber clause. The intended event-guarded
contract is in `GuardedReplay`; its metatheory must use `paperOrder` directly.
The uniform adapter and its negative results do not classify guarded policies.
-/

namespace Sal.MRDTs.Paper1
open Foundation
open Classical

structure OperationPolicy (Update : Type) where
  before : Update → Update → Prop

namespace OperationPolicy

noncomputable def lift {D : UpdateSig} (P : OperationPolicy D.AppOp) : ReplayPolicy D where
  order a b := if P.before a.op b.op then .Fst_then_snd
    else if P.before b.op a.op then .Snd_then_fst else .Either

@[simp] theorem lift_rc_iff {D : UpdateSig} (P : OperationPolicy D.AppOp)
    (a b : Op D.AppOp) :
    @UpdateSig.rc D P.lift a b ↔ P.before a.op b.op := by
  by_cases hab : P.before a.op b.op
  · simp [UpdateSig.rc, ReplayPolicy.Before, lift, hab]
  · by_cases hba : P.before b.op a.op <;>
      simp [UpdateSig.rc, ReplayPolicy.Before, lift, hab, hba]

end OperationPolicy

structure RestrictedLaws (D : UpdateSig) (P : OperationPolicy D.AppOp) : Prop where
  noncomm_exact : ∀ a b : Op D.AppOp,
    ¬ D.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op
  no_chain : ∀ a b c, ¬ (P.before a b ∧ P.before b c)
  conditional_commutation :
    ∀ (s : D.State) (a b c : Op D.AppOp) (between : List (Op D.AppOp)),
    P.before a.op b.op → ¬ D.commutes b c →
    D.update (applySeq D (D.update (D.update s b) a) between) c =
      D.update (applySeq D (D.update (D.update s a) b) between) c

namespace RestrictedLaws

theorem replayLaws {D : UpdateSig} {P : OperationPolicy D.AppOp}
    (L : RestrictedLaws D P) : @ReplayLaws D P.lift := by
  letI : ReplayPolicy D := P.lift
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    rcases (L.noncomm_exact a b).mp h with h | h
    · exact Or.inl ((P.lift_rc_iff a b).mpr h)
    · exact Or.inr ((P.lift_rc_iff b a).mpr h)
  · apply rcAcyclic_of_noRcChain
    intro a b c h
    apply L.no_chain a.op b.op c.op
    exact ⟨(P.lift_rc_iff a b).mp h.1, (P.lift_rc_iff b c).mp h.2⟩
  · intro s a b c between _ _ _ hab hbc
    apply L.conditional_commutation s a b c between
    · exact (P.lift_rc_iff a b).mp hab
    · exact (L.noncomm_exact b c).mpr
        (hbc.elim (fun h => Or.inl ((P.lift_rc_iff b c).mp h))
          (fun h => Or.inr ((P.lift_rc_iff c b).mp h)))

end RestrictedLaws

/-- Exactly the displayed set-relative relation in the manuscript. -/
def paperOrder {D : UpdateSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) (events : Set (Op D.AppOp)) (a b : Op D.AppOp) : Prop :=
  (C.vis a b ∧ ¬ D.commutes a b) ∨
    (¬ C.vis a b ∧ ¬ C.vis b a ∧ P.before a.op b.op ∧
      ¬ ∃ c ∈ events, C.vis b c ∧ ¬ D.commutes b c)

theorem paperOrder_iff_loOn {D : UpdateSig} {P : OperationPolicy D.AppOp}
    (L : RestrictedLaws D P) (C : ReplayContext D) (events : Set (Op D.AppOp))
    (a b : Op D.AppOp) :
    paperOrder P C events a b ↔ @loOn D P.lift C events a b := by
  simp only [paperOrder, loOn, OperationPolicy.lift_rc_iff, ← L.noncomm_exact]

end Sal.MRDTs.Paper1
