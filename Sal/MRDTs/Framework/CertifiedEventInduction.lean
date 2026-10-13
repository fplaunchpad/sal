import Sal.MRDTs.Framework.Certificates

/-! Induction on issuer causal origins. The callback sees only earlier events
in the actual issuance replay; no completed invariant or certificate is assumed. -/
namespace Sal.MRDTs.Foundation

theorem issued_event_induction {D : MRDTSig} (C : Configuration D)
    (guard : Op D.AppOp → D.State → Prop)
    (issued : ∀ e ∈ C.events, ∃ past : List (Op D.AppOp),
      listPermOf past {a ∈ C.events | C.vis a e} ∧
      guard e (applySeq D.toUpdateSig D.init past))
    (P : Op D.AppOp → Prop)
    (step : ∀ e past, e ∈ C.events →
      listPermOf past {a ∈ C.events | C.vis a e} →
      guard e (applySeq D.toUpdateSig D.init past) →
      (∀ a ∈ past, P a) → P e) : ∀ e ∈ C.events, P e := by
  have main : ∀ t, ∀ e : Op D.AppOp, e.1 = t → e ∈ C.events → P e := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro e time eligible
      obtain ⟨past, perm, localGuard⟩ := issued e eligible
      apply step e past eligible perm localGuard
      intro a member
      have prior := (perm.2 a).mp member
      exact ih a.1 (by rw [← time]; exact C.causal_mono prior.2) a rfl prior.1
  exact fun e eligible => main e.1 e rfl eligible

end Sal.MRDTs.Foundation
