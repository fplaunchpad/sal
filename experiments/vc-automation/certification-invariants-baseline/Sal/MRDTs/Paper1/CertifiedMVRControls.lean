import Sal.MRDTs.Paper1.CertifiedMVRReplay

/-! Mint eligibility and replay readiness have different purposes. Concurrent
empty-origin writes keep their carried overwrite lists during replay; replay
does not ask the original issuer to regenerate those operations. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Controls
open Foundation Instances.MVRLive

abbrev left : Event := (1,0,.write 10 [])
abbrev right : Event := (2,1,.write 20 [])

/-- PASS+FAIL: both empty-origin writes are issuable and both replay orders
are legal, concretely commuting, and retain both values. Regenerating the
second write at the first write's state violates the original issuance guard. -/
theorem mint_not_reissuance :
    canIssue left ∅ ∧ canIssue right ∅ ∧
    ¬ canIssue right (update ∅ left) ∧
    spec.Legal [left,right] ∧ spec.Legal [right,left] ∧
    update (update ∅ left) right = {(1,10),(2,20)} ∧
    update (update ∅ right) left = {(1,10),(2,20)} ∧
    update (update ∅ left) right ≠ {(2,20)} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide
  · decide
  · decide
  · constructor
    · decide
    · intro pre e post eq n target
      have mem : e ∈ [left,right] := by rw [eq]; simp
      rcases List.mem_cons.mp mem with rfl | mem
      · cases target
      · have er : e = right := by simpa using mem
        subst e
        cases target
  · constructor
    · decide
    · intro pre e post eq n target
      have mem : e ∈ [right,left] := by rw [eq]; simp
      rcases List.mem_cons.mp mem with rfl | mem
      · cases target
      · have el : e = left := by simpa using mem
        subst e
        cases target
  · decide
  · decide
  · decide

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Controls
