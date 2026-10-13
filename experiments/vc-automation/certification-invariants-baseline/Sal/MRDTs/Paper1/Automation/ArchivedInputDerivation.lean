import Sal.MRDTs.Paper1.Automation.CommonVerification

/-! Structural projection of archive issuance and replay evidence from the
unchanged representation. No completed verification theorem is consulted. -/
macro "derive_archived_adapter " representation:ident " with " issuance:term
    " unfolding " "[" defs:ident,* "]" : tactic => `(tactic| (
  simp only [$[$defs:ident],*] at $representation:ident
  refine ⟨?_, ?_⟩
  · apply ($issuance)
    exact ($representation).1
  · dsimp [Sal.MRDTs.Paper1.Automation.ArchivedOrderedRecords.ReplayEvidence]
    aesop))

macro "derive_archived_input " kit:term " with " issuance:term
    " unfolding " "[" defs:ident,* "]" : tactic => `(tactic| (
  refine Sal.MRDTs.Paper1.Automation.CommonVerification.Input.archived $kit ?_ ?_
  · intros; rfl
  · intro C H s rep
    derive_archived_adapter rep with $issuance unfolding [$defs,*]))
