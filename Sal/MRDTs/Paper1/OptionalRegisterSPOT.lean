import Sal.MRDTs.Paper1.OptionalRegisterHistory

namespace Sal.MRDTs.Paper1.OptionalRegisterSPOT
open Foundation Instances.OptionalRegister

/-- Ordinary overwrite and reset in the independent scalar specification. -/
example : OptionalRegister.spec.admits
      [.update (1,0,.set 10),.update (2,0,.set 20),.query () (some 20)] ∧
    ¬ OptionalRegister.spec.admits
      [.update (1,0,.set 10),.update (2,0,.set 20),.query () (some 10)] := by
  change OptionalRegister.model.toSpec.admits
      (DeterministicSpec.updateLabels [(1,0,Action.set 10),(2,0,Action.set 20)] ++ [.query () (some 20)]) ∧
    ¬ OptionalRegister.model.toSpec.admits
      (DeterministicSpec.updateLabels [(1,0,Action.set 10),(2,0,Action.set 20)] ++ [.query () (some 10)])
  rw [DeterministicSpec.updates_query_iff,DeterministicSpec.updates_query_iff]
  decide

example : OptionalRegister.spec.admits
      [.update (1,0,.set 10),.update (2,0,.unset),.query () none] ∧
    ¬ OptionalRegister.spec.admits
      [.update (1,0,.set 10),.update (2,0,.unset),.query () (some 10)] := by
  change OptionalRegister.model.toSpec.admits
      (DeterministicSpec.updateLabels [(1,0,Action.set 10),(2,0,Action.unset)] ++ [.query () none]) ∧
    ¬ OptionalRegister.model.toSpec.admits
      (DeterministicSpec.updateLabels [(1,0,Action.set 10),(2,0,Action.unset)] ++ [.query () (some 10)])
  rw [DeterministicSpec.updates_query_iff,DeterministicSpec.updates_query_iff]
  decide

/-- The source chosen read honors sequential set/unset. -/
example : query (update (update initial (1,0,.set 10)) (2,0,.unset)) = none ∧
    query (update (update initial (1,0,.set 10)) (2,0,.unset)) ≠ some 10 := by decide

/-- Source concurrent Set wins over Unset and has an observable payload. -/
example : query (merge initial (update initial (1,0,.unset))
      (update initial (2,1,.set 20))) = some 20 ∧
    query (merge initial (update initial (1,0,.unset))
      (update initial (2,1,.set 20))) ≠ none := by decide

/-- Distinct-issuer Sets commute concretely; the chosen read takes the greatest
active timestamp, requiring the appropriate scalar-history ordering. -/
example : query (update (update initial (3,0,.set 30)) (1,1,.set 10)) = some 30 ∧
    query (update (update initial (3,0,.set 30)) (1,1,.set 10)) ≠ some 10 := by decide

/-- A later Unset really removes the greatest active payload. -/
example : query (update (update (update initial (3,0,.set 30)) (1,1,.set 10))
      (4,1,.unset)) = none ∧
    query (update (update (update initial (3,0,.set 30)) (1,1,.set 10))
      (4,1,.unset)) ≠ some 30 := by decide

/-- Timestamp ties exercise source averaging; it is not a branch projection. -/
example : (mergePayload (0,0) (3,10) (3,20)).2 = 15 ∧
    (mergePayload (0,0) (3,10) (3,20)).2 ≠ 10 ∧
    (mergePayload (0,0) (3,10) (3,20)).2 ≠ 20 := by decide
end Sal.MRDTs.Paper1.OptionalRegisterSPOT
