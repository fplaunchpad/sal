import Sal.MRDTs.Paper1.SetWinsMapCertificate

/-! PASS+FAIL source-semantic controls, with distinct issuers for concurrent
branches and hand-derived answers. The overwrite competitor below concerns
our selected read, not every conceivable projection of the source state. -/
namespace Sal.MRDTs.Instances.SetWinsMapSPOT
open Foundation SetWinsMap

/-- Sequential Set accumulates: the selected query returns both values. -/
example : lookup (update (update ∅ (1,0,.set 7 10)) (2,0,.set 7 20)) 7 = {10,20} ∧
    lookup (update (update ∅ (1,0,.set 7 10)) (2,0,.set 7 20)) 7 ≠ {20} := by decide

/-- Delete is effective and clears every value at its key. -/
example : lookup (update (update (update ∅ (1,0,.set 7 10)) (2,0,.set 7 20))
      (3,0,.del 7)) 7 = ∅ ∧
    lookup (update (update (update ∅ (1,0,.set 7 10)) (2,0,.set 7 20))
      (3,0,.del 7)) 7 ≠ {10,20} := by decide

/-- Concurrent Set wins over Delete, while the ancestor value stays deleted. -/
example : lookup (merge {(1,(7,10))}
      (update {(1,(7,10))} (2,0,.del 7))
      (update {(1,(7,10))} (3,1,.set 7 20))) 7 = {20} ∧
    lookup (merge {(1,(7,10))}
      (update {(1,(7,10))} (2,0,.del 7))
      (update {(1,(7,10))} (3,1,.set 7 20))) 7 ≠ {10,20} ∧
    lookup (merge {(1,(7,10))}
      (update {(1,(7,10))} (2,0,.del 7))
      (update {(1,(7,10))} (3,1,.set 7 20))) 7 ≠ ∅ := by decide

/-- Concurrent values both survive; merge is neither input projection. -/
example : merge ∅ (update ∅ (1,0,.set 7 10)) (update ∅ (2,1,.set 7 20)) =
      {(1,(7,10)),(2,(7,20))} ∧
    merge ∅ (update ∅ (1,0,.set 7 10)) (update ∅ (2,1,.set 7 20)) ≠
      update ∅ (1,0,.set 7 10) ∧
    merge ∅ (update ∅ (1,0,.set 7 10)) (update ∅ (2,1,.set 7 20)) ≠
      update ∅ (2,1,.set 7 20) := by decide

/-- The ancestor is material to survivor merge. -/
example : merge {(1,(7,10))} ∅ {(1,(7,10))} = ∅ ∧
    merge ∅ ∅ {(1,(7,10))} ≠ ∅ := by decide

/-- Deleting another key preserves this lookup and has an effect there. -/
example : lookup (update {(1,(7,10)),(2,(8,20))} (3,0,.del 8)) 7 = {10} ∧
    lookup (update {(1,(7,10)),(2,(8,20))} (3,0,.del 8)) 8 ≠ {20} := by decide

/-- The independent language also accumulates sequential values. -/
example : Sal.MRDTs.Paper1.SetWinsMap.spec.admits
      [.update (9,0,.set 7 10),.update (2,0,.set 7 20),.query 7 {10,20}] ∧
    ¬ Sal.MRDTs.Paper1.SetWinsMap.spec.admits
      [.update (9,0,.set 7 10),.update (2,0,.set 7 20),.query 7 {20}] := by
  change Sal.MRDTs.Paper1.SetWinsMap.model.toSpec.admits
      (Sal.MRDTs.Paper1.DeterministicSpec.updateLabels [(9,0,Action.set 7 10),(2,0,Action.set 7 20)] ++ [.query 7 {10,20}]) ∧
    ¬ Sal.MRDTs.Paper1.SetWinsMap.model.toSpec.admits
      (Sal.MRDTs.Paper1.DeterministicSpec.updateLabels [(9,0,Action.set 7 10),(2,0,Action.set 7 20)] ++ [.query 7 {20}])
  rw [Sal.MRDTs.Paper1.DeterministicSpec.updates_query_iff,
    Sal.MRDTs.Paper1.DeterministicSpec.updates_query_iff]
  decide
end Sal.MRDTs.Instances.SetWinsMapSPOT
