import Sal.MRDTs.Paper1.Automation.FiniteSetSimulation

/-! Hand-derived controls for the shared tagged-set bridge. The projection
forgets identifiers, but each surviving element still needs an actual record. -/
namespace Sal.MRDTs.Paper1.Automation.SequentialBridgeControls

def replaceOne : SetAction (Nat × Nat) Nat :=
  .add (1, 9) (fun p => decide (p.1 ≠ 1))

theorem replacement_valid : replaceOne.Valid Prod.fst := by
  intro p different
  simpa [replaceOne] using different

example : (replaceOne.records Prod.fst {(1, 2), (2, 3)}).image Prod.fst = {1, 2} := by
  rw [SetAction.image_records _ _ _ replacement_valid]
  decide

example : (replaceOne.records Prod.fst {(1, 2), (2, 3)}).image Prod.fst ≠ {1} := by
  decide

/- Dropping tags for another element violates the finite premise; this cannot
be repaired by the added element's replacement witness. -/
def dropOthers : SetAction (Nat × Nat) Nat := .add (1, 9) (fun _ => false)

example : ¬ dropOthers.Valid Prod.fst := by
  intro valid
  have bad := valid (2, 3) (by decide)
  cases bad

example : (dropOthers.records Prod.fst {(1, 2), (2, 3)}).image Prod.fst ≠ {1, 2} := by
  decide

/- Removing an element drops all its tags, while preserving other elements. -/
example : ((SetAction.remove 1 : SetAction (Nat × Nat) Nat).records Prod.fst
    {(1, 2), (1, 9), (2, 3)}).image Prod.fst = {2} := by decide

example : ((SetAction.remove 1 : SetAction (Nat × Nat) Nat).records Prod.fst
    {(1, 2), (1, 9), (2, 3)}).image Prod.fst ≠ {1, 2} := by decide

#print axioms replacement_valid
end Sal.MRDTs.Paper1.Automation.SequentialBridgeControls
