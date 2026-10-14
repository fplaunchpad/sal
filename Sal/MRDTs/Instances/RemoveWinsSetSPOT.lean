import Sal.MRDTs.Paper1.RemoveWinsSetCertificate
import Sal.MRDTs.Instances.RemoveWinsSetReadSide

/-! Hand-derived traces on exactly the source's two elements. Fin 2 value zero
names source element 1, and value one names source element 2. Every block pins
an observable rival or a tempting degenerate implementation. -/
namespace Sal.MRDTs.Instances.RemoveWinsSetSPOT
open Foundation RemoveWinsSet
abbrev K := Fin 2
def one : K := 0
def two : K := 1
abbrev init : State K := initial K

def added : State K := step init (1,0,.add one)
def removed : State K := step init (2,1,.remove one)
def raced : State K := merge init added removed

/-- Genesis denotes the empty abstract set, despite two concrete tags. -/
example : init = {(one,0),(two,0)} ∧ view init = ∅ ∧ view init ≠ Finset.univ := by decide

/-- Add removes the genesis tag only for its requested element. -/
example : added = {(two,0)} ∧ query added one = true ∧ query added two = false ∧
    added ≠ init := by decide

/-- Concurrent Add and Rem from distinct issuers select Rem. Neither input
is the merge result, and the add-wins rival gives the wrong answer. -/
example : raced = {(two,0),(one,2)} ∧ query raced one = false ∧
    query raced one ≠ true ∧ raced ≠ added ∧ raced ≠ removed := by decide

/-- A causally later Add clears every observed removal tag. -/
example : query (step raced (3,0,.add one)) one = true ∧
    step raced (3,0,.add one) = {(two,0)} ∧
    step raced (3,0,.add one) ≠ raced := by decide

/-- Different-element Add requests are independent. -/
example : view (merge init added (step init (2,1,.add two))) = {one,two} ∧
    view (merge init added (step init (2,1,.add two))) ≠ view added ∧
    order (1,0,.add one) (2,1,.add two) = .Either := by decide

/-- Both concurrent Rem tags survive; retaining one is a projection bug. -/
example : merge added (step added (2,0,.remove one)) (step added (3,1,.remove one)) =
      {(two,0),(one,2),(one,3)} ∧
    merge added (step added (2,0,.remove one)) (step added (3,1,.remove one)) ≠
      step added (2,0,.remove one) := by decide

/-- Reusing timestamp zero collides with genesis. The concrete merge really
misreports presence; the positive-time issuance guard rejects this event. -/
example : merge init added (step init (0,1,.remove one)) = added ∧
    query (merge init added (step init (0,1,.remove one))) one = true ∧
    query raced one = false ∧
    ¬ (Paper1.RemoveWinsSet.generation K).CanIssue (0,1,.remove one) init ∧
    (Paper1.RemoveWinsSet.generation K).CanIssue (2,1,.remove one) init := by
  simp only [Paper1.RemoveWinsSet.generation,Op.time]
  decide

/-- Sequential Add/Rem has the natural-set verdict and rejects deletion as
an observational no-op. Metadata is discarded by the independent machine. -/
example : (Paper1.RemoveWinsSet.spec K).admits
      [.update (9,0,.add one),.update (2,0,.remove one),.query one false] ∧
    ¬ (Paper1.RemoveWinsSet.spec K).admits
      [.update (9,0,.add one),.update (2,0,.remove one),.query one true] := by
  change (Paper1.RemoveWinsSet.model K).toSpec.admits
      (Paper1.DeterministicSpec.updateLabels [(9,0,Update.add one),(2,0,Update.remove one)] ++ [.query one false]) ∧
    ¬ (Paper1.RemoveWinsSet.model K).toSpec.admits
      (Paper1.DeterministicSpec.updateLabels [(9,0,Update.add one),(2,0,Update.remove one)] ++ [.query one true])
  rw [Paper1.DeterministicSpec.updates_query_iff,Paper1.DeterministicSpec.updates_query_iff]
  simp [Paper1.RemoveWinsSet.model,Paper1.RemoveWinsSet.decode,Op.op]

/-- The source policy has a real edge, in exactly the remove-wins direction. -/
example : order (1,0,.add one) (2,1,.remove one) = .Fst_then_snd ∧
    order (2,1,.remove one) (1,0,.add one) = .Snd_then_fst ∧
    order (1,0,.add one) (2,1,.remove one) ≠ .Either := by decide

end Sal.MRDTs.Instances.RemoveWinsSetSPOT
