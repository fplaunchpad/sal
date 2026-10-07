import Sal.MRDTs.Paper1.RestrictedReplay
import Sal.MRDTs.Instances.Queue
import Sal.MRDTs.Instances.MVRLive

/-! Concrete obstructions to the paper's operation-only exact-noncommutation
policy. These refute the restricted interface, not the broader production
correctness theorems, which retain event-sensitive replay policies. -/
namespace Sal.MRDTs.Paper1.PolicyObstructions
open Foundation

namespace Queue
open Instances.Queue

def left : Op QOp := (1,0,.enq 7)
def right : Op QOp := (2,1,.enq 7)

theorem same_payload_noncommute : ¬ Q.toUpdateSig.commutes left right := by
  intro h
  have he := h ([] : QState)
  have hn : qUpdate (qUpdate [] left) right ≠ qUpdate (qUpdate [] right) left := by decide
  exact hn he

/-- PASS+FAIL: the same application enqueue commutes with itself as an event,
but two fresh instances of that application enqueue do not commute. -/
theorem diagonal_control : Q.toUpdateSig.commutes left left ∧
    ¬ Q.toUpdateSig.commutes left right :=
  ⟨fun _ => rfl, same_payload_noncommute⟩

/-- Exactness alone cannot be operation-only: its diagonal answer would have
to classify both the commuting and noncommuting concrete pairs identically. -/
theorem no_operation_exact_policy :
    ¬ ∃ P : OperationPolicy QOp, ∀ a b : Op QOp,
      ¬ Q.toUpdateSig.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op := by
  rintro ⟨P, exactness⟩
  have conflict := (exactness left right).mp same_payload_noncommute
  have diagonal : ¬ Q.toUpdateSig.commutes left left :=
    (exactness left left).mpr conflict
  exact diagonal (fun _ => rfl)

theorem no_restricted_policy : ¬ ∃ P : OperationPolicy QOp, RestrictedLaws Q.toUpdateSig P := by
  rintro ⟨P, laws⟩
  exact no_operation_exact_policy ⟨P,laws.noncomm_exact⟩
end Queue

namespace MVR
open Instances.MVRLive
open Instances.MVR

def birth : Event := (1,0,.write 10 [])
def overwrite : Event := (2,1,.write 20 [1])
def unrelatedBirth : Event := (3,0,.write 10 [])
def unrelatedOverwrite : Event := (4,1,.write 20 [1])

theorem overwrite_noncommute : ¬ D.toUpdateSig.commutes birth overwrite := by
  intro h
  have hn : update (update ∅ birth) overwrite ≠ update (update ∅ overwrite) birth := by decide
  exact hn (h (∅ : State))

theorem unrelated_commute : D.toUpdateSig.commutes unrelatedBirth unrelatedOverwrite := by
  intro s
  apply Finset.ext
  intro p
  obtain ⟨ts,v⟩ := p
  simp [D, update, Instances.MVR.clientStep, writeValue, overwrites,
    unrelatedBirth, unrelatedOverwrite, or_assoc, or_left_comm, or_comm]
  grind

/-- PASS+FAIL: changing only event timestamps changes concrete commutation,
while both application operation payloads remain identical. -/
theorem metadata_control : D.toUpdateSig.commutes unrelatedBirth unrelatedOverwrite ∧
    ¬ D.toUpdateSig.commutes birth overwrite ∧
    birth.op = unrelatedBirth.op ∧ overwrite.op = unrelatedOverwrite.op :=
  ⟨unrelated_commute, overwrite_noncommute, rfl, rfl⟩

theorem no_operation_exact_policy :
    ¬ ∃ P : OperationPolicy MVROp, ∀ a b : Event,
      ¬ D.toUpdateSig.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op := by
  rintro ⟨P, exactness⟩
  have conflict := (exactness birth overwrite).mp overwrite_noncommute
  have invalid := (exactness unrelatedBirth unrelatedOverwrite).mpr conflict
  exact invalid unrelated_commute

theorem no_restricted_policy : ¬ ∃ P : OperationPolicy MVROp, RestrictedLaws D.toUpdateSig P := by
  rintro ⟨P,laws⟩
  exact no_operation_exact_policy ⟨P,laws.noncomm_exact⟩
end MVR

#print axioms Queue.no_restricted_policy
#print axioms MVR.no_restricted_policy
end Sal.MRDTs.Paper1.PolicyObstructions
