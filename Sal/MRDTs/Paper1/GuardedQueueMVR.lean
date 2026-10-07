import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.ObservationalObstructions
import Sal.MRDTs.Instances.QueueCertificates

/-! Corrected event-guarded reassessment of the production queue and compact
MVR. Both still obstruct every operation-only guarded law bundle, including
raw equality and the complete future-query model. These are policy-interface
obstructions, not failures of the production event-sensitive certificates.
-/
namespace Sal.MRDTs.Paper1.GuardedQueueMVR
open Foundation AbstractMRDT

namespace Queue
open Instances.Queue PolicyObstructions.Queue

def third : Op QOp := (3,2,.enq 7)

/-- Distinct timestamps and replicas remove the diagonal exactness argument,
but no-chain still forbids the forced enqueue payload self-edge. -/
theorem no_laws (A : Model Q) :
    ¬ ∃ P : OperationPolicy QOp, Guarded.Laws A P := by
  rintro ⟨P,h⟩
  have conflict := (h.noncomm_exact left right (by change 1 ≠ 2; decide) (by change 0 ≠ 1; decide)).mp
    (ObservationalObstructions.Queue.noncommute A)
  have self : P.before (QOp.enq 7) (QOp.enq 7) := by
    simpa only [left,right,Op.op,or_self] using conflict
  exact h.no_chain left right third (by change 1 ≠ 2; decide) (by change 2 ≠ 3; decide) ⟨self,self⟩

theorem no_raw_laws : ¬ ∃ P : OperationPolicy QOp, GuardedReplay.Laws Q.toUpdateSig P := by
  rintro ⟨P,h⟩
  exact no_laws (Raw.model Q) ⟨P,Raw.laws h⟩

/-- All three obstruction enqueues are issuable from the empty origin. The
PASS+FAIL query witness retains fresh tags and exposes opposite FIFO heads. -/
theorem control :
    qApplicable left [] ∧ qApplicable right [] ∧ qApplicable third [] ∧
    distinctOps (D := Q.toUpdateSig) left right ∧ left.rep ≠ right.rep ∧
    Q.query (Q.update (Q.update [] left) right) () = some (1,7) ∧
    Q.query (Q.update (Q.update [] right) left) () = some (2,7) ∧
    Q.query (Q.update (Q.update [] left) right) () ≠
      Q.query (Q.update (Q.update [] right) left) () := by
  refine ⟨?_,?_,?_,?_,?_,ObservationalObstructions.Queue.query_control⟩
  all_goals simp [qApplicable,left,right,third,qTags,distinctOps,Op.time,Op.rep]
end Queue

namespace MVR
open Instances.MVRLive PolicyObstructions.MVR
open Instances.MVR (MVROp)

/-- Both pairs meet the corrected exactness guards. Changing only timestamps
changes commutation while preserving both operation payloads. -/
theorem no_laws (A : Model D) :
    ¬ ∃ P : OperationPolicy MVROp, Guarded.Laws A P := by
  rintro ⟨P,h⟩
  have conflict := (h.noncomm_exact birth overwrite (by change 1 ≠ 2; decide) (by change 0 ≠ 1; decide)).mp
    (ObservationalObstructions.MVR.noncommute A)
  have invalid := (h.noncomm_exact unrelatedBirth unrelatedOverwrite
    (by change 3 ≠ 4; decide) (by change 0 ≠ 1; decide)).mpr conflict
  exact invalid (of_state_commutes unrelated_commute)

theorem no_raw_laws : ¬ ∃ P : OperationPolicy MVROp, GuardedReplay.Laws D.toUpdateSig P := by
  rintro ⟨P,h⟩
  exact no_laws (Raw.model D) ⟨P,Raw.laws h⟩

/-- The witnesses are each issuable at explicit legal origin states; the
commuting pair's overwrite observes tag 1, not the unrelated birth's tag 3.
These origin guards do not assert a concurrent execution construction. -/
theorem origin_control :
    canIssue birth ∅ ∧ canIssue overwrite {(1,10)} ∧
    canIssue unrelatedBirth ∅ ∧ canIssue unrelatedOverwrite {(1,10)} ∧
    distinctOps (D := D.toUpdateSig) birth overwrite ∧ birth.rep ≠ overwrite.rep ∧
    distinctOps (D := D.toUpdateSig) unrelatedBirth unrelatedOverwrite ∧
      unrelatedBirth.rep ≠ unrelatedOverwrite.rep := by
  simp [canIssue,birth,overwrite,unrelatedBirth,unrelatedOverwrite,distinctOps,Op.time,Op.rep,Instances.MVR.overwrites]

/-- Hand-derived PASS+FAIL: observed tag 1 is removed after its birth, whereas
reversing those effects resurrects value 10. The metadata-shifted pair commutes. -/
theorem control (A : Model D) :
    Commutes A unrelatedBirth unrelatedOverwrite ∧ ¬ Commutes A birth overwrite ∧
    birth.op = unrelatedBirth.op ∧ overwrite.op = unrelatedOverwrite.op ∧
    10 ∉ Instances.MVR.queryValues (update (update ∅ birth) overwrite) ∧
    10 ∈ Instances.MVR.queryValues (update (update ∅ overwrite) birth) := by
  obtain ⟨hc,hn,he₁,he₂⟩ := ObservationalObstructions.MVR.metadata_control A
  exact ⟨hc,hn,he₁,he₂,ObservationalObstructions.MVR.query_control⟩
end MVR

#print axioms Queue.no_laws
#print axioms Queue.no_raw_laws
#print axioms MVR.no_laws
#print axioms MVR.no_raw_laws
#print axioms Queue.control
#print axioms MVR.origin_control
end Sal.MRDTs.Paper1.GuardedQueueMVR
