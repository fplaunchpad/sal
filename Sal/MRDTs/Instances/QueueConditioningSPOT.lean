import Sal.MRDTs.Instances.QueueCertificates

/-!
# Mergeable-queue sequential-witness audit

Two replicas can observe the same two-element queue and concurrently dequeue
the same head tag.  Both issuer guards pass.  The merged implementation removes
that named tag once, but a plain FIFO replay performs two pops.  This is a
checked obstruction to upgrading the existing replay theorem to FIFO
RA-linearizability without an additional exactly-once dequeue protocol or a
different sequential specification.
-/

namespace Sal.MRDTs.Instances.Queue.ConditioningSPOT

open Sal.MRDTs.Foundation

def enqA : Op QOp := (1, 0, .enq 10)
def enqB : Op QOp := (2, 0, .enq 20)
def deqA : Op QOp := (3, 1, .deq 1)
def deqB : Op QOp := (4, 2, .deq 1)

def shared : QState :=
  applySeq Q.toCRDTSig Q.init [enqA, enqB]

/-- PASS: each replica may mint its dequeue at the shared origin state. -/
example : qApplicable deqA shared := by
  simp [qApplicable, shared, enqA, enqB, deqA, applySeq, Q, qUpdate, qTags]

example : qApplicable deqB shared := by
  simp [qApplicable, shared, enqA, enqB, deqB, applySeq, Q, qUpdate, qTags]

/-- The named-delete implementation retains the second element after both
concurrent dequeues are replayed. -/
example :
    (applySeq Q.toCRDTSig Q.init [enqA, enqB, deqA, deqB]).map Prod.snd = [20] := by
  decide

example :
    (applySeq Q.toCRDTSig Q.init [enqA, enqB, deqB, deqA]).map Prod.snd = [20] := by
  decide

/-- The independent FIFO specification performs two pops and reaches the
empty queue in either possible ordering of the dequeues. -/
example : spec.run [enqA, enqB, deqA, deqB] = [] := by
  rfl

example : spec.run [enqA, enqB, deqB, deqA] = [] := by
  rfl

/-- FAIL controls: neither causally admissible dequeue ordering refines the
plain FIFO observation. -/
example :
    (applySeq Q.toCRDTSig Q.init [enqA, enqB, deqA, deqB]).map Prod.snd ≠
      spec.run [enqA, enqB, deqA, deqB] := by decide

example :
    (applySeq Q.toCRDTSig Q.init [enqA, enqB, deqB, deqA]).map Prod.snd ≠
      spec.run [enqA, enqB, deqB, deqA] := by decide

/-- Named checked obstruction used by the public certificate ledger. -/
theorem duplicate_dequeue_not_fifo :
    (applySeq Q.toCRDTSig Q.init [enqA, enqB, deqA, deqB]).map Prod.snd = [20] ∧
    spec.run [enqA, enqB, deqA, deqB] = [] := by
  exact ⟨by decide, rfl⟩

#print axioms duplicate_dequeue_not_fifo

end Sal.MRDTs.Instances.Queue.ConditioningSPOT
