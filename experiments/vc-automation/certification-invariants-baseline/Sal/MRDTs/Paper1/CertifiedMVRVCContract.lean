import Sal.MRDTs.Paper1.CertifiedMVRReplay
import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.RawVC
open Foundation Classical ConcreteMRDT
set_option maxHeartbeats 1500000
open Instances.MVRLive

abbrev policy := emptyPolicy

def scheme (C : ReplayContext D.toUpdateSig) : MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

/-- Execution eligibility and finite represented history, without a closure
restriction: the generic induction supplies arbitrary finite supported subsets.
Closure remains an independent guard on each merge VC. -/
def representation : Representation D := fun context E s =>
  ∃ C : Configuration D, CertifiedExecution D issuance C ∧ C.replayContext = context ∧
    E ⊆ C.events ∧ E.Finite ∧ Represents E s

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.RawVC
