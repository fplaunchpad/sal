import Sal.MRDTs.Instances.MVR
import Sal.MRDTs.Metatheory.Countermodels.TaggedORSet
import Sal.MRDTs.Instances.QueueConditioningSPOT
import Sal.MRDTs.Instances.RcSPOT
import Sal.MRDTs.Instances.FugueMaxBackward
import Sal.MRDTs.Instances.FugueMaxContractSPOT
import Sal.MRDTs.Metatheory.ConditioningSPOT
import Sal.MRDTs.Metatheory.Join.Convergence_CounterModel
import Sal.MRDTs.Metatheory.Join.Assoc_CounterModel
import Sal.MRDTs.Metatheory.Join.HistoricalVCs

/-!
# Negative and partial evidence ledger

These declarations are deliberately excluded from `Production.registry`.
They record refuted client specifications, framework countermodels, focused
`rc` SPOTs, and internal proof signatures that do not yet supply the
complete public package.
-/

namespace Sal.MRDTs.Negative

#check Instances.MVR.replayAdequate
#check Instances.MVR.concurrentState_no_sequential_register
#check Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo
#check Instances.RcSPOT.LWW.old_no_chain_refuted
#check Instances.RcSPOT.ObservedRemove.rc
#check Instances.SidedEmbedRGA.fuguemax_backward_ni
#check Instances.SidedEmbedRGA.FugueMaxContractSPOT.short_reachable
#check Instances.SidedEmbedRGA.FugueMaxContractSPOT.deleted_reachable
#check Instances.SidedEmbedRGA.FugueMaxContractSPOT.weak_guard_accepts_wrong
#check Instances.SidedEmbedRGA.FugueMaxContractSPOT.exact_issuance_not_state_predicate
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient
#check HistoricalGap_not_joinWithPolicy
#check HistoricalVCs24_not_imply_JoinWithPolicy
#check HistoricalVCs24_not_imply_join

end Sal.MRDTs.Negative
