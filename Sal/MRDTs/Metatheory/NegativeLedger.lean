import Sal.MRDTs.Instances.MVR
import Sal.MRDTs.Instances.QueueConditioningSPOT
import Sal.MRDTs.Instances.InteractionSPOT
import Sal.MRDTs.Instances.FugueMaxReplay
import Sal.MRDTs.Metatheory.ConditioningSPOT
import Sal.MRDTs.Metatheory.Join.Convergence_CounterModel
import Sal.MRDTs.Metatheory.Join.Assoc_CounterModel
import Sal.MRDTs.Metatheory.Join.HistoricalVCs

/-!
# Negative and partial evidence ledger

These declarations are deliberately excluded from `Production.registry`.
They record refuted client specifications, framework countermodels, focused
interaction SPOTs, and internal proof signatures that do not yet supply the
complete public package.
-/

namespace Sal.MRDTs.Negative

#check Instances.MVR.replayAdequate
#check Instances.MVR.concurrentState_no_sequential_register
#check Instances.Queue.replayAdequate
#check Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo
#check Instances.InteractionSPOT.LWW.old_no_chain_refuted
#check Instances.InteractionSPOT.AddWins.interaction
#check Instances.SidedEmbedRGA.fmGeneration
#check Instances.SidedEmbedRGA.fmReplayAdequacy
#check Instances.SidedEmbedRGA.fuguemax_replay_witness
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient
#check HistoricalGap_not_joinWithPolicy
#check HistoricalVCs24_not_imply_JoinWithPolicy
#check HistoricalVCs24_not_imply_join

end Sal.MRDTs.Negative
