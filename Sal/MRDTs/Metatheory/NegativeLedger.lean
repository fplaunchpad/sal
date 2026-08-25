import Sal.MRDTs.Instances.MVR
import Sal.MRDTs.Instances.QueueConditioningSPOT
import Sal.MRDTs.Instances.InteractionSPOT
import Sal.MRDTs.Instances.FugueMaxRALinearization
import Sal.MRDTs.Metatheory.ConditioningSPOT
import Sal.MRDTs.Metatheory.Join.Convergence_CounterModel
import Sal.MRDTs.Metatheory.Join.Assoc_CounterModel

/-!
# Negative and partial evidence ledger

These declarations are deliberately excluded from `Production.registry`.
They record refuted client specifications, framework countermodels, focused
interaction SPOTs, and internal proof signatures that do not yet supply the
complete public package.
-/

namespace Sal.MRDTs.Negative

#check Instances.MVR.replayVerified
#check Instances.MVR.concurrentState_no_sequential_register
#check Instances.Queue.replayVerified
#check Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo
#check Instances.InteractionSPOT.LWW.old_no_chain_refuted
#check Instances.InteractionSPOT.AddWins.interaction
#check Instances.SidedEmbedRGA.fmGeneration
#check Instances.SidedEmbedRGA.fmConvergence
#check Instances.SidedEmbedRGA.fuguemax_ra_linearizable
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.coreVCs_lattice_insufficient

end Sal.MRDTs.Negative
