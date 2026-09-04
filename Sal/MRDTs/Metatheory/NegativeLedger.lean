import Sal.MRDTs.Instances.MVR
import Sal.MRDTs.Instances.QueueConditioningSPOT
import Sal.MRDTs.Instances.InteractionSPOT
import Sal.MRDTs.Instances.AegisSheetRetentionSPOT
import Sal.MRDTs.Instances.AegisSheetMaterialised
import Sal.MRDTs.Instances.AegisSheetMaterialisedJoin
import Sal.MRDTs.Instances.AegisSheetMaterialisedCertificates
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
#check Instances.AegisSheet.RetentionSPOT.dead_position_load_bearing_for_ranges
#check Instances.AegisSheet.RetentionSPOT.eager_reanchoring_refuted
#check Instances.AegisSheet.RetentionSPOT.dead_position_load_bearing_for_revival
#check Instances.AegisSheet.RetentionSPOT.remove_wins_refuted
#check Instances.AegisSheet.RetentionSPOT.undo_revives_later_removal
#check Instances.AegisSheet.Materialised.M
#check Instances.AegisSheet.Materialised.canon
#check Instances.AegisSheet.Materialised.ObservationEquivalence
#check Instances.AegisSheet.Materialised.UpdatePreservesCanon
#check Instances.AegisSheet.Materialised.JoinTarget
#check Instances.AegisSheet.Materialised.m_join_at
#check Instances.AegisSheet.Materialised.joinTarget
#check Instances.AegisSheet.Materialised.generation
#check Instances.AegisSheet.Materialised.issuanceEstablishes
#check Instances.AegisSheet.Materialised.replayAdequacy
#check Instances.SidedEmbedRGA.fmGeneration
#check Instances.SidedEmbedRGA.fmReplayAdequacy
#check Instances.SidedEmbedRGA.fuguemax_replay_witness
#check Foundation.convergence_over_backward_closed_subsets_false
#check Foundation.binaryLaws_insufficient
#check HistoricalGap_not_joinWithPolicy
#check HistoricalVCs24_not_imply_JoinWithPolicy
#check HistoricalVCs24_not_imply_join

end Sal.MRDTs.Negative
