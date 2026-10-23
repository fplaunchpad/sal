import Sal.MRDTs.Instances.NotionCoreRichAtomicCounterexample
import Sal.MRDTs.Instances.NotionCoreFormattingPlannerSPOT
import Sal.MRDTs.Instances.NotionCoreFormattingEvolution

/-! Build gate for the rich formatting investigation. The five VCs prove
carrier convergence. The reachable counterexample refutes uniform atomic
selection refinement for per-segment priorities; this is not an RA certificate
and does not replace the verified plain editing protocol.
-/
namespace Sal.MRDTs.Research.NotionFormattingLedger
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances

structure CheckedObstruction where
  fiveVCs : @Raw.MergeVCs NotionCoreRichMRDT.D
    (commutingPolicy NotionCoreRichPayload.Transaction)
    NotionCoreRichMRDT.representation NotionCoreRichMRDT.scheme
  reachable : NotionCoreRichNetwork.Reach NotionCoreRichAtomicCounterexample.final
  observation : NotionCoreRichAtomicCounterexample.carrierFlags = some [true,false,false,true,true]
  noAtomicHistory : ∀ (document : NotionCoreSpec.Document)
    (events : List NotionCoreFormattingAtomicSpec.HistoryEvent),
    NotionCoreRichAtomicCounterexample.carrierFlags ≠
      some (NotionCoreFormattingAtomicSpec.flags
        (NotionCoreFormattingAtomicSpec.history (NotionCoreFormattingSpec.plain document) events))

noncomputable def entry : CheckedObstruction where
  fiveVCs := NotionCoreRichMRDT.fiveVCs
  reachable := NotionCoreRichAtomicCounterexample.final_reachable
  observation := NotionCoreRichAtomicCounterexample.actual_carrier_read.1
  noAtomicHistory := NotionCoreRichAtomicCounterexample.no_atomic_carrier_history

#check NotionCoreFormattingPlanner.planToggle_refines
#check NotionCoreRichNetwork.new_annotations_fresh
#check NotionCoreRichMRDT.convergence_ordinary
#check NotionCoreRichMRDT.convergence_recursive
#check NotionCoreRichAtomicCounterexample.actual_visible_identity_control
#print axioms entry
#print axioms NotionCoreRichAtomicCounterexample.actual_visible_identity_control
end Sal.MRDTs.Research.NotionFormattingLedger
