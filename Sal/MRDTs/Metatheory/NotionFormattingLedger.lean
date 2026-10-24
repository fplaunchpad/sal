import Sal.MRDTs.Instances.NotionCoreRichAtomicCounterexample
import Sal.MRDTs.Instances.NotionCoreFormattingPlannerSPOT
import Sal.MRDTs.Instances.NotionCoreFormattingEvolution
import Sal.MRDTs.Instances.NotionCoreRichProtocolCertificateSPOT
import Sal.MRDTs.Instances.NotionCoreRichPlainConservation
import Sal.MRDTs.Instances.NotionCoreRichSequentialSelectionSPOT

/-! Checked rich-text results: the old per-segment obstruction, the repaired
shared-priority protocol's five VCs and positive independent history/RA proof,
derived caller selection and plain-query conservation. These specialised
protocol entries do not add a uniform runtime package to the registry.
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

structure CheckedRichProtocol where
  fiveVCs : @Raw.MergeVCs NotionCoreRichProtocolCarrier.D
    (commutingPolicy NotionCoreRichPayload.Transaction)
    NotionCoreRichProtocolCarrier.representation NotionCoreRichProtocolCarrier.scheme
  histories : NotionCoreRichProtocolTransport.HonestHistoryFor
  versions : ∀ {sessions initialLift config network lift}, Function.Injective sessions →
    NotionCoreRichProtocol.Reach sessions initialLift config network lift →
    VersionsWitness (commutingPolicy NotionCoreRichPayload.Transaction)
      NotionCoreRichSequentialInputs.spec config
  nonempty : EventSpecificationRALinearizable NotionCoreRichProtocolCarrier.D
    (commutingPolicy NotionCoreRichPayload.Transaction) NotionCoreRichSequentialInputs.spec
      NotionCoreRichProtocolNonempty.config
  observation : NotionCoreRichProtocolCarrier.D.query NotionCoreRichProtocolNonempty.log () =
    some (NotionCoreRichProtocolNonempty.expected true) ∧
      NotionCoreRichProtocolCarrier.D.query NotionCoreRichProtocolNonempty.log () ≠ none ∧
      NotionCoreRichProtocolCarrier.D.query NotionCoreRichProtocolNonempty.log () ≠ some [] ∧
      NotionCoreRichProtocolCarrier.D.query NotionCoreRichProtocolNonempty.log () ≠
        some (NotionCoreRichProtocolNonempty.expected false)

noncomputable def repaired : CheckedRichProtocol where
  fiveVCs := NotionCoreRichProtocolCarrier.fiveVCs
  histories := NotionCoreRichCanonicalHistory.honest_history
  versions := NotionCoreRichProtocolCertificate.versions_witness
  nonempty := NotionCoreRichProtocolCertificateSPOT.specification_ra
  observation := NotionCoreRichProtocolNonempty.query_control

#check NotionCoreFormattingPlanner.planToggle_refines
#check NotionCoreRichNetwork.new_annotations_fresh
#check NotionCoreRichMRDT.convergence_ordinary
#check NotionCoreRichMRDT.convergence_recursive
#check NotionCoreRichAtomicCounterexample.actual_visible_identity_control
#print axioms entry
#print axioms NotionCoreRichAtomicCounterexample.actual_visible_identity_control
#check NotionCoreRichProtocolCertificate.specification_ra
#check NotionCoreRichProtocolCertificate.selection_exact
#check NotionCoreRichProtocolCertificate.issued_format_effect
#check NotionCoreRichProtocolCertificate.query_total
#check NotionCoreRichPlainConservation.registered_version
#print axioms repaired
#print axioms NotionCoreRichProtocolCertificate.selection_exact
#print axioms NotionCoreRichProtocolCertificate.issued_format_effect
#print axioms NotionCoreRichPlainConservation.registered_version
end Sal.MRDTs.Research.NotionFormattingLedger
