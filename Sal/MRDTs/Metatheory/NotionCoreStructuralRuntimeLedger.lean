import Sal.MRDTs.Metatheory.NotionCoreLedger
import Sal.MRDTs.Instances.NotionCoreStructuralMRDT
import Sal.MRDTs.Instances.NotionCoreRuntimeEndToEnd
import Sal.MRDTs.Instances.NotionCoreRuntimeMain

/-! Checked structural and native refinements of the same honest typed-core
protocol. The original independent history language, factory and positional
client remain authoritative. This is a distinguished research certificate,
not a new VerifiedMRDT package or a whole-program JavaScript correspondence. -/
namespace Sal.MRDTs.Research.NotionCoreStructuralRuntimeLedger
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances
open Sal.MRDTs.Instances.NotionCorePayload (Transaction)

structure CheckedEntry where
  source : NotionCoreLedger.CheckedProtocolEntry
  structuralFiveVCs : @Raw.MergeVCs NotionCoreStructuralMRDT.D
    (commutingPolicy Transaction)
    (NotionCoreStructuralVC.representation NotionCoreStructuralMRDT.query)
    (NotionCoreStructuralVC.scheme NotionCoreStructuralMRDT.query)
  renderer : NotionCoreStructuralHistory.ClosedQueryAgreement NotionCoreStructuralMRDT.query
  versions : ∀ {sessions initialLift C network lift},
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift C network lift →
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec
      (NotionCoreStructuralExecution.mapConfig NotionCoreStructuralMRDT.query C)
  heads : ∀ {sessions initialLift C network lift},
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift C network lift →
    EventSpecificationRALinearizable NotionCoreStructuralMRDT.D (commutingPolicy Transaction)
      NotionCoreMRDT.spec
      (NotionCoreStructuralExecution.mapConfig NotionCoreStructuralMRDT.query C)
  execution : ∀ {sessions initialLift C network lift},
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift C network lift →
    (labeledTSV NotionCoreStructuralMRDT.D
      (canonicalVirtualMergeBase NotionCoreStructuralMRDT.D)).ReachableFrom
      (initConfig NotionCoreStructuralMRDT.D)
      (NotionCoreStructuralExecution.mapConfig NotionCoreStructuralMRDT.query C)
  empty : NotionCoreRuntimeEngine.Refines NotionCoreRuntimeEngine.empty
  receipt : ∀ {state next : NotionCoreRuntimeEngine.State},
    NotionCoreRuntimeEngine.Refines state → ∀ tx : Transaction,
    NotionCoreRuntimeEngine.receive state tx = .ok next → NotionCoreRuntimeEngine.Refines next
  merge : ∀ {left right next : NotionCoreRuntimeEngine.State},
    NotionCoreRuntimeEngine.Refines left → NotionCoreRuntimeEngine.Refines right →
    NotionCoreRuntimeEngine.merge left right = .ok next → NotionCoreRuntimeEngine.Refines next
  honestMerge : ∀ (network : NotionCorePayloadNetwork.State),
    NotionCoreMachineNetwork.Reach network → ∀ left right : NotionCoreRuntimeEngine.State,
    NotionCoreRuntimeEngine.Refines left → NotionCoreRuntimeEngine.Refines right →
    (∀ tx ∈ left.metadata.archive, tx ∈ network.entries.map (·.tx)) →
    (∀ tx ∈ right.metadata.archive, tx ∈ network.entries.map (·.tx)) →
    ∃ next, NotionCoreRuntimeEngine.merge left right = .ok next ∧ NotionCoreRuntimeEngine.Refines next
  registeredQuery : ∀ (state : NotionCoreRuntimeEngine.State),
    NotionCoreRuntimeEngine.Refines state → ∀ {sessions initialLift C network lift},
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift C network lift →
    ∀ (v : Version) (archive : Finset Transaction) (events : Set (Op Transaction)),
    C.ver v = some (archive,events) → state.metadata.archive.toFinset = archive →
    NotionCoreRuntimeAdapter.observeState state.core = NotionCoreMRDT.D.query archive ()
  loadClosedVersion : ∀ (network : NotionCorePayloadNetwork.State),
    NotionCoreMachineNetwork.Reach network → ∀ version : List NotionRunAllocation.Run,
    NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version →
    ∀ txs : List Transaction,
    txs.toFinset = (NotionCoreReconstruction.transactionsFor network version).toFinset →
    ∃ state, NotionCoreRuntimeEngine.receiveMany NotionCoreRuntimeEngine.empty txs = .ok state ∧
      NotionCoreRuntimeEngine.Refines state ∧ state.metadata.archive.toFinset = txs.toFinset ∧
      NotionCoreRuntimeAdapter.observeState state.core =
        (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
          NotionCoreMachine.render)

noncomputable def entry : CheckedEntry where
  source := NotionCoreLedger.entry
  structuralFiveVCs := NotionCoreStructuralMRDT.fiveVCs
  renderer := NotionCoreStructuralMRDT.renderer
  versions := NotionCoreStructuralMRDT.versions_witness
  heads := NotionCoreStructuralMRDT.specification_ra
  execution := NotionCoreStructuralMRDT.operational_reach
  empty := NotionCoreRuntimeEngine.empty_refines
  receipt := NotionCoreRuntimeEngine.receive_refines
  merge := NotionCoreRuntimeEngine.merge_refines
  honestMerge := NotionCoreRuntimeHonestProgress.merge_honest
  registeredQuery := NotionCoreRuntimeTheorem.registered_query
  loadClosedVersion := NotionCoreRuntimeEndToEnd.load_closed_version

#print axioms entry
end Sal.MRDTs.Research.NotionCoreStructuralRuntimeLedger
