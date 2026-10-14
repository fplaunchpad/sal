import Sal.MRDTs.Instances.NotionCoreProtocol
import Sal.MRDTs.Instances.NotionCoreMRDTClient
import Sal.MRDTs.Instances.NotionCoreMachineGenesisControl

/-! A distinguished checked research protocol entry. Its certificates retain
explicit factory/ordinary issuance and canonical recursive-base reachability.
It is not a PackagedMRDT and does not extend the production VerifiedMRDT list.
The implementation is the typed public-demo core, not production Notion or a
whole-program JavaScript extraction. Merge-block/formatting are outside scope. -/
namespace Sal.MRDTs.Research.NotionCoreLedger
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances
open Sal.MRDTs.Instances.NotionCorePayload (Transaction)
open Sal.MRDTs.Instances.NotionCorePayloadNetwork (State)
open Sal.MRDTs.Instances.NotionRunAllocation (Session)
open Sal.MRDTs.Instances.NotionCoreArchiveEvents (Event)
open Sal.MRDTs.Instances.NotionCoreMRDT (D)
open Sal.MRDTs.Instances.NotionCoreMRDTClient (IssuedTransaction peerCarrier)

/-- All allocated versions have the same witness for enumeration, selected
order, specification visibility, and the implementation's actual query. -/
def VersionsCorrect : Prop :=
  ∀ (sessions : Replica → Session) (initialLift : Transaction → Event)
    (config : Configuration D) (network : State) (lift : Transaction → Event),
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift config network lift →
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec config

def HeadsCorrect : Prop :=
  ∀ (sessions : Replica → Session) (initialLift : Transaction → Event)
    (config : Configuration D) (network : State) (lift : Transaction → Event),
    Function.Injective sessions → NotionCoreProtocol.Reach sessions initialLift config network lift →
    EventSpecificationRALinearizable D (commutingPolicy Transaction) NotionCoreMRDT.spec config

def InsertEffect : Prop :=
  ∀ (network : State) (_honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (_reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (_materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (_name : source.id = NotionCoreMachine.blockName block)
    (index : Nat) (atoms : List Nat) (_nonempty : atoms ≠ [])
    (_bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica),
    ∃ tx, IssuedTransaction network peer (.insert block index atoms) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
            (NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks))

def SplitEffect : Prop :=
  ∀ (network : State) (_honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (_reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (_materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (_name : source.id = NotionCoreMachine.blockName block)
    (index : Nat) (_bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica),
    ∃ tx target, IssuedTransaction network peer (.split block index) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index),
            (target,(NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks))

def EraseEffect : Prop :=
  ∀ (network : State) (_honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (_reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (_materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (_name : source.id = NotionCoreMachine.blockName block)
    (start stop : Nat) (_nonempty : start < stop)
    (_bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica),
    ∃ tx, IssuedTransaction network peer (.erase block start stop) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
            (NotionCoreSpec.text source.project.slots).drop stop)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks))

/-- The ledger stores exact proofs, rather than strings naming a raw signature
or a storage-only certificate. Local effects retain the real issued request. -/
structure CheckedProtocolEntry where
  name : String
  fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction) NotionCoreMRDT.representation NotionCoreMRDT.scheme
  versions : VersionsCorrect
  heads : HeadsCorrect
  insertEffect : InsertEffect
  splitEffect : SplitEffect
  eraseEffect : EraseEffect
  factory : NotionCoreProtocol.Reach NotionCoreMachineGenesisControl.sessions
    (fun _ => NotionCoreMachineGenesisControl.factoryEvent)
    NotionCoreMachineGenesisControl.factoryConfig (NotionCorePayloadNetwork.seeded [97,98])
    (NotionCoreMachineExecution.extendLift (fun _ => NotionCoreMachineGenesisControl.factoryEvent)
      (NotionCorePayload.bootstrap [97,98]) NotionCoreMachineGenesisControl.factoryEvent)

noncomputable def entry : CheckedProtocolEntry where
  name := "notion-typed-core-protocol"
  fiveVCs := NotionCoreMRDT.fiveVCs
  versions := fun _ _ _ _ _ injective reachable => NotionCoreProtocol.versions_witness injective reachable
  heads := fun _ _ _ _ _ injective reachable => NotionCoreProtocol.specification_ra injective reachable
  insertEffect := NotionCoreMRDTClient.insert_effect
  splitEffect := NotionCoreMRDTClient.split_effect
  eraseEffect := NotionCoreMRDTClient.erase_effect
  factory := NotionCoreMachineGenesisControl.protocol_factory

/-- Separate from Production.registry, whose eighteen exact VerifiedMRDT
packages retain their existing public contract. -/
noncomputable def registry : List CheckedProtocolEntry := [entry]
example : registry.length = 1 := rfl

namespace TypeGate
example : True := by
  fail_if_success
    have wrong : VerifiedMRDT D := entry
  trivial
example : True := by
  fail_if_success
    have wrong := PackagedMRDT.of "notion-typed-core" entry
  trivial
end TypeGate

#print axioms entry
#print axioms NotionCoreProtocol.specification_ra
#print axioms NotionCoreMRDTClient.insert_effect
#print axioms NotionCoreMRDTClient.split_effect
#print axioms NotionCoreMRDTClient.erase_effect
#print axioms NotionCoreMachineGenesisControl.protocol_factory
end Sal.MRDTs.Research.NotionCoreLedger
