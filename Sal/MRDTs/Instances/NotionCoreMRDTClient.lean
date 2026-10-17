import Sal.MRDTs.Instances.NotionCoreMRDTArchive
import Sal.MRDTs.Instances.NotionCoreMachineInsertEffects
import Sal.MRDTs.Instances.NotionCoreMachineEraseIssueEffects
import Sal.MRDTs.Instances.NotionCoreMachineSplitEffects
import Sal.MRDTs.Instances.NotionCoreMachineMergeEffects

/-! Exact transport from actual client issuance to the concrete MRDT update
and query. Existing local visible-effect theorems can use this equality; no
additional document interpreter or independent client generator is introduced. -/
namespace Sal.MRDTs.Instances.NotionCoreMRDTClient
open Sal.MRDTs.Foundation
open NotionCorePayload (Transaction Payload)
open NotionCorePayloadNetwork (State forget emit)
open NotionRunAllocation (Session)
open NotionCoreMRDT (D)

noncomputable def peerCarrier (network : State) (peer : Session) : Finset Transaction :=
  NotionCoreMRDTArchive.carrierFor network (network.allocation.peers peer).received

theorem peer_observe (network : State) (honest : NotionCoreMachineNetwork.Reach network) (peer : Session) :
    D.query (peerCarrier network peer) () =
      (NotionCoreReconstruction.reconstruct network peer >>= NotionCoreMachine.render) :=
  NotionCoreMRDTArchive.observe_carrierFor network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable honest)) _

theorem emitted_carrier (network : State) (honest : NotionCorePayloadNetwork.Reach network)
    (peer : Session) (payload : Payload) (tx : Transaction)
    (prepared : NotionCorePayload.prepare (forget network) peer payload = some tx)
    (nextHonest : NotionCorePayloadNetwork.Reach (emit network peer payload tx))
    (time : Timestamp) (replica : Replica) :
    D.update (peerCarrier network peer) (time,replica,tx) =
      peerCarrier (emit network peer payload tx) peer := by
  have appended := NotionCoreMachineInsertEffects.emitted_transactions_append
    network honest peer payload tx prepared nextHonest
  change insert tx (NotionCoreReconstruction.transactions network peer).toFinset =
    (NotionCoreReconstruction.transactions (emit network peer payload tx) peer).toFinset
  rw [appended]
  simp

def IssuedTransaction (network : State) (peer : Session)
    (request : NotionCoreMachineNetwork.Request) (tx : Transaction) : Prop :=
  ∃ document payload,
    NotionCoreReconstruction.reconstruct network peer = some document ∧
    NotionCoreMachineNetwork.prepareRequest document request = some payload ∧
    NotionCorePayload.prepare (forget network) peer payload = some tx

/-- A successful source request determines an actual emitted transaction whose
MRDT insertion produces precisely the source issuer's next carrier and query. -/
theorem issued_update (network next : State) (honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (request : NotionCoreMachineNetwork.Request)
    (issued : NotionCoreMachineNetwork.issue network peer request = some next)
    (time : Timestamp) (replica : Replica) :
    ∃ tx, IssuedTransaction network peer request tx ∧
      D.update (peerCarrier network peer) (time,replica,tx) = peerCarrier next peer ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        (NotionCoreReconstruction.reconstruct next peer >>= NotionCoreMachine.render) := by
  have nextHonest : NotionCoreMachineNetwork.Reach next := .request peer request honest issued
  have noSkip : request.earlyNoop = false := by
    cases skip : request.earlyNoop <;> simp_all [NotionCoreMachineNetwork.issue]
  cases reconstructed : NotionCoreReconstruction.reconstruct network peer with
  | none => simp [NotionCoreMachineNetwork.issue, noSkip, reconstructed] at issued
  | some document =>
    cases selected : NotionCoreMachineNetwork.prepareRequest document request with
    | none => simp [NotionCoreMachineNetwork.issue, noSkip, reconstructed, selected] at issued
    | some payload =>
      cases prepared : NotionCorePayload.prepare (forget network) peer payload with
      | none => simp [NotionCoreMachineNetwork.issue, noSkip, reconstructed, selected, prepared] at issued
      | some tx =>
        have equal : emit network peer payload tx = next := by
          simpa [NotionCoreMachineNetwork.issue, noSkip, reconstructed, selected, prepared] using issued
        subst next
        have carrier := emitted_carrier network
          (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable honest))
          peer payload tx prepared
          (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextHonest)) time replica
        exact ⟨tx, ⟨document,payload,reconstructed,selected,prepared⟩, carrier,
          by rw [carrier]; exact peer_observe _ nextHonest peer⟩

#print axioms emitted_carrier
#print axioms issued_update

theorem insert_effect (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (name : source.id = NotionCoreMachine.blockName block)
    (alive : source.alive = true) (index : Nat) (atoms : List Nat) (nonempty : atoms ≠ [])
    (bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica) :
    ∃ tx, IssuedTransaction network peer (.insert block index atoms) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
            (NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨next, issued, effect⟩ := NotionCoreMachineInsertEffects.honest_insert_request_effect
    network honest peer document reconstructed before afterBlocks source materialized block name alive index atoms
    nonempty bound
  obtain ⟨tx, prepared, _, query⟩ := issued_update network next honest peer _ issued time replica
  exact ⟨tx, prepared, query.trans effect⟩

theorem split_effect (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (name : source.id = NotionCoreMachine.blockName block)
    (alive : source.alive = true) (index : Nat)
    (bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica) :
    ∃ tx target, IssuedTransaction network peer (.split block index) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index),
            (target,(NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨next, target, issued, effect⟩ := NotionCoreMachineSplitEffects.honest_split_request_effect
    network honest peer document reconstructed before afterBlocks source materialized block name alive index bound
  obtain ⟨tx, prepared, _, query⟩ := issued_update network next honest peer _ issued time replica
  exact ⟨tx, target, prepared, query.trans effect⟩

theorem erase_effect (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : NotionCoreSource.Block)
    (materialized : NotionCoreMachineDocument.materializeDocument document = some (before ++ source :: afterBlocks))
    (block : NotionCorePayload.BlockKey) (name : source.id = NotionCoreMachine.blockName block)
    (start stop : Nat) (nonempty : start < stop)
    (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength document block)
    (time : Timestamp) (replica : Replica) :
    ∃ tx, IssuedTransaction network peer (.erase block start stop) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
            (NotionCoreSpec.text source.project.slots).drop stop)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨next, result, after, issued, _, nextReplay, _, effect⟩ :=
    NotionCoreMachineEraseIssueEffects.honest_issue_erase_effect network honest peer document reconstructed
      before afterBlocks source materialized block name start stop nonempty bound
  obtain ⟨tx, prepared, _, query⟩ := issued_update network next honest peer _ issued time replica
  refine ⟨tx, prepared, ?_⟩
  simpa [nextReplay, effect] using query

/-- The issuer's own merge of a displayed block that is not the first: its
next query shows the previous displayed block's text followed by the merged
block's text, and the merged block is absent from the display. -/
theorem merge_effect (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (peer : Session) (document : NotionCoreMachine.State)
    (reconstructed : NotionCoreReconstruction.reconstruct network peer = some document)
    (before gap afterBlocks : NotionCoreSourceDocument.Document) (target source : NotionCoreSource.Block)
    (materialized : NotionCoreMachineDocument.materializeDocument document =
      some (before ++ target :: gap ++ source :: afterBlocks))
    (targetAlive : target.alive = true) (sourceAlive : source.alive = true)
    (gapDead : ∀ block ∈ gap, block.alive = false)
    (block : NotionCorePayload.BlockKey) (name : source.id = NotionCoreMachine.blockName block)
    (time : Timestamp) (replica : Replica) :
    ∃ tx, IssuedTransaction network peer (.merge block) tx ∧
      D.query (D.update (peerCarrier network peer) (time,replica,tx)) () =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(target.id,NotionCoreSpec.text target.project.slots ++ NotionCoreSpec.text source.project.slots)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨next, issued, effect⟩ := NotionCoreMachineMergeEffects.honest_merge_request_effect
    network honest peer document reconstructed before gap afterBlocks target source materialized
    targetAlive sourceAlive gapDead block name
  obtain ⟨tx, prepared, _, query⟩ := issued_update network next honest peer _ issued time replica
  exact ⟨tx, prepared, query.trans effect⟩

#print axioms merge_effect
#print axioms insert_effect
#print axioms split_effect
#print axioms erase_effect
end Sal.MRDTs.Instances.NotionCoreMRDTClient
