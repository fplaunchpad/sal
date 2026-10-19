import Sal.MRDTs.Instances.NotionCoreMachineClientEffects
import Sal.MRDTs.Instances.NotionCoreMachineInsertEffects

/-! The immediate local range deletion effect survives actual issuance and
issuer reconstruction. New emission is proved to append to the issuer's
canonical version; no after-render or after-replay equation is a premise. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineEraseIssueEffects
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSource (Block)

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- A valid nonempty positional erase issues a real transaction and its
issuer's newly reconstructed renderer has the ordinary range effect. -/
theorem honest_issue_erase_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (pre post : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (pre ++ source :: post))
    (block : BlockKey) (name : source.id = blockName block) (start stop : Nat)
    (nonempty : start < stop) (bound : stop ≤ NotionCoreMachineDeleteTotal.visibleLength state block) :
    ∃ next result after,
      NotionCoreMachineNetwork.issue network peer (.erase block start stop) = some next ∧
      NotionCoreMachineNetwork.Reach next ∧
      NotionCoreReconstruction.reconstruct next peer = some result ∧
      materializeDocument result = some after ∧
      render result = some (NotionCoreSpec.view (NotionCoreSourceDocument.project pre) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take start ++
          (NotionCoreSpec.text source.project.slots).drop stop)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project post)) := by
  obtain ⟨groups,result,after,selected,operations,afterMat,rendered,_,_⟩ :=
    NotionCoreMachineClientEffects.honest_erase_effect network reachable peer state reconstructed
      pre post source materialized block name start stop nonempty bound
  have stored := NotionCoreMachineDelete.selectErase_stored state block start stop _ selected
  obtain ⟨next,issued,nextReach⟩ := NotionCoreMachineClientTotal.honest_issue_erase network reachable peer
    block start stop (by simpa [reconstructed] using stored) nonempty (by simpa [reconstructed] using bound)
  have skip : (NotionCoreMachineNetwork.Request.erase block start stop).earlyNoop = false := by
    simp [NotionCoreMachineNetwork.Request.earlyNoop,show start ≠ stop by omega]
  cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) peer (.erase block groups) with
  | none => simp [NotionCoreMachineNetwork.issue,skip,reconstructed,NotionCoreMachineNetwork.prepareRequest,
      selected,reserved] at issued
  | some tx =>
    have nextEq : next = NotionCorePayloadNetwork.emit network peer (.erase block groups) tx := by
      simpa [NotionCoreMachineNetwork.issue,skip,reconstructed,NotionCoreMachineNetwork.prepareRequest,
        selected,reserved] using issued.symm
    have networkReach := NotionCoreCreatorNetwork.payload_reachable
      (NotionCoreMachineNetwork.creator_reachable reachable)
    have emittedReach : NotionCorePayloadNetwork.Reach
        (NotionCorePayloadNetwork.emit network peer (.erase block groups) tx) := by
      rw [← nextEq]
      exact NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextReach)
    have append := NotionCoreMachineInsertEffects.emitted_transactions_append network networkReach peer
      (.erase block groups) tx reserved emittedReach
    have txPayload := NotionCorePayloadNetwork.prepared_payload reserved
    have txOperation : applyTransaction state tx = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,txPayload] using operations
    have afterReplay : NotionCoreReconstruction.reconstruct next peer = some result := by
      unfold NotionCoreReconstruction.reconstruct
      rw [nextEq,append,replay_append]
      change replay {} (NotionCoreReconstruction.transactions network peer) = some state at reconstructed
      rw [reconstructed]
      simp [replay,txOperation]
    exact ⟨next,result,after,issued,nextReach,afterReplay,afterMat,rendered⟩

namespace SPOT
private def seed := NotionCorePayloadNetwork.seeded [97,98]
private def original : Block := ⟨0,0,[⟨(0,.start),[
  ⟨NotionCorePhysicalReplay.address 0 ⟨1,[65]⟩,.text 97 false⟩,
  ⟨NotionCorePhysicalReplay.address 0 ⟨2,[65]⟩,.text 98 false⟩],none⟩]⟩
/-- A real issued deletion reconstructs b in the retained block, rejecting
both the no-op and deletion of the other range. The concrete old input is
kernel checked; the actual after-network is constructed by the proved effect. -/
theorem issued_range_control :
    ∃ next, NotionCoreMachineNetwork.issue seed [65] (.erase .initial 0 1) = some next ∧
      (NotionCoreReconstruction.reconstruct next [65] >>= render) = some [(0,[98])] ∧
      (NotionCoreReconstruction.reconstruct next [65] >>= render) ≠ some [(0,[97,98])] ∧
      (NotionCoreReconstruction.reconstruct next [65] >>= render) ≠ some [(0,[97])] := by
  have current : NotionCoreReconstruction.reconstruct seed [65] =
      some (NotionCoreMachineBootstrap.seeded [97,98]) := by decide +kernel
  have materialized : materializeDocument (NotionCoreMachineBootstrap.seeded [97,98]) =
      some [original] := by decide +kernel
  obtain ⟨next,result,after,issued,_,reconstructed,_,rendered⟩ := honest_issue_erase_effect
    seed (.bootstrap [97,98]) [65] (NotionCoreMachineBootstrap.seeded [97,98]) current
    [] [] original materialized .initial rfl 0 1 (by decide)
    (by decide +kernel)
  refine ⟨next,issued,?_,?_,?_⟩
  all_goals simp [reconstructed,rendered,original,NotionCoreSourceDocument.project,
    NotionCoreSpec.view,NotionCoreSource.Block.project,NotionCoreSource.Block.slots,
    NotionCoreSource.Block.alive,NotionCoreSource.Slice.slots,
    NotionCoreSource.Slice.anchor,NotionCoreSource.Slice.close,NotionCoreSource.Atom.slot,NotionCoreSpec.text]
end SPOT

#print axioms SPOT.issued_range_control
#print axioms honest_issue_erase_effect
end Sal.MRDTs.Instances.NotionCoreMachineEraseIssueEffects
