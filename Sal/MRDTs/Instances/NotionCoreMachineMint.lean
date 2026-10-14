import Sal.MRDTs.Instances.NotionCoreMachineNetwork

/-! Clock gaps do not change the reconstructed issuer document. An ordinary
request prepared at that document can therefore mint at any later source
counter. This connects a counter-based issuance guard to the actual issuer. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineMint
open NotionRunAllocation (Session)
open NotionCorePayload (Payload Transaction)
open NotionCorePayloadNetwork (State gap forget emit)
open NotionCoreReconstruction

theorem gap_transactions (network : State) (session peer : Session) (ticks : Nat) :
    transactions (gap network session ticks) peer = transactions network peer := by
  by_cases same : peer = session
  · subst peer
    simp [transactions, gap, NotionRunAllocation.skip, NotionRunAllocation.advance]
  · simp [transactions, gap, NotionRunAllocation.skip, same]

theorem gap_reconstruct (network : State) (session peer : Session) (ticks : Nat) :
    reconstruct (gap network session ticks) peer = reconstruct network peer := by
  simp only [reconstruct, gap_transactions]

theorem prepare_later (network : State) (session : Session) (payload : Payload)
    (draft : Transaction)
    (prepared : NotionCorePayload.prepare (forget network) session payload = some draft)
    (counter : Nat) (later : (network.allocation.peers session).clock < counter) :
    NotionCorePayload.prepare
      (forget (gap network session (counter - ((network.allocation.peers session).clock + 1))))
      session payload = some ⟨⟨counter,session⟩,payload⟩ := by
  have clock : (network.allocation.peers session).clock +
      (counter - ((network.allocation.peers session).clock + 1)) + 1 = counter := by omega
  cases payload <;>
    simp only [NotionCorePayload.prepare] at prepared ⊢
  all_goals try contradiction
  all_goals split at prepared
  all_goals try contradiction
  all_goals simp_all [forget, gap, NotionRunAllocation.skip,
    NotionRunAllocation.advance, NotionRunAllocation.reserve]

theorem issue_later (network : State) (session : Session)
    (request : NotionCoreMachineNetwork.Request) (document : NotionCoreMachine.State)
    (payload : Payload) (draft : Transaction)
    (nonempty : request.earlyNoop = false)
    (reconstructed : reconstruct network session = some document)
    (selected : NotionCoreMachineNetwork.prepareRequest document request = some payload)
    (prepared : NotionCorePayload.prepare (forget network) session payload = some draft)
    (counter : Nat) (later : (network.allocation.peers session).clock < counter) :
    let advanced := gap network session (counter - ((network.allocation.peers session).clock + 1))
    NotionCoreMachineNetwork.issue advanced session request =
      some (emit advanced session payload ⟨⟨counter,session⟩,payload⟩) := by
  dsimp only
  simp [NotionCoreMachineNetwork.issue, nonempty,
    gap_reconstruct, reconstructed, selected,
    prepare_later network session payload draft prepared counter later]

theorem honest_issue_later (network : State)
    (honest : NotionCoreMachineNetwork.Reach network) (session : Session)
    (request : NotionCoreMachineNetwork.Request) (document : NotionCoreMachine.State)
    (payload : Payload) (draft : Transaction)
    (nonempty : request.earlyNoop = false)
    (reconstructed : reconstruct network session = some document)
    (selected : NotionCoreMachineNetwork.prepareRequest document request = some payload)
    (prepared : NotionCorePayload.prepare (forget network) session payload = some draft)
    (counter : Nat) (later : (network.allocation.peers session).clock < counter) :
    let advanced := gap network session (counter - ((network.allocation.peers session).clock + 1))
    NotionCoreMachineNetwork.Reach
      (emit advanced session payload ⟨⟨counter,session⟩,payload⟩) := by
  exact .request session request (.gap session _ honest)
    (issue_later network session request document payload draft nonempty
      reconstructed selected prepared counter later)

#print axioms issue_later
#print axioms honest_issue_later
end Sal.MRDTs.Instances.NotionCoreMachineMint
