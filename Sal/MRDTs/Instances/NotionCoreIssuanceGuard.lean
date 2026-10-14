import Sal.MRDTs.Instances.NotionCoreMRDTArchive
import Sal.MRDTs.Instances.NotionCoreMachineMint
import Sal.MRDTs.Instances.NotionCoreAllocationClock

/-! Local issuance for ordinary requests. Bootstrap is a separate factory
action; this guard neither permits it as a request nor pretends that a local
empty state establishes global initialization. Source sessions are assigned
independently of Sal timestamps. -/
namespace Sal.MRDTs.Instances.NotionCoreIssuanceGuard
open Sal.MRDTs.Foundation
open NotionCorePayload (Payload Transaction reservation)
open NotionCorePayloadNetwork (State forget gap emit)
open NotionRunAllocation (Session)
open NotionCoreMRDT (D)

def OrdinaryEmits : Payload → Prop
  | .bootstrap _ => False
  | payload => payload.emits = true

def Prepared (state : Finset Transaction) (payload : Payload) : Prop :=
  ∃ document request,
    NotionCoreMachine.replay {} (NotionCoreMRDT.transactions state) = some document ∧
    request.earlyNoop = false ∧
    NotionCoreMachineNetwork.prepareRequest document request = some payload ∧
    OrdinaryEmits payload

def CanIssue (sessions : Replica → Session) (event : Op Transaction)
    (state : Finset Transaction) : Prop :=
  event.op.id.session = sessions event.rep ∧
  0 < event.op.id.counter ∧
  (∀ tx ∈ state, (reservation tx).last < event.op.id.counter) ∧
  Prepared state event.op.payload

def issuance (sessions : Replica → Session) : Issuance D := ⟨CanIssue sessions⟩

theorem ordinary_prepares (network : State) (session : Session) (payload : Payload)
    (ordinary : OrdinaryEmits payload) :
    ∃ draft, NotionCorePayload.prepare (forget network) session payload = some draft := by
  cases payload <;> simp_all [OrdinaryEmits, NotionCorePayload.prepare]

theorem received_archived (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (session : Session) (run : NotionRunAllocation.Run)
    (received : run ∈ (network.allocation.peers session).received) :
    ∃ entry ∈ network.entries, reservation entry.tx = run := by
  have issued := NotionCoreMachineNetwork.issuance_reachable honest
  have published := NotionRunAllocation.reachable_received_published
    (NotionCoreIssuance.allocation_reachable issued) session run received
  rw [← NotionCoreIssuance.record_runs issued] at published
  obtain ⟨record, member, same⟩ := List.mem_map.mp published
  obtain ⟨entry, archived, recordEq⟩ := List.mem_map.mp member
  refine ⟨entry, archived, ?_⟩
  simpa [← recordEq, NotionCorePayloadNetwork.Entry.record, NotionCorePayload.record] using same

/-- A local carrier guard supplies actual request preparation and the later
source counter needed by the concrete allocator. Only structural carrier
correspondence and a witnessed clock are premises. -/
theorem guard_prepares (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (sessions : Replica → Session) (event : Op Transaction) (state : Finset Transaction)
    (stateImage : state = NotionCoreMRDTArchive.carrierFor network
      (network.allocation.peers (sessions event.rep)).received)
    (tight : NotionCoreAllocationClock.Tight (network.allocation.peers (sessions event.rep)))
    (guard : CanIssue sessions event state) :
    ∃ document request draft,
      NotionCoreReconstruction.reconstruct network (sessions event.rep) = some document ∧
      request.earlyNoop = false ∧
      NotionCoreMachineNetwork.prepareRequest document request = some event.op.payload ∧
      NotionCorePayload.prepare (forget network) (sessions event.rep) event.op.payload = some draft ∧
      (network.allocation.peers (sessions event.rep)).clock < event.op.id.counter := by
  obtain ⟨sameSession, positive, fresh, document, request, replayed, nonempty, selected, ordinary⟩ := guard
  obtain ⟨draft, prepared⟩ := ordinary_prepares network (sessions event.rep) event.op.payload ordinary
  refine ⟨document, request, draft, ?_, nonempty, selected, prepared, ?_⟩
  · rw [stateImage, NotionCoreMRDTArchive.transactions_carrierFor network
      (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable honest))] at replayed
    exact replayed
  · apply NotionCoreAllocationClock.counter_above_clock tight _ positive
    intro run received
    obtain ⟨entry, archived, same⟩ := received_archived network honest _ run received
    have stored : entry.tx ∈ state := by
      rw [stateImage, NotionCoreMRDTArchive.carrierFor_membership]
      exact ⟨⟨entry, archived, rfl⟩, by simpa [same] using received⟩
    simpa [same] using fresh entry.tx stored

/-- Every guarded ordinary event is produced by actual source preparation and
allocation after a permitted gap. The resulting honest archive is a conclusion. -/
theorem guard_issues (network : State) (honest : NotionCoreMachineNetwork.Reach network)
    (sessions : Replica → Session) (event : Op Transaction) (state : Finset Transaction)
    (stateImage : state = NotionCoreMRDTArchive.carrierFor network
      (network.allocation.peers (sessions event.rep)).received)
    (tight : NotionCoreAllocationClock.Tight (network.allocation.peers (sessions event.rep)))
    (guard : CanIssue sessions event state) :
    let advanced := gap network (sessions event.rep)
      (event.op.id.counter - ((network.allocation.peers (sessions event.rep)).clock + 1))
    ∃ request, NotionCoreMachineNetwork.issue advanced (sessions event.rep) request =
        some (emit advanced (sessions event.rep) event.op.payload event.op) ∧
      NotionCoreMachineNetwork.Reach (emit advanced (sessions event.rep) event.op.payload event.op) := by
  obtain ⟨document, request, draft, reconstructed, nonempty, selected, prepared, later⟩ :=
    guard_prepares network honest sessions event state stateImage tight guard
  have minted := NotionCoreMachineMint.issue_later network (sessions event.rep) request
    document event.op.payload draft nonempty reconstructed selected prepared event.op.id.counter later
  have reachable := NotionCoreMachineMint.honest_issue_later network honest (sessions event.rep) request
    document event.op.payload draft nonempty reconstructed selected prepared event.op.id.counter later
  refine ⟨request, ?_, ?_⟩
  · simpa only [← guard.1] using minted
  · simpa only [← guard.1] using reachable

#print axioms guard_prepares
#print axioms guard_issues

namespace SPOT
private def create : Transaction := ⟨⟨1,[66,0]⟩,.create none⟩
/-- Empty documents can issue an ordinary create with a source counter
independent of the outer event timestamp; zero source counters are rejected. -/
theorem create_control :
    CanIssue (fun replica => [66,replica]) (77,0,create) ∅ ∧
    ¬ CanIssue (fun replica => [66,replica])
      (77,0,⟨⟨0,[66,0]⟩,.create none⟩) ∅ := by
  constructor
  · refine ⟨rfl, by decide, ?_, {}, .create none, ?_, rfl, rfl, rfl⟩
    · simp
    · simp [NotionCoreMRDT.transactions, NotionCoreMachine.replay]
  · intro guarded
    exact Nat.not_lt_zero _ guarded.2.1
end SPOT

#print axioms SPOT.create_control
end Sal.MRDTs.Instances.NotionCoreIssuanceGuard
