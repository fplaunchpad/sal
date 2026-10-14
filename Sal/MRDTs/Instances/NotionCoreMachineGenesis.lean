import Sal.MRDTs.Instances.NotionCoreMachineExecution

/-! Explicit source factory initialization. The empty configuration already
has a concrete source execution partner, and empty forks can precede factory
creation without inventing a global condition inside local issuance. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineGenesis
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCorePayload (Transaction)
open NotionCorePayloadNetwork (initial)
open NotionCoreArchiveEvents (Event)
open NotionCoreMachineExecution (Pair)
open NotionCoreMRDT (D)
open NotionRunAllocation (Session)

theorem initial_events : (initConfig D).events = ∅ := by
  ext event
  constructor
  · rintro ⟨replica, events, head, member⟩
    by_cases zero : replica = 0
    · subst replica
      simp [Configuration.headEvents, headEventsFrom, initConfig] at head
      subst events
      exact member
    · simp [Configuration.headEvents, headEventsFrom, initConfig, zero] at head
  · exact fun impossible => impossible.elim

theorem initial_pair (sessions : Replica → Session) (injective : Function.Injective sessions)
    (lift : Transaction → Event) : Pair (initConfig D) initial sessions lift := by
  refine ⟨.init, injective, ?_, ?_, ?_⟩
  · constructor
    · intro tx member
      simp [NotionCoreArchiveEvents.archive, initial] at member
    · intro event
      simp [initial_events, NotionCoreArchiveEvents.archive, initial]
    · intro left right member
      simp [NotionCoreArchiveEvents.archive, initial] at member
  · constructor
    · intro replica events head entry member
      simp [initial] at member
    · intro replica absent
      rfl
  · intro peer
    exact NotionCoreAllocationClock.empty_tight

#print axioms initial_pair

/-- The factory seed has the same full-run allocation and archive insertion
shape as minting, although ordinary request preparation rejects bootstrap. -/
theorem bootstrap_emission (atoms : List Nat) :
    NotionCorePayloadNetwork.seeded atoms =
      NotionCorePayloadNetwork.emit initial [65] (.bootstrap atoms)
        (NotionCorePayload.bootstrap atoms) := rfl

theorem bootstrap_reservation (atoms : List Nat) :
    NotionCorePayload.reservation (NotionCorePayload.bootstrap atoms) =
      NotionRunAllocation.reserve (initial.allocation.peers [65]) [65]
        (NotionCorePayload.Payload.bootstrap atoms).width := rfl

theorem bootstrap_clocks (atoms : List Nat) :
    ∀ peer, NotionCoreAllocationClock.Tight
      ((NotionCorePayloadNetwork.seeded atoms).allocation.peers peer) := by
  intro peer
  by_cases seedPeer : peer = [65]
  · subst peer
    simpa [NotionCorePayloadNetwork.seeded, NotionRunAllocation.issue] using
      NotionCoreAllocationClock.mint_tight
        NotionCoreAllocationClock.empty_tight.1 [65]
        (NotionCorePayload.Payload.bootstrap atoms).width (NotionCorePayload.width_positive _)
  · simpa [NotionCorePayloadNetwork.seeded, NotionRunAllocation.issue, seedPeer] using
      NotionCoreAllocationClock.empty_tight

theorem gap_zero (network : NotionCorePayloadNetwork.State) (session : Session) :
    NotionCorePayloadNetwork.gap network session 0 = network := by
  have unchanged : NotionRunAllocation.advance (network.allocation.peers session) 0 =
      network.allocation.peers session := by
    cases network.allocation.peers session
    simp [NotionRunAllocation.advance]
  simp [NotionCorePayloadNetwork.gap, NotionRunAllocation.skip, unchanged]

/-- The factory is an actual Sal application from the empty source archive.
Empty forks may already exist. Its exact source reservation and honest seeded
network are constructed; the resulting archive coupling is not a premise. -/
theorem factory_pair {config next : Configuration D}
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config initial sessions lift)
    (time : Timestamp) (sender : Replica) (atoms : List Nat)
    (factorySession : sessions sender = [65])
    (raw : Step D config (.apply time sender (NotionCorePayload.bootstrap atoms)) next) :
    Pair next (NotionCorePayloadNetwork.seeded atoms) sessions
      (NotionCoreMachineExecution.extendLift lift (NotionCorePayload.bootstrap atoms)
        (time,sender,NotionCorePayload.bootstrap atoms)) := by
  have allocated : NotionCorePayload.reservation (NotionCorePayload.bootstrap atoms) =
      NotionRunAllocation.reserve
        ((NotionCorePayloadNetwork.gap initial (sessions sender) 0).allocation.peers (sessions sender))
        (sessions sender) (NotionCorePayload.bootstrap atoms).payload.width := by
    rw [gap_zero, factorySession]
    exact bootstrap_reservation atoms
  have honest : NotionCoreMachineNetwork.Reach
      (NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap initial (sessions sender) 0)
        (sessions sender) (NotionCorePayload.bootstrap atoms).payload (NotionCorePayload.bootstrap atoms)) := by
    rw [gap_zero, factorySession]
    exact .bootstrap atoms
  have pairedNext := NotionCoreMachineExecution.emit_preserves initial sessions lift paired
    time sender (NotionCorePayload.bootstrap atoms) raw 0 allocated honest
  simpa only [gap_zero, factorySession, ← bootstrap_emission] using pairedNext

#print axioms bootstrap_clocks
#print axioms factory_pair
end Sal.MRDTs.Instances.NotionCoreMachineGenesis
