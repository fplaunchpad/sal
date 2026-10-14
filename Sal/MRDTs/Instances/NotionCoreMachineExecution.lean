import Sal.MRDTs.Instances.NotionCoreArchiveEvents
import Sal.MRDTs.Instances.NotionCoreMRDT
import Sal.MRDTs.Instances.NotionCoreMachineSnapshots
import Sal.MRDTs.Instances.NotionCoreMachineMint
import Sal.MRDTs.Instances.NotionCoreAllocationClock

/-! Actual execution coupling from an explicitly initialized factory pair.
The outer genesis authorization is not inferred from a local empty carrier.
These structural simulation statements contain no sequential answer premises. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineExecution
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCorePayload (Transaction reservation)
open NotionCorePayloadNetwork (State Entry)
open NotionCoreArchiveEvents (Event Coupling)
open NotionCoreMRDT (D)
open NotionRunAllocation (Session Run)

/-- Current heads agree with actual whole-run receipts. Unallocated issuer
identities have never been reset: their source peer is genuinely empty. -/
structure HeadMatch (config : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) : Prop where
  receipts : ∀ replica events, config.headEvents replica = some events →
    ∀ entry ∈ network.entries,
      (reservation entry.tx ∈ (network.allocation.peers (sessions replica)).received ↔
        lift entry.tx ∈ events)
  unused : ∀ replica, config.headEvents replica = none →
    network.allocation.peers (sessions replica) = NotionRunAllocation.emptyPeer

structure Pair (config : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) : Prop where
  honest : NotionCoreMachineNetwork.Reach network
  sessionInjective : Function.Injective sessions
  events : Coupling network config.events config.vis lift
  heads : HeadMatch config network sessions lift
  tight : ∀ peer, NotionCoreAllocationClock.Tight (network.allocation.peers peer)

/-- Registering a copy or union of current heads preserves the global event
set. This uses the actual head update, rather than postulating event equality. -/
theorem events_head_update (config next : Configuration D) (replica : Replica)
    (added : Set Event) (update : next.headEvents = updateRep config.headEvents replica added)
    (supported : added ⊆ config.events)
    (retained : ∀ old, config.headEvents replica = some old → old ⊆ added) :
    next.events = config.events := by
  ext event
  constructor
  · rintro ⟨peer,events,head,member⟩
    rw [update] at head
    by_cases same : peer = replica
    · subst peer
      simp [updateRep] at head
      subst events
      exact supported member
    · exact ⟨peer,events,by simpa only [updateRep,if_neg same] using head,member⟩
  · rintro ⟨peer,events,head,member⟩
    by_cases same : peer = replica
    · subst peer
      exact ⟨replica,added,by simp [update,updateRep],retained events head member⟩
    · exact ⟨peer,events,by simpa only [update,updateRep,if_neg same] using head,member⟩

/-- Actual exchange simulates the head event union, regardless of base choice.
The archive and the clocks of other issuer identities are unchanged. -/
theorem heads_exchange_union (config next : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (injective : Function.Injective sessions) (matched : HeadMatch config network sessions lift)
    (target source : Replica) (left right : Set Event)
    (leftHead : config.headEvents target = some left)
    (rightHead : config.headEvents source = some right)
    (updated : next.headEvents = updateRep config.headEvents target (left ∪ right)) :
    HeadMatch next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  constructor
  · intro peer events head entry member
    have archived : entry ∈ network.entries := member
    by_cases same : peer = target
    · subst peer
      simp [updated,updateRep] at head
      subst events
      rw [NotionCoreMachineSnapshots.exchange_received]
      simp only [true_and]
      rw [matched.receipts target left leftHead entry archived,
        matched.receipts source right rightHead entry archived]
      rfl
    · have sessionDifferent : sessions peer ≠ sessions target := fun equal => same (injective equal)
      rw [NotionCoreMachineSnapshots.exchange_other_peer network _ _ _ sessionDifferent]
      apply matched.receipts peer events
      · simpa only [updated,updateRep,if_neg same] using head
      · exact archived
  · intro peer absent
    have different : peer ≠ target := by
      intro equal
      subst peer
      simp [updated,updateRep] at absent
    have oldAbsent : config.headEvents peer = none := by
      simpa only [updated,updateRep,if_neg different] using absent
    rw [NotionCoreMachineSnapshots.exchange_other_peer network _ _ _
      (fun equal => different (injective equal))]
    exact matched.unused peer oldAbsent

/-- A fresh raw fork copies the actual current source receipts, even when the
source head is empty. No destination clock/receipt reset is performed. -/
theorem heads_exchange_fork (config next : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (injective : Function.Injective sessions) (matched : HeadMatch config network sessions lift)
    (target source : Replica) (events : Set Event)
    (empty : config.headEvents target = none)
    (sourceHead : config.headEvents source = some events)
    (updated : next.headEvents = updateRep config.headEvents target events) :
    HeadMatch next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  constructor
  · intro peer selected head entry member
    have archived : entry ∈ network.entries := member
    by_cases same : peer = target
    · subst peer
      simp [updated,updateRep] at head
      subst selected
      rw [NotionCoreMachineSnapshots.exchange_received]
      simp only [true_and]
      rw [matched.unused target empty]
      simp only [NotionRunAllocation.emptyPeer,List.not_mem_nil,false_or]
      exact matched.receipts source events sourceHead entry archived
    · rw [NotionCoreMachineSnapshots.exchange_other_peer network _ _ _ (fun equal => same (injective equal))]
      apply matched.receipts peer selected
      · simpa only [updated,updateRep,if_neg same] using head
      · exact archived
  · intro peer absent
    have different : peer ≠ target := by
      intro equal
      subst peer
      simp [updated,updateRep] at absent
    rw [NotionCoreMachineSnapshots.exchange_other_peer network _ _ _ (fun equal => different (injective equal))]
    exact matched.unused peer (by simpa only [updated,updateRep,if_neg different] using absent)

/-- Every actual raw fork preserves an initialized pair using honest source
exchange. Its fresh replica identity selects an unused source allocator. -/
theorem fork_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : Step D config (.fork target source) next) :
    Pair next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  cases step with
  | fork fresh sourceHead sourceVersion freshVersion rank next vis store heads parents =>
    have update := Configuration.headEvents_update_of_store_head_update config next freshVersion store heads
    have sourceEvents := config.headEvents_eq_of_head_ver sourceHead sourceVersion
    have empty : config.headEvents target = none := by simp [Configuration.headEvents,headEventsFrom,fresh]
    have eventFrame := events_head_update config next target _ update
      (by intro event member; exact ⟨source,_,sourceEvents,member⟩)
      (by intro old oldHead; rw [empty] at oldHead; cases oldHead)
    refine ⟨.exchange _ _ paired.honest,paired.sessionInjective,?_,
      heads_exchange_fork config next network sessions lift paired.sessionInjective paired.heads target source _ empty sourceEvents update,?_⟩
    rw [eventFrame,vis]
    exact NotionCoreArchiveEvents.coupling_archive_frame network (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events
    exact NotionCoreAllocationClock.import_tight network.allocation paired.tight _ _

/-- Actual ordinary merge imports the two CURRENT heads. The saved base is
ignored by the concrete union carrier, while event/receipt correspondence is
preserved independently of its contents. -/
theorem merge_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : Step D config (.merge target source) next) :
    Pair next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  cases step with
  | merge targetHead sourceHead targetVersion sourceVersion gca baseVersion freshVersion rank₁ rank₂ next vis store heads parents =>
    have update := Configuration.headEvents_update_of_store_head_update config next freshVersion store heads
    have leftEvents := config.headEvents_eq_of_head_ver targetHead targetVersion
    have rightEvents := config.headEvents_eq_of_head_ver sourceHead sourceVersion
    have eventFrame := events_head_update config next target _ update
      (by intro event member; rcases member with member | member
          · exact ⟨target,_,leftEvents,member⟩
          · exact ⟨source,_,rightEvents,member⟩)
      (by intro old oldHead; have equal := Option.some.inj (oldHead.symm.trans leftEvents); subst old; exact Set.subset_union_left)
    refine ⟨.exchange _ _ paired.honest,paired.sessionInjective,?_,
      heads_exchange_union config next network sessions lift paired.sessionInjective paired.heads target source _ _ leftEvents rightEvents update,?_⟩
    rw [eventFrame,vis]
    exact NotionCoreArchiveEvents.coupling_archive_frame network (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events
    exact NotionCoreAllocationClock.import_tight network.allocation paired.tight _ _

/-- Canonical recursive-base merge imports the same current heads. The
virtual-base metadata does not alter the source receipt action. -/
theorem mergeV_preserves {config next : Configuration D}
    (resolver : VirtualMergeBaseResolver D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : StepV D resolver config (.merge target source) next) :
    Pair next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  cases step with
  | base ordinary => exact merge_preserves network sessions lift paired target source ordinary
  | mergeVirtual targetHead sourceHead targetVersion sourceVersion freshVersion rank₁ rank₂ next vis store heads parents =>
    have update := Configuration.headEvents_update_of_store_head_update config next freshVersion store heads
    have leftEvents := config.headEvents_eq_of_head_ver targetHead targetVersion
    have rightEvents := config.headEvents_eq_of_head_ver sourceHead sourceVersion
    have eventFrame := events_head_update config next target _ update
      (by intro event member; rcases member with member | member
          · exact ⟨target,_,leftEvents,member⟩
          · exact ⟨source,_,rightEvents,member⟩)
      (by intro old oldHead; have equal := Option.some.inj (oldHead.symm.trans leftEvents); subst old; exact Set.subset_union_left)
    refine ⟨.exchange _ _ paired.honest,paired.sessionInjective,?_,
      heads_exchange_union config next network sessions lift paired.sessionInjective paired.heads target source _ _ leftEvents rightEvents update,
      NotionCoreAllocationClock.import_tight network.allocation paired.tight _ _⟩
    rw [eventFrame,vis]
    exact NotionCoreArchiveEvents.coupling_archive_frame network
      (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events

/-- Extend the outer-label assignment only at the freshly minted source tx. -/
noncomputable def extendLift (lift : Transaction → Event) (tx : Transaction) (event : Event) : Transaction → Event :=
  fun previous => if previous = tx then event else lift previous

/-- Actual immutable archive extension preserves the global event/past
coupling. Captured receipts are the old Sal mint head; freshness and absence
from older pasts are derived from one common reachable source archive. -/
theorem emit_coupling (config next : Configuration D) (network : State)
    (lift : Transaction → Event) (coupled : Coupling network config.events config.vis lift)
    (honest : NotionCoreMachineNetwork.Reach network) (peer : Session)
    (tx : Transaction) (event : Event) (payload : event.op = tx)
    (nextHonest : NotionCoreMachineNetwork.Reach (NotionCorePayloadNetwork.emit network peer tx.payload tx))
    (mintPast : Set Event)
    (receipts : ∀ previous ∈ NotionCoreArchiveEvents.archive network,
      (reservation previous ∈ (network.allocation.peers peer).received ↔ lift previous ∈ mintPast))
    (pastSupported : mintPast ⊆ config.events)
    (eventFrame : next.events = config.events ∪ {event})
    (visFrame : next.vis = fun left right => config.vis left right ∨ (mintPast left ∧ right = event)) :
    Coupling (NotionCorePayloadNetwork.emit network peer tx.payload tx) next.events next.vis
      (extendLift lift tx event) := by
  classical
  have reachable := NotionCoreMachineNetwork.issuance_reachable honest
  have allocation := NotionCoreIssuance.allocation_reachable reachable
  have keys : (tx.id :: (NotionCoreArchiveEvents.archive network).map Transaction.id).Nodup := by
    simpa [NotionCoreArchiveEvents.archive,NotionCorePayloadNetwork.emit] using
      NotionCoreArchiveOrder.archive_keys_unique _
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextHonest))
  have different : ∀ previous ∈ NotionCoreArchiveEvents.archive network, previous.id ≠ tx.id := by
    intro previous member equal
    exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨previous,member,equal⟩)
  have txDifferent : ∀ previous ∈ NotionCoreArchiveEvents.archive network, previous ≠ tx := by
    intro previous member equal
    exact different previous member (congrArg Transaction.id equal)
  have labelDifferent : ∀ previous ∈ NotionCoreArchiveEvents.archive network, lift previous ≠ event := by
    intro previous member equal
    exact txDifferent previous member (by simpa [coupled.payload previous member,payload] using congrArg Op.op equal)
  have freshEvent : event ∉ config.events := by
    intro member
    obtain ⟨previous,archived,equal⟩ := (coupled.events event).mp member
    exact labelDifferent previous archived equal
  have freshRun : ∀ old ∈ network.allocation.published, old ≠ reservation tx := by
    intro old published equal
    have recordRuns := NotionCoreIssuance.record_runs reachable
    have archivedRun : old ∈ (NotionCorePayloadNetwork.forget network).records.map NotionCoreIssuance.Record.run :=
      recordRuns ▸ published
    obtain ⟨record,recordMember,same⟩ := List.mem_map.mp archivedRun
    obtain ⟨entry,entryMember,recordEq⟩ := List.mem_map.mp recordMember
    have runEq : reservation entry.tx = old := by rw [← recordEq] at same; exact same
    exact different entry.tx (List.mem_map.mpr ⟨entry,entryMember,rfl⟩)
      (congrArg NotionRunAllocation.Run.first (runEq.trans equal))
  have absentReceived : reservation tx ∉ (network.allocation.peers peer).received := by
    intro member
    exact freshRun _ (NotionRunAllocation.reachable_received_published allocation peer _ member) rfl
  have absentPast : ∀ entry ∈ network.entries, reservation tx ∉ entry.past := by
    intro entry member present
    have provenance := NotionCoreIssuance.record_provenance reachable entry.record (List.mem_map.mpr ⟨entry,member,rfl⟩)
    exact freshRun _ (provenance.2.2 _ present) rfl
  have oldVisLeft : ∀ right, ¬ config.vis event right := by
    intro right visible
    exact freshEvent (config.vis_src visible)
  have oldVisRight : ∀ left, ¬ config.vis left event := by
    intro left visible
    exact freshEvent (config.vis_tgt visible)
  have eventOutside : event ∉ mintPast := fun member => freshEvent (pastSupported member)
  constructor
  · intro previous member
    simp only [NotionCoreArchiveEvents.archive,NotionCorePayloadNetwork.emit,List.map_cons,List.mem_cons] at member
    rcases member with rfl | member
    · simp [extendLift,payload]
    · simp [extendLift,txDifferent previous member,coupled.payload previous member]
  · intro current
    rw [eventFrame]
    simp only [Set.mem_union,Set.mem_singleton_iff,NotionCoreArchiveEvents.archive,
      NotionCorePayloadNetwork.emit,List.map_cons,List.mem_cons]
    constructor
    · rintro (old | rfl)
      · obtain ⟨previous,member,equal⟩ := (coupled.events current).mp old
        exact ⟨previous,Or.inr member,by simpa [extendLift,txDifferent previous member] using equal⟩
      · exact ⟨tx,Or.inl rfl,by simp [extendLift]⟩
    · rintro ⟨previous,rfl | member,equal⟩
      · exact Or.inr (by simpa [extendLift] using equal.symm)
      · exact Or.inl ((coupled.events current).mpr ⟨previous,member,by simpa [extendLift,txDifferent previous member] using equal⟩)
  · intro left right leftMember rightMember
    simp only [NotionCoreArchiveEvents.archive,NotionCorePayloadNetwork.emit,List.map_cons,List.mem_cons] at leftMember rightMember
    rcases leftMember with rfl | leftMember <;> rcases rightMember with rfl | rightMember
    · simp [extendLift,visFrame,oldVisRight,eventOutside,NotionCorePayloadNetwork.emit,absentReceived]
      constructor
      · intro member; exact False.elim (eventOutside member)
      · rintro ⟨entry,member,same,present⟩
        exact False.elim (absentPast entry member present)
    · simp only [extendLift,if_pos rfl,if_neg (txDifferent right rightMember),if_true,visFrame]
      have noOld : ¬ config.vis event (lift right) := oldVisLeft _
      simp only [noOld,false_or,show ¬ mintPast event from eventOutside,false_and]
      constructor
      · intro h; exact False.elim h
      · simp only [NotionCorePayloadNetwork.emit,List.mem_cons]
        rintro ⟨entry,rfl | member,same,present⟩
        · exact False.elim (txDifferent right rightMember same.symm)
        · exact False.elim (absentPast entry member present)
    · simp only [extendLift,if_neg (txDifferent left leftMember),if_pos rfl,if_true,visFrame]
      try simp only [oldVisRight,false_or,and_true]
      constructor
      · intro member
        exact ⟨⟨right,(network.allocation.peers peer).received⟩,by simp [NotionCorePayloadNetwork.emit],rfl,
          (receipts left leftMember).mpr member⟩
      · rintro ⟨entry,member,same,present⟩
        simp only [NotionCorePayloadNetwork.emit,List.mem_cons] at member
        rcases member with rfl | member
        · exact (receipts left leftMember).mp present
        · exact False.elim (txDifferent entry.tx (List.mem_map.mpr ⟨entry,member,rfl⟩) same)
    · simp only [extendLift,if_neg (txDifferent left leftMember),if_neg (txDifferent right rightMember),visFrame]
      have noLabel := labelDifferent right rightMember
      simp only [noLabel,and_false,or_false]
      rw [coupled.past left right leftMember rightMember]
      constructor
      · rintro ⟨entry,member,same,present⟩
        exact ⟨entry,by simp [NotionCorePayloadNetwork.emit,member],same,present⟩
      · rintro ⟨entry,member,same,present⟩
        simp only [NotionCorePayloadNetwork.emit,List.mem_cons] at member
        rcases member with rfl | member
        · exact False.elim (txDifferent right rightMember same.symm)
        · exact ⟨entry,member,same,present⟩

theorem emitted_receipts (network : State) (sender peer : Session) (tx : Transaction)
    (allocated : reservation tx = NotionRunAllocation.reserve (network.allocation.peers sender) sender tx.payload.width)
    (run : Run) :
    run ∈ ((NotionCorePayloadNetwork.emit network sender tx.payload tx).allocation.peers peer).received ↔
      run ∈ (network.allocation.peers peer).received ∨ peer = sender ∧ run = reservation tx := by
  by_cases same : peer = sender
  · subst peer
    simp [NotionCorePayloadNetwork.emit,NotionRunAllocation.issue,NotionRunAllocation.receive,← allocated,or_comm]
  · simp [NotionCorePayloadNetwork.emit,NotionRunAllocation.issue,same]

/-- A temporary source counter gap changes no actual head receipts, and cannot
reset an unused allocator because its sender is an allocated current head. -/
theorem heads_gap (config : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) (injective : Function.Injective sessions)
    (matched : HeadMatch config network sessions lift) (sender : Replica) (mintPast : Set Event)
    (head : config.headEvents sender = some mintPast) (ticks : Nat) :
    HeadMatch config (NotionCorePayloadNetwork.gap network (sessions sender) ticks) sessions lift := by
  constructor
  · intro peer events actual entry member
    have old := matched.receipts peer events actual entry member
    by_cases same : sessions peer = sessions sender
    · simpa [NotionCorePayloadNetwork.gap,NotionRunAllocation.skip,same,NotionRunAllocation.advance] using old
    · simpa [NotionCorePayloadNetwork.gap,NotionRunAllocation.skip,same] using old
  · intro peer absent
    have different : sessions peer ≠ sessions sender := by
      intro same
      have sameReplica := injective same
      subst peer
      rw [head] at absent
      cases absent
    simpa [NotionCorePayloadNetwork.gap,NotionRunAllocation.skip,different] using matched.unused peer absent

/-- The source emission and actual Sal head update agree on all receipts.
Fresh source transactions are never mistaken for receipt aliases at another
peer, and the new outer event is visible only in the updated mint head. -/
theorem heads_emit (config next : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (injective : Function.Injective sessions) (matched : HeadMatch config network sessions lift)
    (coupled : Coupling network config.events config.vis lift)
    (sender : Replica) (mintPast : Set Event) (head : config.headEvents sender = some mintPast)
    (tx : Transaction) (event : Event) (payload : event.op = tx)
    (honest : NotionCoreMachineNetwork.Reach network)
    (nextHonest : NotionCoreMachineNetwork.Reach (NotionCorePayloadNetwork.emit network (sessions sender) tx.payload tx))
    (allocated : reservation tx = NotionRunAllocation.reserve (network.allocation.peers (sessions sender))
      (sessions sender) tx.payload.width)
    (updated : next.headEvents = updateRep config.headEvents sender (mintPast ∪ {event})) :
    HeadMatch next (NotionCorePayloadNetwork.emit network (sessions sender) tx.payload tx) sessions
      (extendLift lift tx event) := by
  classical
  have keys : (tx.id :: (NotionCoreArchiveEvents.archive network).map Transaction.id).Nodup := by
    simpa [NotionCoreArchiveEvents.archive,NotionCorePayloadNetwork.emit] using
      NotionCoreArchiveOrder.archive_keys_unique _
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextHonest))
  have different : ∀ previous ∈ NotionCoreArchiveEvents.archive network, previous ≠ tx := by
    intro previous member equal
    exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨previous,member,congrArg Transaction.id equal⟩)
  have labels : ∀ previous ∈ NotionCoreArchiveEvents.archive network, lift previous ≠ event := by
    intro previous member equal
    exact different previous member (by simpa [coupled.payload previous member,payload] using congrArg Op.op equal)
  have freshEvent : event ∉ config.events := by
    intro member
    obtain ⟨previous,archived,equal⟩ := (coupled.events event).mp member
    exact labels previous archived equal
  have allocation := NotionCoreIssuance.allocation_reachable (NotionCoreMachineNetwork.issuance_reachable honest)
  have freshReceived : ∀ peer, reservation tx ∉ (network.allocation.peers peer).received := by
    intro peer member
    have published := NotionRunAllocation.reachable_received_published allocation peer _ member
    have fresh := NotionRunAllocation.fresh_transaction_key allocation published (sessions sender) tx.payload.width
    exact fresh (congrArg NotionRunAllocation.Run.first allocated.symm)
  constructor
  · intro peer events actual entry member
    simp only [NotionCorePayloadNetwork.emit,List.mem_cons] at member
    by_cases same : peer = sender
    · subst peer
      simp [updated,updateRep] at actual
      subst events
      rw [emitted_receipts network _ _ tx allocated]
      rcases member with rfl | member
      · simp [extendLift]
      · have archived : entry.tx ∈ NotionCoreArchiveEvents.archive network := List.mem_map.mpr ⟨entry,member,rfl⟩
        have runDifferent : reservation entry.tx ≠ reservation tx := by
          intro equal
          exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨entry.tx,archived,congrArg NotionRunAllocation.Run.first equal⟩)
        simp [runDifferent,extendLift,different entry.tx archived,labels entry.tx archived,
          matched.receipts sender mintPast head entry member]
    · have oldHead : config.headEvents peer = some events := by simpa only [updated,updateRep,if_neg same] using actual
      have sessionDifferent : sessions peer ≠ sessions sender := fun equal => same (injective equal)
      rw [emitted_receipts network _ _ tx allocated]
      simp only [sessionDifferent,false_and,or_false]
      rcases member with rfl | member
      · have outside : event ∉ events := fun present => freshEvent ⟨peer,events,oldHead,present⟩
        simp [freshReceived (sessions peer),extendLift,outside]
      · have archived : entry.tx ∈ NotionCoreArchiveEvents.archive network := List.mem_map.mpr ⟨entry,member,rfl⟩
        simpa [extendLift,different entry.tx archived] using matched.receipts peer events oldHead entry member
  · intro peer absent
    have different : peer ≠ sender := by
      intro equal
      subst peer
      simp [updated,updateRep] at absent
    have sessionDifferent : sessions peer ≠ sessions sender := fun equal => different (injective equal)
    have oldAbsent : config.headEvents peer = none := by simpa only [updated,updateRep,if_neg different] using absent
    simpa [NotionCorePayloadNetwork.emit,NotionRunAllocation.issue,sessionDifferent] using matched.unused peer oldAbsent

/-- Source counter gaps followed immediately by actual emission restore the
stable tight-clock invariant; the new reservation is the witness. -/
theorem emitted_gap_tight (network : State) (tight : ∀ peer, NotionCoreAllocationClock.Tight (network.allocation.peers peer))
    (sender : Session) (ticks : Nat) (tx : Transaction) :
    ∀ peer, NotionCoreAllocationClock.Tight
      ((NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap network sender ticks) sender tx.payload tx).allocation.peers peer) := by
  intro peer
  by_cases same : peer = sender
  · subst peer
    simpa [NotionCorePayloadNetwork.emit,NotionCorePayloadNetwork.gap,NotionRunAllocation.issue,
      NotionRunAllocation.skip] using NotionCoreAllocationClock.gap_mint_tight
        (tight sender).1 ticks sender tx.payload.width (NotionCorePayload.width_positive tx.payload)
  · simpa [NotionCorePayloadNetwork.emit,NotionCorePayloadNetwork.gap,NotionRunAllocation.issue,
      NotionRunAllocation.skip,same] using tight peer

/-- Actual raw apply preserves the initialized pair through a source gap and
emission. This also permits the externally authorized factory bootstrap at
ticks zero; it does not authorize genesis from a local carrier guard. -/
theorem emit_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) (paired : Pair config network sessions lift)
    (time : Timestamp) (sender : Replica) (tx : Transaction)
    (raw : Step D config (.apply time sender tx) next) (ticks : Nat)
    (allocated : reservation tx = NotionRunAllocation.reserve
      ((NotionCorePayloadNetwork.gap network (sessions sender) ticks).allocation.peers (sessions sender))
      (sessions sender) tx.payload.width)
    (nextHonest : NotionCoreMachineNetwork.Reach
      (NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap network (sessions sender) ticks)
        (sessions sender) tx.payload tx)) :
    Pair next (NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap network (sessions sender) ticks)
      (sessions sender) tx.payload tx) sessions (extendLift lift tx (time,sender,tx)) := by
  cases raw with
  | apply headAt versionAt freshTime freshStore freshVersion rank next vis store heads parents =>
    rename_i currentVersion oldState mintPast freshVersionId
    let advanced := NotionCorePayloadNetwork.gap network (sessions sender) ticks
    let event : Event := (time,sender,tx)
    have update := Configuration.headEvents_update_of_store_head_update config next freshVersion store heads
    have mintHead := config.headEvents_eq_of_head_ver headAt versionAt
    have eventFrame : next.events = config.events ∪ {event} := by
      ext current
      constructor
      · rintro ⟨peer,events,head,member⟩
        rw [update] at head
        by_cases same : peer = sender
        · subst peer
          simp only [updateRep,if_true,Option.some.injEq] at head
          subst events
          rcases member with old | new
          · exact Or.inl ⟨sender,_,mintHead,old⟩
          · exact Or.inr new
        · exact Or.inl ⟨peer,events,by simpa only [updateRep,if_neg same] using head,member⟩
      · rintro (⟨peer,events,head,member⟩ | new)
        · by_cases same : peer = sender
          · subst peer
            have equal := Option.some.inj (head.symm.trans mintHead)
            subst events
            exact ⟨sender,mintPast ∪ {event},by simp [update,updateRep,event],Or.inl member⟩
          · exact ⟨peer,events,by simpa only [update,updateRep,if_neg same] using head,member⟩
        · exact ⟨sender,mintPast ∪ {event},by simp [update,updateRep,event],Or.inr new⟩
    have advancedHonest : NotionCoreMachineNetwork.Reach advanced := .gap _ _ paired.honest
    have advancedCoupling : Coupling advanced config.events config.vis lift :=
      NotionCoreArchiveEvents.coupling_archive_frame network advanced rfl _ _ _ paired.events
    have advancedHeads := heads_gap config network sessions lift paired.sessionInjective paired.heads sender _ mintHead ticks
    have captured : ∀ previous ∈ NotionCoreArchiveEvents.archive advanced,
        (reservation previous ∈ (advanced.allocation.peers (sessions sender)).received ↔ lift previous ∈ mintPast) := by
      intro previous member
      obtain ⟨entry,member,equal⟩ := List.mem_map.mp member
      simpa [equal] using advancedHeads.receipts sender mintPast mintHead entry member
    refine ⟨nextHonest,paired.sessionInjective,
      emit_coupling config next advanced lift advancedCoupling advancedHonest (sessions sender) tx event rfl nextHonest
        mintPast captured (by intro previous member; exact ⟨sender,mintPast,mintHead,member⟩) eventFrame vis,
      heads_emit config next advanced sessions lift paired.sessionInjective advancedHeads advancedCoupling sender _ mintHead
        tx event rfl advancedHonest nextHonest allocated update,
      emitted_gap_tight network paired.tight (sessions sender) ticks tx⟩

#print axioms emit_preserves
#print axioms heads_emit
#print axioms emit_coupling
#print axioms mergeV_preserves
#print axioms fork_preserves
#print axioms merge_preserves
end Sal.MRDTs.Instances.NotionCoreMachineExecution
