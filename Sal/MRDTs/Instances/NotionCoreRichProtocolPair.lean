import Sal.MRDTs.Instances.NotionCoreRichProtocolEvents
import Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier
import Sal.MRDTs.Instances.NotionCoreAllocationClock

/-! Actual execution coupling from an explicitly initialized factory pair.
The outer genesis authorization is not inferred from a local empty carrier.
These structural simulation statements contain no sequential answer premises. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolPair
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCoreRichPayload (Transaction)
open NotionCoreRichProtocolEvents (reservation)
open NotionCoreRichProtocolNetwork (State Entry)
open NotionCoreRichProtocolEvents (Event Coupling)
open NotionCoreRichProtocolCarrier (D)
open NotionRunAllocation (Session Run)

/-- Current heads agree with actual whole-run receipts. Unallocated issuer
identities have never been reset: their source peer is genuinely empty. -/
structure HeadMatch (config : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) : Prop where
  receipts : ∀ replica events, config.headEvents replica = some events →
    ∀ entry ∈ network.entries,
      (reservation entry.transaction ∈ (network.allocation.peers (sessions replica)).received ↔
        lift entry.transaction ∈ events)
  unused : ∀ replica, config.headEvents replica = none →
    network.allocation.peers (sessions replica) = NotionRunAllocation.emptyPeer

structure Pair (config : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) : Prop where
  honest : NotionCoreRichProtocolNetwork.Reach network
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
    HeadMatch next (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  constructor
  · intro peer events head entry member
    have archived : entry ∈ network.entries := member
    by_cases same : peer = target
    · subst peer
      simp [updated,updateRep] at head
      subst events
      rw [NotionCoreRichProtocolNetwork.exchange_received]
      simp only [true_and]
      rw [matched.receipts target left leftHead entry archived,
        matched.receipts source right rightHead entry archived]
      rfl
    · have sessionDifferent : sessions peer ≠ sessions target := fun equal => same (injective equal)
      rw [NotionCoreRichProtocolNetwork.exchange_other_peer network _ _ _ sessionDifferent]
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
    rw [NotionCoreRichProtocolNetwork.exchange_other_peer network _ _ _
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
    HeadMatch next (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
  constructor
  · intro peer selected head entry member
    have archived : entry ∈ network.entries := member
    by_cases same : peer = target
    · subst peer
      simp [updated,updateRep] at head
      subst selected
      rw [NotionCoreRichProtocolNetwork.exchange_received]
      simp only [true_and]
      rw [matched.unused target empty]
      simp only [NotionRunAllocation.emptyPeer,List.not_mem_nil,false_or]
      exact matched.receipts source events sourceHead entry archived
    · rw [NotionCoreRichProtocolNetwork.exchange_other_peer network _ _ _ (fun equal => same (injective equal))]
      apply matched.receipts peer selected
      · simpa only [updated,updateRep,if_neg same] using head
      · exact archived
  · intro peer absent
    have different : peer ≠ target := by
      intro equal
      subst peer
      simp [updated,updateRep] at absent
    rw [NotionCoreRichProtocolNetwork.exchange_other_peer network _ _ _ (fun equal => different (injective equal))]
    exact matched.unused peer (by simpa only [updated,updateRep,if_neg different] using absent)

/-- Every actual raw fork preserves an initialized pair using honest source
exchange. Its fresh replica identity selects an unused source allocator. -/
theorem fork_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : Step D config (.fork target source) next) :
    Pair next (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
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
    exact NotionCoreRichProtocolEvents.coupling_archive_frame network (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events
    exact NotionCoreAllocationClock.import_tight network.allocation paired.tight _ _

/-- Actual ordinary merge imports the two CURRENT heads. The saved base is
ignored by the concrete union carrier, while event/receipt correspondence is
preserved independently of its contents. -/
theorem merge_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : Step D config (.merge target source) next) :
    Pair next (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
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
    exact NotionCoreRichProtocolEvents.coupling_archive_frame network (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events
    exact NotionCoreAllocationClock.import_tight network.allocation paired.tight _ _

/-- Canonical recursive-base merge imports the same current heads. The
virtual-base metadata does not alter the source receipt action. -/
theorem mergeV_preserves {config next : Configuration D}
    (resolver : VirtualMergeBaseResolver D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift) (target source : Replica)
    (step : StepV D resolver config (.merge target source) next) :
    Pair next (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) sessions lift := by
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
    exact NotionCoreRichProtocolEvents.coupling_archive_frame network
      (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) rfl _ _ _ paired.events

/-- Extend the outer-label assignment only at the freshly minted source tx. -/
noncomputable def extendLift (lift : Transaction → Event) (tx : Transaction) (event : Event) : Transaction → Event :=
  fun previous => if previous = tx then event else lift previous

/-- Actual immutable archive extension preserves the global event/past
coupling. Captured receipts are the old Sal mint head; freshness and absence
from older pasts are derived from one common reachable source archive. -/
theorem emit_coupling (config next : Configuration D) (network : State)
    (lift : Transaction → Event) (coupled : Coupling network config.events config.vis lift)
    (honest : NotionCoreRichProtocolNetwork.Reach network) (peer : Session)
    (tx : Transaction) (event : Event) (payload : event.op = tx)
    (nextHonest : NotionCoreRichProtocolNetwork.Reach (NotionCoreRichProtocolNetwork.publish network peer tx))
    (mintPast : Set Event)
    (receipts : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network,
      (reservation previous ∈ (network.allocation.peers peer).received ↔ lift previous ∈ mintPast))
    (pastSupported : mintPast ⊆ config.events)
    (eventFrame : next.events = config.events ∪ {event})
    (visFrame : next.vis = fun left right => config.vis left right ∨ (mintPast left ∧ right = event)) :
    Coupling (NotionCoreRichProtocolNetwork.publish network peer tx) next.events next.vis
      (extendLift lift tx event) := by
  classical
  have allocation := NotionCoreRichProtocolNetwork.allocation_reachable honest
  have keys : (tx.id :: (NotionCoreRichProtocolEvents.archive network).map Transaction.id).Nodup := by
    simpa [NotionCoreRichProtocolEvents.archive,NotionCoreRichProtocolNetwork.publish] using
      NotionCoreRichProtocolNetwork.archive_keys_unique nextHonest
  have different : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network, previous.id ≠ tx.id := by
    intro previous member equal
    exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨previous,member,equal⟩)
  have txDifferent : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network, previous ≠ tx := by
    intro previous member equal
    exact different previous member (congrArg Transaction.id equal)
  have labelDifferent : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network, lift previous ≠ event := by
    intro previous member equal
    exact txDifferent previous member (by simpa [coupled.payload previous member,payload] using congrArg Op.op equal)
  have freshEvent : event ∉ config.events := by
    intro member
    obtain ⟨previous,archived,equal⟩ := (coupled.events event).mp member
    exact labelDifferent previous archived equal
  have freshRun : ∀ old ∈ network.allocation.published, old ≠ reservation tx := by
    intro old published equal
    rw [← NotionCoreRichProtocolNetwork.archive_runs honest] at published
    obtain ⟨entry,entryMember,runEq⟩ := List.mem_map.mp published
    exact different entry.transaction (List.mem_map.mpr ⟨entry,entryMember,rfl⟩)
      (congrArg NotionRunAllocation.Run.first (runEq.trans equal))
  have absentReceived : reservation tx ∉ (network.allocation.peers peer).received := by
    intro member
    exact freshRun _ (NotionRunAllocation.reachable_received_published allocation peer _ member) rfl
  have absentPast : ∀ entry ∈ network.entries, reservation tx ∉ entry.past := by
    intro entry member present
    have provenance := NotionCoreRichProtocolNetwork.entry_provenance honest entry member
    exact freshRun _ (provenance.2 _ present) rfl
  have oldVisLeft : ∀ right, ¬ config.vis event right := by
    intro right visible
    exact freshEvent (config.vis_src visible)
  have oldVisRight : ∀ left, ¬ config.vis left event := by
    intro left visible
    exact freshEvent (config.vis_tgt visible)
  have eventOutside : event ∉ mintPast := fun member => freshEvent (pastSupported member)
  constructor
  · intro previous member
    simp only [NotionCoreRichProtocolEvents.archive,NotionCoreRichProtocolNetwork.publish,List.map_cons,List.mem_cons] at member
    rcases member with rfl | member
    · simp [extendLift,payload]
    · simp [extendLift,txDifferent previous member,coupled.payload previous member]
  · intro current
    rw [eventFrame]
    simp only [Set.mem_union,Set.mem_singleton_iff,NotionCoreRichProtocolEvents.archive,
      NotionCoreRichProtocolNetwork.publish,List.map_cons,List.mem_cons]
    constructor
    · rintro (old | rfl)
      · obtain ⟨previous,member,equal⟩ := (coupled.events current).mp old
        exact ⟨previous,Or.inr member,by simpa [extendLift,txDifferent previous member] using equal⟩
      · exact ⟨tx,Or.inl rfl,by simp [extendLift]⟩
    · rintro ⟨previous,rfl | member,equal⟩
      · exact Or.inr (by simpa [extendLift] using equal.symm)
      · exact Or.inl ((coupled.events current).mpr ⟨previous,member,by simpa [extendLift,txDifferent previous member] using equal⟩)
  · intro left right leftMember rightMember
    simp only [NotionCoreRichProtocolEvents.archive,NotionCoreRichProtocolNetwork.publish,List.map_cons,List.mem_cons] at leftMember rightMember
    rcases leftMember with rfl | leftMember <;> rcases rightMember with rfl | rightMember
    · simp [extendLift,visFrame,oldVisRight,eventOutside,NotionCoreRichProtocolNetwork.publish,absentReceived]
      constructor
      · intro member; exact False.elim (eventOutside member)
      · rintro ⟨entry,member,same,present⟩
        exact False.elim (absentPast entry member present)
    · simp only [extendLift,if_pos rfl,if_neg (txDifferent right rightMember),if_true,visFrame]
      have noOld : ¬ config.vis event (lift right) := oldVisLeft _
      simp only [noOld,false_or,show ¬ mintPast event from eventOutside,false_and]
      constructor
      · intro h; exact False.elim h
      · simp only [NotionCoreRichProtocolNetwork.publish,List.mem_cons]
        rintro ⟨entry,rfl | member,same,present⟩
        · exact False.elim (txDifferent right rightMember same.symm)
        · exact False.elim (absentPast entry member present)
    · simp only [extendLift,if_neg (txDifferent left leftMember),if_pos rfl,if_true,visFrame]
      try simp only [oldVisRight,false_or,and_true]
      constructor
      · intro member
        exact ⟨⟨right,(network.allocation.peers peer).received⟩,by simp [NotionCoreRichProtocolNetwork.publish],rfl,
          (receipts left leftMember).mpr member⟩
      · rintro ⟨entry,member,same,present⟩
        simp only [NotionCoreRichProtocolNetwork.publish,List.mem_cons] at member
        rcases member with rfl | member
        · exact (receipts left leftMember).mp present
        · exact False.elim (txDifferent entry.transaction (List.mem_map.mpr ⟨entry,member,rfl⟩) same)
    · simp only [extendLift,if_neg (txDifferent left leftMember),if_neg (txDifferent right rightMember),visFrame]
      have noLabel := labelDifferent right rightMember
      simp only [noLabel,and_false,or_false]
      rw [coupled.past left right leftMember rightMember]
      constructor
      · rintro ⟨entry,member,same,present⟩
        exact ⟨entry,by simp [NotionCoreRichProtocolNetwork.publish,member],same,present⟩
      · rintro ⟨entry,member,same,present⟩
        simp only [NotionCoreRichProtocolNetwork.publish,List.mem_cons] at member
        rcases member with rfl | member
        · exact False.elim (txDifferent right rightMember same.symm)
        · exact ⟨entry,member,same,present⟩

theorem emitted_receipts (network : State) (sender peer : Session) (tx : Transaction)
    (allocated : reservation tx = NotionRunAllocation.reserve (network.allocation.peers sender) sender tx.payload.width)
    (run : Run) :
    run ∈ ((NotionCoreRichProtocolNetwork.publish network sender tx).allocation.peers peer).received ↔
      run ∈ (network.allocation.peers peer).received ∨ peer = sender ∧ run = reservation tx := by
  by_cases same : peer = sender
  · subst peer
    simp [NotionCoreRichProtocolNetwork.publish,NotionRunAllocation.issue,NotionRunAllocation.receive,← allocated,or_comm]
  · simp [NotionCoreRichProtocolNetwork.publish,NotionRunAllocation.issue,same]

/-- The source emission and actual Sal head update agree on all receipts.
Fresh source transactions are never mistaken for receipt aliases at another
peer, and the new outer event is visible only in the updated mint head. -/
theorem heads_emit (config next : Configuration D) (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (injective : Function.Injective sessions) (matched : HeadMatch config network sessions lift)
    (coupled : Coupling network config.events config.vis lift)
    (sender : Replica) (mintPast : Set Event) (head : config.headEvents sender = some mintPast)
    (tx : Transaction) (event : Event) (payload : event.op = tx)
    (honest : NotionCoreRichProtocolNetwork.Reach network)
    (nextHonest : NotionCoreRichProtocolNetwork.Reach (NotionCoreRichProtocolNetwork.publish network (sessions sender) tx))
    (allocated : reservation tx = NotionRunAllocation.reserve (network.allocation.peers (sessions sender))
      (sessions sender) tx.payload.width)
    (updated : next.headEvents = updateRep config.headEvents sender (mintPast ∪ {event})) :
    HeadMatch next (NotionCoreRichProtocolNetwork.publish network (sessions sender) tx) sessions
      (extendLift lift tx event) := by
  classical
  have keys : (tx.id :: (NotionCoreRichProtocolEvents.archive network).map Transaction.id).Nodup := by
    simpa [NotionCoreRichProtocolEvents.archive,NotionCoreRichProtocolNetwork.publish] using
      NotionCoreRichProtocolNetwork.archive_keys_unique nextHonest
  have different : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network, previous ≠ tx := by
    intro previous member equal
    exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨previous,member,congrArg Transaction.id equal⟩)
  have labels : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network, lift previous ≠ event := by
    intro previous member equal
    exact different previous member (by simpa [coupled.payload previous member,payload] using congrArg Op.op equal)
  have freshEvent : event ∉ config.events := by
    intro member
    obtain ⟨previous,archived,equal⟩ := (coupled.events event).mp member
    exact labels previous archived equal
  have allocation := NotionCoreRichProtocolNetwork.allocation_reachable honest
  have freshReceived : ∀ peer, reservation tx ∉ (network.allocation.peers peer).received := by
    intro peer member
    have published := NotionRunAllocation.reachable_received_published allocation peer _ member
    have fresh := NotionRunAllocation.fresh_transaction_key allocation published (sessions sender) tx.payload.width
    exact fresh (congrArg NotionRunAllocation.Run.first allocated.symm)
  constructor
  · intro peer events actual entry member
    simp only [NotionCoreRichProtocolNetwork.publish,List.mem_cons] at member
    by_cases same : peer = sender
    · subst peer
      simp [updated,updateRep] at actual
      subst events
      rw [emitted_receipts network _ _ tx allocated]
      rcases member with rfl | member
      · simp [extendLift]
      · have archived : entry.transaction ∈ NotionCoreRichProtocolEvents.archive network := List.mem_map.mpr ⟨entry,member,rfl⟩
        have runDifferent : reservation entry.transaction ≠ reservation tx := by
          intro equal
          exact (List.nodup_cons.mp keys).1 (List.mem_map.mpr ⟨entry.transaction,archived,congrArg NotionRunAllocation.Run.first equal⟩)
        simp [runDifferent,extendLift,different entry.transaction archived,labels entry.transaction archived,
          matched.receipts sender mintPast head entry member]
    · have oldHead : config.headEvents peer = some events := by simpa only [updated,updateRep,if_neg same] using actual
      have sessionDifferent : sessions peer ≠ sessions sender := fun equal => same (injective equal)
      rw [emitted_receipts network _ _ tx allocated]
      simp only [sessionDifferent,false_and,or_false]
      rcases member with rfl | member
      · have outside : event ∉ events := fun present => freshEvent ⟨peer,events,oldHead,present⟩
        simp [freshReceived (sessions peer),extendLift,outside]
      · have archived : entry.transaction ∈ NotionCoreRichProtocolEvents.archive network := List.mem_map.mpr ⟨entry,member,rfl⟩
        simpa [extendLift,different entry.transaction archived] using matched.receipts peer events oldHead entry member
  · intro peer absent
    have different : peer ≠ sender := by
      intro equal
      subst peer
      simp [updated,updateRep] at absent
    have sessionDifferent : sessions peer ≠ sessions sender := fun equal => different (injective equal)
    have oldAbsent : config.headEvents peer = none := by simpa only [updated,updateRep,if_neg different] using absent
    simpa [NotionCoreRichProtocolNetwork.publish,NotionRunAllocation.issue,sessionDifferent] using matched.unused peer oldAbsent

/-- Actual raw apply preserves the source/Sal structural pair. The transaction
is the one constructed by the source allocator; no state-image equation is a
premise or a protocol constructor field. -/
theorem emit_preserves {config next : Configuration D} (network : State)
    (sessions : Replica → Session) (lift : Transaction → Event) (paired : Pair config network sessions lift)
    (time : Timestamp) (sender : Replica) (tx : Transaction)
    (raw : Step D config (.apply time sender tx) next)
    (allocated : reservation tx = NotionRunAllocation.reserve
      (network.allocation.peers (sessions sender)) (sessions sender) tx.payload.width)
    (nextHonest : NotionCoreRichProtocolNetwork.Reach
      (NotionCoreRichProtocolNetwork.publish network (sessions sender) tx)) :
    Pair next (NotionCoreRichProtocolNetwork.publish network (sessions sender) tx)
      sessions (extendLift lift tx (time,sender,tx)) := by
  cases raw with
  | apply headAt versionAt freshTime freshStore freshVersion rank next vis store heads parents =>
    rename_i currentVersion oldState mintPast freshVersionId
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
    have captured : ∀ previous ∈ NotionCoreRichProtocolEvents.archive network,
        (reservation previous ∈ (network.allocation.peers (sessions sender)).received ↔ lift previous ∈ mintPast) := by
      intro previous member
      obtain ⟨entry,member,equal⟩ := List.mem_map.mp member
      simpa [equal] using paired.heads.receipts sender _ mintHead entry member
    exact ⟨nextHonest,paired.sessionInjective,
      emit_coupling config next network lift paired.events paired.honest (sessions sender) tx event rfl nextHonest
        _ captured (by intro previous member; exact ⟨sender,_,mintHead,member⟩) eventFrame vis,
      heads_emit config next network sessions lift paired.sessionInjective paired.heads paired.events sender _ mintHead
        tx event rfl paired.honest nextHonest allocated update,
      NotionCoreRichProtocolNetwork.clocks_tight nextHonest⟩

#print axioms emit_preserves
#print axioms mergeV_preserves
end Sal.MRDTs.Instances.NotionCoreRichProtocolPair
