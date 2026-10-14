import Sal.MRDTs.Instances.NotionCoreMachineHistory

/-! Structural coupling to one honest archive. This is conditional event/version
transport, not a proof that Sal issuance constructs the coupling. In particular,
bootstrap initialization and per-replica allocation preservation remain obligations.
No sequential correctness or observation equation occurs in the coupling. -/
namespace Sal.MRDTs.Instances.NotionCoreArchiveEvents
open Sal.MRDTs.Foundation
open NotionCorePayload (Transaction reservation)
open NotionCorePayloadNetwork (State Entry forget)
open NotionRunAllocation (Run)
abbrev Event := Op Transaction
abbrev archive (network : State) := network.entries.map Entry.tx

/-- Outer event labels are assigned separately from compound source IDs.
The captured source mint past agrees with visibility, in one common archive. -/
structure Coupling (network : State) (events : Set Event) (vis : Event → Event → Prop)
    (lift : Transaction → Event) : Prop where
  payload : ∀ tx ∈ archive network, (lift tx).op = tx
  events : ∀ event, event ∈ events ↔ ∃ tx ∈ archive network, lift tx = event
  past : ∀ left right, left ∈ archive network → right ∈ archive network →
    (vis (lift left) (lift right) ↔
      ∃ entry ∈ network.entries, entry.tx = right ∧ reservation left ∈ entry.past)

/-- A version selects archived transactions by event membership. It contains
no unknown reservations and does not require any current peer to hold it. -/
noncomputable def version (network : State) (selected : Set Event)
    (lift : Transaction → Event) : List Run := by
  classical
  exact ((archive network).filter (fun tx => lift tx ∈ selected)).map reservation

noncomputable def witness (network : State) (selected : Set Event)
    (lift : Transaction → Event) : List Event :=
  (NotionCoreReconstruction.transactionsFor network (version network selected lift)).map lift

private theorem reservation_injective (network : State)
    (reachable : NotionCorePayloadNetwork.Reach network) (left right : Transaction)
    (leftMember : left ∈ archive network) (rightMember : right ∈ archive network)
    (same : reservation left = reservation right) : left = right :=
  List.inj_on_of_nodup_map (NotionCoreArchiveOrder.archive_keys_unique network reachable)
    leftMember rightMember (congrArg Run.first same)

theorem version_supported (network : State) (selected : Set Event) (lift : Transaction → Event) :
    ∀ run ∈ version network selected lift,
      run ∈ (forget network).records.map NotionCoreIssuance.Record.run := by
  classical
  intro run member
  obtain ⟨tx,filtered,equal⟩ := List.mem_map.mp member
  obtain ⟨entry,entryMember,txEq⟩ := List.mem_map.mp (List.mem_filter.mp filtered).1
  exact List.mem_map.mpr ⟨entry.record,List.mem_map.mpr ⟨entry,entryMember,rfl⟩,
    by simpa [Entry.record,NotionCorePayload.record,txEq] using equal⟩

theorem version_unique (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (selected : Set Event) (lift : Transaction → Event) : (version network selected lift).Nodup := by
  classical
  have keys := NotionCoreArchiveOrder.archive_keys_unique network reachable
  have pairwise : (archive network).Pairwise (fun a b => a.id ≠ b.id) :=
    (List.pairwise_map (f := Transaction.id) (R := fun a b => a ≠ b)).mp keys
  apply (List.pairwise_map (f := reservation) (R := fun a b => a ≠ b)).mpr
  apply (pairwise.filter (fun tx => lift tx ∈ selected)).imp
  intro left right different same
  exact different (congrArg Run.first same)

 theorem selected_transactions (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (selected : Set Event) (lift : Transaction → Event) (tx : Transaction) :
    tx ∈ NotionCoreReconstruction.transactionsFor network (version network selected lift) ↔
      tx ∈ archive network ∧ lift tx ∈ selected := by
  classical
  rw [NotionCoreReconstruction.transactionsFor_membership]
  constructor
  · rintro ⟨⟨entry,entryMember,same⟩,runMember⟩
    have archived : tx ∈ archive network := List.mem_map.mpr ⟨entry,entryMember,same⟩
    obtain ⟨other,otherMember,runEq⟩ := List.mem_map.mp runMember
    have filtered := List.mem_filter.mp otherMember
    have txEq := reservation_injective network reachable other tx filtered.1 archived runEq
    exact ⟨archived,txEq ▸ (of_decide_eq_true filtered.2)⟩
  · rintro ⟨archived,present⟩
    obtain ⟨entry,member,same⟩ := List.mem_map.mp archived
    exact ⟨⟨entry,member,same⟩,List.mem_map.mpr ⟨tx,List.mem_filter.mpr ⟨archived,by simpa using present⟩,rfl⟩⟩

 theorem event_payload (network : State) (events : Set Event) (vis : Event → Event → Prop)
    (lift : Transaction → Event) (coupled : Coupling network events vis lift)
    (event : Event) (member : event ∈ events) :
    event.op ∈ archive network ∧ lift event.op = event := by
  obtain ⟨tx,archived,equal⟩ := (coupled.events event).mp member
  subst event
  rw [coupled.payload tx archived]
  exact ⟨archived,rfl⟩

 theorem source_key_injective (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (left right : Event)
    (leftMember : left ∈ events) (rightMember : right ∈ events)
    (same : left.op.id = right.op.id) : left = right := by
  have a := event_payload network events vis lift coupled left leftMember
  have b := event_payload network events vis lift coupled right rightMember
  have txEq := List.inj_on_of_nodup_map (NotionCoreArchiveOrder.archive_keys_unique network reachable)
    a.1 b.1 same
  rw [← a.2,← b.2,txEq]

/-- Visibility increases source counters, independently of outer timestamps. -/
theorem visibility_before (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (left right : Event)
    (leftMember : left ∈ events) (rightMember : right ∈ events) (visible : vis left right) :
    NotionRunAllocation.Before left.op.id right.op.id := by
  have a := event_payload network events vis lift coupled left leftMember
  have b := event_payload network events vis lift coupled right rightMember
  obtain ⟨entry,member,same,past⟩ := (coupled.past left.op right.op a.1 b.1).mp (by simpa [a.2,b.2] using visible)
  have issued := NotionCorePayloadNetwork.forget_reachable reachable
  have recordMember : entry.record ∈ (forget network).records := List.mem_map.mpr ⟨entry,member,rfl⟩
  have smaller := (NotionCoreIssuance.record_provenance issued entry.record recordMember).2.1 _ past
  have positive := NotionCorePayload.width_positive left.op.payload
  change (reservation left.op).last < entry.tx.id.counter at smaller
  have lower : left.op.id.counter ≤ (reservation left.op).last := by
    simp only [reservation,NotionRunAllocation.Run.last]
    omega
  rw [same] at smaller
  exact Or.inl (lt_of_le_of_lt lower smaller)

 theorem witness_enumerates (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (supported : selected ⊆ events) :
    listPermOf (witness network selected lift) selected := by
  have ordered := NotionCoreReconstruction.transactionsFor_ordered network reachable (version network selected lift)
  constructor
  · apply (List.pairwise_map (f := lift) (R := fun a b : Event => a ≠ b)).mpr
    apply ordered.imp_of_mem
    intro left right leftMember rightMember before equal
    have a := (selected_transactions network reachable selected lift left).mp leftMember
    have b := (selected_transactions network reachable selected lift right).mp rightMember
    have payloadEq : left = right := by
      have h := congrArg Op.op equal
      simpa [coupled.payload left a.1,coupled.payload right b.1] using h
    exact NotionCoreSourceInvariant.before_irrefl _ (payloadEq ▸ before)
  · intro event
    constructor
    · intro member
      obtain ⟨tx,txMember,same⟩ := List.mem_map.mp member
      exact same ▸ ((selected_transactions network reachable selected lift tx).mp txMember).2
    · intro member
      have found := event_payload network events vis lift coupled event (supported member)
      exact List.mem_map.mpr ⟨event.op,
        (selected_transactions network reachable selected lift event.op).mpr ⟨found.1,by simpa [found.2] using member⟩,found.2⟩

 theorem witness_payloads (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) :
    (witness network selected lift).map Op.op =
      NotionCoreReconstruction.transactionsFor network (version network selected lift) := by
  unfold witness
  simp only [List.map_map]
  conv_rhs => rw [← List.map_id (NotionCoreReconstruction.transactionsFor network (version network selected lift))]
  apply List.map_congr_left
  intro tx member
  exact coupled.payload tx ((selected_transactions network reachable selected lift tx).mp member).1

/-- The very same event enumeration respects source-visible dependencies. -/
theorem witness_respects (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (_supported : selected ⊆ events) :
    respects (witness network selected lift) vis := by
  have ordered := NotionCoreReconstruction.transactionsFor_ordered network reachable (version network selected lift)
  apply (List.pairwise_map (f := lift) (R := fun a b => ¬ vis b a)).mpr
  apply ordered.imp_of_mem
  intro left right leftMember rightMember before reverse
  have a := (selected_transactions network reachable selected lift left).mp leftMember
  have b := (selected_transactions network reachable selected lift right).mp rightMember
  have leftEvent := (coupled.events (lift left)).mpr ⟨left,a.1,rfl⟩
  have rightEvent := (coupled.events (lift right)).mpr ⟨right,b.1,rfl⟩
  have backwards := visibility_before network reachable events vis lift coupled _ _ rightEvent leftEvent reverse
  rw [coupled.payload left a.1,coupled.payload right b.1] at backwards
  exact NotionCoreSourceInvariant.before_asymm before backwards

/-- Event causal closure transports to the archive's captured reservation past.
This is the structural obligation used by closed-version replay; no replay
acceptance, state invariant, or sequential observation is assumed. -/
theorem version_closed (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift)
    (closed : ∀ left right, vis left right → right ∈ selected → left ∈ selected) :
    NotionCoreIssuance.Closed (forget network).records (version network selected lift) := by
  classical
  intro record recordMember present old past
  obtain ⟨entry,entryMember,recordEq⟩ := List.mem_map.mp recordMember
  subst record
  have entryArchived : entry.tx ∈ archive network := List.mem_map.mpr ⟨entry,entryMember,rfl⟩
  have txSelected : entry.tx ∈ NotionCoreReconstruction.transactionsFor network (version network selected lift) :=
    (NotionCoreReconstruction.transactionsFor_membership network _ entry.tx).mpr ⟨⟨entry,entryMember,rfl⟩,present⟩
  have selectedEntry := ((selected_transactions network reachable selected lift entry.tx).mp txSelected).2
  have issued := NotionCorePayloadNetwork.forget_reachable reachable
  have published := (NotionCoreIssuance.record_provenance issued entry.record
    (List.mem_map.mpr ⟨entry,entryMember,rfl⟩)).2.2 old past
  rw [← NotionCoreIssuance.record_runs issued] at published
  obtain ⟨oldRecord,oldMember,runEq⟩ := List.mem_map.mp published
  obtain ⟨provider,providerMember,providerEq⟩ := List.mem_map.mp oldMember
  have providerRun : reservation provider.tx = old := by
    rw [← providerEq] at runEq
    exact runEq
  have providerArchived : provider.tx ∈ archive network := List.mem_map.mpr ⟨provider,providerMember,rfl⟩
  have visible := (coupled.past provider.tx entry.tx providerArchived entryArchived).mpr
    ⟨entry,entryMember,rfl,by simpa [providerRun] using past⟩
  have providerSelected := closed _ _ visible selectedEntry
  exact List.mem_map.mpr ⟨provider.tx,List.mem_filter.mpr ⟨providerArchived,by simpa using providerSelected⟩,providerRun⟩

/-- Non-mint steps, including saved-version snapshots and restoration, keep
the same event coupling because archive entries and their captured past do
not change. Allocation receipt/clock changes are deliberately not constrained. -/
theorem coupling_archive_frame (network next : State) (entries : next.entries = network.entries)
    (events : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) : Coupling next events vis lift := by
  constructor
  · intro tx member
    apply coupled.payload tx
    simpa [archive,entries] using member
  · intro event
    simpa [archive,entries] using coupled.events event
  · intro left right leftMember rightMember
    simpa [archive,entries] using coupled.past left right
      (by simpa [archive,entries] using leftMember) (by simpa [archive,entries] using rightMember)

/-- Exact obligations for extending the common coupling at a Sal apply.
The issuer's saved mint version must match the actual source receipts; the
new outer label is separate from the prepared transaction ID. This predicate
contains no sequential correctness or next-state observation assertion.
Proving extension from actual Sal/source issuance remains a separate theorem. -/
structure MintMatch (network : State) (mintPast : Set Event) (lift : Transaction → Event)
    (peer : NotionRunAllocation.Session) (tx : Transaction) (event : Event) : Prop where
  payload : event.op = tx
  receipts : ∀ previous ∈ archive network,
    (reservation previous ∈ (network.allocation.peers peer).received ↔ lift previous ∈ mintPast)
  labelFresh : ∀ previous ∈ archive network, lift previous ≠ event
  client : ∃ state request, NotionCoreReconstruction.reconstruct network peer = some state ∧
    NotionCoreMachineNetwork.prepareRequest state request = some tx.payload ∧ request.earlyNoop = false
  prepared : NotionCorePayload.prepare (forget network) peer tx.payload = some tx

/- A source key does not prescribe its Sal timestamp. The singleton coupling
is positive, while equality with the source counter is explicitly rejected. -/
namespace SPOT
private def tx := NotionCorePayload.bootstrap [97]
private def lift (value : Transaction) : Event := (99,7,value)
theorem distinct_clock_control :
    Coupling (NotionCorePayloadNetwork.seeded [97]) {lift tx} (fun _ _ => False) lift ∧
    (lift tx).time = 99 ∧ (lift tx).time ≠ tx.id.counter := by
  constructor
  · constructor
    · intro value member
      rfl
    · intro event
      simp [archive,NotionCorePayloadNetwork.seeded,tx,eq_comm]
    · intro left right leftMember rightMember
      simp [archive,NotionCorePayloadNetwork.seeded] at leftMember rightMember
      subst left; subst right
      simp [NotionCorePayloadNetwork.seeded]
  · decide +kernel
end SPOT

#print axioms version_unique
#print axioms version_supported
#print axioms coupling_archive_frame
#print axioms source_key_injective
#print axioms visibility_before
#print axioms witness_enumerates
#print axioms witness_payloads
#print axioms witness_respects
#print axioms version_closed
#print axioms SPOT.distinct_clock_control
end Sal.MRDTs.Instances.NotionCoreArchiveEvents
