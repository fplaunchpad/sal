import Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier
import Mathlib.Tactic

/-! Structural event/version transport for one honest rich archive. Coupling
contains only payload coverage and captured-past/visibility correspondence.
The actual protocol derives it by initialization and step induction in
NotionCoreRichProtocol; it contains no sequential correctness or query equation. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolEvents
open Sal.MRDTs.Foundation
open NotionCoreRichPayload (Transaction)
abbrev reservation (tx : Transaction) := tx.reservation
open NotionCoreRichProtocolNetwork (State Entry)
open NotionRunAllocation (Run)
abbrev Event := Op Transaction
abbrev archive (network : State) := network.entries.map Entry.transaction

theorem archive_keys_unique (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network) :
    ((archive network).map Transaction.id).Nodup := by
  simpa only [archive,List.map_map,Function.comp_def] using
    NotionCoreRichProtocolNetwork.archive_keys_unique reachable

/-- Outer event labels are assigned separately from compound source IDs.
The captured source mint past agrees with visibility, in one common archive. -/
structure Coupling (network : State) (events : Set Event) (vis : Event → Event → Prop)
    (lift : Transaction → Event) : Prop where
  payload : ∀ tx ∈ archive network, (lift tx).op = tx
  events : ∀ event, event ∈ events ↔ ∃ tx ∈ archive network, lift tx = event
  past : ∀ left right, left ∈ archive network → right ∈ archive network →
    (vis (lift left) (lift right) ↔
      ∃ entry ∈ network.entries, entry.transaction = right ∧ reservation left ∈ entry.past)

/-- A version selects archived transactions by event membership. It contains
no unknown reservations and does not require any current peer to hold it. -/
noncomputable def version (network : State) (selected : Set Event)
    (lift : Transaction → Event) : List Run := by
  classical
  exact ((archive network).filter (fun tx => lift tx ∈ selected)).map reservation

def transactionsFor (network : State) (runs : List Run) : List Transaction :=
  NotionCoreRichPayload.sort ((network.entries.filter fun entry =>
    runs.contains entry.transaction.reservation).map Entry.transaction)

theorem transactionsFor_membership (network : State) (runs : List Run) (tx : Transaction) :
    tx ∈ transactionsFor network runs ↔
      (∃ entry ∈ network.entries, entry.transaction = tx) ∧ reservation tx ∈ runs := by
  rw [transactionsFor, (NotionCoreRichPayload.sort_perm _).mem_iff]
  simp only [List.mem_map,List.mem_filter,List.contains_iff_mem]
  constructor
  · rintro ⟨entry,⟨he,hr⟩,rfl⟩
    exact ⟨⟨entry,he,rfl⟩,hr⟩
  · rintro ⟨⟨entry,he,rfl⟩,hr⟩
    exact ⟨entry,⟨he,hr⟩,rfl⟩

theorem transactionsFor_ordered (network : State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (runs : List Run) :
    (transactionsFor network runs).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) := by
  apply NotionCoreRichPayload.sort_ordered
  have kept := (List.filter_sublist (p := fun entry : Entry =>
    runs.contains entry.transaction.reservation) (l := network.entries)).map
      (fun entry => entry.transaction.id)
  simpa only [List.map_map,Function.comp_def] using
    kept.nodup (NotionCoreRichProtocolNetwork.archive_keys_unique reachable)

noncomputable def witness (network : State) (selected : Set Event)
    (lift : Transaction → Event) : List Event :=
  (NotionCoreRichProtocolEvents.transactionsFor network (version network selected lift)).map lift

private theorem reservation_injective (network : State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (left right : Transaction)
    (leftMember : left ∈ archive network) (rightMember : right ∈ archive network)
    (same : reservation left = reservation right) : left = right :=
  List.inj_on_of_nodup_map (archive_keys_unique network reachable)
    leftMember rightMember (congrArg Run.first same)

theorem version_supported (network : State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (selected : Set Event) (lift : Transaction → Event) :
    ∀ run ∈ version network selected lift, run ∈ network.allocation.published := by
  classical
  intro run member
  obtain ⟨tx, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨entry, archived, rfl⟩ := List.mem_map.mp (List.mem_filter.mp filtered).1
  rw [← NotionCoreRichProtocolNetwork.archive_runs reachable]
  exact List.mem_map.mpr ⟨entry,archived,rfl⟩

theorem version_unique (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (selected : Set Event) (lift : Transaction → Event) : (version network selected lift).Nodup := by
  classical
  have keys := archive_keys_unique network reachable
  have pairwise : (archive network).Pairwise (fun a b => a.id ≠ b.id) :=
    (List.pairwise_map (f := Transaction.id) (R := fun a b => a ≠ b)).mp keys
  apply (List.pairwise_map (f := reservation) (R := fun a b => a ≠ b)).mpr
  apply (pairwise.filter (fun tx => lift tx ∈ selected)).imp
  intro left right different same
  exact different (congrArg Run.first same)

 theorem selected_transactions (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (selected : Set Event) (lift : Transaction → Event) (tx : Transaction) :
    tx ∈ NotionCoreRichProtocolEvents.transactionsFor network (version network selected lift) ↔
      tx ∈ archive network ∧ lift tx ∈ selected := by
  classical
  rw [NotionCoreRichProtocolEvents.transactionsFor_membership]
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

 theorem source_key_injective (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (left right : Event)
    (leftMember : left ∈ events) (rightMember : right ∈ events)
    (same : left.op.id = right.op.id) : left = right := by
  have a := event_payload network events vis lift coupled left leftMember
  have b := event_payload network events vis lift coupled right rightMember
  have txEq := List.inj_on_of_nodup_map (archive_keys_unique network reachable)
    a.1 b.1 same
  rw [← a.2,← b.2,txEq]

/-- Visibility increases source counters, independently of outer timestamps. -/
theorem visibility_before (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (left right : Event)
    (leftMember : left ∈ events) (rightMember : right ∈ events) (visible : vis left right) :
    NotionRunAllocation.Before left.op.id right.op.id := by
  have a := event_payload network events vis lift coupled left leftMember
  have b := event_payload network events vis lift coupled right rightMember
  obtain ⟨entry,member,same,past⟩ := (coupled.past left.op right.op a.1 b.1).mp (by simpa [a.2,b.2] using visible)
  have smaller := (NotionCoreRichProtocolNetwork.entry_provenance reachable entry member).1 _ past
  have positive := NotionCoreRichProtocolNetwork.width_positive left.op.payload
  change (reservation left.op).last < entry.transaction.id.counter at smaller
  have lower : left.op.id.counter ≤ (reservation left.op).last := by
    simp only [reservation,NotionCoreRichPayload.Transaction.reservation,NotionRunAllocation.Run.last]
    omega
  rw [same] at smaller
  exact Or.inl (lt_of_le_of_lt lower smaller)

theorem witness_enumerates (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (supported : selected ⊆ events) :
    listPermOf (witness network selected lift) selected := by
  have ordered := NotionCoreRichProtocolEvents.transactionsFor_ordered network reachable (version network selected lift)
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

 theorem witness_payloads (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) :
    (witness network selected lift).map Op.op =
      NotionCoreRichProtocolEvents.transactionsFor network (version network selected lift) := by
  unfold witness
  simp only [List.map_map]
  conv_rhs => rw [← List.map_id (NotionCoreRichProtocolEvents.transactionsFor network (version network selected lift))]
  apply List.map_congr_left
  intro tx member
  exact coupled.payload tx ((selected_transactions network reachable selected lift tx).mp member).1

/-- The very same event enumeration respects source-visible dependencies. -/
theorem witness_respects (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift) (_supported : selected ⊆ events) :
    respects (witness network selected lift) vis := by
  have ordered := NotionCoreRichProtocolEvents.transactionsFor_ordered network reachable (version network selected lift)
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
abbrev Closed (network : State) (runs : List Run) : Prop :=
  ∀ entry ∈ network.entries, reservation entry.transaction ∈ runs →
    ∀ previous ∈ entry.past, previous ∈ runs

theorem version_closed (network : State) (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (events selected : Set Event) (vis : Event → Event → Prop) (lift : Transaction → Event)
    (coupled : Coupling network events vis lift)
    (closed : ∀ left right, vis left right → right ∈ selected → left ∈ selected) :
    Closed network (version network selected lift) := by
  classical
  intro entry entryMember present old past
  have entryArchived : entry.transaction ∈ archive network := List.mem_map.mpr ⟨entry,entryMember,rfl⟩
  have txSelected : entry.transaction ∈ transactionsFor network (version network selected lift) :=
    (transactionsFor_membership network _ entry.transaction).mpr ⟨⟨entry,entryMember,rfl⟩,present⟩
  have selectedEntry := ((selected_transactions network reachable selected lift entry.transaction).mp txSelected).2
  have published := (NotionCoreRichProtocolNetwork.entry_provenance reachable entry entryMember).2 old past
  rw [← NotionCoreRichProtocolNetwork.archive_runs reachable] at published
  obtain ⟨provider,providerMember,providerRun⟩ := List.mem_map.mp published
  have providerArchived : provider.transaction ∈ archive network := List.mem_map.mpr ⟨provider,providerMember,rfl⟩
  have visible := (coupled.past provider.transaction entry.transaction providerArchived entryArchived).mpr
    ⟨entry,entryMember,rfl,by simpa [providerRun] using past⟩
  have providerSelected := closed _ _ visible selectedEntry
  exact List.mem_map.mpr ⟨provider.transaction,List.mem_filter.mpr
    ⟨providerArchived,by simpa using providerSelected⟩,providerRun⟩

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


#print axioms witness_enumerates
#print axioms witness_respects
#print axioms version_closed
end Sal.MRDTs.Instances.NotionCoreRichProtocolEvents
