import Sal.MRDTs.Instances.NotionCorePayload

/-! Typed transaction archives with located item provenance.
The question is whether the actual payload that supplied an origin occurs in
the sorted prefix, in the selected text instance. A globally allocated ID in
another instance is a falsifier of the weaker, unlocated condition.

This layer derives issuance records from payloads. Client selection still
supplies membership in a received provider's births; connecting that selection
to the joint document interpreter remains a separate obligation.
-/
namespace Sal.MRDTs.Instances.NotionCorePayloadNetwork
open NotionRunAllocation (Id Run Session Network)
open NotionCorePayload

abbrev Address := BlockKey × Id

def locatedReferences : Payload → List Address
  | .insert _ inst origin _ | .split _ inst origin => (originReference origin).map (inst, ·)
  | .erase _ inst targets => targets.map (inst, ·)
  | .bootstrap _ | .create _ => []

theorem located_references_ids (payload : Payload) :
    (locatedReferences payload).map Prod.snd = payload.references := by
  cases payload <;> simp [locatedReferences, Payload.references, List.map_map]

def birthAddresses (tx : Transaction) : List Address :=
  (births tx (fun _ _ => false)).map (fun birth => (birth.1, birthId birth))

theorem runRows_addresses (inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (items : List NotionCoreOriginTree.Item) :
    (NotionCoreParentMap.runRows origin items).map
      (fun row => (inst, birthId (inst, row))) = items.map (fun item => (inst, item.id)) := by
  induction items generalizing origin with
  | nil => rfl
  | cons item rest ih =>
    simp only [NotionCoreParentMap.runRows, List.map_cons]
    rw [ih]
    rfl

/-- Tombstones alter visibility, never the instance or ID of a birth. Thus
the archive's provider theorem applies to actual replay with pending deletes. -/
theorem birthAddresses_deleted (tx : Transaction) (deleted : BlockKey → Id → Bool) :
    (births tx deleted).map (fun birth => (birth.1, birthId birth)) = birthAddresses tx := by
  cases tx with
  | mk id payload =>
    cases payload <;>
      simp only [birthAddresses, births, operations, Operation.births,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
        List.map_cons, List.map_nil, runRows_addresses,
        textItems, List.map_map, Function.comp_def]

theorem birth_address_record {tx : Transaction} {address : Address}
    (member : address ∈ birthAddresses tx) (past : List Run) :
    (record tx past).items = true ∧ (record tx past).run.Contains address.2 := by
  apply (born_iff_record tx past (fun _ _ => false) address.2).mp
  obtain ⟨birth, present, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨birth, present, congrArg Prod.snd same⟩

structure Entry where
  tx : Transaction
  past : List Run
  deriving DecidableEq, Repr

def Entry.record (entry : Entry) : NotionCoreIssuance.Record := NotionCorePayload.record entry.tx entry.past

structure State where
  allocation : Network
  entries : List Entry

def forget (state : State) : NotionCoreIssuance.State :=
  ⟨state.allocation, state.entries.map Entry.record⟩

def initial : State := ⟨NotionRunAllocation.initial, []⟩

def seeded (atoms : List Nat) : State :=
  ⟨NotionRunAllocation.issue initial.allocation [65] (Payload.bootstrap atoms).width,
    [⟨bootstrap atoms, []⟩]⟩

def exchange (state : State) (target source : Session) : State :=
  {state with allocation := (NotionCoreIssuance.importRuns state.allocation target
    (state.allocation.peers source).received)}

def gap (state : State) (session : Session) (ticks : Nat) : State :=
  {state with allocation := NotionRunAllocation.skip state.allocation session ticks}

def emit (state : State) (session : Session) (payload : Payload) (tx : Transaction) : State :=
  ⟨NotionRunAllocation.issue state.allocation session payload.width,
    ⟨tx, (state.allocation.peers session).received⟩ :: state.entries⟩

def Known (state : State) (session : Session) (address : Address) : Prop :=
  ∃ entry ∈ state.entries,
    reservation entry.tx ∈ (state.allocation.peers session).received ∧
    address ∈ birthAddresses entry.tx

theorem known_forget {state : State} {session : Session} {address : Address}
    (known : Known state session address) :
    NotionCoreIssuance.ItemKnown (forget state) session address.2 := by
  obtain ⟨entry, present, received, born⟩ := known
  exact ⟨entry.record, List.mem_map.mpr ⟨entry, present, rfl⟩, received,
    birth_address_record born entry.past⟩

theorem references_known {state : State} {session : Session} {payload : Payload}
    (known : ∀ address ∈ locatedReferences payload, Known state session address) :
    ∀ id ∈ payload.references, NotionCoreIssuance.ItemKnown (forget state) session id := by
  intro id member
  rw [← located_references_ids payload] at member
  obtain ⟨address, reference, rfl⟩ := List.mem_map.mp member
  exact known_forget (known address reference)

theorem forget_emit {state : State} {session : Session} {payload : Payload} {tx : Transaction}
    (prepared : prepare (forget state) session payload = some tx) :
    forget (emit state session payload tx) =
      NotionCoreIssuance.mint (forget state) session payload.width
        (decide (0 < payload.itemCount)) payload.references := by
  have same := prepare_record prepared
  change (⟨NotionRunAllocation.issue state.allocation session payload.width,
    record tx (state.allocation.peers session).received :: state.entries.map Entry.record⟩ :
      NotionCoreIssuance.State) = _
  change record tx (state.allocation.peers session).received = _ at same
  rw [same]
  rfl

inductive Reach : State → Prop where
  | init : Reach initial
  | bootstrap (atoms : List Nat) : Reach (seeded atoms)
  | exchange {state : State} (target source : Session) :
      Reach state → Reach (exchange state target source)
  | gap {state : State} (session : Session) (ticks : Nat) :
      Reach state → Reach (gap state session ticks)
  | emit {state : State} (session : Session) (payload : Payload) (tx : Transaction) :
      Reach state → prepare (forget state) session payload = some tx →
      (∀ address ∈ locatedReferences payload, Known state session address) →
      Reach (emit state session payload tx)

theorem forget_reachable {state : State} (reachable : Reach state) :
    NotionCoreIssuance.Reach (forget state) := by
  induction reachable with
  | init => exact .init
  | bootstrap atoms =>
    exact NotionCoreIssuance.Reach.mint [65] (Payload.bootstrap atoms).width
      (decide (0 < (Payload.bootstrap atoms).itemCount)) [] .init
      (width_positive _) (by simp)
  | exchange target source _ ih => exact .exchange target source ih
  | gap session ticks _ ih => exact .gap session ticks ih
  | emit session payload tx _ prepared known ih =>
    rw [forget_emit prepared]
    exact (prepare_admitted ih prepared (references_known known)).1

theorem birth_ids_unique (tx : Transaction) (deleted : BlockKey → Id → Bool) :
    ((births tx deleted).map birthId).Nodup := by
  rw [birth_ids]
  apply List.Nodup.map _ List.nodup_range
  intro x y equal
  have counters := congrArg Id.counter equal
  simpa [offsetId] using counters

/-- Every actual prepared payload is fresh against all earlier typed births,
including transactions not received at its issuer. This derives the freshness
input needed by the parent-map insertion theorem from session allocation. -/
theorem prepared_births_fresh {state : State} (reachable : Reach state)
    {session : Session} {payload : Payload} {tx : Transaction}
    (prepared : prepare (forget state) session payload = some tx)
    (deleted : BlockKey → Id → Bool) :
    List.Disjoint ((births tx deleted).map birthId)
      (state.entries.flatMap (fun entry => (births entry.tx deleted).map birthId)) := by
  apply List.disjoint_left.mpr
  intro id newBirth oldBirth
  obtain ⟨entry, member, oldBirth⟩ := List.mem_flatMap.mp oldBirth
  have reachable' := forget_reachable reachable
  have allocation := NotionCoreIssuance.allocation_reachable reachable'
  have member' : entry.record ∈ (forget state).records := List.mem_map.mpr ⟨entry, member, rfl⟩
  have published := NotionCoreIssuance.record_published reachable' member'
  have reserved : reservation tx =
      NotionRunAllocation.reserve (state.allocation.peers session) session payload.width :=
    congrArg NotionCoreIssuance.Record.run (prepare_record prepared)
  have newContains := ((born_iff_record tx [] deleted id).mp newBirth).2
  change (reservation tx).Contains id at newContains
  rw [reserved] at newContains
  have oldContains := ((born_iff_record entry.tx entry.past deleted id).mp oldBirth).2
  have issued := NotionRunAllocation.Reach.issuance payload.width session allocation (width_positive payload)
  have equal := NotionRunAllocation.reachable_unique_owner issued _ (by simp [NotionRunAllocation.issue, forget])
    (reservation entry.tx) (List.mem_cons_of_mem _ published) id newContains oldContains
  exact NotionRunAllocation.fresh_transaction_key allocation published session payload.width
    (congrArg Run.first equal)

theorem prepared_payload {state : NotionCoreIssuance.State} {session : Session}
    {payload : Payload} {tx : Transaction} (prepared : prepare state session payload = some tx) :
    tx.payload = payload := by
  cases payload <;> simp only [prepare] at prepared
  all_goals try contradiction
  all_goals split at prepared <;> simp_all
  all_goals subst tx; rfl

/-- The provider has the requested instance as well as the item ID. Its past
membership is saved from the actual emission state, not supplied on replay. -/
theorem reference_provenance {state : State} (reachable : Reach state) :
    ∀ entry ∈ state.entries, ∀ address ∈ locatedReferences entry.tx.payload,
      ∃ provider ∈ state.entries, reservation provider.tx ∈ entry.past ∧
        address ∈ birthAddresses provider.tx := by
  induction reachable with
  | init => simp [initial]
  | bootstrap atoms => simp [seeded, bootstrap, locatedReferences]
  | exchange target source _ ih => exact ih
  | gap session ticks _ ih => exact ih
  | @emit state session payload tx _ prepared known ih =>
    intro entry present address reference
    rcases List.mem_cons.mp present with rfl | present
    · rw [prepared_payload prepared] at reference
      obtain ⟨provider, member, received, born⟩ := known address reference
      exact ⟨provider, List.mem_cons_of_mem _ member, received, born⟩
    · obtain ⟨provider, member, received, born⟩ := ih entry present address reference
      exact ⟨provider, List.mem_cons_of_mem _ member, received, born⟩

/-- Located payload origins/deletion targets have an actual typed provider in
every canonical replay prefix of a received whole version. No free birth tag,
provider-order premise, or desired observation equation appears here. -/
theorem replay_located_provider {state : State} (reachable : Reach state) (peer : Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received =
      pre ++ reservation entry.tx :: suffix)
    {address : Address} (reference : address ∈ locatedReferences entry.tx.payload) :
    ∃ provider ∈ state.entries, reservation provider.tx ∈ pre ∧
      address ∈ birthAddresses provider.tx ∧
      (reservation provider.tx).last < entry.tx.id.counter := by
  obtain ⟨provider, present, past, born⟩ := reference_provenance reachable entry member address reference
  have reachable' := forget_reachable reachable
  have member' : entry.record ∈ (forget state).records := List.mem_map.mpr ⟨entry, member, rfl⟩
  have earlier := NotionCoreIssuance.past_in_prefix reachable' member' pre suffix
    (position ▸ NotionCoreIssuance.replay_closed reachable' _
      (NotionCoreIssuance.peers_closed reachable' peer))
    (position ▸ NotionCoreIssuance.replay_ordered reachable' _) (reservation provider.tx) past
  exact ⟨provider, present, earlier, born,
    (NotionCoreIssuance.record_provenance reachable' entry.record member').2.1 _ past⟩

private def firstA : Id := ⟨1,[65]⟩
private def secondA : Id := ⟨2,[65]⟩
private def newB : Id := ⟨3,[66]⟩
private def copied : State := exchange (seeded [97,98]) [66] [65]
private def insertion : Payload := .insert .initial .initial (.item firstA) [88]
private def inserted : State := emit copied [66] insertion ⟨newB, insertion⟩

/-- PASS+FAIL: an item in the bootstrap text instance is not also present in
the unrelated generated instance, even though its global reservation exists. -/
theorem located_presence_control :
    Known copied [66] (.initial, secondA) ∧
    ¬ Known copied [66] (.issued firstA, secondA) := by
  simp [Known, copied, exchange, seeded, initial, reservation, bootstrap,
    NotionCoreIssuance.importRuns, NotionRunAllocation.issue, NotionRunAllocation.reserve,
    NotionRunAllocation.initial, NotionRunAllocation.emptyPeer, NotionRunAllocation.receive,
    NotionRunAllocation.deliver, Payload.width, Payload.itemCount, birthAddresses,
    births, operations, Operation.births, textItems, NotionCoreParentMap.runRows,
    birthId, offsetId, firstA, secondA, List.range_succ]

private theorem copied_known : Known copied [66] (.initial, firstA) := by
  simp [Known, copied, exchange, seeded, initial, reservation, bootstrap,
    NotionCoreIssuance.importRuns, NotionRunAllocation.issue, NotionRunAllocation.reserve,
    NotionRunAllocation.initial, NotionRunAllocation.emptyPeer, NotionRunAllocation.receive,
    NotionRunAllocation.deliver, Payload.width, Payload.itemCount, birthAddresses,
    births, operations, Operation.births, textItems, NotionCoreParentMap.runRows,
    birthId, offsetId, firstA, List.range_succ]

/-- The fixture exercises real typed emission after a whole-version exchange;
the two-atom provider reserves B@3, excluding the overlapping B@2 rival. -/
theorem typed_emission_control : Reach inserted ∧
    inserted.entries.head?.map (fun entry => entry.tx.id) = some newB ∧
    inserted.entries.head?.map (fun entry => entry.tx.id) ≠ some (⟨2,[66]⟩ : Id) := by
  refine ⟨?_, by decide, by decide⟩
  apply Reach.emit [66] insertion ⟨newB, insertion⟩ (.exchange [66] [65] (.bootstrap [97,98]))
  · decide
  · intro address reference
    have same : address = (.initial, firstA) := by
      simpa [insertion, locatedReferences, originReference] using reference
    exact same ▸ copied_known

/-- The actual canonical replay keeps the provider before its dependent edit,
despite the archive storing newest records first. -/
theorem typed_replay_control :
    (NotionCoreIssuance.replay (forget inserted) (inserted.allocation.peers [66]).received).map Run.first =
      [firstA, newB] ∧
    (NotionCoreIssuance.replay (forget inserted) (inserted.allocation.peers [66]).received).map Run.first ≠
      [newB, firstA] := by
  simp [NotionCoreIssuance.replay, forget, inserted, emit, copied, exchange, seeded, initial,
    Entry.record, record, reservation, bootstrap, insertion,
    NotionCoreIssuance.importRuns, NotionRunAllocation.issue, NotionRunAllocation.reserve,
    NotionRunAllocation.initial, NotionRunAllocation.emptyPeer, NotionRunAllocation.receive,
    NotionRunAllocation.deliver, Payload.width, Payload.itemCount, firstA, newB,
    Run.last, List.mergeSort, NotionCoreIssuance.Ascending,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]

#print axioms forget_reachable
#print axioms prepared_births_fresh
#print axioms replay_located_provider
end Sal.MRDTs.Instances.NotionCorePayloadNetwork
