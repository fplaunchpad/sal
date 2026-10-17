import Sal.MRDTs.Instances.NotionCorePayloadNetwork
import Sal.MRDTs.Instances.NotionCoreMachine

/-! Creator provenance strengthens typed network admission without copying its
state. Creator knowledge supplies metadata availability, not active-gap
selection or complete machine replay progress. -/
namespace Sal.MRDTs.Instances.NotionCoreCreatorNetwork
open NotionRunAllocation (Id Run Session)
open NotionCorePayload
open NotionCorePayloadNetwork (State Entry)

def createdBlocks (tx : Transaction) : List BlockKey := match tx.payload with
  | .bootstrap _ => [.initial]
  | .create _ | .split _ _ _ => [.issued tx.id]
  | _ => []

def requiredBlocks : Payload → List BlockKey
  | .bootstrap _ => []
  | .create afterBlock => afterBlock.toList
  | .insert block inst _ _ | .split block inst _ => [block, inst]
  | .erase block groups => block :: groups.map Prod.fst
  | .merge source target => [source, target]

def KnownCreator (state : State) (session : Session) (block : BlockKey) : Prop :=
  ∃ provider ∈ state.entries,
    reservation provider.tx ∈ (state.allocation.peers session).received ∧
      block ∈ createdBlocks provider.tx

inductive Reach : State → Prop where
  | init : Reach NotionCorePayloadNetwork.initial
  | bootstrap (atoms : List Nat) : Reach (NotionCorePayloadNetwork.seeded atoms)
  | exchange {state : State} (target source : Session) :
      Reach state → Reach (NotionCorePayloadNetwork.exchange state target source)
  | gap {state : State} (session : Session) (ticks : Nat) :
      Reach state → Reach (NotionCorePayloadNetwork.gap state session ticks)
  | emit {state : State} (session : Session) (payload : Payload) (tx : Transaction) :
      Reach state → prepare (NotionCorePayloadNetwork.forget state) session payload = some tx →
      (∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
        NotionCorePayloadNetwork.Known state session address) →
      (∀ block ∈ requiredBlocks payload, KnownCreator state session block) →
      Reach (NotionCorePayloadNetwork.emit state session payload tx)

theorem payload_reachable {state : State} (reachable : Reach state) :
    NotionCorePayloadNetwork.Reach state := by
  induction reachable with
  | init => exact .init
  | bootstrap atoms => exact .bootstrap atoms
  | exchange target source _ ih => exact .exchange target source ih
  | gap session ticks _ ih => exact .gap session ticks ih
  | emit session payload tx _ prepared known creators ih => exact .emit session payload tx ih prepared known

theorem creator_provenance {state : State} (reachable : Reach state) :
    ∀ entry ∈ state.entries, ∀ block ∈ requiredBlocks entry.tx.payload,
      ∃ provider ∈ state.entries, reservation provider.tx ∈ entry.past ∧
        block ∈ createdBlocks provider.tx := by
  induction reachable with
  | init => simp [NotionCorePayloadNetwork.initial]
  | bootstrap atoms => simp [NotionCorePayloadNetwork.seeded, bootstrap, requiredBlocks]
  | exchange target source _ ih => exact ih
  | gap session ticks _ ih => exact ih
  | @emit state session payload tx _ prepared known creators ih =>
      intro entry member block required
      rcases List.mem_cons.mp member with rfl | member
      · rw [NotionCorePayloadNetwork.prepared_payload prepared] at required
        obtain ⟨provider, present, received, created⟩ := creators block required
        exact ⟨provider, List.mem_cons_of_mem _ present, received, created⟩
      · obtain ⟨provider, present, past, created⟩ := ih entry member block required
        exact ⟨provider, List.mem_cons_of_mem _ present, past, created⟩

/-- Metadata creator availability is an archive-closed property, not tied
to a currently registered peer version. -/
theorem replay_creator_provider_version {state : State} (reachable : Reach state)
    (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget state).records version)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      version = pre ++ reservation entry.tx :: suffix)
    {block : BlockKey} (required : block ∈ requiredBlocks entry.tx.payload) :
    ∃ provider ∈ state.entries, reservation provider.tx ∈ pre ∧
      block ∈ createdBlocks provider.tx ∧
      (reservation provider.tx).last < entry.tx.id.counter := by
  obtain ⟨provider, present, past, created⟩ := creator_provenance reachable entry member block required
  have issued := NotionCorePayloadNetwork.forget_reachable (payload_reachable reachable)
  have member' : entry.record ∈ (NotionCorePayloadNetwork.forget state).records :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have prior := NotionCoreIssuance.past_in_prefix issued member' pre suffix
    (position ▸ NotionCoreIssuance.replay_closed issued version closed)
    (position ▸ NotionCoreIssuance.replay_ordered issued version) (reservation provider.tx) past
  exact ⟨provider, present, prior, created,
    (NotionCoreIssuance.record_provenance issued entry.record member').2.1 _ past⟩

/-- Existing receipt replay specializes the explicit closed archive version. -/
theorem replay_creator_provider {state : State} (reachable : Reach state) (peer : Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      (state.allocation.peers peer).received = pre ++ reservation entry.tx :: suffix)
    {block : BlockKey} (required : block ∈ requiredBlocks entry.tx.payload) :
    ∃ provider ∈ state.entries, reservation provider.tx ∈ pre ∧
      block ∈ createdBlocks provider.tx ∧
      (reservation provider.tx).last < entry.tx.id.counter :=
  replay_creator_provider_version reachable _
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable (payload_reachable reachable)) peer)
    member pre suffix position required

#print axioms replay_creator_provider_version

private def first : Id := ⟨1,[66]⟩
private def second : Id := ⟨2,[66]⟩
private def insertion : Transaction := ⟨first, .insert .initial .initial .start [97]⟩
private def cut : Transaction := ⟨second, .split .initial .initial (.item first)⟩
private def inserted : State := NotionCorePayloadNetwork.emit NotionCorePayloadNetwork.initial
  [66] insertion.payload insertion
private def splitIssued : State := NotionCorePayloadNetwork.emit inserted [66] cut.payload cut

private theorem first_admitted : NotionCorePayloadNetwork.Reach inserted := by
  apply NotionCorePayloadNetwork.Reach.emit [66] insertion.payload insertion .init
  · decide
  · simp [insertion, NotionCorePayloadNetwork.locatedReferences, originReference]
private theorem second_admitted : NotionCorePayloadNetwork.Reach splitIssued := by
  apply NotionCorePayloadNetwork.Reach.emit [66] cut.payload cut first_admitted
  · decide
  · intro address member
    have same : address = (.initial, first) := by simpa [cut, NotionCorePayloadNetwork.locatedReferences, originReference] using member
    subst address
    simp [NotionCorePayloadNetwork.Known, inserted, NotionCorePayloadNetwork.emit,
      NotionCorePayloadNetwork.initial, reservation, insertion, NotionRunAllocation.issue,
      NotionRunAllocation.reserve, NotionRunAllocation.initial, NotionRunAllocation.emptyPeer,
      NotionRunAllocation.receive, Payload.width, Payload.itemCount, NotionCorePayloadNetwork.birthAddresses,
      births, operations, Operation.births, textItems, NotionCoreParentMap.runRows,
      birthId, offsetId, first]

/-- PASS+FAIL: the old typed admission accepts both transactions, but the
actual two-step machine replay fails to find a source slice for the marker. -/
theorem missing_creator_control : NotionCorePayloadNetwork.Reach splitIssued ∧
    NotionCoreMachine.replay {} [insertion, cut] = none ∧
    NotionCoreMachine.replay {} [insertion, cut] ≠ some {} := by
  exact ⟨second_admitted, by decide, by decide⟩

/-- PASS+FAIL: known item provenance after the first transaction does not
manufacture a creator for the initial block. -/
theorem absent_creator_control :
    .initial ∈ requiredBlocks insertion.payload ∧
    ¬ KnownCreator inserted [66] .initial := by
  simp [requiredBlocks, insertion, KnownCreator, inserted, NotionCorePayloadNetwork.emit,
    NotionCorePayloadNetwork.initial, createdBlocks]


/-- The stronger admission relation excludes the unseeded insertion. This
negative belongs to the theorem layer: it uses reachable provenance rather
than attempting to decide an inductive execution relation in a SPOT. -/
theorem unseeded_insertion_excluded : ¬ Reach inserted := by
  intro reachable
  have member : (⟨insertion, []⟩ : Entry) ∈ inserted.entries := by
    simp [inserted, NotionCorePayloadNetwork.emit, NotionCorePayloadNetwork.initial,
      NotionRunAllocation.initial, NotionRunAllocation.emptyPeer]
  have required : .initial ∈ requiredBlocks insertion.payload := by decide
  obtain ⟨provider, present, past, created⟩ := creator_provenance reachable _ member .initial required
  have same : provider = ⟨insertion, []⟩ := by
    simpa [inserted, NotionCorePayloadNetwork.emit, NotionCorePayloadNetwork.initial,
      NotionRunAllocation.initial, NotionRunAllocation.emptyPeer] using present
  subst provider
  simp [createdBlocks, insertion] at created

/-- PASS+FAIL: bootstrap creates initial, despite sharing its transaction key
with its first text atom; it does not create the issued-key block. -/
theorem bootstrap_creator_control :
    KnownCreator (NotionCorePayloadNetwork.seeded [97]) [65] .initial ∧
    ¬ KnownCreator (NotionCorePayloadNetwork.seeded [97]) [65] (.issued ⟨1,[65]⟩) := by
  simp [KnownCreator, NotionCorePayloadNetwork.seeded, NotionCorePayloadNetwork.initial,
    NotionRunAllocation.reserve, bootstrap, createdBlocks,
    reservation, NotionRunAllocation.issue, NotionRunAllocation.initial,
    NotionRunAllocation.emptyPeer, NotionRunAllocation.receive]

/-- PASS+FAIL: a metadata-only creation supplies a block creator without an
RGA item birth. The item-production filter cannot serve as creator provenance. -/
theorem metadata_creator_control :
    createdBlocks ⟨first, .create none⟩ = [.issued first] ∧
    births ⟨first, .create none⟩ (fun _ _ => false) = [] ∧
    createdBlocks ⟨first, .create none⟩ ≠ [] := by decide

#print axioms replay_creator_provider
#print axioms missing_creator_control
end Sal.MRDTs.Instances.NotionCoreCreatorNetwork
