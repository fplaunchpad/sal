import Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
import Sal.MRDTs.Instances.NotionCoreAllocationClock
import Sal.MRDTs.Instances.NotionCoreMachineNetwork

/-! Executable rich caller issuance. Whole-version exchange reconstructs whole
atomic transactions; clocks reserve one ID per formatting segment. Formatting
selects the actual rich query, not caller-supplied identities or bold bits.
The caller additionally checks located source references before publication.
This repaired typed caller uses one shared priority per whole format batch.
The outer framework protocol is defined in NotionCoreRichProtocol.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolNetwork
open NotionRunAllocation (Id Run Session)
open NotionCoreRichPayload (Transaction Payload Part)
open NotionCoreFormattingSource (MarkOp Character Endpoint)

structure Entry where
  transaction : Transaction
  past : List Run
  deriving DecidableEq, Repr

structure State where
  allocation : NotionRunAllocation.Network
  entries : List Entry

def initial : State := ⟨NotionRunAllocation.initial,[]⟩

/-- Internal publication primitive. Reachable requests call `emit`, which
constructs this transaction from the actual allocator rather than accepting
an independently supplied ID. -/
def publish (state : State) (session : Session) (transaction : Transaction) : State :=
  ⟨NotionRunAllocation.issue state.allocation session transaction.payload.width,
    ⟨transaction,(state.allocation.peers session).received⟩ :: state.entries⟩

def emit (state : State) (session : Session) (payload : Payload) : State :=
  let run := NotionRunAllocation.reserve (state.allocation.peers session) session payload.width
  publish state session ⟨run.first,payload⟩

def seeded (text : List Nat) : State := emit initial [65] (.edit (.bootstrap text))

def exchange (state : State) (target source : Session) : State :=
  {state with allocation := (NotionCoreIssuance.importRuns state.allocation target
    (state.allocation.peers source).received)}

theorem exchange_received (state : State) (target source peer : Session) (run : Run) :
    run ∈ ((exchange state target source).allocation.peers peer).received ↔
      run ∈ (state.allocation.peers peer).received ∨
        peer = target ∧ run ∈ (state.allocation.peers source).received :=
  NotionCoreIssuance.import_received state.allocation target _ peer run

theorem exchange_other_peer (state : State) (target source peer : Session)
    (different : peer ≠ target) :
    (exchange state target source).allocation.peers peer = state.allocation.peers peer := by
  have untouched : ∀ runs : List Run,
      (NotionCoreIssuance.importRuns state.allocation target runs).peers peer = state.allocation.peers peer := by
    intro runs
    generalize state.allocation = allocation
    induction runs generalizing allocation with
    | nil => rfl
    | cons run rest ih =>
      rw [NotionCoreIssuance.importRuns, ih]
      simp [NotionRunAllocation.deliver, different]
  exact untouched _

def receivedTransactions (state : State) (session : Session) : List Transaction :=
  (state.entries.filter fun entry =>
    (state.allocation.peers session).received.contains entry.transaction.reservation).map Entry.transaction

def reconstruct (state : State) (session : Session) : Option NotionCoreAtomicFormattingMachine.State :=
  NotionCoreAtomicFormattingMachine.replay {} (NotionCoreRichPayload.sort (receivedTransactions state session))

def birthAddresses (transaction : Transaction) : List (Nat × Id) :=
  match transaction.payload with
  | .edit payload => (NotionCorePayloadNetwork.birthAddresses ⟨transaction.id,payload⟩).map
      fun (inst,id) => (NotionCoreMachine.blockName inst,id)
  | .format _ _ => []

def endpointReferences (inst : Nat) : Endpoint → List (Nat × Id)
  | .item id => [(inst,id)]
  | _ => []

def references : Payload → List (Nat × Id)
  | .edit payload => (NotionCorePayloadNetwork.locatedReferences payload).map
      fun (inst,id) => (NotionCoreMachine.blockName inst,id)
  | .format parts _ => parts.flatMap fun part =>
      endpointReferences part.instanceId part.lower.endpoint ++
        endpointReferences part.instanceId part.upper.endpoint

def known (state : State) (session : Session) (address : Nat × Id) : Bool :=
  state.entries.any fun entry =>
    (state.allocation.peers session).received.contains entry.transaction.reservation &&
      (birthAddresses entry.transaction).contains address

def decodeCharacter (state : NotionCoreAtomicFormattingMachine.State)
    (atom : NotionCoreAtomicFormattingMachine.RichAtom) : Option Character := do
  let found ← (NotionCoreAtomicFormattingMachine.resolvedInstance state atom.address.1).find? fun formatted =>
    NotionCorePhysicalReplay.address atom.address.1 formatted.item.id == atom.address
  pure ⟨atom.address.1,found.item,atom.bold⟩

def selection (state : NotionCoreAtomicFormattingMachine.State) (block : NotionCorePayload.BlockKey)
    (start stop : Nat) : Option (List Character) := do
  let characters ← NotionCoreAtomicFormattingMachine.blockRich state (NotionCoreMachine.blockName block)
  ((characters.drop start).take (stop - start)).mapM (decodeCharacter state)

def formatPayload (state : NotionCoreAtomicFormattingMachine.State) (block : NotionCorePayload.BlockKey)
    (start stop : Nat) : Option Payload := do
  let characters ← selection state block start stop
  if characters.isEmpty then none else do
    let instances := (state.core.instances.map Prod.fst).eraseDups
    let targets := characters.map fun character =>
      NotionCorePhysicalReplay.address character.textInstance character.item.id
    let segments := NotionCoreFormattingPlanner.locatedSegments
      (NotionCoreAtomicFormattingMachine.instanceForest state) NotionCorePhysicalReplay.address targets instances
    if segments.isEmpty then none else
      pure (.format (NotionCoreRichPayload.partsOf segments) (!(characters.all Character.bold)))

inductive Request where
  | edit (request : NotionCoreMachineNetwork.Request)
  | toggle (block : NotionCorePayload.BlockKey) (start stop : Nat)
  deriving DecidableEq, Repr

def prepare (state : NotionCoreAtomicFormattingMachine.State) : Request → Option Payload
  | .edit request =>
      if request.earlyNoop then none else do
        let payload ← NotionCoreMachineNetwork.prepareRequest state.core request
        if payload.emits then some (.edit payload) else none
  | .toggle block start stop => formatPayload state block start stop

def prepareAt (state : State) (session : Session) (request : Request) : Option Payload := do
  let current ← reconstruct state session
  prepare current request

def issue (state : State) (session : Session) (request : Request) : Option State := do
  let payload ← prepareAt state session request
  if (references payload).all (known state session) then some (emit state session payload) else none

theorem width_positive (payload : Payload) : 0 < payload.width := by
  cases payload with
  | edit payload => exact NotionCorePayload.width_positive payload
  | format parts value => exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

theorem issue_data (state next : State) (session : Session) (request : Request)
    (accepted : issue state session request = some next) :
    ∃ current payload, reconstruct state session = some current ∧ prepare current request = some payload ∧
      (references payload).all (known state session) = true ∧ next = emit state session payload := by
  unfold issue at accepted
  obtain ⟨payload,prepared,afterPayload⟩ := Option.bind_eq_some_iff.mp accepted
  unfold prepareAt at prepared
  obtain ⟨current,currentEq,payloadEq⟩ := Option.bind_eq_some_iff.mp prepared
  split at afterPayload
  · exact ⟨current,payload,currentEq,payloadEq,by assumption,(Option.some.inj afterPayload).symm⟩
  · contradiction

/-- No supplied query, reference-knowledge, coordinate or freshness premise
occurs in protocol reachability. All requests execute the caller above. -/
inductive Reach : State → Prop where
  | init : Reach initial
  | bootstrap (text : List Nat) : Reach (seeded text)
  | exchange {state : State} (target source : Session) : Reach state → Reach (exchange state target source)
  | request {state next : State} (session : Session) (request : Request) :
      Reach state → issue state session request = some next → Reach next

theorem allocation_reachable {state : State} (reachable : Reach state) :
    NotionRunAllocation.Reach state.allocation := by
  induction reachable with
  | init => exact .init
  | bootstrap text => exact .issuance _ [65] .init (width_positive _)
  | @exchange state target source prior ih =>
      exact NotionCoreIssuance.import_reachable ih target _ (fun run member =>
        NotionRunAllocation.reachable_received_published ih source run member)
  | @request state next session request prior issued ih =>
      obtain ⟨current,payload,currentEq,payloadEq,known,rfl⟩ := issue_data state next session request issued
      exact .issuance _ session ih (width_positive payload)

theorem archive_runs {state : State} (reachable : Reach state) :
    (state.entries.map fun entry => entry.transaction.reservation) = state.allocation.published := by
  induction reachable with
  | init => rfl
  | bootstrap text => rfl
  | exchange target source prior ih => simpa [exchange] using ih
  | @request state next session request prior issued ih =>
      obtain ⟨current,payload,currentEq,payloadEq,known,rfl⟩ := issue_data state next session request issued
      simpa [emit,publish,NotionRunAllocation.issue,NotionRunAllocation.reserve,
        NotionCoreRichPayload.Transaction.reservation] using
        congrArg (NotionRunAllocation.reserve (state.allocation.peers session) session payload.width :: ·) ih

theorem archive_keys_unique {state : State} (reachable : Reach state) :
    (state.entries.map fun entry => entry.transaction.id).Nodup := by
  have keys := NotionRunAllocation.reachable_transaction_keys_unique (allocation_reachable reachable)
  rw [← archive_runs reachable] at keys
  simpa only [List.map_map,NotionCoreRichPayload.Transaction.reservation,Function.comp_def] using keys

theorem received_keys_unique {state : State} (reachable : Reach state) (session : Session) :
    ((receivedTransactions state session).map Transaction.id).Nodup := by
  have filtered : (state.entries.filter (fun entry : Entry =>
    (state.allocation.peers session).received.contains entry.transaction.reservation)).Sublist state.entries :=
    List.filter_sublist
  have kept := filtered.map (fun entry => entry.transaction.id)
  simpa only [receivedTransactions,List.map_map,Function.comp_def] using
    kept.nodup (archive_keys_unique reachable)

/-- A newly allocated run is disjoint from every old run, globally, including
unreceived annotations and edit births. It is not enough to guard tx IDs only. -/
theorem new_run_disjoint {state : State} (reachable : Reach state) (session : Session)
    (payload : Payload) (entry : Entry) (member : entry ∈ state.entries) (id : Id)
    (fresh : (NotionRunAllocation.reserve (state.allocation.peers session) session payload.width).Contains id)
    (old : entry.transaction.reservation.Contains id) : False := by
  have allocation := allocation_reachable reachable
  have published : entry.transaction.reservation ∈ state.allocation.published := by
    rw [← archive_runs reachable]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  have next := NotionRunAllocation.Reach.issuance payload.width session allocation (width_positive payload)
  have same := NotionRunAllocation.reachable_unique_owner next _ (by simp [NotionRunAllocation.issue])
    entry.transaction.reservation (by simp [NotionRunAllocation.issue,published]) id fresh old
  exact NotionRunAllocation.fresh_transaction_key allocation published session payload.width
    (congrArg NotionRunAllocation.Run.first same)

theorem birth_reserved (transaction : Transaction) (address : Nat × Id)
    (member : address ∈ birthAddresses transaction) : transaction.reservation.Contains address.2 := by
  cases transaction with
  | mk first payload =>
    cases payload with
    | format parts value => simp [birthAddresses] at member
    | edit payload =>
      obtain ⟨source,sourceMember,equal⟩ := List.mem_map.mp member
      have reserved := (NotionCorePayloadNetwork.birth_address_record sourceMember []).2
      simpa only [NotionCorePayload.record,NotionCorePayload.reservation,
        NotionCoreRichPayload.Transaction.reservation,NotionCoreRichPayload.Payload.width,
        ← congrArg Prod.snd equal] using reserved

/-- Every format ID is fresh against both prior edit births and prior
annotations. Raw duplicate-transaction-ID checks alone do not prove this. -/
theorem new_annotations_fresh {state : State} (reachable : Reach state) (session : Session)
    (payload : Payload) (located : Nat × MarkOp)
    (member : located ∈ (⟨(NotionRunAllocation.reserve (state.allocation.peers session)
      session payload.width).first,payload⟩ : Transaction).annotations)
    (entry : Entry) (oldEntry : entry ∈ state.entries) :
    (∀ address ∈ birthAddresses entry.transaction, located.2.id ≠ address.2) ∧
      (∀ old ∈ entry.transaction.annotations, located.2.id ≠ old.2.id) := by
  have reserved := NotionCoreRichPayload.annotation_reserved _ located member
  have fresh : (NotionRunAllocation.reserve (state.allocation.peers session)
      session payload.width).Contains located.2.id := by
    simpa [NotionCoreRichPayload.Transaction.reservation,NotionRunAllocation.reserve] using reserved
  constructor
  · intro address born equal
    exact new_run_disjoint reachable session payload entry oldEntry located.2.id fresh
      (equal.symm ▸ birth_reserved entry.transaction address born)
  · intro old annotated equal
    exact new_run_disjoint reachable session payload entry oldEntry located.2.id fresh
      (equal.symm ▸ NotionCoreRichPayload.annotation_reserved entry.transaction old annotated)

/-- Runtime reference checking yields actual located providers in the issuer's
received past. This is a proved result of the executable caller, not a Reach
constructor premise. Annotation IDs are not mistaken for item providers. -/
theorem issued_references (state next : State) (session : Session) (request : Request)
    (accepted : issue state session request = some next) :
    ∃ payload, next = emit state session payload ∧
      ∀ address ∈ references payload, ∃ entry ∈ state.entries,
        entry.transaction.reservation ∈ (state.allocation.peers session).received ∧
        address ∈ birthAddresses entry.transaction := by
  obtain ⟨current,payload,currentEq,payloadEq,checked,equal⟩ := issue_data state next session request accepted
  refine ⟨payload,equal,?_⟩
  intro address member
  have available := List.all_eq_true.mp checked address member
  simpa only [known,List.any_eq_true,Bool.and_eq_true,List.contains_iff_mem] using available

theorem received_archived {state : State} (reachable : Reach state)
    (session : Session) (run : Run)
    (received : run ∈ (state.allocation.peers session).received) :
    ∃ entry ∈ state.entries, entry.transaction.reservation = run := by
  have published := NotionRunAllocation.reachable_received_published
    (allocation_reachable reachable) session run received
  rw [← archive_runs reachable] at published
  exact List.mem_map.mp published

/-- Captured mint pasts are genuine previously published full reservations,
and precede the transaction's entire newly reserved run. -/
theorem entry_provenance {state : State} (reachable : Reach state)
    (entry : Entry) (member : entry ∈ state.entries) :
    (∀ run ∈ entry.past, run.last < entry.transaction.id.counter) ∧
      ∀ run ∈ entry.past, run ∈ state.allocation.published := by
  induction reachable with
  | init => simp [initial] at member
  | bootstrap text =>
    simp only [seeded,emit,publish,initial,List.mem_cons,List.not_mem_nil,or_false] at member
    subst entry
    constructor <;> simp [NotionRunAllocation.initial,NotionRunAllocation.emptyPeer]
  | @exchange state target source prior ih =>
    obtain ⟨earlier,published⟩ := ih (by simpa [exchange] using member)
    exact ⟨earlier,by simpa [exchange,NotionCoreIssuance.import_published] using published⟩
  | @request state next session request prior issued ih =>
    obtain ⟨current,payload,currentEq,payloadEq,known,rfl⟩ := issue_data state next session request issued
    simp only [emit,publish,List.mem_cons] at member
    rcases member with rfl | member
    · constructor
      · intro run hr
        have bound := NotionRunAllocation.reachable_bounded (allocation_reachable prior) session run hr
        change run.last < (state.allocation.peers session).clock + 1
        omega
      · intro run hr
        exact List.mem_cons_of_mem _ (NotionRunAllocation.reachable_received_published
          (allocation_reachable prior) session run hr)
    · obtain ⟨earlier,published⟩ := ih member
      exact ⟨earlier,fun run hr => List.mem_cons_of_mem _ (published run hr)⟩

theorem clocks_tight {state : State} (reachable : Reach state) :
    ∀ session, NotionCoreAllocationClock.Tight (state.allocation.peers session) := by
  induction reachable with
  | init => intro session; exact NotionCoreAllocationClock.empty_tight
  | bootstrap text =>
    intro session
    by_cases same : session = [65]
    · subst session
      simpa [seeded,emit,publish,initial,NotionRunAllocation.issue] using
        NotionCoreAllocationClock.mint_tight NotionCoreAllocationClock.empty_tight.1
          [65] (Payload.edit (.bootstrap text)).width (width_positive _)
    · simpa [seeded,emit,publish,initial,NotionRunAllocation.issue,same] using
        NotionCoreAllocationClock.empty_tight
  | @exchange state target source prior ih =>
    exact NotionCoreAllocationClock.import_tight state.allocation ih target _
  | @request state next session request prior issued ih =>
    obtain ⟨current,payload,currentEq,payloadEq,known,rfl⟩ := issue_data state next session request issued
    intro peer
    by_cases same : peer = session
    · subst peer
      simpa [emit,publish,NotionRunAllocation.issue] using
        NotionCoreAllocationClock.mint_tight (ih session).1 session payload.width (width_positive payload)
    · simpa [emit,publish,NotionRunAllocation.issue,same] using ih peer

#print axioms allocation_reachable
#print axioms archive_runs
#print axioms issued_references
#print axioms new_annotations_fresh
end Sal.MRDTs.Instances.NotionCoreRichProtocolNetwork
