import Sal.MRDTs.Instances.NotionCoreRichProtocolEvents
import Sal.MRDTs.Instances.NotionCoreRichSequentialInputs

/-! Formatting metadata derived from the executable positional caller.
The saved issuer state is retained as provenance; neither endpoint validity
nor a sequential replay conclusion is an assumption of source reachability. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolFormatFacts
open NotionRunAllocation (Id Run Session)
open NotionCoreRichPayload (Transaction Payload Part)
open NotionCoreRichProtocolNetwork

theorem prepare_format {current : NotionCoreAtomicFormattingMachine.State}
    {request : Request} {parts : List Part} {value : Bool}
    (prepared : prepare current request = some (.format parts value)) :
    ∃ block start stop, request = .toggle block start stop ∧
      formatPayload current block start stop = some (.format parts value) := by
  cases request with
  | toggle block start stop => exact ⟨block,start,stop,rfl,prepared⟩
  | edit request =>
    simp only [prepare] at prepared
    split at prepared
    · contradiction
    · cases payloadEq : NotionCoreMachineNetwork.prepareRequest current.core request with
      | none => simp [payloadEq] at prepared
      | some payload =>
        by_cases emits : payload.emits <;> simp [payloadEq,emits] at prepared

def plannedSegments (current : NotionCoreAtomicFormattingMachine.State)
    (characters : List NotionCoreFormattingSource.Character) :=
  NotionCoreFormattingPlanner.locatedSegments
    (NotionCoreAtomicFormattingMachine.instanceForest current) NotionCorePhysicalReplay.address
    (characters.map fun character =>
      NotionCorePhysicalReplay.address character.textInstance character.item.id)
    ((current.core.instances.map Prod.fst).eraseDups)

theorem formatPayload_data {current : NotionCoreAtomicFormattingMachine.State}
    {block : NotionCorePayload.BlockKey} {start stop : Nat} {parts : List Part} {value : Bool}
    (prepared : formatPayload current block start stop = some (.format parts value)) :
    ∃ characters, selection current block start stop = some characters ∧
      characters.isEmpty = false ∧
      (plannedSegments current characters).isEmpty = false ∧
      parts = NotionCoreRichPayload.partsOf (plannedSegments current characters) ∧
        value = !(characters.all NotionCoreFormattingSource.Character.bold) := by
  unfold formatPayload at prepared
  obtain ⟨characters,selected,rest⟩ := Option.bind_eq_some_iff.mp prepared
  by_cases empty : characters.isEmpty = true
  · simp [empty] at rest
  · simp only [empty,Bool.false_eq_true,if_false] at rest
    change (if (plannedSegments current characters).isEmpty then none else
      some (Payload.format (NotionCoreRichPayload.partsOf (plannedSegments current characters))
        (!(characters.all NotionCoreFormattingSource.Character.bold)))) =
      some (Payload.format parts value) at rest
    by_cases segmentsEmpty : (plannedSegments current characters).isEmpty = true
    · simp [segmentsEmpty] at rest
    · have fields : NotionCoreRichPayload.partsOf (plannedSegments current characters) = parts ∧
          (!(characters.all NotionCoreFormattingSource.Character.bold)) = value := by
        simpa [segmentsEmpty] using rest
      exact ⟨characters,selected,Bool.eq_false_iff.mpr empty,
        Bool.eq_false_iff.mpr segmentsEmpty,fields.1.symm,fields.2.symm⟩

/-- An archived format was minted by this actual positional preparation at
this saved issuer state. The source-local Boolean and source IDs are fixed. -/
def Origin (entry : Entry) : Prop :=
  ∃ (prior : State) (session : Session) (block : NotionCorePayload.BlockKey)
      (start stop : Nat) (current : NotionCoreAtomicFormattingMachine.State),
    Reach prior ∧ reconstruct prior session = some current ∧
    formatPayload current block start stop = some entry.transaction.payload ∧
    (references entry.transaction.payload).all (known prior session) = true ∧
    entry.transaction.id =
      (NotionRunAllocation.reserve (prior.allocation.peers session) session entry.transaction.payload.width).first ∧
    entry.past = (prior.allocation.peers session).received

theorem archived_origin {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries) (parts : List Part) (value : Bool)
    (format : entry.transaction.payload = .format parts value) : Origin entry := by
  induction reachable with
  | init => simp [initial] at member
  | bootstrap text =>
    simp only [seeded,emit,publish,initial,List.mem_cons,List.not_mem_nil,or_false] at member
    subst entry
    cases format
  | exchange target source prior ih => exact ih (by simpa [exchange] using member)
  | @request state next session request prior issued ih =>
    obtain ⟨current,payload,reconstructed,prepared,checked,rfl⟩ := issue_data state next session request issued
    simp only [emit,publish,List.mem_cons] at member
    rcases member with rfl | old
    · have same : payload = .format parts value := format
      obtain ⟨block,start,stop,rfl,prepared⟩ := prepare_format (same ▸ prepared)
      exact ⟨state,session,block,start,stop,current,prior,reconstructed,by simpa [same] using prepared,
        checked,rfl,rfl⟩
    · exact ih old

theorem origin_compiles {entry : Entry} (origin : Origin entry)
    {parts : List Part} {value : Bool} (format : entry.transaction.payload = .format parts value) :
    ∃ command, NotionCoreRichSequentialInputs.command entry.transaction = some command := by
  obtain ⟨prior,session,block,start,stop,current,reachable,reconstructed,prepared,checked,allocated,captured⟩ := origin
  rw [format] at prepared
  obtain ⟨characters,selected,nonempty,segmentsNonempty,partsEq,valueEq⟩ := formatPayload_data prepared
  have planned := NotionCoreRichSequentialInputs.planned_command entry.transaction.id value
    (plannedSegments current characters)
  refine ⟨.format ((plannedSegments current characters).map fun (inst,segment) =>
    NotionCoreRichSequentialInputs.segmentRegion inst segment) value,?_⟩
  simpa only [NotionCoreRichSequentialInputs.command,format,partsEq] using planned

theorem archived_compiles {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries) :
    ∃ command, NotionCoreRichSequentialInputs.command entry.transaction = some command := by
  cases format : entry.transaction.payload with
  | edit payload => simp [NotionCoreRichSequentialInputs.command,format]
  | format parts value =>
    exact origin_compiles (archived_origin reachable entry member parts value format) format

theorem archived_regions {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value) :
    ∃ regions, parts.mapM NotionCoreRichSequentialInputs.region = some regions := by
  obtain ⟨prior,session,block,start,stop,current,priorReach,reconstructed,prepared,checked,allocated,captured⟩ :=
    archived_origin reachable entry member parts value format
  rw [format] at prepared
  obtain ⟨characters,selected,nonempty,segmentsNonempty,partsEq,valueEq⟩ := formatPayload_data prepared
  rw [partsEq]
  exact ⟨_,NotionCoreRichSequentialInputs.planned_regions _⟩

theorem selected_format_regions {network : State} (reachable : Reach network)
    (runs : List Run) (tx : Transaction)
    (member : tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs)
    (parts : List Part) (value : Bool) (format : tx.payload = .format parts value) :
    ∃ regions, parts.mapM NotionCoreRichSequentialInputs.region = some regions := by
  obtain ⟨⟨entry,published,same⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp member
  exact archived_regions reachable entry published parts value (same ▸ format)

theorem planned_part_shape (segments : List (Nat × NotionCoreFormattingPlanner.Segment))
    (part : Part) (member : part ∈ NotionCoreRichPayload.partsOf segments) :
    (∃ id, part.lower = ⟨.item id,.before⟩) ∧
      (part.upper = ⟨.finish,.before⟩ ∨ ∃ id, part.upper = ⟨.item id,.before⟩) := by
  obtain ⟨⟨inst,segment⟩,present,rfl⟩ := List.mem_map.mp member
  refine ⟨⟨segment.first.item.id,rfl⟩,?_⟩
  cases ending : segment.next with
  | none => exact Or.inl (by simp [NotionCoreFormattingPlanner.Segment.operation,ending])
  | some next => exact Or.inr ⟨next.item.id,by simp [NotionCoreFormattingPlanner.Segment.operation,ending]⟩

theorem archived_part_shape {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) :
    (∃ id, part.lower = ⟨.item id,.before⟩) ∧
      (part.upper = ⟨.finish,.before⟩ ∨ ∃ id, part.upper = ⟨.item id,.before⟩) := by
  obtain ⟨prior,session,block,start,stop,current,priorReach,reconstructed,prepared,checked,allocated,captured⟩ :=
    archived_origin reachable entry member parts value format
  rw [format] at prepared
  obtain ⟨characters,selected,nonempty,segmentsNonempty,partsEq,valueEq⟩ := formatPayload_data prepared
  rw [partsEq] at partMember
  exact planned_part_shape _ part partMember

theorem transactionsFor_compiles {network : State} (reachable : Reach network) (runs : List Run) :
    ∃ commands, ((NotionCoreRichProtocolEvents.transactionsFor network runs).mapM
      NotionCoreRichSequentialInputs.command) = some commands := by
  have supported : ∀ tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs,
      ∃ command, NotionCoreRichSequentialInputs.command tx = some command := by
    intro tx member
    obtain ⟨⟨entry,published,rfl⟩,_⟩ :=
      (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp member
    exact archived_compiles reachable entry published
  generalize transactionsEq : NotionCoreRichProtocolEvents.transactionsFor network runs = transactions at supported ⊢
  clear transactionsEq
  induction transactions with
  | nil => exact ⟨[],rfl⟩
  | cons tx rest ih =>
    obtain ⟨command,compiled⟩ := supported tx (by simp)
    obtain ⟨commands,compiledRest⟩ := ih (fun tx member => supported tx (List.mem_cons_of_mem _ member))
    exact ⟨command :: commands,by simp [List.mapM_cons,compiled,compiledRest]⟩

/-- Reference checking at mint time persists in the common archive. Each
located endpoint has a real item provider in this transaction's saved past. -/
theorem archived_references {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries) :
    ∀ address ∈ references entry.transaction.payload, ∃ provider ∈ network.entries,
      provider.transaction.reservation ∈ entry.past ∧
        address ∈ birthAddresses provider.transaction := by
  induction reachable with
  | init => simp [initial] at member
  | bootstrap text =>
    simp only [seeded,emit,publish,initial,List.mem_cons,List.not_mem_nil,or_false] at member
    subst entry
    simp [references,NotionCorePayloadNetwork.locatedReferences]
  | exchange target source prior ih => exact ih (by simpa [exchange] using member)
  | @request state next session request prior issued ih =>
    obtain ⟨current,payload,reconstructed,prepared,checked,rfl⟩ := issue_data state next session request issued
    simp only [emit,publish,List.mem_cons] at member
    rcases member with rfl | old
    · intro address referenced
      have available := List.all_eq_true.mp checked address referenced
      obtain ⟨provider,published,received,born⟩ : ∃ provider ∈ state.entries,
          provider.transaction.reservation ∈ (state.allocation.peers session).received ∧
          address ∈ birthAddresses provider.transaction := by
        simpa only [known,List.any_eq_true,Bool.and_eq_true,List.contains_iff_mem] using available
      exact ⟨provider,List.mem_cons_of_mem _ published,received,born⟩
    · intro address referenced
      obtain ⟨provider,published,received,born⟩ := ih old address referenced
      exact ⟨provider,List.mem_cons_of_mem _ published,received,born⟩

theorem part_endpoint_reference (parts : List Part) (value : Bool) (part : Part)
    (member : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    (part.instanceId,id) ∈ references (.format parts value) := by
  apply List.mem_flatMap.mpr
  refine ⟨part,member,?_⟩
  rcases endpoint with lower | upper
  · exact List.mem_append_left _ (by simp [endpointReferences,lower])
  · exact List.mem_append_right _ (by simp [endpointReferences,upper])

theorem past_before {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries)
    (provider : Entry) (past : provider.transaction.reservation ∈ entry.past) :
    NotionRunAllocation.Before provider.transaction.id entry.transaction.id := by
  have smaller := (entry_provenance reachable entry member).1 _ past
  have positive := width_positive provider.transaction.payload
  have lower : provider.transaction.id.counter ≤ provider.transaction.reservation.last := by
    simp only [Transaction.reservation,NotionRunAllocation.Run.last]
    omega
  exact Or.inl (lt_of_le_of_lt lower smaller)

theorem endpoint_provider {network : State} (reachable : Reach network)
    (entry : Entry) (member : entry ∈ network.entries)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    ∃ provider ∈ network.entries,
      provider.transaction.reservation ∈ entry.past ∧
      (part.instanceId,id) ∈ birthAddresses provider.transaction ∧
      NotionRunAllocation.Before provider.transaction.id entry.transaction.id := by
  have referenced := part_endpoint_reference parts value part partMember id endpoint
  rw [← format] at referenced
  obtain ⟨provider,published,past,born⟩ := archived_references reachable entry member _ referenced
  exact ⟨provider,published,past,born,past_before reachable entry member provider past⟩

theorem endpoint_provider_selected {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (entry : Entry) (member : entry ∈ network.entries)
    (selected : entry.transaction.reservation ∈ runs)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    ∃ provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs,
      (part.instanceId,id) ∈ birthAddresses provider ∧
      NotionRunAllocation.Before provider.id entry.transaction.id := by
  obtain ⟨provider,published,past,born,before⟩ :=
    endpoint_provider reachable entry member parts value format part partMember id endpoint
  refine ⟨provider.transaction,?_,born,before⟩
  exact (NotionCoreRichProtocolEvents.transactionsFor_membership network runs _).mpr
    ⟨⟨provider,published,rfl⟩,closed entry member selected _ past⟩

theorem before_in_prefix {network : State} (reachable : Reach network)
    (runs : List Run) (pre post : List Transaction) (tx provider : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (member : provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs)
    (before : NotionRunAllocation.Before provider.id tx.id) : provider ∈ pre := by
  have ordered := NotionCoreRichProtocolEvents.transactionsFor_ordered network reachable runs
  rw [position] at ordered member
  rcases List.mem_append.mp member with prior | later
  · exact prior
  · rcases List.mem_cons.mp later with same | suffix
    · subst provider
      exact (NotionCoreSourceInvariant.before_irrefl _ before).elim
    · have reverse := (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 provider suffix
      exact (NotionCoreSourceInvariant.before_asymm before reverse).elim

theorem endpoint_provider_prefix {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (entry : Entry) (member : entry ∈ network.entries)
    (selected : entry.transaction.reservation ∈ runs)
    (pre post : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ entry.transaction :: post)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    ∃ provider ∈ pre, (part.instanceId,id) ∈ birthAddresses provider := by
  obtain ⟨provider,present,born,before⟩ :=
    endpoint_provider_selected reachable runs closed entry member selected parts value format part partMember id endpoint
  exact ⟨provider,before_in_prefix reachable runs pre post entry.transaction provider position present before,born⟩

theorem prefix_before {network : State} (reachable : Reach network)
    (runs : List Run) (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post) :
    ∀ prior ∈ pre, NotionRunAllocation.Before prior.id tx.id := by
  have ordered := NotionCoreRichProtocolEvents.transactionsFor_ordered network reachable runs
  rw [position] at ordered
  intro prior member
  exact (List.pairwise_append.mp ordered).2.2 prior member tx (by simp)

/-- Shared batch priority is the transaction header, so canonical order puts
every already replayed batch strictly below the next whole transaction. -/
theorem replayed_batches_before {network : State} (reachable : Reach network)
    (runs : List Run) (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (current : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some current) :
    ∀ batch ∈ current.batches, NotionRunAllocation.Before batch.priority tx.id := by
  have batches := NotionCoreAtomicFormattingMachine.replay_batches {} current pre replayed
  simp only [List.nil_append] at batches
  intro batch member
  rw [batches] at member
  obtain ⟨prior,present,decoded⟩ := List.mem_filterMap.mp member
  have priority := NotionCoreAtomicFormatting.ofTransaction_priority prior batch decoded
  rw [priority]
  exact prefix_before reachable runs pre post tx position prior present

#print axioms archived_origin
#print axioms origin_compiles
#print axioms endpoint_provider_selected
#print axioms endpoint_provider_prefix
#print axioms replayed_batches_before
end Sal.MRDTs.Instances.NotionCoreRichProtocolFormatFacts
