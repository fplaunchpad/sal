import Sal.MRDTs.Instances.NotionCoreRichProtocolFormatFacts
import Sal.MRDTs.Instances.NotionCoreRichPlainReach
import Sal.MRDTs.Instances.NotionCoreRichRetainedProviders
import Sal.MRDTs.Instances.NotionCoreRichSequentialCoreSimulation
import Sal.MRDTs.Instances.NotionCoreRichSequentialRefinement

/-! Actual physical endpoint presence in arbitrary canonical rich prefixes.
Located providers come from executable source provenance; retained physical
items come from the proved plain-protocol projection and table/forest model. -/
namespace Sal.MRDTs.Instances.NotionCoreRichCanonicalIntegrity
open NotionRunAllocation (Id Run)
open NotionCoreRichPayload (Transaction Part)
open NotionCoreRichProtocolNetwork (State Entry Reach birthAddresses)
open NotionCoreRichCoreProjection (project edits)
open NotionCoreRichPlainNetwork (erase keep)

theorem birth_projects (tx : Transaction) (address : Nat × Id)
    (born : address ∈ birthAddresses tx) :
    ∃ plain inst, project tx = some plain ∧ NotionCoreMachine.blockName inst = address.1 ∧
      (inst,address.2) ∈ NotionCorePayloadNetwork.birthAddresses plain := by
  cases tx with
  | mk first payload =>
    cases payload with
    | format parts value => simp [birthAddresses] at born
    | edit payload =>
      obtain ⟨⟨inst,id⟩,member,equal⟩ := List.mem_map.mp born
      have instanceEq := congrArg Prod.fst equal
      have idEq := congrArg Prod.snd equal
      refine ⟨⟨first,payload⟩,inst,rfl,instanceEq,?_⟩
      change id = address.2 at idEq
      exact idEq ▸ member

theorem prefix_birth_row {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (provider : Transaction) (earlier : provider ∈ pre) (address : Nat × Id)
    (born : address ∈ birthAddresses provider) :
    address.2 ∈ (NotionCoreMachine.getInstance actual.core address.1).rows.map
      (fun row => row.item.id) := by
  obtain ⟨plain,inst,projected,instanceEq,plainBorn⟩ := birth_projects provider address born
  have whole : provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]
    exact List.mem_append_left _ earlier
  obtain ⟨⟨entry,published,same⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs provider).mp whole
  let plainEntry : NotionCorePayloadNetwork.Entry := ⟨plain,entry.past.filter (keep network)⟩
  have plainPublished : plainEntry ∈ (erase network).entries :=
    (NotionCoreRichPlainNetwork.erase_entry_member network plainEntry).mpr
      ⟨entry,published,plain,same ▸ projected,rfl⟩
  have plainEarlier : NotionCorePayload.reservation plain ∈ (edits pre).map NotionCorePayload.reservation :=
    List.mem_map.mpr ⟨plain,List.mem_filterMap.mpr ⟨provider,earlier,projected⟩,rfl⟩
  have plainReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable (NotionCoreRichPlainReach.erase_reachable reachable))
  have plainPosition : NotionCoreReconstruction.transactionsFor (erase network) (runs.filter (keep network)) =
      edits pre ++ edits suffix := by
    rw [NotionCoreRichPlainReach.transactionsFor_eq network reachable runs,position,
      NotionCoreRichCoreProjection.edits_append]
  have coreReplay : NotionCoreMachine.replay {} (edits pre) = some actual.core := by
    have projection := NotionCoreAtomicFormattingMachine.replay_core_projection {} pre
    rw [replayed,NotionCoreRichPlainReach.eraseFormats_eq] at projection
    exact projection.symm
  have retained := NotionCoreRichRetainedProviders.prefix_birth_row (erase network) plainReach
    (runs.filter (keep network)) (edits pre) (edits suffix) plainPosition actual.core coreReplay
    inst address.2 plainEntry plainPublished plainEarlier plainBorn
  rwa [instanceEq] at retained

theorem prefix_birth_forest {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (provider : Transaction) (earlier : provider ∈ pre) (address : Nat × Id)
    (born : address ∈ birthAddresses provider) :
    address.2 ∈ (NotionCoreOriginTree.preorder
      (NotionCoreAtomicFormattingMachine.instanceForest actual address.1)).map
        NotionCoreOriginTree.Item.id := by
  obtain ⟨plain,inst,projected,instanceEq,plainBorn⟩ := birth_projects provider address born
  have whole : provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]
    exact List.mem_append_left _ earlier
  obtain ⟨⟨entry,published,same⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs provider).mp whole
  let plainEntry : NotionCorePayloadNetwork.Entry := ⟨plain,entry.past.filter (keep network)⟩
  have plainPublished : plainEntry ∈ (erase network).entries :=
    (NotionCoreRichPlainNetwork.erase_entry_member network plainEntry).mpr
      ⟨entry,published,plain,same ▸ projected,rfl⟩
  have plainEarlier : NotionCorePayload.reservation plain ∈ (edits pre).map NotionCorePayload.reservation :=
    List.mem_map.mpr ⟨plain,List.mem_filterMap.mpr ⟨provider,earlier,projected⟩,rfl⟩
  have plainReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable (NotionCoreRichPlainReach.erase_reachable reachable))
  have plainPosition : NotionCoreReconstruction.transactionsFor (erase network) (runs.filter (keep network)) =
      edits pre ++ edits suffix := by
    rw [NotionCoreRichPlainReach.transactionsFor_eq network reachable runs,position,
      NotionCoreRichCoreProjection.edits_append]
  have coreReplay : NotionCoreMachine.replay {} (edits pre) = some actual.core := by
    have projection := NotionCoreAtomicFormattingMachine.replay_core_projection {} pre
    rw [replayed,NotionCoreRichPlainReach.eraseFormats_eq] at projection
    exact projection.symm
  have retained := NotionCoreRichRetainedProviders.prefix_birth_forest (erase network) plainReach
    (runs.filter (keep network)) (NotionCoreRichPlainReach.erase_closed network runs closed)
    (edits pre) (edits suffix) plainPosition actual coreReplay inst address.2
    plainEntry plainPublished plainEarlier plainBorn
  rwa [instanceEq] at retained

theorem prefix_birth_registered {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (provider : Transaction) (earlier : provider ∈ pre) (address : Nat × Id)
    (born : address ∈ birthAddresses provider) :
    ∃ stored, (address.1,stored) ∈ actual.core.instances := by
  have row := prefix_birth_row reachable runs closed pre suffix position actual replayed provider earlier address born
  obtain ⟨stored,present,item⟩ := NotionCoreMachineBirths.getInstance_stored actual.core address.1 address.2 row
  exact ⟨stored,present⟩

theorem endpoint_forest {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (entry : Entry) (member : entry ∈ network.entries)
    (selected : entry.transaction.reservation ∈ runs)
    (pre post : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ entry.transaction :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    id ∈ (NotionCoreOriginTree.preorder
      (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId)).map
        NotionCoreOriginTree.Item.id := by
  obtain ⟨provider,earlier,born⟩ := NotionCoreRichProtocolFormatFacts.endpoint_provider_prefix
    reachable runs closed entry member selected pre post position parts value format part partMember id endpoint
  exact prefix_birth_forest reachable runs closed pre (entry.transaction :: post) position actual replayed
    provider earlier (part.instanceId,id) born

theorem batch_origin (actual : NotionCoreAtomicFormattingMachine.State) (pre : List Transaction)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (batch : NotionCoreAtomicFormatting.Batch) (member : batch ∈ actual.batches) :
    ∃ tx ∈ pre, ∃ parts value, tx.payload = .format parts value ∧
      batch = NotionCoreAtomicFormatting.Batch.ofFormat tx.id parts value := by
  have batches := NotionCoreAtomicFormattingMachine.replay_batches {} actual pre replayed
  simp only [List.nil_append] at batches
  rw [batches] at member
  obtain ⟨tx,present,decoded⟩ := List.mem_filterMap.mp member
  cases payloadEq : tx.payload with
  | edit payload => simp [NotionCoreAtomicFormatting.Batch.ofTransaction?,payloadEq] at decoded
  | format parts value =>
    refine ⟨tx,present,parts,value,payloadEq,?_⟩
    exact (Option.some.inj (by simpa [NotionCoreAtomicFormatting.Batch.ofTransaction?,payloadEq] using decoded)).symm

theorem earlier_in_prefix {network : State} (reachable : Reach network)
    (runs : List Run) (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (tx : Transaction) (earlier : tx ∈ pre) (provider : Transaction)
    (member : provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs)
    (before : NotionRunAllocation.Before provider.id tx.id) : provider ∈ pre := by
  have ordered := NotionCoreRichProtocolEvents.transactionsFor_ordered network reachable runs
  rw [position] at ordered member
  rcases List.mem_append.mp member with prior | later
  · exact prior
  · have reverse := (List.pairwise_append.mp ordered).2.2 tx earlier provider later
    exact (NotionCoreSourceInvariant.before_asymm before reverse).elim

theorem prefix_endpoint_provider {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (tx : Transaction) (earlier : tx ∈ pre)
    (parts : List Part) (value : Bool) (format : tx.payload = .format parts value)
    (part : Part) (partMember : part ∈ parts) (id : Id)
    (endpoint : part.lower.endpoint = .item id ∨ part.upper.endpoint = .item id) :
    ∃ provider ∈ pre, (part.instanceId,id) ∈ birthAddresses provider := by
  have whole : tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]; exact List.mem_append_left _ earlier
  obtain ⟨⟨entry,published,same⟩,selected⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp whole
  subst tx
  obtain ⟨provider,present,born,before⟩ := NotionCoreRichProtocolFormatFacts.endpoint_provider_selected
    reachable runs closed entry published selected parts value format part partMember id endpoint
  exact ⟨provider,earlier_in_prefix reachable runs pre suffix position entry.transaction earlier provider present before,born⟩

theorem prefix_batch_part (actual : NotionCoreAtomicFormattingMachine.State) (pre : List Transaction)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (batch : NotionCoreAtomicFormatting.Batch) (member : batch ∈ actual.batches)
    (segment : NotionCoreAtomicFormatting.Segment) (inside : segment ∈ batch.segments) :
    ∃ tx ∈ pre, ∃ parts value, tx.payload = .format parts value ∧ segment.part ∈ parts := by
  obtain ⟨tx,present,parts,value,format,rfl⟩ := batch_origin actual pre replayed batch member
  refine ⟨tx,present,parts,value,format,?_⟩
  have partMember : segment.part ∈ (NotionCoreAtomicFormatting.Batch.ofFormat tx.id parts value).segments.map
      NotionCoreAtomicFormatting.Segment.part := List.mem_map.mpr ⟨segment,inside,rfl⟩
  rwa [NotionCoreAtomicFormatting.ofFormat_parts] at partMember

theorem batch_endpoint_forest {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (batch : NotionCoreAtomicFormatting.Batch) (member : batch ∈ actual.batches)
    (segment : NotionCoreAtomicFormatting.Segment) (inside : segment ∈ batch.segments)
    (id : Id) (endpoint : segment.lower.endpoint = .item id ∨ segment.upper.endpoint = .item id) :
    id ∈ (NotionCoreOriginTree.preorder
      (NotionCoreAtomicFormattingMachine.instanceForest actual segment.instanceId)).map
        NotionCoreOriginTree.Item.id := by
  obtain ⟨tx,present,parts,value,format,partMember⟩ := prefix_batch_part actual pre replayed batch member segment inside
  obtain ⟨provider,earlier,born⟩ := prefix_endpoint_provider reachable runs closed pre suffix position tx present
    parts value format segment.part partMember id endpoint
  exact prefix_birth_forest reachable runs closed pre suffix position actual replayed provider earlier
    (segment.instanceId,id) born

theorem batch_part_shape {network : State} (reachable : Reach network)
    (runs : List Run) (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (batch : NotionCoreAtomicFormatting.Batch) (member : batch ∈ actual.batches)
    (segment : NotionCoreAtomicFormatting.Segment) (inside : segment ∈ batch.segments) :
    (∃ id, segment.lower = ⟨.item id,.before⟩) ∧
      (segment.upper = ⟨.finish,.before⟩ ∨ ∃ id, segment.upper = ⟨.item id,.before⟩) := by
  obtain ⟨tx,present,parts,value,format,partMember⟩ := prefix_batch_part actual pre replayed batch member segment inside
  have whole : tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]; exact List.mem_append_left _ present
  obtain ⟨⟨entry,published,same⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp whole
  exact NotionCoreRichProtocolFormatFacts.archived_part_shape reachable entry published parts value
    (same ▸ format) segment.part partMember

theorem supported_batches {network : State} (reachable : Reach network)
    (runs : List Run) (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual) :
    NotionCoreRichSequential.Refinement.SupportedBatches actual := by
  intro batch member segment inside
  obtain ⟨⟨lower,lowerEq⟩,upperEq | ⟨upper,upperEq⟩⟩ :=
    batch_part_shape reachable runs pre suffix position actual replayed batch member segment inside
  · simp [NotionCoreRichSequential.Refinement.BeforeEndpoint,lowerEq,upperEq]
  · simp [NotionCoreRichSequential.Refinement.BeforeEndpoint,lowerEq,upperEq]

theorem registered_segments {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre suffix : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual) :
    NotionCoreRichSequential.Refinement.RegisteredSegments actual := by
  intro batch member segment inside
  obtain ⟨lower,lowerEq⟩ := (batch_part_shape reachable runs pre suffix position actual replayed batch member segment inside).1
  obtain ⟨tx,present,parts,value,format,partMember⟩ := prefix_batch_part actual pre replayed batch member segment inside
  obtain ⟨provider,earlier,born⟩ := prefix_endpoint_provider reachable runs closed pre suffix position tx present
    parts value format segment.part partMember lower (Or.inl (congrArg NotionCoreFormattingSource.Anchor.endpoint lowerEq))
  obtain ⟨stored,published⟩ := prefix_birth_registered reachable runs closed pre suffix position actual replayed
    provider earlier (segment.instanceId,lower) born
  exact ⟨(segment.instanceId,stored),published,rfl⟩

theorem anchor_item_present (forest : NotionCoreOriginTree.Forest) (id : Id)
    (present : id ∈ (NotionCoreOriginTree.preorder forest).map NotionCoreOriginTree.Item.id) :
    ∃ index, NotionCoreFormattingSource.anchorPosition forest ⟨.item id,.before⟩ = some index := by
  have inWalk : id ∈ (NotionCoreFormattingSource.walk 0 forest).map
      (fun positioned => positioned.item.id) := by
    have walkIds := congrArg (List.map NotionCoreOriginTree.Item.id)
      (NotionCoreFormattingSource.walk_items 0 forest)
    simp only [List.map_map,Function.comp_def] at walkIds
    rw [walkIds]
    exact present
  obtain ⟨positioned,member,same⟩ := List.mem_map.mp inWalk
  cases found : (NotionCoreFormattingSource.walk 0 forest).find? (fun positioned => positioned.item.id == id) with
  | none =>
    have absent := List.find?_eq_none.mp found positioned member
    simp [same] at absent
  | some foundItem => exact ⟨foundItem.entry,by simp [NotionCoreFormattingSource.anchorPosition,found]⟩

theorem format_parts_available {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (entry : Entry) (member : entry ∈ network.entries)
    (selected : entry.transaction.reservation ∈ runs)
    (pre post : List Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ entry.transaction :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (parts : List Part) (value : Bool) (format : entry.transaction.payload = .format parts value) :
    ∀ part ∈ parts, NotionCoreRichSequential.Refinement.Registered actual part.instanceId ∧
      ∃ lower upper,
        NotionCoreFormattingSource.anchorPosition
          (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId) part.lower = some lower ∧
        NotionCoreFormattingSource.anchorPosition
          (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId) part.upper = some upper := by
  intro part partMember
  obtain ⟨⟨lower,lowerEq⟩,upperShape⟩ :=
    NotionCoreRichProtocolFormatFacts.archived_part_shape reachable entry member parts value format part partMember
  have lowerEndpoint := congrArg NotionCoreFormattingSource.Anchor.endpoint lowerEq
  obtain ⟨provider,earlier,born⟩ := NotionCoreRichProtocolFormatFacts.endpoint_provider_prefix
    reachable runs closed entry member selected pre post position parts value format part partMember lower (Or.inl lowerEndpoint)
  obtain ⟨stored,published⟩ := prefix_birth_registered reachable runs closed pre (entry.transaction :: post)
    position actual replayed provider earlier (part.instanceId,lower) born
  refine ⟨⟨(part.instanceId,stored),published,rfl⟩,?_⟩
  have lowerMember := endpoint_forest reachable runs closed entry member selected pre post position actual replayed
    parts value format part partMember lower (Or.inl lowerEndpoint)
  obtain ⟨lo,lowerAt⟩ := anchor_item_present _ lower lowerMember
  rw [← lowerEq] at lowerAt
  rcases upperShape with upperEq | ⟨upper,upperEq⟩
  · exact ⟨lo,_,lowerAt,by rw [upperEq]; rfl⟩
  · have upperMember := endpoint_forest reachable runs closed entry member selected pre post position actual replayed
      parts value format part partMember upper (Or.inr (congrArg NotionCoreFormattingSource.Anchor.endpoint upperEq))
    obtain ⟨hi,upperAt⟩ := anchor_item_present _ upper upperMember
    rw [← upperEq] at upperAt
    exact ⟨lo,hi,lowerAt,upperAt⟩

theorem prefix_reserved_apart {network : State} (reachable : Reach network)
    (runs : List Run) (pre post : List Transaction) (tx provider : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (earlier : provider ∈ pre) (address : Nat × Id) (born : address ∈ birthAddresses provider)
    (id : Id) (fresh : tx.reservation.Contains id) : id ≠ address.2 := by
  have txMember : tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]; exact List.mem_append_right _ (by simp)
  have providerMember : provider ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]; exact List.mem_append_left _ earlier
  obtain ⟨⟨txEntry,txPublished,txSame⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp txMember
  obtain ⟨⟨providerEntry,providerPublished,providerSame⟩,_⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs provider).mp providerMember
  have allPublished := NotionCoreRichProtocolNetwork.archive_runs reachable
  have published (entry : Entry) (member : entry ∈ network.entries) :
      entry.transaction.reservation ∈ network.allocation.published := by
    rw [← allPublished]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  intro same
  have collision := NotionRunAllocation.reachable_unique_owner
    (NotionCoreRichProtocolNetwork.allocation_reachable reachable)
    txEntry.transaction.reservation (published txEntry txPublished)
    providerEntry.transaction.reservation (published providerEntry providerPublished) id
    (txSame.symm ▸ fresh)
    (providerSame.symm ▸ (same.symm ▸ NotionCoreRichProtocolNetwork.birth_reserved provider address born))
  have headers := congrArg Run.first collision
  change txEntry.transaction.id = providerEntry.transaction.id at headers
  rw [txSame,providerSame] at headers
  have before := NotionCoreRichProtocolFormatFacts.prefix_before reachable runs pre post tx position provider earlier
  exact NotionCoreSourceInvariant.before_irrefl _ (headers ▸ before)

theorem canonical_format_ready {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (parts : List Part) (value : Bool) (format : tx.payload = .format parts value) :
    NotionCoreRichSequential.Refinement.FormatReady actual parts := by
  have whole : tx ∈ NotionCoreRichProtocolEvents.transactionsFor network runs := by
    rw [position]; exact List.mem_append_right _ (by simp)
  obtain ⟨⟨entry,published,same⟩,selected⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs tx).mp whole
  subst tx
  exact format_parts_available reachable runs closed entry published selected pre post position actual replayed parts value format

theorem insert_item_reserved (tx : Transaction)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .edit (.insert block inst origin atoms))
    (item : NotionCoreOriginTree.Item)
    (member : item ∈ NotionCorePayload.textItems tx.id atoms (fun _ => false)) :
    tx.reservation.Contains item.id := by
  have ids : item.id ∈ (NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
      NotionCoreOriginTree.Item.id := List.mem_map.mpr ⟨item,member,rfl⟩
  rw [NotionCorePayload.textItems_ids] at ids
  obtain ⟨offset,bounded,equal⟩ := List.mem_map.mp ids
  have bound := List.mem_range.mp bounded
  refine ⟨offset,?_,?_⟩
  · simp only [Transaction.reservation,payload,NotionCoreRichPayload.Payload.width,
      NotionCorePayload.Payload.width,NotionCorePayload.Payload.itemCount]
    exact lt_of_lt_of_le bound (Nat.le_max_right _ _)
  · simpa only [Transaction.reservation,NotionRunAllocation.Run.at,NotionCorePayload.offsetId] using equal.symm

theorem fresh_endpoints_insert {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .edit (.insert block inst origin atoms)) :
    NotionCoreRichSequential.Refinement.FreshEndpoints actual (NotionCoreMachine.blockName inst)
      (NotionCorePayload.textItems tx.id atoms (fun _ => false)) := by
  intro batch member segment inside sameInstance id endpoint item freshItem
  obtain ⟨old,present,parts,value,format,partMember⟩ := prefix_batch_part actual pre replayed batch member segment inside
  obtain ⟨provider,earlier,born⟩ := prefix_endpoint_provider reachable runs closed pre (tx :: post) position old present
    parts value format segment.part partMember id endpoint
  exact prefix_reserved_apart reachable runs pre post tx provider position earlier (segment.instanceId,id) born item.id
    (insert_item_reserved tx block inst origin atoms payload item freshItem)

theorem fresh_endpoints_reserved {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (inst : Nat) (fresh : List NotionCoreOriginTree.Item)
    (reserved : ∀ item ∈ fresh, tx.reservation.Contains item.id) :
    NotionCoreRichSequential.Refinement.FreshEndpoints actual inst fresh := by
  intro batch member segment inside sameInstance id endpoint item freshItem
  obtain ⟨old,present,parts,value,format,partMember⟩ := prefix_batch_part actual pre replayed batch member segment inside
  obtain ⟨provider,earlier,born⟩ := prefix_endpoint_provider reachable runs closed pre (tx :: post) position old present
    parts value format segment.part partMember id endpoint
  exact prefix_reserved_apart reachable runs pre post tx provider position earlier (segment.instanceId,id) born item.id
    (reserved item freshItem)

theorem fresh_endpoints_split {network : State} (reachable : Reach network)
    (runs : List Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (tx : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ tx :: post)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (inst : Nat) :
    NotionCoreRichSequential.Refinement.FreshEndpoints actual inst [⟨tx.id,.split⟩] := by
  apply fresh_endpoints_reserved reachable runs closed pre post tx position actual replayed inst
  intro item member
  have same := List.mem_singleton.mp member
  subst item
  exact ⟨0,NotionCoreRichProtocolNetwork.width_positive tx.payload,by
    simp [Transaction.reservation,NotionRunAllocation.Run.at]⟩

#print axioms prefix_birth_forest
#print axioms endpoint_forest
#print axioms supported_batches
#print axioms registered_segments
#print axioms format_parts_available
#print axioms canonical_format_ready
#print axioms fresh_endpoints_insert
end Sal.MRDTs.Instances.NotionCoreRichCanonicalIntegrity
