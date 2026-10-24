import Sal.MRDTs.Instances.NotionCoreRichSequentialRelation
import Sal.MRDTs.Instances.NotionCoreAtomicFormattingEffects
import Sal.MRDTs.Instances.NotionCoreMachineHistory

/-! Core-edit preservation for the independent current character/sticky-gap
state. Structural retained-list effects are obtained from the actual core
interpreter. The helpers keep source-document evolution separate from the
new mark argument; no rich observation equation is an input. -/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
open NotionCoreSpec
open NotionCoreOriginTree (Forest Item)
open NotionCoreAtomicFormattingEffects (storedItems originGap)

def edited (actual : NotionCoreAtomicFormattingMachine.State) (core : NotionCoreMachine.State) :
    NotionCoreAtomicFormattingMachine.State := ⟨core,actual.batches⟩

theorem core_replay_append (state : NotionCoreMachine.State) (first later : List NotionCorePayload.Transaction) :
    NotionCoreMachine.replay state (first ++ later) =
      (NotionCoreMachine.replay state first >>= fun next => NotionCoreMachine.replay next later) := by
  induction first generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,NotionCoreMachine.replay]
    cases step : NotionCoreMachine.applyTransaction state tx <;> simp [ih]

abbrev itemSlots (inst : Nat) (items : List Item) : List Slot :=
  (items.map (NotionCorePhysicalReplay.atom inst)).map NotionCoreSource.Atom.slot

theorem physicalSlots_actual (actual : NotionCoreAtomicFormattingMachine.State) (inst : Nat) :
    NotionCoreRichCoordinates.physicalSlots inst (NotionCoreAtomicFormattingMachine.instanceForest actual inst) =
      itemSlots inst (storedItems actual.core inst) := by
  simp only [NotionCoreRichCoordinates.physicalSlots,NotionCoreAtomicFormattingEffects.storedItems_forest]

theorem forest_of_storage (actual : NotionCoreAtomicFormattingMachine.State) (core : NotionCoreMachine.State)
    (inst : Nat) (storage : NotionCoreMachine.getInstance core inst = NotionCoreMachine.getInstance actual.core inst) :
    NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) inst =
      NotionCoreAtomicFormattingMachine.instanceForest actual inst := by
  simp only [NotionCoreAtomicFormattingMachine.instanceForest,NotionCoreAtomicFormattingMachine.plainState,
    NotionCoreFormattingMachine.instanceForest,edited,storage]

theorem unique_of_physical (actual : NotionCoreAtomicFormattingMachine.State)
    (unique : ∀ inst, ((NotionCoreMachine.physical actual.core inst).map NotionCoreSource.Atom.address).Nodup) :
    ∀ inst, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest actual inst) := by
  intro inst
  have ids := List.nodup_cons.mp (unique inst) |>.2
  change ((storedItems actual.core inst).map (NotionCorePhysicalReplay.atom inst) |>.map
    NotionCoreSource.Atom.address).Nodup at ids
  have inj : Function.Injective (NotionCorePhysicalReplay.address inst) :=
    NotionCorePhysicalReplay.address_injective inst
  have oldIds : ((storedItems actual.core inst).map Item.id).Nodup := by
    apply List.Nodup.of_map (f := NotionCorePhysicalReplay.address inst)
    simpa only [List.map_map,Function.comp_def,NotionCorePhysicalReplay.atom_address] using ids
  simpa only [NotionCoreFormattingPlanner.UniqueIds,NotionCoreAtomicFormattingEffects.storedItems_forest]
    using oldIds

theorem marks_of_forest_frame (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (inst : Nat) (text : Text)
    (related : AtomicBridge.MarksRelated (NotionCoreAtomicFormattingMachine.instanceForest actual)
      actual.batches inst text)
    (frame : NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) inst =
      NotionCoreAtomicFormattingMachine.instanceForest actual inst) :
    AtomicBridge.MarksRelated (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core))
      actual.batches inst text := by
  constructor
  · intro index
    rw [related.1 index]
    simp only [NotionCoreAtomicFormatting.resolveAt,NotionCoreAtomicFormatting.covers,
      NotionCoreAtomicFormatting.segmentCovers,frame]
  · intro gap
    rw [related.2 gap]
    simp only [NotionCoreAtomicFormatting.resolveGapAt,NotionCoreAtomicFormatting.gapCovers,
      NotionCoreAtomicFormatting.segmentGapCovers,frame]

/-- Forest-only core edits preserve every current mark and every latent gap.
This covers the corrected source merge, irrespective of displayed slice order. -/
theorem frame_related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (core : NotionCoreMachine.State)
    (storage : ∀ inst, NotionCoreMachine.getInstance core inst = NotionCoreMachine.getInstance actual.core inst)
    (registered : ∀ inst, Registered (edited actual core) inst ↔ Registered actual inst)
    (source : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some source) :
    Related (edited actual core) ⟨NotionCoreSourceDocument.project source,abstract.texts⟩ := by
  constructor
  · exact ⟨source,materialized,rfl⟩
  · intro inst
    exact (related.registered inst).trans (registered inst).symm
  · intro inst text found
    rw [related.physical inst text found,forest_of_storage actual core inst (storage inst)]
  · intro inst
    rw [forest_of_storage actual core inst (storage inst)]
    exact related.unique inst
  · intro inst text found
    exact marks_of_forest_frame actual core inst text (related.marks inst text found)
      (forest_of_storage actual core inst (storage inst))

theorem merge_related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (core : NotionCoreMachine.State)
    (source inst : NotionCorePayload.BlockKey) (stop : Option NotionRunAllocation.Id)
    (operation : NotionCoreMachine.applyOperation actual.core (.merge source inst stop) = some core)
    (after : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some after) :
    Related (edited actual core) ⟨NotionCoreSourceDocument.project after,abstract.texts⟩ := by
  apply frame_related actual abstract related core
    (NotionCoreAtomicFormattingEffects.merge_storage actual.core core source inst stop operation)
    _ after materialized
  simp only [NotionCoreMachine.applyOperation,Option.some.injEq] at operation
  subst core
  exact fun _ => Iff.rfl

/-- Supported before-item/END anchors depend only on the retained identity
sequence, including invisible tombstones and split markers. -/
def BeforeEndpoint (anchor : NotionCoreFormattingSource.Anchor) : Prop :=
  anchor.side = .before ∧ (anchor.endpoint = .finish ∨ ∃ id, anchor.endpoint = .item id)

theorem before_anchor_ids (old new : Forest)
    (ids : (NotionCoreOriginTree.preorder new).map Item.id = (NotionCoreOriginTree.preorder old).map Item.id)
    (anchor : NotionCoreFormattingSource.Anchor) (supported : BeforeEndpoint anchor) :
    NotionCoreFormattingSource.anchorPosition new anchor = NotionCoreFormattingSource.anchorPosition old anchor := by
  obtain ⟨side,endpoint | ⟨id,endpoint⟩⟩ := supported
  · cases anchor with
    | mk endpoint' side' =>
      simp only at side endpoint
      subst endpoint'; subst side'
      have lengths := congrArg List.length ids
      simpa [NotionCoreFormattingSource.anchorPosition] using congrArg some lengths
  · cases anchor with
    | mk endpoint' side' =>
      simp only at side endpoint
      subst endpoint'; subst side'
      rw [NotionCoreRichCoordinates.anchor_before_findIdx,NotionCoreRichCoordinates.anchor_before_findIdx]
      have mapped := congrArg (fun items : List NotionRunAllocation.Id => items.findIdx? (· == id)) ids
      simpa only [List.findIdx?_map,Function.comp_def] using mapped

theorem before_anchor_splice (old new : Forest) (gap : Nat) (fresh : List Item)
    (equation : NotionCoreOriginTree.preorder new =
      (NotionCoreOriginTree.preorder old).take gap ++ fresh ++ (NotionCoreOriginTree.preorder old).drop gap)
    (bounded : gap ≤ (NotionCoreOriginTree.preorder old).length)
    (anchor : NotionCoreFormattingSource.Anchor) (supported : BeforeEndpoint anchor)
    (apart : ∀ id, anchor.endpoint = .item id → ∀ item ∈ fresh, item.id ≠ id) :
    NotionCoreFormattingSource.anchorPosition new anchor =
      (NotionCoreFormattingSource.anchorPosition old anchor).map (shift gap fresh.length) := by
  obtain ⟨side,endpoint | ⟨id,endpoint⟩⟩ := supported
  · cases anchor with
    | mk endpoint' side' =>
      simp only at side endpoint
      subst endpoint'; subst side'
      simp only [NotionCoreFormattingSource.anchorPosition,Option.map_some,equation,
        List.length_append,List.length_take,List.length_drop,shift,bounded,↓reduceIte]
      congr 1
      omega
  · cases anchor with
    | mk endpoint' side' =>
      simp only at side endpoint
      subst endpoint'; subst side'
      rw [NotionCoreRichCoordinates.anchor_before_findIdx,NotionCoreRichCoordinates.anchor_before_findIdx,equation]
      exact NotionCoreRichCoordinates.findIdx_splice _ _ _ gap (fun item member => by
        simpa using apart id rfl item member)

/-- The source alphabet guard used by the repaired compiler. It is a
structural integrity property, not a postulated final observation relation. -/
def SupportedBatches (actual : NotionCoreAtomicFormattingMachine.State) : Prop :=
  ∀ batch ∈ actual.batches, ∀ segment ∈ batch.segments,
    BeforeEndpoint segment.lower ∧ BeforeEndpoint segment.upper

def RegisteredSegments (actual : NotionCoreAtomicFormattingMachine.State) : Prop :=
  ∀ batch ∈ actual.batches, ∀ segment ∈ batch.segments, Registered actual segment.instanceId

theorem plain_marks_of_no_segments (actual : NotionCoreAtomicFormattingMachine.State) (inst : Nat)
    (items : List Slot)
    (outside : ∀ batch ∈ actual.batches, ∀ segment ∈ batch.segments, segment.instanceId ≠ inst) :
    AtomicBridge.MarksRelated (NotionCoreAtomicFormattingMachine.instanceForest actual) actual.batches
      inst (Text.plain items) := by
  have orderedOutside : ∀ batch ∈ NotionCoreAtomicFormatting.sort actual.batches,
      ∀ segment ∈ batch.segments, segment.instanceId ≠ inst := by
    intro batch member
    exact outside batch ((NotionCoreAtomicFormatting.sort_perm _).mem_iff.mp member)
  constructor
  · intro index
    symm
    apply NotionCoreAtomicFormatting.untouched
    intro batch member
    simp only [NotionCoreAtomicFormatting.covers,List.any_eq_false]
    intro segment inside
    simp [NotionCoreAtomicFormatting.segmentCovers,orderedOutside batch member segment inside]
  · intro gap
    symm
    apply NotionCoreAtomicFormatting.untouched
    intro batch member
    simp only [NotionCoreAtomicFormatting.gapCovers,List.any_eq_false]
    intro segment inside
    simp [NotionCoreAtomicFormatting.segmentGapCovers,orderedOutside batch member segment inside]

theorem create_related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (registeredSegments : RegisteredSegments actual)
    (core : NotionCoreMachine.State) (block : NotionCorePayload.BlockKey)
    (after : Option NotionCorePayload.BlockKey)
    (fresh : ∀ entry ∈ actual.core.instances, entry.1 ≠ NotionCoreMachine.blockName block)
    (freshBlock : NotionCoreMachine.FreshBlock actual.core (NotionCoreMachine.blockName block))
    (operation : NotionCoreMachine.applyOperation actual.core (.create block after) = some core)
    (source : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some source) :
    Related (edited actual core)
      ⟨NotionCoreSourceDocument.project source,
        putText abstract.texts (NotionCoreMachine.blockName block) (Text.plain [])⟩ := by
  let inst := NotionCoreMachine.blockName block
  change Related (edited actual core)
    ⟨NotionCoreSourceDocument.project source,putText abstract.texts inst (Text.plain [])⟩
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape actual.core core block after fresh freshBlock operation
  have storage := NotionCoreMachineCanonicalCreate.fresh_create_storage actual.core core block after fresh freshBlock operation
  change ∀ key, NotionCoreMachine.getInstance core key =
    if key = inst then {} else NotionCoreMachine.getInstance actual.core key at storage
  have absent : ¬ Registered actual inst := by
    rintro ⟨entry,member,same⟩
    exact fresh entry member same
  have actualDomain (key : Nat) : Registered (edited actual core) key ↔ key = inst ∨ Registered actual key := by
    simp only [Registered,edited,shape.1,List.mem_append,List.mem_singleton]
    constructor
    · rintro ⟨entry,old | rfl,same⟩
      · exact Or.inr ⟨entry,old,same⟩
      · exact Or.inl same.symm
    · rintro (rfl | ⟨entry,member,same⟩)
      · exact ⟨_,Or.inr rfl,rfl⟩
      · exact ⟨entry,Or.inl member,same⟩
  have frame (key : Nat) (different : key ≠ inst) := forest_of_storage actual core key (by
    simpa only [if_neg different] using storage key)
  have empty : NotionCoreMachine.getInstance core inst = {} := by simpa only [if_pos rfl] using storage inst
  have emptyForest : NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) inst = .nil := by
    simp [NotionCoreAtomicFormattingMachine.instanceForest,NotionCoreAtomicFormattingMachine.plainState,
      NotionCoreFormattingMachine.instanceForest,edited,empty,NotionCoreFormattingMachine.extract]
  constructor
  · exact ⟨source,materialized,rfl⟩
  · intro key
    rw [actualDomain]
    by_cases same : key = inst
    · simp [putText,same]
    · simp only [putText,if_neg same,or_iff_right same]
      exact related.registered key
  · intro key text found
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at found
      subst text
      simp [Text.plain,emptyForest,NotionCoreRichCoordinates.physicalSlots,NotionCoreOriginTree.preorder]
    · simp only [putText,if_neg same] at found
      rw [related.physical key text found,frame key same]
  · intro key
    by_cases same : key = inst
    · simp [same,emptyForest,NotionCoreFormattingPlanner.UniqueIds,NotionCoreOriginTree.preorder]
    · rw [frame key same]
      exact related.unique key
  · intro key text found
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at found
      subst text
      apply plain_marks_of_no_segments
      intro batch member segment inside sameInstance
      have registered := registeredSegments batch member segment inside
      exact absent (sameInstance ▸ registered)
    · simp only [putText,if_neg same] at found
      exact marks_of_forest_frame actual core key text (related.marks key text found) (frame key same)

def FreshEndpoints (actual : NotionCoreAtomicFormattingMachine.State) (inst : Nat) (fresh : List Item) : Prop :=
  ∀ batch ∈ actual.batches, ∀ segment ∈ batch.segments, segment.instanceId = inst →
    ∀ id, segment.lower.endpoint = .item id ∨ segment.upper.endpoint = .item id →
      ∀ item ∈ fresh, item.id ≠ id

/-- Lift an actual retained-list splice to the global relation. Every mark,
including the newly created cells and latent gaps, is derived by insert_refines.
The source-document part can come directly from the existing canonical core
simulation, independently of the annotation argument. -/
theorem insert_related_of_splice (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (core : NotionCoreMachine.State) (inst gap : Nat)
    (fresh : List Item) (text : Text) (found : abstract.texts inst = some text)
    (splice : storedItems core inst =
      (storedItems actual.core inst).take gap ++ fresh ++ (storedItems actual.core inst).drop gap)
    (bounded : gap ≤ (storedItems actual.core inst).length)
    (frame : ∀ key, key ≠ inst → NotionCoreMachine.getInstance core key = NotionCoreMachine.getInstance actual.core key)
    (registration : ∀ key, Registered (edited actual core) key ↔ Registered actual key)
    (unique : ∀ key, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) key))
    (supported : SupportedBatches actual) (apart : FreshEndpoints actual inst fresh)
    (source : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some source) :
    Related (edited actual core)
      ⟨NotionCoreSourceDocument.project source,
        putText abstract.texts inst (insertAt text gap (itemSlots inst fresh))⟩ := by
  let next := edited actual core
  have preorders : NotionCoreOriginTree.preorder (NotionCoreAtomicFormattingMachine.instanceForest next inst) =
      (NotionCoreOriginTree.preorder (NotionCoreAtomicFormattingMachine.instanceForest actual inst)).take gap ++
        fresh ++ (NotionCoreOriginTree.preorder (NotionCoreAtomicFormattingMachine.instanceForest actual inst)).drop gap := by
    simpa only [NotionCoreAtomicFormattingEffects.storedItems_forest] using splice
  have coordinates : AtomicBridge.CoordinatesShift (NotionCoreAtomicFormattingMachine.instanceForest actual)
      (NotionCoreAtomicFormattingMachine.instanceForest next) actual.batches inst gap (itemSlots inst fresh).length := by
    apply AtomicBridge.coordinatesShift_of_endpoints
    intro batch member segment inside instanceId
    have both := supported batch member segment inside
    constructor
    · simpa only [List.length_map] using before_anchor_splice _ _ gap fresh preorders
        (by simpa only [NotionCoreAtomicFormattingEffects.storedItems_forest] using bounded)
        segment.lower both.1 (fun id equal => apart batch member segment inside instanceId id (Or.inl equal))
    · simpa only [List.length_map] using before_anchor_splice _ _ gap fresh preorders
        (by simpa only [NotionCoreAtomicFormattingEffects.storedItems_forest] using bounded)
        segment.upper both.2 (fun id equal => apart batch member segment inside instanceId id (Or.inr equal))
  constructor
  · exact ⟨source,materialized,rfl⟩
  · intro key
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true]
      exact ⟨fun _ => (registration inst).mpr ((related.registered inst).mp ⟨text,found⟩),fun _ => ⟨_,rfl⟩⟩
    · simp only [putText,if_neg same]
      exact (related.registered key).trans (registration key).symm
  · intro key resultText resultFound
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at resultFound
      subst resultText
      change (text.items.take gap ++ itemSlots inst fresh ++ text.items.drop gap) = _
      rw [related.physical inst text found]
      simp only [physicalSlots_actual,edited,splice,itemSlots,List.map_append,List.map_take,List.map_drop]
    · simp only [putText,if_neg same] at resultFound
      rw [related.physical key resultText resultFound,
        forest_of_storage actual core key (frame key same)]
  · exact unique
  · intro key resultText resultFound
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at resultFound
      subst resultText
      exact AtomicBridge.insert_refines _ _ actual.batches inst gap (itemSlots inst fresh) text
        (related.marks inst text found) coordinates
    · simp only [putText,if_neg same] at resultFound
      exact marks_of_forest_frame actual core key resultText (related.marks key resultText resultFound)
        (forest_of_storage actual core key (frame key same))

theorem actual_insert_registration (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (block inst : NotionCorePayload.BlockKey)
    (first : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (registered : Registered actual (NotionCoreMachine.blockName inst))
    (operation : NotionCoreMachine.applyOperation actual.core (.insert block inst first origin atoms) = some core) :
    ∀ key, Registered (edited actual core) key ↔ Registered actual key := by
  simp only [NotionCoreMachine.applyOperation] at operation
  cases integrated : NotionCoreMachine.integrateRows
      (NotionCoreMachine.getInstance actual.core (NotionCoreMachine.blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (NotionCoreMachine.getInstance actual.core (NotionCoreMachine.blockName inst)).pending)))) with
  | none => simp [integrated] at operation
  | some rows =>
    simp [integrated] at operation
    subst core
    intro key
    exact NotionCoreMachinePartitionUpdates.putInstance_exists_iff actual.core _ key _ registered

theorem canonical_insert_related (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (core : NotionCoreMachine.State) (step : NotionCoreMachine.applyTransaction actual.core tx = some core)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (text : Text)
    (found : abstract.texts (NotionCoreMachine.blockName inst) = some text)
    (supported : SupportedBatches actual)
    (apart : FreshEndpoints actual (NotionCoreMachine.blockName inst)
      (NotionCorePayload.textItems tx.id atoms (fun _ => false)))
    (source : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some source) :
    Related (edited actual core)
      ⟨NotionCoreSourceDocument.project source,putText abstract.texts (NotionCoreMachine.blockName inst)
        (insertAt text (originGap (storedItems actual.core (NotionCoreMachine.blockName inst)) origin)
          (itemSlots (NotionCoreMachine.blockName inst) (NotionCorePayload.textItems tx.id atoms (fun _ => false))))⟩ := by
  obtain ⟨splice,bounded⟩ := NotionCoreAtomicFormattingEffects.canonical_insert_items_all network reachable
    version closed pre suffix tx position actual.core core replayed block inst origin atoms payload step
  have operation : NotionCoreMachine.applyOperation actual.core (.insert block inst tx.id origin atoms) = some core := by
    simpa [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload,NotionCoreMachine.applyOperations] using step
  have oldRegistered := (related.registered _).mp ⟨text,found⟩
  have registration := actual_insert_registration actual core block inst tx.id origin atoms oldRegistered operation
  have nextReplay : NotionCoreMachine.replay {} (pre ++ [tx]) = some core := by
    rw [core_replay_append,replayed]
    simp [NotionCoreMachine.replay,step]
  have nextPosition : NotionCoreReconstruction.transactionsFor network version = (pre ++ [tx]) ++ suffix := by
    simpa only [List.append_assoc,List.singleton_append] using position
  apply insert_related_of_splice actual abstract related core _ _ _ text found splice bounded
    (fun key different => NotionCoreAtomicFormattingEffects.insert_frame actual.core core block inst tx.id
      origin atoms operation key different) registration
    (unique_of_physical _ (NotionCoreMachineVersionTables.version_physical_unique_all network reachable
      version closed (pre ++ [tx]) suffix nextPosition core nextReplay)) supported apart source materialized

theorem insertionGap_actual (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (inst : Nat) (text : Text) (found : abstract.texts inst = some text)
    (origin : NotionCoreOriginTree.Origin)
    (present : NotionCorePhysicalReplay.originAddress inst origin ∈
      (NotionCoreMachine.physical actual.core inst).map NotionCoreSource.Atom.address) :
    insertionGap inst text (NotionCorePhysicalReplay.originAddress inst origin).2 =
      some (originGap (storedItems actual.core inst) origin) := by
  cases origin with
  | start => rfl
  | item id =>
    have member : id ∈ (storedItems actual.core inst).map Item.id := by
      simp only [NotionCoreMachine.physical,NotionCorePhysicalReplay.physical,List.map_cons,
        NotionCorePhysicalReplay.start_address,List.mem_cons,List.mem_map] at present
      rcases present with impossible | ⟨item,member,equal⟩
      · exact False.elim (NotionCorePhysicalReplay.address_ne_start inst id impossible)
      · obtain ⟨original,originalMember,rfl⟩ := member
        exact List.mem_map.mpr ⟨original,originalMember,NotionCorePhysicalReplay.address_injective inst equal⟩
    have addresses : text.items.map Slot.address = (storedItems actual.core inst).map
        (fun item => NotionCorePhysicalReplay.address inst item.id) := by
      rw [related.physical inst text found,NotionCoreRichCoordinates.physicalSlots_addresses,
        NotionCoreAtomicFormattingEffects.storedItems_forest]
    have pred : (fun item : Item => NotionCorePhysicalReplay.address inst item.id ==
        NotionCorePhysicalReplay.address inst id) = (fun item => item.id == id) := by
      funext item
      exact Bool.eq_iff_iff.mpr (by
        simp only [beq_iff_eq]
        exact (NotionCorePhysicalReplay.address_injective inst).eq_iff)
    have search : ((storedItems actual.core inst).map Item.id).findIdx? (· == id) =
        some (((storedItems actual.core inst).map Item.id).idxOf id) := by
      exact List.findIdx?_eq_some_of_exists ⟨id,member,by simp⟩
    change ((text.items.map Slot.address).findIdx?
      (fun address => address == NotionCorePhysicalReplay.address inst id)).map (·+1) = _
    rw [addresses,List.findIdx?_map]
    change ((storedItems actual.core inst).findIdx? (fun item =>
      NotionCorePhysicalReplay.address inst item.id == NotionCorePhysicalReplay.address inst id)).map (·+1) = _
    rw [pred]
    have search' : (storedItems actual.core inst).findIdx? (fun item => item.id == id) =
        some (((storedItems actual.core inst).map Item.id).idxOf id) := by
      simpa only [List.findIdx?_map,Function.comp_def] using search
    rw [search']
    rfl

/-- Actual canonical insert plus the old plain-source document theorem gives
an independent coreStep, with all rich marks and gaps obtained by direct
insertion. The only annotation premises are source endpoint integrity. -/
theorem canonical_insert_coreStep (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (supported : SupportedBatches actual)
    (apart : FreshEndpoints actual (NotionCoreMachine.blockName inst)
      (NotionCorePayload.textItems tx.id atoms (fun _ => false))) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreStep abstract (.insert (NotionCorePhysicalReplay.originAddress (NotionCoreMachine.blockName inst) origin)
        (itemSlots (NotionCoreMachine.blockName inst) (NotionCorePayload.textItems tx.id atoms (fun _ => false)))) = some after ∧
      Related (edited actual core) after := by
  obtain ⟨source,materialized,document⟩ := related.document
  obtain ⟨core,afterSource,operation,afterMat,execution⟩ := NotionCoreMachineHistory.canonical_step_version
    network reachable version closed pre suffix tx position actual.core replayed source materialized
  have sourceStep := NotionCoreSourceDocument.execution_sound execution
  have docStep : NotionCoreSpec.step abstract.document
      (.insert (NotionCorePhysicalReplay.originAddress (NotionCoreMachine.blockName inst) origin)
        (itemSlots (NotionCoreMachine.blockName inst) (NotionCorePayload.textItems tx.id atoms (fun _ => false)))) =
      some (NotionCoreSourceDocument.project afterSource) := by
    simpa [NotionCoreMachineCommands.commands,payload,NotionCoreSourceDocument.Command.semantic,
      NotionCoreMachineCommands.text,NotionCoreSpec.execute,document,itemSlots] using sourceStep
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have plainReach := NotionCoreCreatorNetwork.payload_reachable creators
  have registered := NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators
    version closed pre suffix tx position actual.core replayed inst (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  obtain ⟨text,found⟩ := (related.registered _).mpr registered
  have present := NotionCoreMachineCanonicalForest.canonical_insert_origin_present_version network plainReach
    version closed pre suffix tx position actual.core replayed block inst origin atoms payload
  have gap := insertionGap_actual actual abstract related _ text found origin present
  let after : State := ⟨NotionCoreSourceDocument.project afterSource,
    putText abstract.texts (NotionCoreMachine.blockName inst)
      (insertAt text (originGap (storedItems actual.core (NotionCoreMachine.blockName inst)) origin)
        (itemSlots (NotionCoreMachine.blockName inst) (NotionCorePayload.textItems tx.id atoms (fun _ => false))))⟩
  refine ⟨core,after,operation,?_,?_⟩
  · unfold coreStep
    rw [docStep]
    have fstOrigin : (NotionCorePhysicalReplay.originAddress (NotionCoreMachine.blockName inst) origin).1 =
        NotionCoreMachine.blockName inst := by cases origin <;> rfl
    simp only [coreTexts,insertPhysical,fstOrigin,found,gap,after,Bind.bind,Option.bind,pure]
  · exact canonical_insert_related network plainReach version closed pre suffix tx position actual abstract related
      replayed core operation block inst origin atoms payload text found supported apart afterSource afterMat

theorem canonical_create_coreStep (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (afterBlock : Option NotionCorePayload.BlockKey) (payload : tx.payload = .create afterBlock)
    (segments : RegisteredSegments actual) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreStep abstract (.create (NotionCoreMachine.blockName (.issued tx.id))
        (NotionCoreMachine.blockName (.issued tx.id)) (afterBlock.map NotionCoreMachine.blockName)) = some after ∧
      Related (edited actual core) after := by
  obtain ⟨source,materialized,document⟩ := related.document
  obtain ⟨core,afterSource,operation,afterMat,execution⟩ := NotionCoreMachineHistory.canonical_step_version
    network reachable version closed pre suffix tx position actual.core replayed source materialized
  have sourceStep := NotionCoreSourceDocument.execution_sound execution
  have docStep : NotionCoreSpec.step abstract.document
      (.create (NotionCoreMachine.blockName (.issued tx.id)) (NotionCoreMachine.blockName (.issued tx.id))
        (afterBlock.map NotionCoreMachine.blockName)) = some (NotionCoreSourceDocument.project afterSource) := by
    simpa [NotionCoreMachineCommands.commands,payload,NotionCoreSourceDocument.Command.semantic,
      NotionCoreSpec.execute,document] using sourceStep
  obtain ⟨fresh,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network (NotionCoreMachineNetwork.creator_reachable reachable) version closed pre suffix tx position actual.core replayed
  have missing : abstract.texts (NotionCoreMachine.blockName (.issued tx.id)) = none := by
    cases selected : abstract.texts (NotionCoreMachine.blockName (.issued tx.id)) with
    | none => rfl
    | some text =>
      obtain ⟨entry,member,same⟩ := (related.registered _).mp ⟨text,selected⟩
      exact False.elim (fresh entry member same)
  have raw : NotionCoreMachine.applyOperation actual.core (.create (.issued tx.id) afterBlock) = some core := by
    simpa [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload,NotionCoreMachine.applyOperations] using operation
  let after : State := ⟨NotionCoreSourceDocument.project afterSource,
    putText abstract.texts (NotionCoreMachine.blockName (.issued tx.id)) (Text.plain [])⟩
  refine ⟨core,after,operation,?_,?_⟩
  · unfold coreStep
    rw [docStep]
    simp only [coreTexts,missing,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
      Bind.bind,Option.bind,pure,after]
  · exact create_related actual abstract related segments core (.issued tx.id) afterBlock fresh freshBlock raw afterSource afterMat

theorem canonical_merge_coreStep (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (source inst : NotionCorePayload.BlockKey) (stop : Option NotionRunAllocation.Id)
    (payload : tx.payload = .merge source inst stop) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreStep abstract (.merge (NotionCoreMachine.blockName source)
        (NotionCoreMachineCommands.anchorAddress inst stop)) = some after ∧ Related (edited actual core) after := by
  obtain ⟨oldSource,materialized,document⟩ := related.document
  obtain ⟨core,afterSource,operation,afterMat,execution⟩ := NotionCoreMachineHistory.canonical_step_version
    network reachable version closed pre suffix tx position actual.core replayed oldSource materialized
  have sourceStep := NotionCoreSourceDocument.execution_sound execution
  have docStep : NotionCoreSpec.step abstract.document (.merge (NotionCoreMachine.blockName source)
      (NotionCoreMachineCommands.anchorAddress inst stop)) = some (NotionCoreSourceDocument.project afterSource) := by
    simpa [NotionCoreMachineCommands.commands,payload,NotionCoreSourceDocument.Command.semantic,
      NotionCoreSpec.execute,document] using sourceStep
  have raw : NotionCoreMachine.applyOperation actual.core (.merge source inst stop) = some core := by
    simpa [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload,NotionCoreMachine.applyOperations] using operation
  let after : State := ⟨NotionCoreSourceDocument.project afterSource,abstract.texts⟩
  refine ⟨core,after,operation,?_,?_⟩
  · unfold coreStep
    rw [docStep]
    rfl
  · exact merge_related actual abstract related core source inst stop raw afterSource afterMat

private theorem ordered_coverage_congr (old new : NotionCoreAtomicFormatting.Batch → Bool)
    (batches : List NotionCoreAtomicFormatting.Batch) (initial : Bool)
    (agree : ∀ batch ∈ batches, old batch = new batch) :
    NotionCoreAtomicFormatting.applyOrdered old batches initial =
      NotionCoreAtomicFormatting.applyOrdered new batches initial := by
  induction batches generalizing initial with
  | nil => rfl
  | cons batch rest ih =>
    simp only [NotionCoreAtomicFormatting.applyOrdered,List.foldl_cons]
    rw [agree batch (by simp)]
    exact ih _ (fun old member => agree old (by simp [member]))

private theorem resolve_coverage_congr (old new : NotionCoreAtomicFormatting.Batch → Bool)
    (batches : List NotionCoreAtomicFormatting.Batch)
    (agree : ∀ batch ∈ batches, old batch = new batch) :
    NotionCoreAtomicFormatting.resolveWith old batches = NotionCoreAtomicFormatting.resolveWith new batches := by
  apply ordered_coverage_congr
  intro batch member
  exact agree batch ((NotionCoreAtomicFormatting.sort_perm _).mem_iff.mp member)

private theorem any_congr_mem {α : Type} (items : List α) (p q : α → Bool)
    (agree : ∀ item ∈ items, p item = q item) : items.any p = items.any q := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.any_cons,agree item (by simp)]
    rw [ih (fun old member => agree old (by simp [member]))]

theorem marks_of_ids (actual : NotionCoreAtomicFormattingMachine.State) (core : NotionCoreMachine.State)
    (inst : Nat) (text : Text) (related : AtomicBridge.MarksRelated
      (NotionCoreAtomicFormattingMachine.instanceForest actual) actual.batches inst text)
    (supported : SupportedBatches actual)
    (ids : (storedItems core inst).map Item.id = (storedItems actual.core inst).map Item.id) :
    AtomicBridge.MarksRelated (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core))
      actual.batches inst text := by
  have anchors (anchor : NotionCoreFormattingSource.Anchor) (ha : BeforeEndpoint anchor) :
      NotionCoreFormattingSource.anchorPosition (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) inst) anchor =
      NotionCoreFormattingSource.anchorPosition (NotionCoreAtomicFormattingMachine.instanceForest actual inst) anchor := by
    apply before_anchor_ids _ _ _ anchor ha
    simpa only [NotionCoreAtomicFormattingEffects.storedItems_forest] using ids
  constructor
  · intro index
    rw [related.1 index]
    apply resolve_coverage_congr
    intro batch member
    unfold NotionCoreAtomicFormatting.covers
    apply any_congr_mem
    intro segment inside
    simp only [NotionCoreAtomicFormatting.segmentCovers,NotionCoreFormattingSource.covers,
      NotionCoreAtomicFormatting.Segment.operation,anchors segment.lower (supported batch member segment inside).1,
      anchors segment.upper (supported batch member segment inside).2]
  · intro gap
    rw [related.2 gap]
    apply resolve_coverage_congr
    intro batch member
    unfold NotionCoreAtomicFormatting.gapCovers
    apply any_congr_mem
    intro segment inside
    simp only [NotionCoreAtomicFormatting.segmentGapCovers,
      anchors segment.lower (supported batch member segment inside).1,
      anchors segment.upper (supported batch member segment inside).2]

theorem actual_erase_registration (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (block inst : NotionCorePayload.BlockKey)
    (targets : List NotionRunAllocation.Id)
    (registered : Registered actual (NotionCoreMachine.blockName inst))
    (operation : NotionCoreMachine.applyOperation actual.core (.erase block inst targets) = some core) :
    ∀ key, Registered (edited actual core) key ↔ Registered actual key := by
  simp only [NotionCoreMachine.applyOperation,Option.some.injEq] at operation
  subst core
  exact fun key => NotionCoreMachinePartitionUpdates.putInstance_exists_iff actual.core _ key _ registered

theorem itemSlots_erase (inst : Nat) (items : List Item) (targets : List NotionRunAllocation.Id) :
    itemSlots inst (items.map (NotionCoreParentErase.eraseItem targets)) =
      (itemSlots inst items).map (eraseSlot (targets.map (NotionCorePhysicalReplay.address inst))) := by
  simp only [itemSlots,List.map_map]
  apply List.map_congr_left
  intro item member
  change (NotionCorePhysicalReplay.atom inst (NotionCoreParentErase.eraseItem targets item)).slot = _
  rw [NotionCoreMachineErase.atom_erase,NotionCoreSource.erase_atom_projection]
  rfl

theorem itemSlots_erase_other (inst selected : Nat) (different : inst ≠ selected)
    (items : List Item) (targets : List NotionRunAllocation.Id) :
    (itemSlots inst items).map (eraseSlot (targets.map (NotionCorePhysicalReplay.address selected))) = itemSlots inst items := by
  simp only [itemSlots,List.map_map]
  apply List.map_congr_left
  intro item member
  have absent : ((targets.map (NotionCorePhysicalReplay.address selected)).contains
      (NotionCorePhysicalReplay.atom inst item).slot.address) = false := by
    simp only [List.contains_eq_mem,decide_eq_false_iff_not,List.mem_map]
    rintro ⟨id,inside,equal⟩
    exact different (by simpa only [NotionCoreSource.Atom.slot_address,
      NotionCorePhysicalReplay.atom_address,NotionCorePhysicalReplay.address] using (congrArg Prod.fst equal).symm)
  simp only [Function.comp_apply,eraseSlot,absent,Bool.not_false,Bool.and_true]

theorem erase_related_coreStep (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (supported : SupportedBatches actual)
    (core : NotionCoreMachine.State) (block inst : NotionCorePayload.BlockKey) (targets : List NotionRunAllocation.Id)
    (registered : Registered actual (NotionCoreMachine.blockName inst))
    (operation : NotionCoreMachine.applyOperation actual.core (.erase block inst targets) = some core) :
    ∃ after, coreStep abstract (.delete (targets.map (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName inst)))) = some after ∧
      Related (edited actual core) after := by
  obtain ⟨source,materialized,document⟩ := related.document
  obtain ⟨afterSource,afterMat,sourceStep⟩ := NotionCoreMachineDocumentErase.erase_source_step
    actual.core core block inst targets source operation materialized
  have docStep : NotionCoreSpec.step abstract.document
      (.delete (targets.map (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName inst)))) =
      some (NotionCoreSourceDocument.project afterSource) := by
    have projected := NotionCoreSourceDocument.project_delete source
      (targets.map (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName inst)))
    rw [sourceStep] at projected
    simpa only [Option.map_some,document] using projected.symm
  let addresses := targets.map (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName inst))
  let after : State := ⟨NotionCoreSourceDocument.project afterSource,
    fun key => (abstract.texts key).map (fun text => erase text addresses)⟩
  refine ⟨after,?_,?_⟩
  · unfold coreStep
    rw [docStep]
    rfl
  · constructor
    · exact ⟨afterSource,afterMat,rfl⟩
    · intro key
      change (∃ text, (abstract.texts key).map _ = some text) ↔ _
      rw [actual_erase_registration actual core block inst targets registered operation key]
      constructor
      · rintro ⟨text,found⟩
        obtain ⟨oldText,oldFound,_⟩ := Option.map_eq_some_iff.mp found
        exact (related.registered key).mp ⟨oldText,oldFound⟩
      · intro oldRegistered
        obtain ⟨text,found⟩ := (related.registered key).mpr oldRegistered
        exact ⟨_,by rw [found]; rfl⟩
    · intro key text found
      obtain ⟨oldText,oldFound,same⟩ := Option.map_eq_some_iff.mp found
      subst text
      change (oldText.items.map _) = _
      rw [related.physical key oldText oldFound,physicalSlots_actual,physicalSlots_actual]
      simp only [edited]
      rw [
        NotionCoreAtomicFormattingEffects.erase_items actual.core core block inst targets operation key]
      by_cases selected : key = NotionCoreMachine.blockName inst
      · simp only [selected,ite_true,itemSlots_erase,addresses]
      · simp only [if_neg selected]
        exact itemSlots_erase_other key _ selected _ targets
    · intro key
      have ids := NotionCoreAtomicFormattingEffects.erase_item_ids actual.core core block inst targets operation key
      change ((NotionCoreOriginTree.preorder _).map Item.id).Nodup
      rw [NotionCoreAtomicFormattingEffects.storedItems_forest]
      simp only [edited]
      rw [ids,
        ← NotionCoreAtomicFormattingEffects.storedItems_forest actual key]
      exact related.unique key
    · intro key text found
      obtain ⟨oldText,oldFound,same⟩ := Option.map_eq_some_iff.mp found
      subst text
      exact marks_of_ids actual core key oldText (related.marks key oldText oldFound) supported
        (NotionCoreAtomicFormattingEffects.erase_item_ids actual.core core block inst targets operation key)

def textBatch (texts : Nat → Option Text) : List NotionCoreSpec.Command → Option (Nat → Option Text)
  | [] => some texts
  | command :: rest => do textBatch (← coreTexts texts command) rest

theorem coreBatch_components (document : Document) (texts : Nat → Option Text) (commands : List NotionCoreSpec.Command) :
    coreBatch ⟨document,texts⟩ commands = (do
      let nextDoc ← NotionCoreSpec.execute document commands
      let nextTexts ← textBatch texts commands
      pure ⟨nextDoc,nextTexts⟩) := by
  induction commands generalizing document texts with
  | nil => rfl
  | cons command rest ih =>
    simp only [coreBatch,coreStep,NotionCoreSpec.execute,textBatch]
    cases docStep : NotionCoreSpec.step document command <;>
      cases textsStep : coreTexts texts command <;> simp [ih]

theorem plain_insert_empty (fresh : List Slot) : insertAt (Text.plain []) 0 fresh = Text.plain fresh := by
  apply Text.ext
  · simp [insertAt,Text.plain]
  · funext index
    simp [insertAt,Text.plain]
  · funext gap
    simp [insertAt,Text.plain]

theorem putText_overwrite (texts : Nat → Option Text) (inst : Nat) (first later : Text) :
    putText (putText texts inst first) inst later = putText texts inst later := by
  funext key
  by_cases same : key = inst <;> simp [putText,same]

theorem actual_create_registration (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (block : NotionCorePayload.BlockKey)
    (after : Option NotionCorePayload.BlockKey)
    (fresh : ∀ entry ∈ actual.core.instances, entry.1 ≠ NotionCoreMachine.blockName block)
    (freshBlock : NotionCoreMachine.FreshBlock actual.core (NotionCoreMachine.blockName block))
    (operation : NotionCoreMachine.applyOperation actual.core (.create block after) = some core) :
    ∀ key, Registered (edited actual core) key ↔ key = NotionCoreMachine.blockName block ∨ Registered actual key := by
  have shape := (NotionCoreMachineCanonicalCreate.fresh_create_shape actual.core core block after fresh freshBlock operation).1
  intro key
  simp only [Registered,edited,shape,List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨entry,old | rfl,same⟩
    · exact Or.inr ⟨entry,old,same⟩
    · exact Or.inl same.symm
  · rintro (rfl | ⟨entry,member,same⟩)
    · exact ⟨_,Or.inr rfl,rfl⟩
    · exact ⟨entry,Or.inl member,same⟩

theorem fresh_instance_related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (segments : RegisteredSegments actual)
    (core : NotionCoreMachine.State) (inst : Nat) (items : List Item)
    (absent : ¬ Registered actual inst)
    (domain : ∀ key, Registered (edited actual core) key ↔ key = inst ∨ Registered actual key)
    (freshItems : storedItems core inst = items)
    (frame : ∀ key, key ≠ inst → NotionCoreMachine.getInstance core key = NotionCoreMachine.getInstance actual.core key)
    (unique : ∀ key, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) key))
    (source : NotionCoreSourceDocument.Document)
    (materialized : NotionCoreMachineDocument.materializeDocument core = some source) :
    Related (edited actual core) ⟨NotionCoreSourceDocument.project source,
      putText abstract.texts inst (Text.plain (itemSlots inst items))⟩ := by
  constructor
  · exact ⟨source,materialized,rfl⟩
  · intro key
    rw [domain]
    by_cases same : key = inst
    · simp [putText,same]
    · simp only [putText,if_neg same,or_iff_right same]
      exact related.registered key
  · intro key text found
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at found
      subst text
      simp only [Text.plain,physicalSlots_actual,edited,freshItems]
    · simp only [putText,if_neg same] at found
      rw [related.physical key text found,forest_of_storage actual core key (frame key same)]
  · exact unique
  · intro key text found
    by_cases same : key = inst
    · subst key
      simp only [putText,ite_true,Option.some.injEq] at found
      subst text
      apply plain_marks_of_no_segments
      intro batch member segment inside sameInstance
      exact absent (sameInstance ▸ segments batch member segment inside)
    · simp only [putText,if_neg same] at found
      exact marks_of_forest_frame actual core key text (related.marks key text found)
        (forest_of_storage actual core key (frame key same))

theorem canonical_next_unique (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (core : NotionCoreMachine.State) (step : NotionCoreMachine.applyTransaction actual.core tx = some core) :
    ∀ key, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest (edited actual core) key) := by
  have nextReplay : NotionCoreMachine.replay {} (pre ++ [tx]) = some core := by
    rw [core_replay_append,replayed]
    simp [NotionCoreMachine.replay,step]
  have nextPosition : NotionCoreReconstruction.transactionsFor network version = (pre ++ [tx]) ++ suffix := by
    simpa only [List.append_assoc,List.singleton_append] using position
  exact unique_of_physical _ (NotionCoreMachineVersionTables.version_physical_unique_all network reachable
    version closed (pre ++ [tx]) suffix nextPosition core nextReplay)

theorem canonical_bootstrap_coreBatch (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) (segments : RegisteredSegments actual) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreBatch abstract ((NotionCoreMachineCommands.commands tx).map NotionCoreSourceDocument.Command.semantic) = some after ∧
      Related (edited actual core) after := by
  obtain ⟨source,materialized,document⟩ := related.document
  obtain ⟨core,afterSource,operation,afterMat,execution⟩ := NotionCoreMachineHistory.canonical_step_version
    network reachable version closed pre suffix tx position actual.core replayed source materialized
  have docBatch := NotionCoreSourceDocument.execution_sound execution
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have plainReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨fresh,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh_version
    network creators version closed pre suffix tx position atoms payload actual.core replayed
  have absent : ¬ Registered actual 0 := by
    rintro ⟨entry,member,same⟩
    exact fresh entry member same
  have missing : abstract.texts 0 = none := by
    cases selected : abstract.texts 0 with
    | none => rfl
    | some text => exact False.elim (absent ((related.registered 0).mp ⟨text,selected⟩))
  have steps : NotionCoreMachine.applyOperations actual.core [.create .initial none,
      .insert .initial .initial tx.id .start atoms] = some core := by
    simpa [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload] using operation
  cases first : NotionCoreMachine.applyOperation actual.core (.create .initial none) with
  | none => simp [NotionCoreMachine.applyOperations,first] at steps
  | some created =>
    have inserted : NotionCoreMachine.applyOperation created (.insert .initial .initial tx.id .start atoms) = some core := by
      simpa [NotionCoreMachine.applyOperations,first] using steps
    have createdDomain := actual_create_registration actual created .initial none fresh freshBlock first
    have regCreated : Registered (edited actual created) 0 := (createdDomain 0).mpr (Or.inl rfl)
    have insertDomain := actual_insert_registration (edited actual created) core .initial .initial tx.id .start atoms regCreated inserted
    have domain : ∀ key, Registered (edited actual core) key ↔ key = 0 ∨ Registered actual key := by
      intro key
      exact (insertDomain key).trans (createdDomain key)
    have contents := NotionCoreAtomicFormattingEffects.canonical_bootstrap_items network creators version closed
      pre suffix tx position actual.core core replayed atoms payload operation
    let freshItems := NotionCorePayload.textItems tx.id atoms (fun _ => false)
    let after : State := ⟨NotionCoreSourceDocument.project afterSource,putText abstract.texts 0
      (Text.plain (itemSlots 0 freshItems))⟩
    refine ⟨core,after,operation,?_,?_⟩
    · rw [show abstract = ⟨abstract.document,abstract.texts⟩ from rfl,coreBatch_components,document,docBatch]
      simp [textBatch,NotionCoreMachineCommands.commands,payload,NotionCoreMachineCommands.text,
        NotionCoreSourceDocument.Command.semantic,coreTexts,missing,putText,insertPhysical,insertionGap,
        plain_insert_empty,putText_overwrite,after,freshItems,itemSlots]
    · apply fresh_instance_related actual abstract related segments core 0 freshItems absent domain contents.1
        _ (canonical_next_unique network plainReach version closed pre suffix tx position actual replayed core operation)
        afterSource afterMat
      intro key different
      exact (NotionCoreAtomicFormattingEffects.insert_frame created core .initial .initial tx.id .start atoms inserted key
        (by simpa [NotionCoreMachine.blockName] using different)).trans
        (NotionCoreAtomicFormattingEffects.create_storage actual.core created .initial none first key)

theorem actual_marker_registration (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (block inst : NotionCorePayload.BlockKey)
    (id : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin)
    (registered : Registered actual (NotionCoreMachine.blockName inst))
    (operation : NotionCoreMachine.applyOperation actual.core (.marker block inst id origin) = some core) :
    ∀ key, Registered (edited actual core) key ↔ Registered actual key := by
  simp only [NotionCoreMachine.applyOperation] at operation
  cases integrated : NotionCoreMachine.integrate
      (NotionCoreMachine.getInstance actual.core (NotionCoreMachine.blockName inst)).rows
      ⟨⟨id,.split⟩,origin⟩ with
  | none => simp [integrated] at operation
  | some rows =>
    simp only [integrated] at operation
    dsimp only [Bind.bind,Option.bind] at operation
    split at operation
    · contradiction
    · dsimp only at operation
      split at operation
      · simp at operation
        subst core
        exact fun key => NotionCoreMachinePartitionUpdates.putInstance_exists_iff actual.core _ key _ registered
      · contradiction

theorem actual_move_registration (actual : NotionCoreAtomicFormattingMachine.State)
    (core : NotionCoreMachine.State) (block inst : NotionCorePayload.BlockKey)
    (id : NotionRunAllocation.Id) (target : NotionCorePayload.BlockKey)
    (operation : NotionCoreMachine.applyOperation actual.core (.moveInto block inst id target) = some core) :
    ∀ key, Registered (edited actual core) key ↔ Registered actual key := by
  simp only [NotionCoreMachine.applyOperation] at operation
  split at operation
  · contradiction
  · cases selected : NotionCoreSliceForest.detachForest
      (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName inst) id) actual.core.forest with
    | none => simp [selected] at operation
    | some pair => simp [selected] at operation; subst core; exact fun _ => Iff.rfl

theorem canonical_split_coreBatch (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (segments : RegisteredSegments actual) (supported : SupportedBatches actual)
    (apart : FreshEndpoints actual (NotionCoreMachine.blockName inst) [⟨tx.id,.split⟩]) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreBatch abstract ((NotionCoreMachineCommands.commands tx).map NotionCoreSourceDocument.Command.semantic) = some after ∧
      Related (edited actual core) after := by
  obtain ⟨source,materialized,document⟩ := related.document
  obtain ⟨core,afterSource,operation,afterMat,execution⟩ := NotionCoreMachineHistory.canonical_step_version
    network reachable version closed pre suffix tx position actual.core replayed source materialized
  have docBatch := NotionCoreSourceDocument.execution_sound execution
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have plainReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨fresh,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network creators version closed pre suffix tx position actual.core replayed
  have registered := NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators
    version closed pre suffix tx position actual.core replayed inst (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  obtain ⟨text,found⟩ := (related.registered _).mpr registered
  let oldInst := NotionCoreMachine.blockName inst
  let newInst := NotionCoreMachine.blockName (.issued tx.id)
  have different : oldInst ≠ newInst := by
    obtain ⟨entry,member,same⟩ := registered
    intro equal
    exact fresh entry member (same.trans equal)
  have missing : abstract.texts newInst = none := by
    cases selected : abstract.texts newInst with
    | none => rfl
    | some text =>
      obtain ⟨entry,member,same⟩ := (related.registered _).mp ⟨text,selected⟩
      exact False.elim (fresh entry member same)
  have steps : NotionCoreMachine.applyOperations actual.core [.create (.issued tx.id) (some block),
      .marker block inst tx.id origin,.moveInto block inst tx.id (.issued tx.id)] = some core := by
    simpa [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload] using operation
  cases createStep : NotionCoreMachine.applyOperation actual.core (.create (.issued tx.id) (some block)) with
  | none => simp [NotionCoreMachine.applyOperations,createStep] at steps
  | some created =>
    cases markerStep : NotionCoreMachine.applyOperation created (.marker block inst tx.id origin) with
    | none => simp [NotionCoreMachine.applyOperations,createStep,markerStep] at steps
    | some marked =>
      have moveStep : NotionCoreMachine.applyOperation marked (.moveInto block inst tx.id (.issued tx.id)) = some core := by
        simpa [NotionCoreMachine.applyOperations,createStep,markerStep] using steps
      have createStorage := NotionCoreAtomicFormattingEffects.create_storage actual.core created (.issued tx.id) (some block) createStep
      have createDomain := actual_create_registration actual created (.issued tx.id) (some block) fresh freshBlock createStep
      have registeredCreated : Registered (edited actual created) oldInst := (createDomain oldInst).mpr (Or.inr registered)
      have markerDomain := actual_marker_registration (edited actual created) marked block inst tx.id origin registeredCreated markerStep
      have moveDomain := actual_move_registration (edited actual marked) core block inst tx.id (.issued tx.id) moveStep
      have registration : ∀ key, Registered (edited (edited actual created) core) key ↔ Registered (edited actual created) key := by
        intro key
        exact (moveDomain key).trans (markerDomain key)
      obtain ⟨checked,checkedReplay,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version
        network reachable version closed pre (tx :: suffix) position
      have checkedEq : checked = actual.core := Option.some.inj (checkedReplay.symm.trans replayed)
      rw [checkedEq] at part
      have createdPart := NotionCoreMachinePartitionCreate.create_preserves_partitioned actual.core created
        (.issued tx.id) (some block) part fresh freshBlock.1 createStep
      have createdPhysical := NotionCoreMachineCanonicalCreate.fresh_create_physical actual.core created
        (.issued tx.id) (some block) fresh freshBlock createStep
      have oldUnique := NotionCoreMachineVersionTables.version_physical_unique_all network plainReach version closed
        pre (tx :: suffix) position actual.core replayed
      have createdUnique : ∀ key, ((NotionCoreMachine.physical created key).map NotionCoreSource.Atom.address).Nodup := by
        intro key
        by_cases selected : key = newInst
        · subst key
          rw [createdPhysical.1]
          simp [NotionCoreSliceForest.emptyPhysical]
        · rw [createdPhysical.2 key selected]
          exact oldUnique key
      obtain ⟨createdSource,createdMat⟩ := NotionCoreMachineDocument.materializeDocument_total created createdPart createdUnique
      let createdAbstract : State := ⟨NotionCoreSourceDocument.project createdSource,
        putText abstract.texts newInst (Text.plain [])⟩
      have createdRelated : Related (edited actual created) createdAbstract := create_related actual abstract related
        segments created (.issued tx.id) (some block) fresh freshBlock createStep createdSource createdMat
      have oldText : createdAbstract.texts oldInst = some text := by simp only [createdAbstract,putText,if_neg different]; exact found
      have contents := NotionCoreAtomicFormattingEffects.canonical_split_items network plainReach version closed pre suffix tx
        position actual.core core replayed block inst origin payload operation
      let gap := originGap (storedItems actual.core oldInst) origin
      have oldItems : storedItems created oldInst = storedItems actual.core oldInst := by simp only [storedItems,createStorage]
      have splice : storedItems core oldInst =
          (storedItems created oldInst).take gap ++ [⟨tx.id,.split⟩] ++ (storedItems created oldInst).drop gap := by
        rw [oldItems]
        exact contents.1
      obtain ⟨rows,integrated,_,_,present⟩ := NotionCoreMachineMarkerProgress.canonical_marker_physical_version
        network plainReach version closed pre suffix tx position actual.core replayed block inst origin payload
      have storage := NotionCoreAtomicFormattingEffects.split_storage actual.core core tx block inst origin rows payload integrated operation
      have frame : ∀ key, key ≠ oldInst → NotionCoreMachine.getInstance core key = NotionCoreMachine.getInstance created key := by
        intro key different
        rw [storage,NotionCoreMachineTables.getInstance_put,if_neg different,createStorage]
      let after : State := ⟨NotionCoreSourceDocument.project afterSource,
        putText createdAbstract.texts oldInst (insertAt text gap (itemSlots oldInst [⟨tx.id,.split⟩]))⟩
      have afterRelated : Related (edited actual core) after := insert_related_of_splice (edited actual created)
        createdAbstract createdRelated core oldInst gap [⟨tx.id,.split⟩] text oldText splice
        (by change gap ≤ (storedItems created oldInst).length
            rw [oldItems]
            exact contents.2.1) frame registration
        (canonical_next_unique network plainReach version closed pre suffix tx position actual replayed core operation)
        supported apart afterSource afterMat
      have insertion := insertionGap_actual actual abstract related oldInst text found origin present
      have fstOrigin : (NotionCorePhysicalReplay.originAddress oldInst origin).1 = oldInst := by cases origin <;> rfl
      refine ⟨core,after,operation,?_,afterRelated⟩
      rw [show abstract = ⟨abstract.document,abstract.texts⟩ from rfl,coreBatch_components,document,docBatch]
      simp only [textBatch,NotionCoreMachineCommands.commands,payload,List.map_cons,List.map_nil,
        NotionCoreSourceDocument.Command.semantic,coreTexts,missing,Option.isSome_none,Bool.false_eq_true,
        ↓reduceIte,insertPhysical,fstOrigin,putText,if_neg different,found,insertion,
        Bind.bind,Option.bind,pure,after,createdAbstract,gap,oldInst,newInst,itemSlots,
        NotionCorePhysicalReplay.atom,NotionCoreSource.Atom.slot,NotionCoreSpec.boundary,
        NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId,NotionCorePhysicalReplay.markerKey]

#print axioms canonical_insert_coreStep
#print axioms canonical_create_coreStep
#print axioms canonical_merge_coreStep
#print axioms canonical_bootstrap_coreBatch
#print axioms canonical_split_coreBatch

end Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
