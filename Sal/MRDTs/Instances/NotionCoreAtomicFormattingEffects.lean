import Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest
import Sal.MRDTs.Instances.NotionCoreMachineFreshText
import Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress
import Sal.MRDTs.Instances.NotionCoreMachineErase
import Sal.MRDTs.Instances.NotionCoreMachineDocumentBootstrap

/-! Structural effects of actual core edits used by the repaired rich interpreter.
The insertion equations below consume honest canonical replay prefixes; their
physical splice is derived by the existing core interpreter proof. START is a
virtual atom and is excluded from the retained item coordinates. -/
namespace Sal.MRDTs.Instances.NotionCoreAtomicFormattingEffects
open NotionCoreMachine
open NotionCorePayload (BlockKey Transaction)
open NotionCoreOriginTree (Item Origin)
open NotionRunAllocation (Id Run)

abbrev storedItems (state : State) (inst : Nat) : List Item :=
  traversal (getInstance state inst).rows.length (getInstance state inst).rows .start

def originGap (items : List Item) : Origin → Nat
  | .start => 0
  | .item id => (items.map Item.id).idxOf id + 1

theorem storedItems_forest (state : NotionCoreAtomicFormattingMachine.State) (inst : Nat) :
    NotionCoreOriginTree.preorder (NotionCoreAtomicFormattingMachine.instanceForest state inst) = storedItems state.core inst :=
  NotionCoreAtomicFormattingMachine.instanceForest_traversal state inst

theorem atom_injective (inst : Nat) : Function.Injective (NotionCorePhysicalReplay.atom inst) := by
  intro a b equal
  have ids := NotionCorePhysicalReplay.address_injective inst
    (congrArg NotionCoreSource.Atom.address equal)
  cases a with
  | mk ai ak =>
    cases b with
    | mk bi bk =>
      simp only at ids
      subst bi
      cases ak <;> cases bk <;> simp_all [NotionCorePhysicalReplay.atom]

theorem physical_injective (inst : Nat) : Function.Injective (NotionCorePhysicalReplay.physical inst) := by
  intro a b equal
  have maps := List.cons.inj equal |>.2
  exact List.map_injective_iff.mpr (atom_injective inst) maps

/-- Exact retained gap for the executable augmented splice, with START removed. -/
theorem physical_splice_gap (inst : Nat) (items fresh : List Item) (origin : Origin) :
    NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
      (NotionCorePhysicalReplay.originAddress inst origin)
      (fresh.map (NotionCorePhysicalReplay.atom inst))
      (NotionCorePhysicalReplay.physical inst items) =
    NotionCorePhysicalReplay.physical inst
      (items.take (originGap items origin) ++ fresh ++ items.drop (originGap items origin)) := by
  cases origin with
  | start => simp [NotionCorePartition.spliceAfterBy, NotionCorePhysicalReplay.originAddress,
      NotionCorePhysicalReplay.physical, originGap]
  | item id =>
    simp only [NotionCorePartition.spliceAfterBy, NotionCorePhysicalReplay.originAddress,
      NotionCorePhysicalReplay.physical_origin_index]
    simp [NotionCorePhysicalReplay.physical, originGap, List.map_take, List.map_drop,
      List.append_assoc]

theorem originGap_le (state : State) (inst : Nat) (origin : Origin)
    (present : NotionCorePhysicalReplay.originAddress inst origin ∈
      (physical state inst).map NotionCoreSource.Atom.address) :
    originGap (storedItems state inst) origin ≤ (storedItems state inst).length := by
  cases origin with
  | start => simp [originGap]
  | item id =>
    have member : id ∈ (storedItems state inst).map Item.id := by
      simp only [physical, NotionCorePhysicalReplay.physical, List.map_cons,
        NotionCorePhysicalReplay.start_address, List.mem_cons, List.mem_map] at present
      rcases present with impossible | ⟨item, member, equal⟩
      · exact False.elim (NotionCorePhysicalReplay.address_ne_start inst id impossible)
      · obtain ⟨original, originalMember, rfl⟩ := member
        exact List.mem_map.mpr ⟨original, originalMember,
          NotionCorePhysicalReplay.address_injective inst equal⟩
    have bound := List.idxOf_lt_length_iff.mpr member
    simp only [originGap, List.length_map] at *
    omega

/-- Honest next text insertion is exactly a retained-list splice at its actual
origin gap. Fresh flags are derived from reference causality, not assumed. -/
theorem canonical_insert_items (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network)
    (version : List Run) (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state)
    (block inst : BlockKey) (origin : Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (nonempty : atoms ≠ [])
    (step : applyTransaction state tx = some result) :
    storedItems result (blockName inst) =
      (storedItems state (blockName inst)).take (originGap (storedItems state (blockName inst)) origin) ++
      NotionCorePayload.textItems tx.id atoms (fun _ => false) ++
      (storedItems state (blockName inst)).drop (originGap (storedItems state (blockName inst)) origin) ∧
    originGap (storedItems state (blockName inst)) origin ≤ (storedItems state (blockName inst)).length := by
  obtain ⟨next, operation, equation⟩ :=
    NotionCoreMachineCanonicalForest.canonical_insert_physical_version network reachable
      version closed pre suffix tx position state accepted block inst origin atoms payload nonempty
  have nextIs : next = result := by
    have same : applyOperation state (.insert block inst tx.id origin atoms) = some result := by
      simpa [applyTransaction, NotionCorePayload.operations, payload, applyOperations] using step
    exact Option.some.inj (operation.symm.trans same)
  subst next
  rw [NotionCoreMachineFreshText.version_textItems_pending_false network reachable version
    pre suffix tx position state accepted inst atoms] at equation
  change NotionCorePhysicalReplay.physical _ _ = _ at equation
  unfold physical at equation
  rw [physical_splice_gap] at equation
  refine ⟨physical_injective _ equation, ?_⟩
  exact originGap_le state (blockName inst) origin
    (NotionCoreMachineCanonicalForest.canonical_insert_origin_present_version network reachable
      version closed pre suffix tx position state accepted block inst origin atoms payload)

/-- Creating an empty instance changes registration, but does not change any
retained instance contents (a missing instance already reads as empty). -/
theorem create_storage (state result : State) (block : BlockKey) (after : Option BlockKey)
    (step : applyOperation state (.create block after) = some result) (key : Nat) :
    getInstance result key = getInstance state key := by
  simp only [applyOperation] at step
  split at step
  · simp only [Option.some.injEq] at step; subst result; rfl
  · simp only [Option.some.injEq] at step; subst result
    change getInstance (if state.instances.any (fun pair => pair.1 == blockName block)
      then state else putInstance state (blockName block) {}) key = _
    split
    · rfl
    · rename_i absent
      rw [NotionCoreMachineTables.getInstance_put]
      split
      · rename_i same
        subst key
        have missing : state.instances.find? (fun pair => pair.1 == blockName block) = none :=
          List.find?_eq_none.mpr (by
            intro pair member selected
            exact absent (List.any_eq_true.mpr ⟨pair,member,selected⟩))
        simp [getInstance, missing]
      · rfl

theorem move_storage (state result : State) (block inst : BlockKey)
    (marker : Id) (target : BlockKey)
    (step : applyOperation state (.moveInto block inst marker target) = some result) (key : Nat) :
    getInstance result key = getInstance state key := by
  simp only [applyOperation] at step
  split at step
  · contradiction
  · cases selected : NotionCoreSliceForest.detachForest
      (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
    | none => simp [selected] at step
    | some pair => simp [selected] at step; subst result; rfl

theorem marker_storage (state result : State) (block inst : BlockKey)
    (id : Id) (origin : Origin) (rows : NotionCoreParentMap.Table)
    (integrated : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ = some rows)
    (step : applyOperation state (.marker block inst id origin) = some result) (key : Nat) :
    getInstance result key = getInstance
      (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}) key := by
  simp only [applyOperation, integrated] at step
  dsimp only [Bind.bind, Option.bind] at step
  split at step
  · contradiction
  · dsimp only at step
    split at step
    · simp at step; subst result; rfl
    · contradiction

/-- The whole split transaction has exactly the marker integration's storage
effect; create and slice movement preserve the previous retained instances. -/
theorem split_storage (state result : State) (tx : Transaction) (block inst : BlockKey)
    (origin : Origin) (rows : NotionCoreParentMap.Table)
    (payload : tx.payload = .split block inst origin)
    (integrated : integrate (getInstance state (blockName inst)).rows ⟨⟨tx.id,.split⟩,origin⟩ = some rows)
    (step : applyTransaction state tx = some result) (key : Nat) :
    getInstance result key = getInstance
      (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}) key := by
  have steps : applyOperations state [.create (.issued tx.id) (some block),
      .marker block inst tx.id origin, .moveInto block inst tx.id (.issued tx.id)] = some result := by
    simpa [applyTransaction, NotionCorePayload.operations, payload] using step
  cases createdStep : applyOperation state (.create (.issued tx.id) (some block)) with
  | none => simp [applyOperations, createdStep] at steps
  | some created =>
    have frame := create_storage state created (.issued tx.id) (some block) createdStep
    have integrated' : integrate (getInstance created (blockName inst)).rows
        ⟨⟨tx.id,.split⟩,origin⟩ = some rows := by rw [frame]; exact integrated
    cases markerStep : applyOperation created (.marker block inst tx.id origin) with
    | none => simp [applyOperations, createdStep, markerStep] at steps
    | some marked =>
      have moved : applyOperation marked (.moveInto block inst tx.id (.issued tx.id)) = some result := by
        simpa [applyOperations, createdStep, markerStep] using steps
      rw [move_storage marked result block inst tx.id (.issued tx.id) moved key,
        marker_storage created marked block inst tx.id origin rows integrated' markerStep key]
      simp only [NotionCoreMachineTables.getInstance_put, frame]

theorem canonical_split_items (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state)
    (block inst : BlockKey) (origin : Origin) (payload : tx.payload = .split block inst origin)
    (step : applyTransaction state tx = some result) :
    storedItems result (blockName inst) =
      (storedItems state (blockName inst)).take (originGap (storedItems state (blockName inst)) origin) ++
      [⟨tx.id,.split⟩] ++
      (storedItems state (blockName inst)).drop (originGap (storedItems state (blockName inst)) origin) ∧
    originGap (storedItems state (blockName inst)) origin ≤ (storedItems state (blockName inst)).length ∧
    ∀ key, key ≠ blockName inst → storedItems result key = storedItems state key := by
  obtain ⟨rows, integrated, equation, _, present⟩ :=
    NotionCoreMachineMarkerProgress.canonical_marker_physical_version network reachable
      version closed pre suffix tx position state accepted block inst origin payload
  have storage := split_storage state result tx block inst origin rows payload integrated step
  have actual : physical result (blockName inst) = physical
      (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows})
      (blockName inst) := by simp only [physical, storage]
  rw [equation] at actual
  have marker : [NotionCorePartition.boundary (NotionCorePhysicalReplay.address (blockName inst) tx.id)] =
      [⟨tx.id,.split⟩].map (NotionCorePhysicalReplay.atom (blockName inst)) := rfl
  rw [marker] at actual
  unfold physical at actual
  rw [physical_splice_gap] at actual
  refine ⟨physical_injective _ actual, originGap_le state _ origin present, ?_⟩
  intro key different
  simp only [storedItems, storage, NotionCoreMachineTables.getInstance_put, if_neg different]

/-- Corrected merge only changes the slice forest. All physical instances,
including tombstones and markers, remain identical. -/
theorem merge_storage (state result : State) (source inst : BlockKey) (stop : Option Id)
    (step : applyOperation state (.merge source inst stop) = some result) (key : Nat) :
    getInstance result key = getInstance state key := by
  simp only [applyOperation, Option.some.injEq] at step
  subst result
  rfl

theorem erase_items (state result : State) (block inst : BlockKey) (targets : List Id)
    (step : applyOperation state (.erase block inst targets) = some result) (key : Nat) :
    storedItems result key = if key = blockName inst then
      (storedItems state key).map (NotionCoreParentErase.eraseItem targets) else storedItems state key := by
  simp only [applyOperation, Option.some.injEq] at step
  subst result
  simp only [storedItems, NotionCoreMachineTables.getInstance_put]
  split
  · rename_i same
    subst key
    simp only [NotionCoreParentErase.erase, List.length_map, traversal_correct]
    exact NotionCoreMachineErase.traverse_erase targets _ _ _
  · rfl

theorem erase_item_ids (state result : State) (block inst : BlockKey) (targets : List Id)
    (step : applyOperation state (.erase block inst targets) = some result) (key : Nat) :
    (storedItems result key).map Item.id = (storedItems state key).map Item.id := by
  rw [erase_items state result block inst targets step key]
  split <;> simp

theorem insert_frame (state result : State) (block inst : BlockKey) (first : Id)
    (origin : Origin) (atoms : List Nat)
    (step : applyOperation state (.insert block inst first origin atoms) = some result)
    (key : Nat) (different : key ≠ blockName inst) :
    getInstance result key = getInstance state key := by
  simp only [applyOperation] at step
  cases integrated : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
  | none => simp [integrated] at step
  | some rows =>
    simp [integrated] at step
    subst result
    simp [NotionCoreMachineTables.getInstance_put, different]

theorem canonical_insert_frame (state result : State) (tx : Transaction)
    (block inst : BlockKey) (origin : Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms)
    (step : applyTransaction state tx = some result) (key : Nat) (different : key ≠ blockName inst) :
    storedItems result key = storedItems state key := by
  have operation : applyOperation state (.insert block inst tx.id origin atoms) = some result := by
    simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
  simp only [storedItems, insert_frame state result block inst tx.id origin atoms operation key different]

theorem create_items (state result : State) (tx : Transaction) (after : Option BlockKey)
    (payload : tx.payload = .create after) (step : applyTransaction state tx = some result) (key : Nat) :
    storedItems result key = storedItems state key := by
  have operation : applyOperation state (.create (.issued tx.id) after) = some result := by
    simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
  simp only [storedItems, create_storage state result (.issued tx.id) after operation key]

theorem merge_items (state result : State) (tx : Transaction) (source inst : BlockKey) (stop : Option Id)
    (payload : tx.payload = .merge source inst stop) (step : applyTransaction state tx = some result)
    (key : Nat) : storedItems result key = storedItems state key := by
  have operation : applyOperation state (.merge source inst stop) = some result := by
    simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
  simp only [storedItems, merge_storage state result source inst stop operation key]

theorem erase_groups_ids (state result : State) (block : BlockKey) (groups : List (BlockKey × List Id))
    (step : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result)
    (key : Nat) : (storedItems result key).map Item.id = (storedItems state key).map Item.id := by
  induction groups generalizing state with
  | nil => simp [applyOperations] at step; subst result; rfl
  | cons group rest ih =>
    cases first : applyOperation state (.erase block group.1 group.2) with
    | none => simp [applyOperations,first] at step
    | some middle =>
      have later : applyOperations middle (rest.map fun group => .erase block group.1 group.2) = some result := by
        simpa [applyOperations,first] using step
      exact (ih middle later).trans (erase_item_ids state middle block group.1 group.2 first key)

theorem erase_transaction_ids (state result : State) (tx : Transaction)
    (block : BlockKey) (groups : List (BlockKey × List Id))
    (payload : tx.payload = .erase block groups) (step : applyTransaction state tx = some result)
    (key : Nat) : (storedItems result key).map Item.id = (storedItems state key).map Item.id := by
  apply erase_groups_ids state result block groups _ key
  simpa [applyTransaction,NotionCorePayload.operations,payload] using step

theorem eraseItem_append (first later : List Id) (item : Item) :
    NotionCoreParentErase.eraseItem later (NotionCoreParentErase.eraseItem first item) =
      NotionCoreParentErase.eraseItem (first ++ later) item := by
  cases item with
  | mk id kind => cases kind <;> simp [NotionCoreParentErase.eraseItem, Bool.or_assoc]

theorem erase_groups_items (state result : State) (block : BlockKey) (groups : List (BlockKey × List Id))
    (step : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result)
    (query : BlockKey) :
    storedItems result (blockName query) = (storedItems state (blockName query)).map
      (NotionCoreParentErase.eraseItem (groups.flatMap fun group => if group.1 = query then group.2 else [])) := by
  induction groups generalizing state with
  | nil =>
    simp only [List.map_nil,applyOperations,Option.some.injEq] at step
    subst result
    simp only [List.flatMap_nil]
    exact (List.map_id _).symm.trans (by
      congr 1
      funext item
      cases item with
      | mk id kind => cases kind <;> simp [NotionCoreParentErase.eraseItem])
  | cons group rest ih =>
    cases first : applyOperation state (.erase block group.1 group.2) with
    | none => simp [applyOperations,first] at step
    | some middle =>
      have later : applyOperations middle (rest.map fun group => .erase block group.1 group.2) = some result := by
        simpa [applyOperations,first] using step
      rw [ih middle later,erase_items state middle block group.1 group.2 first]
      by_cases same : group.1 = query
      · subst query
        simp only [ite_true,List.map_map,List.flatMap_cons]
        apply List.map_congr_left
        intro item _
        exact eraseItem_append _ _ item
      · have different : blockName query ≠ blockName group.1 := by
          intro equal
          exact same (blockName_injective equal).symm
        simp only [if_neg different,List.flatMap_cons,if_neg same,List.nil_append]

theorem erase_transaction_items (state result : State) (tx : Transaction)
    (block : BlockKey) (groups : List (BlockKey × List Id))
    (payload : tx.payload = .erase block groups) (step : applyTransaction state tx = some result)
    (query : BlockKey) :
    storedItems result (blockName query) = (storedItems state (blockName query)).map
      (NotionCoreParentErase.eraseItem (groups.flatMap fun group => if group.1 = query then group.2 else [])) := by
  apply erase_groups_items state result block groups _ query
  simpa [applyTransaction,NotionCorePayload.operations,payload] using step

/-- Empty text insertion also has the same splice equation. Its accepted raw
dispatch may register a missing table, but every retained item remains the same. -/
theorem canonical_insert_items_all (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state)
    (block inst : BlockKey) (origin : Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms)
    (step : applyTransaction state tx = some result) :
    storedItems result (blockName inst) =
      (storedItems state (blockName inst)).take (originGap (storedItems state (blockName inst)) origin) ++
      NotionCorePayload.textItems tx.id atoms (fun _ => false) ++
      (storedItems state (blockName inst)).drop (originGap (storedItems state (blockName inst)) origin) ∧
    originGap (storedItems state (blockName inst)) origin ≤ (storedItems state (blockName inst)).length := by
  by_cases empty : atoms = []
  · subst atoms
    have operation : applyOperation state (.insert block inst tx.id origin []) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
    simp [applyOperation,NotionCorePayload.textItems,NotionCoreParentMap.runRows,integrateRows] at operation
    subst result
    refine ⟨?_, ?_⟩
    · simp [storedItems,NotionCoreMachineTables.getInstance_put,NotionCorePayload.textItems]
    · apply originGap_le state _ origin
      exact NotionCoreMachineCanonicalForest.canonical_insert_origin_present_version network reachable
        version closed pre suffix tx position state accepted block inst origin [] payload
  · exact canonical_insert_items network reachable version closed pre suffix tx position state result
      accepted block inst origin atoms payload empty step

/-- The canonical create request really registers a fresh empty instance.
No assumed freshness or empty-instance output enters the conclusion. -/
theorem canonical_create_empty (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state) (after : Option BlockKey)
    (payload : tx.payload = .create after) (step : applyTransaction state tx = some result) :
    result.instances = state.instances ++ [(blockName (.issued tx.id),({} : Instance))] ∧
    storedItems result (blockName (.issued tx.id)) = [] := by
  obtain ⟨fresh, freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network reachable version closed pre suffix tx position state accepted
  have operation : applyOperation state (.create (.issued tx.id) after) = some result := by
    simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
  refine ⟨(NotionCoreMachineCanonicalCreate.fresh_create_shape state result (.issued tx.id)
    after fresh freshBlock operation).1, ?_⟩
  have empty := NotionCoreMachineCanonicalCreate.fresh_create_storage state result (.issued tx.id)
    after fresh freshBlock operation (blockName (.issued tx.id))
  simp [storedItems, empty, traversal]

theorem canonical_split_empty_target (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state)
    (block inst : BlockKey) (origin : Origin) (payload : tx.payload = .split block inst origin)
    (step : applyTransaction state tx = some result) :
    storedItems result (blockName (.issued tx.id)) = [] := by
  obtain ⟨fresh, _⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network reachable version closed pre suffix tx position state accepted
  obtain ⟨entry, member, same⟩ := NotionCoreMachineCreatorPresence.canonical_required_instance_version
    network reachable version closed pre suffix tx position state accepted inst
    (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  have different : blockName (.issued tx.id) ≠ blockName inst := by
    intro equal
    exact fresh entry member (same.trans equal.symm)
  have frame := (canonical_split_items network (NotionCoreCreatorNetwork.payload_reachable reachable)
    version closed pre suffix tx position state result accepted block inst origin payload step).2.2
      (blockName (.issued tx.id)) different
  rw [frame]
  have missing : state.instances.find? (fun pair => pair.1 == blockName (.issued tx.id)) = none :=
    List.find?_eq_none.mpr (by
      intro pair member selected
      exact fresh pair member (by simpa using selected))
  simp [storedItems,getInstance,missing,traversal]

/-- Bootstrap's retained text equation in an arbitrary earlier context with a
fresh initial instance. In particular, the whole previous state may be nonempty. -/
theorem fresh_bootstrap_items (state result : State) (tx : Transaction) (atoms : List Nat)
    (payload : tx.payload = .bootstrap atoms)
    (fresh : ∀ entry ∈ state.instances, entry.1 ≠ blockName .initial)
    (freshBlock : FreshBlock state (blockName .initial))
    (step : applyTransaction state tx = some result) :
    storedItems result 0 = NotionCorePayload.textItems tx.id atoms (fun _ => false) ∧
    ∀ key, key ≠ 0 → storedItems result key = storedItems state key := by
  have steps : applyOperations state [.create .initial none,
      .insert .initial .initial tx.id .start atoms] = some result := by
    simpa [applyTransaction,NotionCorePayload.operations,payload] using step
  cases first : applyOperation state (.create .initial none) with
  | none => simp [applyOperations,first] at steps
  | some created =>
    have empty : getInstance created 0 = {} := by
      simpa [blockName] using NotionCoreMachineCanonicalCreate.fresh_create_storage
        state created .initial none fresh freshBlock first 0
    have insertStep : applyOperation created (.insert .initial .initial tx.id .start atoms) = some result := by
      simpa [applyOperations,first] using steps
    obtain ⟨next,actual,equation⟩ := NotionCoreMachineDocumentBootstrap.empty_instance_insert
      created .initial tx.id atoms empty
    have same : next = result := Option.some.inj (actual.symm.trans insertStep)
    subst next
    change NotionCorePhysicalReplay.physical 0 _ = _ at equation
    unfold physical at equation
    change NotionCorePhysicalReplay.physical 0 (storedItems result 0) =
      NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
        (NotionCorePhysicalReplay.originAddress 0 .start)
        ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
          (NotionCorePhysicalReplay.atom 0))
        (NotionCorePhysicalReplay.physical 0 (storedItems created 0)) at equation
    rw [physical_splice_gap] at equation
    have itemsEq := physical_injective 0 equation
    have createdItems : storedItems created 0 = [] := by simp [storedItems,empty,traversal]
    refine ⟨?_,?_⟩
    · simpa [createdItems,originGap] using itemsEq
    · intro key different
      simp only [storedItems,insert_frame created result .initial .initial tx.id .start atoms insertStep key
        (by simpa [blockName] using different),create_storage state created .initial none first key]

theorem canonical_bootstrap_items (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : State) (accepted : replay {} pre = some state) (atoms : List Nat)
    (payload : tx.payload = .bootstrap atoms) (step : applyTransaction state tx = some result) :
    storedItems result 0 = NotionCorePayload.textItems tx.id atoms (fun _ => false) ∧
    ∀ key, key ≠ 0 → storedItems result key = storedItems state key := by
  obtain ⟨fresh, freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh_version
    network reachable version closed pre suffix tx position atoms payload state accepted
  exact fresh_bootstrap_items state result tx atoms payload fresh freshBlock step

#print axioms canonical_insert_items
#print axioms canonical_split_items
#print axioms erase_transaction_ids
#print axioms canonical_create_empty
#print axioms canonical_split_empty_target

end Sal.MRDTs.Instances.NotionCoreAtomicFormattingEffects
