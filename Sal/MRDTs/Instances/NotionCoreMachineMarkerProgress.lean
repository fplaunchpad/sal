import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate

/-! Actual marker integration reaches a partitioned pre-tree-split stage and
then passes recursive split search and endpoint checks. Ownership restoration
through the following detach/move phase is a separate atomic obligation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (boundary)
open NotionCoreMachine
open NotionCoreMachinePartition
open NotionCoreMachinePartitionUpdates
open NotionCoreForestRefs (ownedRefs)
open NotionCorePayload (BlockKey Transaction)
open NotionRunAllocation (Id Session)

structure MarkerStage (state : State) (marker : Address) : Prop where
  partitioned : Partitioned state
  unique : ∀ inst, ((physical state inst).map Atom.address).Nodup
  present : boundary marker ∈ physical state marker.1
  fresh : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker

theorem ref_start_present (state : State) (partitioned : Partitioned state)
    (owned : Nat × NotionCoreSliceForest.Ref) (member : owned ∈ ownedRefs state.forest) :
    owned.2.start ∈ (physical state owned.2.start.1).map Atom.address := by
  obtain ⟨before,cell,after,physicalEq,equal⟩ := ref_factor state partitioned owned member
  rw [physicalEq, equal]
  simp [NotionCorePartition.flatten, NotionCorePartition.Cell.physical, boundary]

/-- Include unallocated numeric keys: their actual default table has only
virtual START. Allocated keys are traced to typed instances in accepted replay. -/
theorem canonical_physical_unique_all (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ suffix)
    (state : State) (accepted : replay {} pre = some state) :
    ∀ key, ((physical state key).map Atom.address).Nodup := by
  intro key
  by_cases existsInstance : ∃ entry ∈ state.instances, entry.1 = key
  · obtain ⟨entry,member,equal⟩ := existsInstance
    have stored : key ∈ NotionCoreMachineCreators.instanceKeys state :=
      List.mem_map.mpr ⟨entry,member,equal⟩
    obtain ⟨tx,inPre,inst,used,encoded⟩ :=
      NotionCoreMachineCreators.replay_instance_used pre state accepted key stored
    rw [encoded]
    exact NotionCoreMachineTableGraph.canonical_physical_unique
      network reachable peer pre suffix position state accepted inst
  · have absent : state.instances.find? (fun entry => entry.1 == key) = none := by
      apply List.find?_eq_none.mpr
      intro entry member selected
      exact existsInstance ⟨entry,member,by simpa using selected⟩
    simp [physical,getInstance,absent,traversal,NotionCorePhysicalReplay.physical,
      NotionCorePhysicalReplay.start]

/-- The raw marker splice preserves the old intervals and makes the new
marker a physical interior point, before the tree algorithm adds its boundary. -/
theorem integrated_marker_stage (state : State) (inst : BlockKey) (id : Id)
    (origin : NotionCoreOriginTree.Origin) (rows : NotionCoreParentMap.Table)
    (prior : Partitioned state)
    (unique : ∀ key, ((physical state key).map Atom.address).Nodup)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = blockName inst)
    (originPresent : NotionCorePhysicalReplay.originAddress (blockName inst) origin ∈
      (physical state (blockName inst)).map Atom.address)
    (fresh : NotionCorePhysicalReplay.address (blockName inst) id ∉
      (physical state (blockName inst)).map Atom.address)
    (physicalEq : physical (putInstance state (blockName inst)
        {getInstance state (blockName inst) with rows := rows}) (blockName inst) =
      NotionCorePartition.spliceAfterBy Atom.address
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        [boundary (NotionCorePhysicalReplay.address (blockName inst) id)]
        (physical state (blockName inst))) :
    MarkerStage (putInstance state (blockName inst)
      {getInstance state (blockName inst) with rows := rows})
      (NotionCorePhysicalReplay.address (blockName inst) id) := by
  let key := blockName inst
  let marker := NotionCorePhysicalReplay.address key id
  let updated := putInstance state key {getInstance state key with rows := rows}
  have forestFrame : updated.forest = state.forest := by unfold updated putInstance; split <;> rfl
  have otherFrame : ∀ other, other ≠ key → physical updated other = physical state other := by
    intro other distinct
    simp [updated, physical, NotionCoreMachineTables.getInstance_put, distinct]
  have part : Partitioned updated := splice_partitioned state updated key
    (NotionCorePhysicalReplay.originAddress key origin) [boundary marker] prior forestFrame
    (fun other => putInstance_exists_iff state key other _ existsInstance)
    existsInstance (unique key) originPresent physicalEq otherFrame
  have apart : List.Disjoint ((physical state key).map Atom.address) [marker] :=
    List.disjoint_left.mpr (by intro old member selected; simp only [List.mem_singleton] at selected; subst old; exact fresh member)
  refine ⟨part, ?_, ?_, ?_⟩
  · intro other
    by_cases selected : other = key
    · subst other
      rw [physicalEq]
      exact NotionCorePartition.splice_nodup Atom.address _ [boundary marker] _ (unique key)
        (by simp) (by simpa [boundary] using apart)
    · change ((physical updated other).map Atom.address).Nodup
      rw [otherFrame other selected]
      exact unique other
  · change boundary marker ∈ physical updated key
    rw [physicalEq]
    simp [NotionCorePartition.spliceAfterBy,marker,key]
  · intro owned member equal
    have present := ref_start_present state prior owned (forestFrame ▸ member)
    rw [equal] at present
    exact fresh present

/-- Integration's successful row result and physical correspondence imply
success of the actual marker operation, including both recursive search and
its final endpoint validation. No marker-operation acceptance is assumed. -/
theorem marker_operation_progress (state : State) (block inst : BlockKey) (id : Id)
    (origin : NotionCoreOriginTree.Origin) (rows : NotionCoreParentMap.Table)
    (integrated : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ = some rows)
    (stage : MarkerStage (putInstance state (blockName inst)
      {getInstance state (blockName inst) with rows := rows})
      (NotionCorePhysicalReplay.address (blockName inst) id)) :
    ∃ next, applyOperation state (.marker block inst id origin) = some next := by
  let updated := putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) id
  have existsInstance : ∃ entry ∈ updated.instances, entry.1 = marker.1 := by
    by_cases priorExists : state.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ state.instances, entry.1 = blockName inst := by simpa using priorExists
      exact (putInstance_exists_iff state (blockName inst) (blockName inst) _ old).mpr old
    · simp [updated,putInstance,priorExists,marker,NotionCorePhysicalReplay.address]
  have markerPresent : marker ∈ (physical updated marker.1).map Atom.address :=
    List.mem_map.mpr ⟨boundary marker,stage.present,rfl⟩
  obtain ⟨forest,divided,bounds⟩ := splitForest_partition_progress updated stage.partitioned stage.unique
    marker existsInstance markerPresent stage.fresh
  refine ⟨{updated with forest := forest},?_⟩
  simp only [applyOperation,integrated]
  change ((NotionCoreSliceForest.splitForest (physical updated) marker updated.forest).bind
    (fun newForest => if validForestBounds {updated with forest := newForest} then
      some {updated with forest := newForest} else none)) = some {updated with forest := forest}
  rw [divided]
  simp [bounds]

/-- The next canonical split supplies a fresh physical marker and an actual
origin, and its raw integration has the proved splice. These facts precede
the source tree phases and require only acceptance of the old prefix. -/
theorem canonical_marker_physical (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin) :
    ∃ rows, integrate (getInstance state (blockName inst)).rows ⟨⟨tx.id,.split⟩,origin⟩ = some rows ∧
      physical (putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows})
        (blockName inst) = NotionCorePartition.spliceAfterBy Atom.address
          (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
          [boundary (NotionCorePhysicalReplay.address (blockName inst) tx.id)] (physical state (blockName inst)) ∧
      NotionCorePhysicalReplay.address (blockName inst) tx.id ∉ (physical state (blockName inst)).map Atom.address ∧
      NotionCorePhysicalReplay.originAddress (blockName inst) origin ∈ (physical state (blockName inst)).map Atom.address := by
  let forest := NotionCoreMachineCanonicalForest.originForest state inst
  have edges := NotionCoreMachineCanonicalForest.canonical_forest
    network reachable peer pre (tx :: suffix) position state accepted inst
  have graph := NotionCoreMachineTableGraph.canonical_prefix_graph
    network reachable peer pre (tx :: suffix) position state accepted inst
  have birthRows : NotionCoreMachinePrefix.transactionRows tx inst (fun _ _ => false) =
      [⟨⟨tx.id,.split⟩,origin⟩] := by
    simp [NotionCoreMachinePrefix.transactionRows,NotionCorePayload.births,
      NotionCorePayload.operations,payload,NotionCorePayload.Operation.births]
  have apart := NotionCoreMachineCanonicalForest.canonical_births_apart
    network reachable peer pre suffix tx position state accepted inst (fun _ _ => false)
  rw [birthRows] at apart
  have fresh : tx.id ∉ (getInstance state (blockName inst)).rows.map (fun row => row.item.id) := by
    intro present
    exact List.disjoint_left.mp apart present (by simp)
  have ready := NotionCoreMachineCanonicalForest.canonical_ready
    network reachable peer pre suffix tx position state accepted inst (.node ⟨tx.id,.split⟩ .nil) rfl
  have ready' : NotionCoreOriginTree.Ready origin (.node ⟨tx.id,.split⟩ .nil) forest := by
    simpa [payload,NotionCorePayloadParents.payloadOrigin] using ready
  have present : NotionCorePhysicalReplay.Present origin forest := by
    cases origin with
    | start => trivial
    | item id =>
        apply NotionCoreMachineCanonicalForest.canonical_reference_in_forest
          network reachable peer pre suffix tx position state accepted inst id
        simp [payload,NotionCorePayloadNetwork.locatedReferences,NotionCorePayload.originReference]
  obtain ⟨rows,integrated,physicalEq⟩ := NotionCoreMachineSplice.integrate_marker_physical
    state (blockName inst) origin tx.id forest edges.1 graph.1 edges.2 fresh ready' present
  refine ⟨rows,integrated,physicalEq,?_,?_⟩
  · rw [NotionCoreMachineCanonicalForest.canonical_physical_forest
      network reachable peer pre (tx :: suffix) position state accepted inst]
    apply NotionCorePhysicalReplay.fresh_address
    intro member
    have old : tx.id ∈ (NotionCoreParentMap.forestRows .start forest).map (fun row => row.item.id) := by
      simpa only [NotionCoreParentCoupling.forestRows_ids] using member
    exact fresh ((edges.1.map (fun row => row.item.id)).mem_iff.mpr old)
  · rw [NotionCoreMachineCanonicalForest.canonical_physical_forest
      network reachable peer pre (tx :: suffix) position state accepted inst]
    exact NotionCorePhysicalReplay.origin_present_physical (blockName inst) origin forest present

/-- Canonical split execution reaches its checked marker phase through the
actual fresh create operation. Raw storage, uniqueness, marker freshness and
search progress are derived from the old accepted prefix; only its partition
is assumed. The final detach/move partition is a separate obligation. -/
theorem canonical_split_marker_phase (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin) :
    ∃ created rows,
      applyOperation state (.create (.issued tx.id) (some block)) = some created ∧
      integrate (getInstance created (blockName inst)).rows ⟨⟨tx.id,.split⟩,origin⟩ = some rows ∧
      MarkerStage (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows})
        (NotionCorePhysicalReplay.address (blockName inst) tx.id) ∧
      (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows}).forest =
        state.forest ++ [⟨blockName (.issued tx.id),
          NotionCoreSliceForest.freshTitle (blockName (.issued tx.id))⟩] ∧
      physical (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows}) (blockName (.issued tx.id)) =
        NotionCoreSliceForest.emptyPhysical (blockName (.issued tx.id)) ∧
      ∃ marked, applyOperation created (.marker block inst tx.id origin) = some marked := by
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable reachable
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
    network reachable peer pre suffix tx position state accepted
  have existsOld := NotionCoreMachineCreatorPresence.canonical_required_instance
    network reachable peer pre suffix tx position state accepted inst
    (by simp [payload, NotionCoreCreatorNetwork.requiredBlocks])
  have distinct : blockName inst ≠ blockName (.issued tx.id) := by
    obtain ⟨entry,member,equal⟩ := existsOld
    exact fun same => freshInstance entry member (equal.trans same)
  obtain ⟨created,createStep,createPart,emptyTarget,storage⟩ :=
    NotionCoreMachineCanonicalCreate.canonical_create_phase network reachable peer pre suffix tx
      position state accepted prior (some block)
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state created (.issued tx.id)
    (some block) freshInstance freshBlock createStep
  have sourceStorage : getInstance created (blockName inst) = getInstance state (blockName inst) := by
    simpa [distinct] using storage (blockName inst)
  have sourcePhysical : physical created (blockName inst) = physical state (blockName inst) := by
    simp only [physical,sourceStorage]
  have uniqueOld := canonical_physical_unique_all network payloadReach peer pre (tx :: suffix)
    position state accepted
  have uniqueCreated : ∀ key, ((physical created key).map Atom.address).Nodup := by
    intro key
    by_cases selected : key = blockName (.issued tx.id)
    · subst key
      rw [emptyTarget]
      simp [NotionCoreSliceForest.emptyPhysical]
    · have same : physical created key = physical state key := by
        simp only [physical,storage key,if_neg selected]
      rw [same]
      exact uniqueOld key
  have existsCreated : ∃ entry ∈ created.instances, entry.1 = blockName inst := by
    obtain ⟨entry,member,equal⟩ := existsOld
    exact ⟨entry,shape.1 ▸ List.mem_append_left _ member,equal⟩
  obtain ⟨rows,integrated,physicalEq,fresh,originPresent⟩ := canonical_marker_physical
    network payloadReach peer pre suffix tx position state accepted block inst origin payload
  have integratedCreated : integrate (getInstance created (blockName inst)).rows
      ⟨⟨tx.id,.split⟩,origin⟩ = some rows := by rw [sourceStorage]; exact integrated
  have physicalEqCreated : physical (putInstance created (blockName inst)
      {getInstance created (blockName inst) with rows := rows}) (blockName inst) =
      NotionCorePartition.spliceAfterBy Atom.address
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        [boundary (NotionCorePhysicalReplay.address (blockName inst) tx.id)]
        (physical created (blockName inst)) := by
    rw [sourcePhysical]
    simpa only [physical,NotionCoreMachineTables.getInstance_put,if_pos rfl,sourceStorage] using physicalEq
  have stage := integrated_marker_stage created inst tx.id origin rows createPart uniqueCreated existsCreated
    (sourcePhysical ▸ originPresent) (sourcePhysical ▸ fresh) physicalEqCreated
  refine ⟨created,rows,createStep,integratedCreated,stage,?_,?_,
    marker_operation_progress created block inst tx.id origin rows integratedCreated stage⟩
  · have frame : (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows}).forest = created.forest := by
      unfold putInstance; split <;> rfl
    exact frame.trans shape.2.1
  · have frame : physical (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows}) (blockName (.issued tx.id)) =
        physical created (blockName (.issued tx.id)) := by
      simp [physical,NotionCoreMachineTables.getInstance_put,Ne.symm distinct]
    exact frame.trans emptyTarget

private theorem splitForest_ids (physical : Nat → List Atom) (marker : Address)
    (forest result : NotionCoreSliceForest.Forest)
    (accepted : NotionCoreSliceForest.splitForest physical marker forest = some result) :
    result.map NotionCoreSliceForest.Block.id = forest.map NotionCoreSliceForest.Block.id := by
  induction forest generalizing result with
  | nil => simp [NotionCoreSliceForest.splitForest] at accepted
  | cons block rest ih =>
    cases selected : NotionCoreSliceForest.splitTree physical marker block.title with
    | some title =>
      simp only [NotionCoreSliceForest.splitForest,selected,Option.some.injEq] at accepted
      subst result
      rfl
    | none =>
      simp only [NotionCoreSliceForest.splitForest,selected,Option.map_eq_some_iff] at accepted
      obtain ⟨tail,split,equal⟩ := accepted
      subst result
      simp only [List.map_cons,ih tail split]

/-- Connect the structural atomic tree algorithm to the checked interpreter.
The marker stage derives the intermediate bounds check, and preservation of
forest block identities derives the move target check. -/
theorem split_transaction_of_atomic (state created : State) (tx : Transaction)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (rows : NotionCoreParentMap.Table) (forest : NotionCoreSliceForest.Forest)
    (payload : tx.payload = .split block inst origin)
    (createStep : applyOperation state (.create (.issued tx.id) (some block)) = some created)
    (integrated : integrate (getInstance created (blockName inst)).rows
      ⟨⟨tx.id,.split⟩,origin⟩ = some rows)
    (stage : MarkerStage (putInstance created (blockName inst)
      {getInstance created (blockName inst) with rows := rows})
      (NotionCorePhysicalReplay.address (blockName inst) tx.id))
    (shape : (putInstance created (blockName inst)
      {getInstance created (blockName inst) with rows := rows}).forest =
      state.forest ++ [⟨blockName (.issued tx.id),
        NotionCoreSliceForest.freshTitle (blockName (.issued tx.id))⟩])
    (atomic : NotionCoreSliceForest.atomicSplit
      (physical (putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows}))
      (NotionCorePhysicalReplay.address (blockName inst) tx.id)
      (blockName (.issued tx.id)) state.forest = some forest) :
    applyTransaction state tx = some
      {putInstance created (blockName inst)
        {getInstance created (blockName inst) with rows := rows} with forest := forest} := by
  let raw := putInstance created (blockName inst)
    {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let target := blockName (.issued tx.id)
  have treeStep : NotionCoreSliceForest.splitMove (physical raw) marker target raw.forest = some forest := by
    rw [shape]
    exact atomic
  obtain ⟨marked,markerStep⟩ := marker_operation_progress created block inst tx.id origin rows integrated stage
  cases divided : NotionCoreSliceForest.splitForest (physical raw) marker raw.forest with
  | none => simp [NotionCoreSliceForest.splitMove,divided] at treeStep
  | some split =>
    have targetExists : split.any (fun b => b.id == target) = true := by
      have ids := splitForest_ids (physical raw) marker raw.forest split divided
      apply List.any_eq_true.mpr
      have member : target ∈ split.map NotionCoreSliceForest.Block.id := by
        rw [ids,shape]
        simp [target]
      obtain ⟨found,inForest,equal⟩ := List.mem_map.mp member
      exact ⟨found,inForest,by simpa using equal⟩
    have markerExact : applyOperation created (.marker block inst tx.id origin) =
        some {raw with forest := split} := by
      simp only [applyOperation,integrated] at markerStep ⊢
      change ((NotionCoreSliceForest.splitForest (physical raw) marker raw.forest).bind
        (fun newForest => if validForestBounds {raw with forest := newForest} then
          some {raw with forest := newForest} else none)) = some marked at markerStep
      change ((NotionCoreSliceForest.splitForest (physical raw) marker raw.forest).bind
        (fun newForest => if validForestBounds {raw with forest := newForest} then
          some {raw with forest := newForest} else none)) = some {raw with forest := split}
      rw [divided] at markerStep ⊢
      change (if validForestBounds {raw with forest := split} then
        some {raw with forest := split} else none) = some marked at markerStep
      have bounds : validForestBounds {raw with forest := split} = true := by
        split at markerStep
        · assumption
        · contradiction
      simp [bounds]
    cases detached : NotionCoreSliceForest.detachForest marker split with
    | none => simp [NotionCoreSliceForest.splitMove,divided,detached] at treeStep
    | some pair =>
      have finalEq : NotionCoreSliceForest.appendToBlock target pair.2 pair.1 = forest := by
        simpa [NotionCoreSliceForest.splitMove,divided,detached] using treeStep
      have moveStep : applyOperation {raw with forest := split} (.moveInto block inst tx.id (.issued tx.id)) =
          some {raw with forest := forest} := by
        simp [applyOperation,targetExists,detached,finalEq,target,marker]
      change applyTransaction state tx = some {raw with forest := forest}
      simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,createStep,markerExact,moveStep]

/-- A literal event-marker boundary cannot occur in a START-only destination. -/
theorem marker_instance_ne_empty (state : State) (inst target : Nat) (id : Id)
    (present : boundary (NotionCorePhysicalReplay.address inst id) ∈ physical state inst)
    (empty : physical state target = NotionCoreSliceForest.emptyPhysical target) : inst ≠ target := by
  intro equal
  subst inst
  rw [empty] at present
  simp [NotionCoreSliceForest.emptyPhysical,boundary,NotionCorePhysicalReplay.address,
    NotionCorePhysicalReplay.localId] at present

/-- A fresh destination has no old owner cell in the marker's instance. Its
new empty title belongs to its distinct own instance and is retained there. -/
theorem fresh_target_ref_owner (forest : NotionCoreSliceForest.Forest) (target inst : Nat)
    (fresh : target ∉ forest.map NotionCoreSliceForest.Block.id) (distinct : inst ≠ target) :
    ∀ owned ∈ ownedRefs (forest ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩]),
      owned.2.start.1 = inst → owned.1 ≠ target := by
  intro owned member sameInstance sameOwner
  rw [NotionCoreForestRefs.ownedRefs_create] at member
  rcases List.mem_append.mp member with old | newest
  · obtain ⟨block,member,inside⟩ := List.mem_flatMap.mp old
    obtain ⟨ref,_,equal⟩ := List.mem_map.mp inside
    apply fresh
    have owner : block.id = target := (congrArg Prod.fst equal).trans sameOwner
    exact List.mem_map.mpr ⟨block,member,owner⟩
  · have equal := List.mem_singleton.mp newest
    subst owned
    exact distinct sameInstance.symm

#print axioms fresh_target_ref_owner

#print axioms split_transaction_of_atomic

#print axioms canonical_split_marker_phase

#print axioms canonical_physical_unique_all
#print axioms integrated_marker_stage
#print axioms marker_operation_progress
#print axioms canonical_marker_physical
end Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress
