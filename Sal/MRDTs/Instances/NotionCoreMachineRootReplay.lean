import Sal.MRDTs.Instances.NotionCoreMachineCanonicalSplit
import Sal.MRDTs.Instances.NotionCoreRootCreators
import Sal.MRDTs.Instances.NotionCoreBootstrapProvenance

/-! Canonical replay with exact active-root provenance. Whole split changes
owners while retaining active instances; unused destination titles are excluded
from the active set. The archive root-provenance condition is separate from
mere creator-aware admission and is not source-client correspondence. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineRootReplay
open NotionCoreMachine
open NotionCoreMachineShape
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSliceForest (forestNodes)

private theorem insert_result (state result : State) (block inst : BlockKey)
    (id : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (accepted : applyOperation state (.insert block inst id origin atoms) = some result) :
    ∃ rows, result = putInstance state (blockName inst)
      {getInstance state (blockName inst) with rows := rows} := by
  cases integrated : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems id atoms
        (fun item => decide (item ∈ (getInstance state (blockName inst)).pending)))) with
  | none => simp [applyOperation,integrated] at accepted
  | some rows => exact ⟨rows,by simpa [applyOperation,integrated] using accepted.symm⟩

private theorem put_forest (state : State) (inst : Nat) (value : Instance) :
    (putInstance state inst value).forest = state.forest := by
  unfold putInstance
  split <;> rfl

/-- Actual successful insertion is a physical update of the selected active
instance; its forest and exact active set remain unchanged. -/
theorem insert_shape_active (state result : State) (block inst : BlockKey)
    (id : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (prior : ShapeInvariant state) (selected : ActiveInstance state (blockName inst))
    (accepted : applyOperation state (.insert block inst id origin atoms) = some result) :
    ShapeInvariant result ∧ ∀ name, ActiveInstance result name ↔ ActiveInstance state name := by
  obtain ⟨rows,rfl⟩ := insert_result state result block inst id origin atoms accepted
  refine ⟨put_active_preserves state (blockName inst) _ prior selected,?_⟩
  intro name
  simp only [ActiveInstance,put_forest]

/-- Erasure changes only text tombstones, so empty dead START titles stay
empty even without a live-instance assumption on the deletion payload. -/
theorem erase_shape_active (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (prior : ShapeInvariant state)
    (accepted : applyOperation state (.erase block inst targets) = some result) :
    ShapeInvariant result ∧ ∀ name, ActiveInstance result name ↔ ActiveInstance state name := by
  have frames := NotionCoreMachineErase.erase_physical state result block inst targets accepted
  constructor
  · refine ⟨?_,?_,?_⟩
    · simpa only [ShapeInvariant,shapeView,frames.1] using prior.1
    · simpa only [ShapeInvariant,shapeView,frames.1] using prior.2.1
    · intro dead member
      have oldMember : (dead,false) ∈ forestNodes state.forest := by
        simpa only [shapeView,frames.1] using member
      obtain ⟨form,empty,lives⟩ := prior.2.2 dead oldMember
      refine ⟨form,?_,fun live liveMember => lives live (by simpa only [shapeView,frames.1] using liveMember)⟩
      change physical result dead.start.1 = _
      change physical state dead.start.1 = _ at empty
      rw [frames.2.2 dead.start.1]
      split
      · rw [empty]
        simp [NotionCoreSliceForest.emptyPhysical,NotionCoreSource.eraseAtom,NotionCorePartition.boundary]
      · exact empty
  · intro name
    simp only [ActiveInstance,frames.1]

/-- Fresh ordinary creation adds exactly its own active instance. -/
theorem create_active_exact (state result : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : FreshBlock state (blockName block))
    (accepted : applyOperation state (.create block afterBlock) = some result) :
    ∀ name, ActiveInstance result name ↔ ActiveInstance state name ∨ name = blockName block := by
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state result block afterBlock
    freshInstance freshBlock accepted
  intro name
  simp only [ActiveInstance,shape.2.1,NotionCoreSliceForest.forestNodes_append,
    NotionCoreSliceForest.forestNodes_fresh,List.mem_append,List.mem_singleton,Prod.mk.injEq,and_true]
  constructor
  · rintro ⟨found,member,equal⟩
    rcases member with old | rfl
    · exact Or.inl ⟨found,old,equal⟩
    · exact Or.inr equal.symm
  · rintro (⟨found,member,equal⟩ | rfl)
    · exact ⟨found,Or.inl member,equal⟩
    · exact ⟨_,Or.inr rfl,rfl⟩

/-- One erase per instance group keeps the shape and every live instance. -/
theorem erase_groups_shape_active (state result : State) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id)) (prior : ShapeInvariant state)
    (accepted : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result) :
    ShapeInvariant result ∧ ∀ name, ActiveInstance result name ↔ ActiveInstance state name := by
  induction groups generalizing state with
  | nil =>
    simp only [List.map_nil, applyOperations, Option.some.injEq] at accepted
    subst result
    exact ⟨prior, fun _ => Iff.rfl⟩
  | cons group rest ih =>
    cases first : applyOperation state (.erase block group.1 group.2) with
    | none => simp [applyOperations, first] at accepted
    | some middle =>
      have later : applyOperations middle (rest.map fun group => .erase block group.1 group.2) =
          some result := by simpa [applyOperations, first] using accepted
      obtain ⟨middleShape, middleActive⟩ := erase_shape_active state middle block group.1 group.2 prior first
      obtain ⟨resultShape, resultActive⟩ := ih middle middleShape later
      exact ⟨resultShape, fun name => (resultActive name).trans (middleActive name)⟩

#print axioms erase_shape_active
#print axioms insert_shape_active
#print axioms create_active_exact

private theorem prepared_emits (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (payload : NotionCorePayload.Payload) (tx : Transaction)
    (prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) session payload = some tx) :
    tx.payload.emits = true := by
  have same := NotionCorePayloadNetwork.prepared_payload prepared
  rw [same]
  cases payload <;> simp only [NotionCorePayload.prepare] at prepared
  all_goals first | contradiction | split at prepared <;> simp_all

/-- The actual archive admission excludes an ordinary empty insertion. -/
theorem archived_emits (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) :
    ∀ entry ∈ network.entries, entry.tx.payload.emits = true := by
  induction reachable with
  | init => simp [NotionCorePayloadNetwork.initial]
  | bootstrap atoms => simp [NotionCorePayloadNetwork.seeded,NotionCorePayload.bootstrap,
      NotionCorePayload.Payload.emits]
  | exchange target source _ ih => exact ih
  | gap session ticks _ ih => exact ih
  | @emit state session payload tx _ prepared known ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | previous
    · exact prepared_emits state session payload tx prepared
    · exact ih entry previous

theorem canonical_insert_nonempty (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (tx : Transaction) (member : tx ∈ NotionCoreReconstruction.transactions network peer)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) : atoms ≠ [] := by
  obtain ⟨entry,present,same,_⟩ := NotionCoreReconstruction.transactions_received network peer tx member
  have emits := archived_emits network (NotionCoreCreatorNetwork.payload_reachable reachable) entry present
  rw [same,payload] at emits
  simpa [NotionCorePayload.Payload.emits] using emits

open NotionCoreRootCreators (rootCreatedBlocks RootProvenance)
open NotionCoreMachinePartition (Partitioned)

def RootActive (txs : List Transaction) (state : State) : Prop :=
  ∀ name, ActiveInstance state name ↔
    ∃ tx ∈ txs, ∃ key ∈ rootCreatedBlocks tx, blockName key = name

private theorem extend_roots (pre : List Transaction) (tx : Transaction) (state next : State)
    (prior : RootActive pre state)
    (active : ∀ name, ActiveInstance next name ↔ ActiveInstance state name ∨
      ∃ key ∈ rootCreatedBlocks tx, blockName key = name) : RootActive (pre ++ [tx]) next := by
  intro name
  rw [active name,prior name]
  constructor
  · rintro (⟨old,member,key,root,equal⟩ | ⟨key,root,equal⟩)
    · exact ⟨old,List.mem_append_left _ member,key,root,equal⟩
    · exact ⟨tx,by simp,key,root,equal⟩
  · rintro ⟨old,member,key,root,equal⟩
    rcases List.mem_append.mp member with earlier | newest
    · exact Or.inl ⟨old,earlier,key,root,equal⟩
    · have same := List.mem_singleton.mp newest
      subst old
      exact Or.inr ⟨key,root,equal⟩

private theorem selected_active (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : NotionRunAllocation.Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (prior : RootActive pre state) (inst : BlockKey)
    (selected : inst ∈ NotionCoreRootCreators.selectedInstances tx.payload) :
    ActiveInstance state (blockName inst) := by
  obtain ⟨provider,member,root,_⟩ := NotionCoreRootCreators.canonical_selected_root_provider
    network reachable roots peer pre suffix tx position inst selected
  exact (prior _).mpr ⟨provider,member,inst,root,rfl⟩

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- Every ordinary next transaction executes, using earlier root creators to
supply active-instance guards for insertion and splitting. -/
theorem canonical_ordinary_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : NotionRunAllocation.Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (part : Partitioned state) (shape : ShapeInvariant state) (rootActive : RootActive pre state)
    (ordinary : ∀ atoms, tx.payload ≠ .bootstrap atoms) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next ∧ ShapeInvariant next ∧
      RootActive (pre ++ [tx]) next := by
  cases payload : tx.payload with
  | bootstrap atoms => exact False.elim (ordinary atoms payload)
  | create afterBlock =>
    obtain ⟨next,step,nextPart,_,_⟩ := NotionCoreMachineCanonicalCreate.canonical_create_phase
      network reachable peer pre suffix tx position state accepted part afterBlock
    have nextShape := canonical_create_shape network reachable peer pre suffix tx position state next accepted shape
      part afterBlock step
    obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh
      network reachable peer pre suffix tx position state accepted
    have active := create_active_exact state next (.issued tx.id) afterBlock freshInstance freshBlock step
    refine ⟨next,by simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step,
      nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload,eq_comm] using active name
  | insert block inst origin atoms =>
    have selected := selected_active network reachable roots peer pre suffix tx position state rootActive inst
      (by simp [NotionCoreRootCreators.selectedInstances,payload])
    have nonempty := canonical_insert_nonempty network reachable peer tx
      (position ▸ List.mem_append_right pre (by simp)) block inst origin atoms payload
    obtain ⟨next,step,nextPart⟩ := NotionCoreMachinePartitionUpdates.canonical_insert_partitioned
      network reachable peer pre suffix tx position state accepted part block inst origin atoms payload nonempty
    have operation : applyOperation state (.insert block inst tx.id origin atoms) = some next := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
    obtain ⟨nextShape,active⟩ := insert_shape_active state next block inst tx.id origin atoms shape selected operation
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | erase block groups =>
    obtain ⟨next,step,nextPart⟩ := NotionCoreMachinePartitionUpdates.canonical_erase_partitioned
      network reachable peer pre suffix tx position state accepted part block groups payload
    have operations : applyOperations state (groups.map fun group => .erase block group.1 group.2) =
        some next := by
      simpa [applyTransaction,NotionCorePayload.operations,payload] using step
    obtain ⟨nextShape,active⟩ := erase_groups_shape_active state next block groups shape operations
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | split block inst origin =>
    have selected := selected_active network reachable roots peer pre suffix tx position state rootActive inst
      (by simp [NotionCoreRootCreators.selectedInstances,payload])
    obtain ⟨next,step,nextPart,nextShape,active⟩ := NotionCoreMachineCanonicalSplit.canonical_split_preserves_active
      network reachable peer pre suffix tx position state accepted part shape block inst origin payload selected
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | merge source target =>
    obtain ⟨next,step,nextPart,nextShape,active⟩ := NotionCoreMachineCanonicalSplit.canonical_merge_preserves_active
      network reachable peer pre suffix tx position state accepted part shape source target payload
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name

namespace SPOT
private def cut : Transaction := ⟨⟨2,[66]⟩,.split .initial .initial .start⟩
private def back : Transaction := ⟨⟨3,[66]⟩,.merge (.issued cut.id) .initial⟩
private def liveInstances (state : State) : List Nat :=
  (forestNodes state.forest).filterMap fun node => if node.2 then some node.1.start.1 else none
/-- Split retains the original instance in both live slices; the fresh
split destination's own empty title is not a live instance. Merging it back
keeps both live slices and the dead title inside the absorbing block. -/
theorem split_active_control :
    (replay {} [NotionCorePayload.bootstrap [],cut]).map liveInstances = some [0,0] ∧
    (replay {} [NotionCorePayload.bootstrap [],cut]).map liveInstances ≠
        some [0,blockName (.issued cut.id)] ∧
    (replay {} [NotionCorePayload.bootstrap [],cut,back]).map liveInstances = some [0,0] ∧
    (replay {} [NotionCorePayload.bootstrap [],cut,back]).map (fun state => state.forest.length) =
        some 1 := by decide +kernel
end SPOT

#print axioms canonical_ordinary_step

private theorem root_frame_active (state result : State) (bid : Nat)
    (forest : result.forest = state.forest ++ [⟨bid,NotionCoreSliceForest.freshTitle bid⟩]) :
    ∀ name, ActiveInstance result name ↔ ActiveInstance state name ∨ name = bid := by
  intro name
  simp only [ActiveInstance,forest,NotionCoreSliceForest.forestNodes_append,
    NotionCoreSliceForest.forestNodes_fresh,List.mem_append,List.mem_singleton,Prod.mk.injEq,and_true]
  constructor
  · rintro ⟨found,member,equal⟩
    rcases member with old | rfl
    · exact Or.inl ⟨found,old,equal⟩
    · exact Or.inr equal.symm
  · rintro (⟨found,member,equal⟩ | rfl)
    · exact ⟨found,Or.inl member,equal⟩
    · exact ⟨_,Or.inr rfl,rfl⟩

private theorem canonical_bootstrap_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (part : Partitioned state) (shape : ShapeInvariant state) (rootActive : RootActive pre state)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next ∧ ShapeInvariant next ∧
      RootActive (pre ++ [tx]) next := by
  have same := NotionCoreBootstrapProvenance.canonical_bootstrap_transaction
    network reachable peer pre suffix tx position atoms payload
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh
    network reachable peer pre suffix tx position atoms payload state accepted
  obtain ⟨next,step,nextPart,forest,other⟩ := NotionCoreMachineBootstrap.fresh_bootstrap_preserves
    state atoms part freshInstance freshBlock
  have fresh := fresh_name_of_instance state part 0 freshInstance
  refine ⟨next,by simpa only [same] using step,nextPart,
    fresh_root_frame_shape state next 0 shape fresh forest other,
    extend_roots pre tx state next rootActive ?_⟩
  intro name
  simpa [rootCreatedBlocks,payload,blockName,eq_comm] using root_frame_active state next 0 forest name

/-! Archive-general closed-version replay. -/
theorem canonical_insert_nonempty_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (tx : Transaction) (member : tx ∈ NotionCoreReconstruction.transactionsFor network version)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) : atoms ≠ [] := by
  obtain ⟨entry,present,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx member
  have emits := archived_emits network (NotionCoreCreatorNetwork.payload_reachable reachable) entry present
  rw [same,payload] at emits
  simpa [NotionCorePayload.Payload.emits] using emits

private theorem selected_active_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (prior : RootActive pre state) (inst : BlockKey)
    (selected : inst ∈ NotionCoreRootCreators.selectedInstances tx.payload) :
    ActiveInstance state (blockName inst) := by
  obtain ⟨provider,member,root,_⟩ := NotionCoreRootCreators.canonical_selected_root_provider_version
    network reachable roots version closed pre suffix tx position inst selected
  exact (prior _).mpr ⟨provider,member,inst,root,rfl⟩

theorem canonical_ordinary_step_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (part : Partitioned state) (shape : ShapeInvariant state) (rootActive : RootActive pre state)
    (ordinary : ∀ atoms, tx.payload ≠ .bootstrap atoms) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next ∧ ShapeInvariant next ∧
      RootActive (pre ++ [tx]) next := by
  cases payload : tx.payload with
  | bootstrap atoms => exact False.elim (ordinary atoms payload)
  | create afterBlock =>
    obtain ⟨next,step,nextPart,_,_⟩ := NotionCoreMachineCanonicalCreate.canonical_create_phase_version
      network reachable version closed pre suffix tx position state accepted part afterBlock
    obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
      network reachable version closed pre suffix tx position state accepted
    have nextShape := fresh_create_shape_preserves state next (.issued tx.id) afterBlock
      shape part freshInstance freshBlock step
    have active := create_active_exact state next (.issued tx.id) afterBlock freshInstance freshBlock step
    refine ⟨next,by simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step,
      nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload,eq_comm] using active name
  | insert block inst origin atoms =>
    have selected := selected_active_version network reachable roots version closed pre suffix tx position state rootActive inst
      (by simp [NotionCoreRootCreators.selectedInstances,payload])
    have nonempty := canonical_insert_nonempty_version network reachable version tx
      (position ▸ List.mem_append_right pre (by simp)) block inst origin atoms payload
    obtain ⟨next,step,nextPart⟩ := NotionCoreMachinePartitionUpdates.canonical_insert_partitioned_version
      network reachable version closed pre suffix tx position state accepted part block inst origin atoms payload nonempty
    have operation : applyOperation state (.insert block inst tx.id origin atoms) = some next := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
    obtain ⟨nextShape,active⟩ := insert_shape_active state next block inst tx.id origin atoms shape selected operation
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | erase block groups =>
    obtain ⟨next,step,nextPart⟩ := NotionCoreMachinePartitionUpdates.canonical_erase_partitioned_version
      network reachable version closed pre suffix tx position state accepted part block groups payload
    have operations : applyOperations state (groups.map fun group => .erase block group.1 group.2) =
        some next := by
      simpa [applyTransaction,NotionCorePayload.operations,payload] using step
    obtain ⟨nextShape,active⟩ := erase_groups_shape_active state next block groups shape operations
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | split block inst origin =>
    have selected := selected_active_version network reachable roots version closed pre suffix tx position state rootActive inst
      (by simp [NotionCoreRootCreators.selectedInstances,payload])
    obtain ⟨next,step,nextPart,nextShape,active⟩ := NotionCoreMachineCanonicalSplit.canonical_split_preserves_active_version
      network reachable version closed pre suffix tx position state accepted part shape block inst origin payload selected
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name
  | merge source target =>
    obtain ⟨next,step,nextPart,nextShape,active⟩ := NotionCoreMachineCanonicalSplit.canonical_merge_preserves_active_version
      network reachable version closed pre suffix tx position state accepted part shape source target payload
    refine ⟨next,step,nextPart,nextShape,extend_roots pre tx state next rootActive ?_⟩
    intro name
    simpa [rootCreatedBlocks,payload] using active name

private theorem canonical_bootstrap_step_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (part : Partitioned state) (shape : ShapeInvariant state) (rootActive : RootActive pre state)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next ∧ ShapeInvariant next ∧
      RootActive (pre ++ [tx]) next := by
  have same := NotionCoreBootstrapProvenance.canonical_bootstrap_transaction_version
    network reachable version pre suffix tx position atoms payload
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh_version
    network reachable version closed pre suffix tx position atoms payload state accepted
  obtain ⟨next,step,nextPart,forest,other⟩ := NotionCoreMachineBootstrap.fresh_bootstrap_preserves
    state atoms part freshInstance freshBlock
  have fresh := fresh_name_of_instance state part 0 freshInstance
  refine ⟨next,by simpa only [same] using step,nextPart,
    fresh_root_frame_shape state next 0 shape fresh forest other,
    extend_roots pre tx state next rootActive ?_⟩
  intro name
  simpa [rootCreatedBlocks,payload,blockName,eq_comm] using root_frame_active state next 0 forest name

theorem canonical_prefix_reconstruct_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) :
    ∃ state, replay {} pre = some state ∧ Partitioned state ∧ ShapeInvariant state ∧ RootActive pre state := by
  induction pre using List.reverseRecOn generalizing suffix with
  | nil =>
    exact ⟨{},rfl,NotionCoreMachinePartition.initial_partitioned,initial_shape,by simp [RootActive,ActiveInstance,forestNodes]⟩
  | append_singleton pre tx ih =>
    have located : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix := by
      simpa only [List.append_assoc,List.singleton_append] using position
    obtain ⟨state,accepted,part,shape,rootActive⟩ := ih (tx :: suffix) located
    have nextStep : ∃ next, applyTransaction state tx = some next ∧ Partitioned next ∧
        ShapeInvariant next ∧ RootActive (pre ++ [tx]) next := by
      cases payload : tx.payload with
      | bootstrap atoms =>
        exact canonical_bootstrap_step_version network reachable version closed pre suffix tx located
          state accepted part shape rootActive atoms payload
      | create afterBlock =>
        exact canonical_ordinary_step_version network reachable roots version closed pre suffix tx located
          state accepted part shape rootActive (by intro atoms; simp [payload])
      | insert block inst origin atoms =>
        exact canonical_ordinary_step_version network reachable roots version closed pre suffix tx located
          state accepted part shape rootActive (by intro other; simp [payload])
      | erase block groups =>
        exact canonical_ordinary_step_version network reachable roots version closed pre suffix tx located
          state accepted part shape rootActive (by intro atoms; simp [payload])
      | split block inst origin =>
        exact canonical_ordinary_step_version network reachable roots version closed pre suffix tx located
          state accepted part shape rootActive (by intro atoms; simp [payload])
      | merge source target =>
        exact canonical_ordinary_step_version network reachable roots version closed pre suffix tx located
          state accepted part shape rootActive (by intro atoms; simp [payload])
    obtain ⟨next,step,nextPart,nextShape,nextRoots⟩ := nextStep
    refine ⟨next,?_,nextPart,nextShape,nextRoots⟩
    simp [replay_append,accepted,replay,step,Bind.bind,Option.bind]

/-- Whole closed-version execution, including recursively constructed
virtual merge-base versions of this same archive. -/
theorem reconstruct_version_invariant (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      Partitioned state ∧ ShapeInvariant state ∧
      RootActive (NotionCoreReconstruction.transactionsFor network version) state :=
  canonical_prefix_reconstruct_version network reachable roots version closed _ [] (by simp)

#print axioms canonical_prefix_reconstruct_version
#print axioms reconstruct_version_invariant
/-- Peer replay is a specialization of the same closed archive-prefix
induction; no separate peer-only progress argument is needed. -/
theorem canonical_prefix_reconstruct (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : NotionRunAllocation.Session) (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ suffix) :
    ∃ state, replay {} pre = some state ∧ Partitioned state ∧ ShapeInvariant state ∧ RootActive pre state :=
  canonical_prefix_reconstruct_version network reachable roots _
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix position

/-- Complete peer reconstruction retains the existing API. -/
theorem reconstruct_invariant (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : NotionRunAllocation.Session) :
    ∃ state, NotionCoreReconstruction.reconstruct network peer = some state ∧
      Partitioned state ∧ ShapeInvariant state ∧
      RootActive (NotionCoreReconstruction.transactions network peer) state :=
  canonical_prefix_reconstruct network reachable roots peer _ [] (by simp)

#print axioms canonical_prefix_reconstruct
#print axioms reconstruct_invariant
end Sal.MRDTs.Instances.NotionCoreMachineRootReplay
