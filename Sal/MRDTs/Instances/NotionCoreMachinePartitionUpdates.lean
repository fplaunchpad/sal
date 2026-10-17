import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreMachineErase
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest
import Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence

/-! Structural partition preservation under physical insertion and erasure.
The physical-update equations are interfaces to actual table-update theorems;
no next partition, extracted result or selected owner is assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (Cell Entry flatten)
open NotionCoreMachine
open NotionCoreMachinePartition
open NotionCoreForestRefs (ownedRefs)

def refsOfEntries : List Entry → List (Nat × NotionCoreSliceForest.Ref)
  | [] => []
  | entry :: rest =>
      (entry.owner, ⟨entry.start, rest.head?.map Entry.start⟩) :: refsOfEntries rest

theorem cellRefs_entries (cells : List Cell) :
    cellRefs cells = refsOfEntries (cells.map Cell.entry) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have head : (rest.map Cell.entry).head?.map Entry.start =
          rest.head?.map (fun next => next.slice.start) := by cases rest <;> rfl
      simp only [cellRefs, List.map_cons, refsOfEntries, Cell.entry, head, ih]

theorem cellRefs_congr (a b : List Cell)
    (same : a.map Cell.entry = b.map Cell.entry) : cellRefs a = cellRefs b := by
  rw [cellRefs_entries, cellRefs_entries, same]

/-- Physical insertion leaves all endpoint triples unchanged. The affected
cell is derived from origin membership in the old traversal. -/
theorem splice_partitioned (state next : State) (inst : Nat)
    (origin : Address) (fresh : List Atom) (prior : Partitioned state)
    (forestFrame : next.forest = state.forest)
    (instanceFrame : ∀ key, (∃ entry ∈ next.instances, entry.1 = key) ↔
      ∃ entry ∈ state.instances, entry.1 = key)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst)
    (unique : ((physical state inst).map Atom.address).Nodup)
    (present : origin ∈ (physical state inst).map Atom.address)
    (changed : physical next inst = NotionCorePartition.spliceAfterBy Atom.address
      origin fresh (physical state inst))
    (unchanged : ∀ key, key ≠ inst → physical next key = physical state key) :
    Partitioned next := by
  constructor
  · intro owned member
    apply (instanceFrame owned.2.start.1).mpr
    exact prior.refsExist owned (forestFrame ▸ member)
  · intro key existsKey
    by_cases selected : key = inst
    · subst key
      obtain ⟨cells, physicalEq, permutation⟩ := prior.partitions inst existsInstance
      have representation : NotionCorePartition.Represents
          ⟨physical state inst, cells.map Cell.entry⟩ cells :=
        ⟨physicalEq, rfl, unique⟩
      obtain ⟨cell, ⟨member, active⟩, _⟩ :=
        NotionCorePartition.physical_unique_owner origin representation present
      obtain ⟨before, after, shape⟩ := List.append_of_mem member
      subst cells
      let inserted := NotionCorePartition.insertCell cell origin fresh
      refine ⟨before ++ inserted :: after, ?_, ?_⟩
      · rw [changed, physicalEq]
        exact NotionCorePartition.insert_physical before after cell origin fresh
          (by simpa [physicalEq] using unique) active
      · have endpoints : cellRefs (before ++ inserted :: after) = cellRefs (before ++ cell :: after) := by
          apply cellRefs_congr
          simp [inserted, NotionCorePartition.insertCell, NotionCoreSource.insertSlice, Cell.entry]
        rw [endpoints, forestFrame]
        exact permutation
    · obtain ⟨cells, physicalEq, permutation⟩ :=
        prior.partitions key ((instanceFrame key).mp existsKey)
      exact ⟨cells, (unchanged key selected).trans physicalEq, by simpa [forestFrame] using permutation⟩

/-- Tombstoning keeps interval boundaries and all physical identities. Empty
inactive title cells are mapped along with active cells. -/
theorem erase_partitioned (state next : State) (inst : Nat) (targets : List Address)
    (prior : Partitioned state)
    (forestFrame : next.forest = state.forest)
    (instanceFrame : ∀ key, (∃ entry ∈ next.instances, entry.1 = key) ↔
      ∃ entry ∈ state.instances, entry.1 = key)
    (changed : physical next inst = (physical state inst).map (NotionCoreSource.eraseAtom targets))
    (unchanged : ∀ key, key ≠ inst → physical next key = physical state key) :
    Partitioned next := by
  constructor
  · intro owned member
    apply (instanceFrame owned.2.start.1).mpr
    exact prior.refsExist owned (forestFrame ▸ member)
  · intro key existsKey
    obtain ⟨cells, physicalEq, permutation⟩ :=
      prior.partitions key ((instanceFrame key).mp existsKey)
    by_cases selected : key = inst
    · subst key
      refine ⟨cells.map (NotionCorePartition.eraseCell targets), ?_, ?_⟩
      · rw [changed, physicalEq]
        simp only [flatten, List.map_flatMap, List.flatMap_map]
        congr 1
      · have endpoints : cellRefs (cells.map (NotionCorePartition.eraseCell targets)) = cellRefs cells := by
          apply cellRefs_congr
          simp [List.map_map, NotionCorePartition.eraseCell, NotionCoreSource.eraseSlice, Cell.entry, Function.comp_def]
        rw [endpoints, forestFrame]
        exact permutation
    · exact ⟨cells, (unchanged key selected).trans physicalEq, by simpa [forestFrame] using permutation⟩

/-- Updating an existing instance changes its value, not the set of allocated
instance names. This frame is proved from actual list-map lookup storage. -/
theorem putInstance_exists_iff (state : State) (inst key : Nat) (value : Instance)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst) :
    (∃ entry ∈ (putInstance state inst value).instances, entry.1 = key) ↔
      ∃ entry ∈ state.instances, entry.1 = key := by
  have found : state.instances.any (fun entry => entry.1 == inst) = true := by
    simpa using existsInstance
  have keys : (putInstance state inst value).instances.map Prod.fst = state.instances.map Prod.fst := by
    simp only [putInstance, found, if_true, List.map_map]
    apply List.map_congr_left
    intro entry member
    by_cases selected : entry.1 = inst <;> simp [selected]
  have same : key ∈ (putInstance state inst value).instances.map Prod.fst ↔
      key ∈ state.instances.map Prod.fst := by rw [keys]
  simpa only [List.mem_map] using same

/-- Actual erase both executes and preserves every represented interval.
Existence of the selected instance is needed: the raw primitive can otherwise
allocate a table without creating a title. No physical-update equation or
next-step acceptance is supplied by the caller. -/
theorem erase_operation_partitioned (state : State)
    (block inst : NotionCorePayload.BlockKey) (targets : List NotionRunAllocation.Id)
    (prior : Partitioned state)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = blockName inst) :
    ∃ next, applyOperation state (.erase block inst targets) = some next ∧
      Partitioned next := by
  let value : Instance :=
    ⟨NotionCoreParentErase.erase targets (getInstance state (blockName inst)).rows,
      (getInstance state (blockName inst)).pending ++ targets⟩
  let next := putInstance state (blockName inst) value
  have accepted : applyOperation state (.erase block inst targets) = some next := rfl
  have frames := NotionCoreMachineErase.erase_physical state next block inst targets accepted
  refine ⟨next, accepted, erase_partitioned state next (blockName inst)
    (targets.map (NotionCorePhysicalReplay.address (blockName inst))) prior frames.1
    (fun key => putInstance_exists_iff state (blockName inst) key value existsInstance) ?_ ?_⟩
  · simpa using frames.2.2 (blockName inst)
  · intro key distinct
    simpa [distinct] using frames.2.2 key

/-- One erase per instance group executes and preserves every represented
interval when every group names an existing instance. -/
theorem erase_operations_partitioned (state : State) (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id))
    (prior : Partitioned state)
    (existsInstance : ∀ group ∈ groups, ∃ entry ∈ state.instances, entry.1 = blockName group.1) :
    ∃ next, applyOperations state (groups.map fun group => .erase block group.1 group.2) = some next ∧
      Partitioned next := by
  induction groups generalizing state with
  | nil => exact ⟨state, rfl, prior⟩
  | cons group rest ih =>
    obtain ⟨middle, first, middlePart⟩ := erase_operation_partitioned state block group.1 group.2 prior
      (existsInstance group (by simp))
    have kept : ∀ other ∈ rest, ∃ entry ∈ middle.instances, entry.1 = blockName other.1 := by
      intro other member
      simp only [applyOperation, Option.some.injEq] at first
      subst middle
      exact (putInstance_exists_iff state _ _ _ (existsInstance group (by simp))).mpr
        (existsInstance other (List.mem_cons_of_mem _ member))
    obtain ⟨next, later, nextPart⟩ := ih middle middlePart kept
    exact ⟨next, by simp [applyOperations, first, later], nextPart⟩

private theorem insert_result (state next : State) (block inst : NotionCorePayload.BlockKey)
    (first : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (accepted : applyOperation state (.insert block inst first origin atoms) = some next) :
    ∃ rows, next = putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows} := by
  cases integrated : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
  | none => simp [applyOperation, integrated] at accepted
  | some rows =>
      exact ⟨rows, by simpa [applyOperation, integrated] using accepted.symm⟩

/-- Actual canonical nonempty insertion preserves the full partition. The
origin, freshness and physical splice are derived from issuance; only the old
partition and the selected instance's existence remain structural inputs. -/
theorem canonical_insert_partitioned_of_instance_version
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCorePayloadNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (nonempty : atoms ≠ [])
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = blockName inst) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next := by
  obtain ⟨next, executed, physicalEq⟩ := NotionCoreMachineCanonicalForest.canonical_insert_physical_version
    network reachable version closed pre suffix tx position state accepted block inst origin atoms payload nonempty
  have transaction : applyTransaction state tx = some next := by
    simp [applyTransaction, NotionCorePayload.operations, payload, applyOperations, executed]
  obtain ⟨rows, nextEq⟩ := insert_result state next block inst tx.id origin atoms executed
  have frame : next.forest = state.forest := by
    rw [nextEq]
    unfold putInstance
    split <;> rfl
  refine ⟨next, transaction, splice_partitioned state next (blockName inst)
    (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
    ((NotionCorePayload.textItems tx.id atoms
      (fun id => decide (id ∈ (getInstance state (blockName inst)).pending))).map
      (NotionCorePhysicalReplay.atom (blockName inst))) prior frame ?_ existsInstance
    (NotionCoreMachineVersionTables.version_physical_unique_all network reachable version closed pre (tx :: suffix)
      position state accepted (blockName inst))
    (NotionCoreMachineCanonicalForest.canonical_insert_origin_present_version network reachable version closed pre suffix tx
      position state accepted block inst origin atoms payload) physicalEq ?_⟩
  · intro key
    rw [nextEq]
    exact putInstance_exists_iff state (blockName inst) key _ existsInstance
  · intro key distinct
    rw [nextEq]
    simp [physical, NotionCoreMachineTables.getInstance_put, distinct]

/-- Creator-aware canonical issuance supplies the selected instance as well
as all insertion guards. The only remaining execution invariant is the old
all-reference partition; next acceptance is a conclusion. -/
theorem canonical_insert_partitioned_version
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCoreCreatorNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (nonempty : atoms ≠ []) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next := by
  apply canonical_insert_partitioned_of_instance_version network
    (NotionCoreCreatorNetwork.payload_reachable reachable) version closed pre suffix tx position state accepted prior
    block inst origin atoms payload nonempty
  apply NotionCoreMachineCreatorPresence.canonical_required_instance_version
    network reachable version closed pre suffix tx position state accepted inst
  simp [payload, NotionCoreCreatorNetwork.requiredBlocks]

/-- The complete canonical erase transaction preserves the partition, with
the existence of every group's instance derived from a replayed creator.
Empty target lists are covered too; no item-reference witness is used to
infer creation. -/
theorem canonical_erase_partitioned_version
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCoreCreatorNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id))
    (payload : tx.payload = .erase block groups) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next := by
  have existsInstance : ∀ group ∈ groups, ∃ entry ∈ state.instances, entry.1 = blockName group.1 :=
    fun group member => NotionCoreMachineCreatorPresence.canonical_required_instance_version
      network reachable version closed pre suffix tx position state accepted group.1
      (by simp only [payload, NotionCoreCreatorNetwork.requiredBlocks]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨group, member, rfl⟩))
  obtain ⟨next, executed, represented⟩ := erase_operations_partitioned state block groups prior existsInstance
  exact ⟨next, by simpa [applyTransaction, NotionCorePayload.operations, payload] using executed, represented⟩

theorem canonical_insert_partitioned_of_instance
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCorePayloadNetwork.Reach network)
    (peer : NotionRunAllocation.Session) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (nonempty : atoms ≠ [])
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = blockName inst) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next :=
  canonical_insert_partitioned_of_instance_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable reachable) peer)
    pre suffix tx position state accepted prior block inst origin atoms payload nonempty existsInstance

theorem canonical_insert_partitioned
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCoreCreatorNetwork.Reach network)
    (peer : NotionRunAllocation.Session) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block inst : NotionCorePayload.BlockKey) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms) (nonempty : atoms ≠ []) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next :=
  canonical_insert_partitioned_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix tx position state accepted prior block inst origin atoms payload nonempty

theorem canonical_erase_partitioned
    (network : NotionCorePayloadNetwork.State) (reachable : NotionCoreCreatorNetwork.Reach network)
    (peer : NotionRunAllocation.Session) (pre suffix : List NotionCorePayload.Transaction)
    (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (prior : Partitioned state)
    (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id))
    (payload : tx.payload = .erase block groups) :
    ∃ next, applyTransaction state tx = some next ∧ Partitioned next :=
  canonical_erase_partitioned_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix tx position state accepted prior block groups payload

#print axioms canonical_insert_partitioned_version
#print axioms canonical_erase_partitioned_version
#print axioms splice_partitioned
#print axioms erase_partitioned
#print axioms erase_operation_partitioned
#print axioms canonical_insert_partitioned_of_instance
#print axioms canonical_insert_partitioned
#print axioms canonical_erase_partitioned
end Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
