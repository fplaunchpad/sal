import Sal.MRDTs.Instances.NotionCoreMachineCreators
import Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence

/-! Stored blocks persist and every executed creator is present. This derives
canonical predecessor existence needed by the independent create transition. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineBlockPresence
open NotionCoreMachine
open NotionCoreMachineCreators
open NotionCorePayload (Operation Transaction BlockKey reservation)

theorem operation_members (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    ∀ bid, bid ∈ names result.forest ↔ bid ∈ names state.forest ∨ bid ∈ operationCreates op := by
  cases op with
  | create block after =>
    by_cases existsBlock : state.forest.any (fun b => b.id == blockName block) = true
    · have same : state = result := by simpa [applyOperation,existsBlock] using accepted
      subst result
      have present : blockName block ∈ names state.forest := by
        simpa [names] using existsBlock
      intro bid
      simp only [operationCreates,List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (member | rfl)
        · exact member
        · exact present
    · simp only [applyOperation,existsBlock,Bool.false_eq_true,if_false] at accepted
      simp only [apply_ite,putInstance_forest,ite_self] at accepted
      simp only [existsBlock,Bool.false_eq_true,if_false,Option.some.injEq] at accepted
      subst result
      simp [names,operationCreates]
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted
      subst result
      simp [operationCreates]
  | erase block inst targets =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    simp [operationCreates]
  | marker block inst id origin =>
    simp only [applyOperation] at accepted
    cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
    | none => simp [selected] at accepted
    | some rows =>
      simp only [selected] at accepted
      dsimp only [Bind.bind, Option.bind] at accepted
      let updated := putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows}
      cases divided : NotionCoreSliceForest.splitForest (physical updated)
          (NotionCorePhysicalReplay.address (blockName inst) id) updated.forest with
      | none =>
        have divided' := divided
        simp only [updated, putInstance_forest] at divided'
        simp [divided'] at accepted
      | some forest =>
        have equal := splitForest_names _ _ _ forest divided
        simp only [updated, putInstance_forest] at equal
        have divided' := divided
        simp only [updated, putInstance_forest] at divided'
        simp only [putInstance_forest, divided'] at accepted
        split at accepted
        · simp at accepted
          subst result
          simp [operationCreates,equal]
        · contradiction
  | moveInto block inst marker target =>
    simp only [applyOperation] at accepted
    split at accepted
    · contradiction
    · cases detached : NotionCoreSliceForest.detachForest
          (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
      | none => simp [detached] at accepted
      | some pair =>
        simp [detached] at accepted
        subst result
        have same := detachForest_names _ _ pair.1 pair.2 detached
        simp [operationCreates,same]


theorem operations_members (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) :
    ∀ bid, bid ∈ names result.forest ↔ bid ∈ names state.forest ∨ bid ∈ ops.flatMap operationCreates := by
  induction ops generalizing state with
  | nil =>
    have same : state = result := by simpa [applyOperations] using accepted
    subst result
    simp
  | cons op rest ih =>
    cases first : applyOperation state op with
    | none => simp [applyOperations,first] at accepted
    | some middle =>
      have later : applyOperations middle rest = some result := by simpa [applyOperations,first] using accepted
      intro bid
      rw [ih middle later,operation_members state middle op first]
      simp [List.flatMap_cons,or_assoc]

theorem transaction_members (state result : State) (tx : Transaction)
    (accepted : applyTransaction state tx = some result) :
    ∀ bid, bid ∈ names result.forest ↔ bid ∈ names state.forest ∨
      bid ∈ (NotionCoreCreatorNetwork.createdBlocks tx).map blockName := by
  have translated : (NotionCorePayload.operations tx).flatMap operationCreates =
      (NotionCoreCreatorNetwork.createdBlocks tx).map blockName := by
    cases tx with
    | mk id payload => cases payload <;> simp [NotionCorePayload.operations,operationCreates,NotionCoreCreatorNetwork.createdBlocks]
  simpa [translated] using operations_members state result (NotionCorePayload.operations tx) accepted

theorem replay_members (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) :
    ∀ bid, bid ∈ names result.forest ↔ bid ∈ names state.forest ∨
      ∃ tx ∈ txs, ∃ key ∈ NotionCoreCreatorNetwork.createdBlocks tx, blockName key = bid := by
  induction txs generalizing state with
  | nil =>
    have same : state = result := by simpa [replay] using accepted
    subst result
    simp
  | cons tx rest ih =>
    cases first : applyTransaction state tx with
    | none => simp [replay,first] at accepted
    | some middle =>
      have later : replay middle rest = some result := by simpa [replay,first] using accepted
      intro bid
      rw [ih middle later,transaction_members state middle tx first]
      simp only [List.mem_map,List.mem_cons]
      aesop

theorem canonical_required_block (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (inst : BlockKey)
    (required : inst ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    blockName inst ∈ names state.forest := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactions_received network peer tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      (network.allocation.peers peer).received =
      pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactions_runs,position,List.map_append,List.map_cons,same]
  obtain ⟨provider,published,earlier,born,_⟩ :=
    NotionCoreCreatorNetwork.replay_creator_provider reachable peer member
      (pre.map reservation) (suffix.map reservation) runPosition (same ▸ required)
  obtain ⟨previous,inPre,runSame⟩ := List.mem_map.mp earlier
  obtain ⟨archived,archiveMember,previousEq,_⟩ := NotionCoreReconstruction.transactions_received network peer previous
    (position ▸ List.mem_append_left _ inPre)
  have keys := NotionCoreArchiveOrder.archive_keys_unique network
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  have providerMember : provider.tx ∈ network.entries.map NotionCorePayloadNetwork.Entry.tx :=
    List.mem_map.mpr ⟨provider,published,rfl⟩
  have previousMember : previous ∈ network.entries.map NotionCorePayloadNetwork.Entry.tx :=
    List.mem_map.mpr ⟨archived,archiveMember,previousEq⟩
  have transactionEq : previous = provider.tx :=
    List.inj_on_of_nodup_map keys previousMember providerMember
      (congrArg NotionRunAllocation.Run.first runSame)
  exact (replay_members {} state pre accepted (blockName inst)).mpr
    (Or.inr ⟨previous,inPre,inst,transactionEq ▸ born,rfl⟩)

#print axioms canonical_required_block
#print axioms replay_members
end Sal.MRDTs.Instances.NotionCoreMachineBlockPresence
