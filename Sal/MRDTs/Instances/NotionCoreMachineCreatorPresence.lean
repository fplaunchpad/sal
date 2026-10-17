import Sal.MRDTs.Instances.NotionCoreArchiveOrder
import Sal.MRDTs.Instances.NotionCoreMachineCreators

/-! Forward creator persistence in actual accepted replay. Stored instances
and forest support are conclusions; no next-operation acceptance is assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence
open NotionCoreMachine
open NotionCoreMachineCreators (names operationCreates)
open NotionCorePayload (BlockKey Operation Transaction reservation)

def StoredInstance (state : State) (key : Nat) : Prop :=
  ∃ entry ∈ state.instances, entry.1 = key
/-- Every forest block and every display entry, tombstones included, has a
stored text instance. -/
def Supported (state : State) : Prop :=
  ∀ key ∈ names state.forest ++ state.display, StoredInstance state key

private theorem put_mono (state : State) (inst key : Nat) (value : Instance)
    (stored : StoredInstance state key) : StoredInstance (putInstance state inst value) key := by
  obtain ⟨entry,present,equal⟩ := stored
  unfold putInstance
  split
  · refine ⟨if entry.1 == inst then (inst,value) else entry,List.mem_map.mpr ⟨entry,present,rfl⟩,?_⟩
    by_cases changed : entry.1 = inst <;> simp_all
  · exact ⟨entry,List.mem_append_left _ present,equal⟩
private theorem put_contains (state : State) (inst : Nat) (value : Instance) :
    StoredInstance (putInstance state inst value) inst := by
  by_cases found : state.instances.any (fun entry => entry.1 == inst) = true
  · obtain ⟨entry,present,equal⟩ := List.any_eq_true.mp found
    exact put_mono state inst inst value ⟨entry,present,by simpa using equal⟩
  · have no : state.instances.any (fun entry => entry.1 == inst) = false := Bool.eq_false_iff.mpr found
    simp [StoredInstance,putInstance,no]

private theorem operation_presence (state result : State) (op : Operation)
    (supported : Supported state) (accepted : applyOperation state op = some result) :
    (∀ key, StoredInstance state key → StoredInstance result key) ∧
      (∀ key ∈ operationCreates op, StoredInstance result key) := by
  cases op with
  | create block afterBlock =>
    simp only [applyOperation] at accepted
    split at accepted
    · rename_i found
      simp only [Option.some.injEq] at accepted; subst result
      refine ⟨fun _ h => h,?_⟩
      intro key member
      have same : key = blockName block := by simpa [operationCreates] using member
      subst key
      exact supported _ (List.mem_append_right _ found)
    · simp only [Option.some.injEq] at accepted; subst result
      change (∀ key, StoredInstance state key → StoredInstance
        (if state.instances.any (fun entry => entry.1 == blockName block) then state
          else putInstance state (blockName block) {}) key) ∧ _
      split
      · rename_i found
        refine ⟨fun _ h => h,?_⟩
        intro key member
        have same : key = blockName block := by simpa [operationCreates] using member
        subst key
        obtain ⟨entry,present,equal⟩ := List.any_eq_true.mp found
        exact ⟨entry,present,by simpa using equal⟩
      · exact ⟨fun key h => put_mono state _ key {} h,by
          intro key member
          have same : key = blockName block := by simpa [operationCreates] using member
          subst key
          exact put_contains state _ {}⟩
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted; subst result
      exact ⟨fun key h => put_mono state _ key _ h,by simp [operationCreates]⟩
  | erase block inst targets =>
    simp only [applyOperation,Option.some.injEq] at accepted; subst result
    exact ⟨fun key h => put_mono state _ key _ h,by simp [operationCreates]⟩
  | marker block inst id origin =>
    simp only [applyOperation] at accepted
    cases integrated : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
    | none => simp [integrated] at accepted
    | some rows =>
      simp only [integrated] at accepted
      dsimp only [Bind.bind,Option.bind] at accepted
      split at accepted
      · contradiction
      · dsimp only at accepted
        split at accepted
        · simp at accepted; subst result
          exact ⟨fun key h => put_mono state _ key _ h,by simp [operationCreates]⟩
        · contradiction
  | moveInto block inst marker target =>
    simp only [applyOperation] at accepted
    split at accepted
    · contradiction
    · cases selected : NotionCoreSliceForest.detachForest
        (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
      | none => simp [selected] at accepted
      | some pair =>
        simp [selected] at accepted; subst result
        exact ⟨fun _ h => h,by simp [operationCreates]⟩
  | merge source target =>
    simp only [applyOperation,Option.some.injEq] at accepted; subst result
    exact ⟨fun _ h => h,by simp [operationCreates]⟩

/-- Display entries after an operation were displayed before or are created by it. -/
theorem operation_display_names (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    ∀ bid ∈ result.display, bid ∈ state.display ++ operationCreates op := by
  cases op with
  | create block afterBlock =>
    simp only [applyOperation] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      intro bid member
      exact List.mem_append_left _ member
    · simp only [Option.some.injEq] at accepted
      subst result
      intro bid member
      have inserted := (NotionCoreDisplayOrder.insert_perm _ _ _).mem_iff.mp member
      rcases List.mem_cons.mp inserted with fresh | old
      · simp [operationCreates, fresh]
      · exact List.mem_append_left _ (List.mem_of_mem_filter old)
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted; subst result
      intro bid member
      exact List.mem_append_left _ (by simpa using member)
  | erase block inst targets =>
    simp only [applyOperation,Option.some.injEq] at accepted; subst result
    intro bid member
    exact List.mem_append_left _ (by simpa using member)
  | marker block inst id origin =>
    simp only [applyOperation] at accepted
    cases integrated : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
    | none => simp [integrated] at accepted
    | some rows =>
      simp only [integrated] at accepted
      dsimp only [Bind.bind,Option.bind] at accepted
      split at accepted
      · contradiction
      · dsimp only at accepted
        split at accepted
        · simp at accepted; subst result
          intro bid member
          exact List.mem_append_left _ (by simpa using member)
        · contradiction
  | moveInto block inst marker target =>
    simp only [applyOperation] at accepted
    split at accepted
    · contradiction
    · cases selected : NotionCoreSliceForest.detachForest
        (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
      | none => simp [selected] at accepted
      | some pair =>
        simp [selected] at accepted; subst result
        exact fun bid member => List.mem_append_left _ member
  | merge source target =>
    simp only [applyOperation,Option.some.injEq] at accepted; subst result
    exact fun bid member => List.mem_append_left _ member

private theorem operation_supported (state result : State) (op : Operation)
    (supported : Supported state) (accepted : applyOperation state op = some result) : Supported result := by
  have presence := operation_presence state result op supported accepted
  intro key member
  rcases List.mem_append.mp member with stored | shown
  · rcases List.mem_append.mp (NotionCoreMachineCreators.operation_names state result op accepted key stored) with old | fresh
    · exact presence.1 key (supported key (List.mem_append_left _ old))
    · exact presence.2 key fresh
  · rcases List.mem_append.mp (operation_display_names state result op accepted key shown) with old | fresh
    · exact presence.1 key (supported key (List.mem_append_right _ old))
    · exact presence.2 key fresh

private theorem operations_presence (state result : State) (ops : List Operation)
    (supported : Supported state) (accepted : applyOperations state ops = some result) :
    Supported result ∧ (∀ key, StoredInstance state key → StoredInstance result key) ∧
      (∀ key ∈ ops.flatMap operationCreates, StoredInstance result key) := by
  induction ops generalizing state with
  | nil => simp [applyOperations] at accepted; subst result; exact ⟨supported,fun _ h => h,by simp⟩
  | cons op rest ih =>
    cases first : applyOperation state op with
    | none => simp [applyOperations,first] at accepted
    | some middle =>
      simp [applyOperations,first] at accepted
      have oneStep :=  operation_presence state middle op supported first
      obtain ⟨support,mono,created⟩ := ih middle (operation_supported state middle op supported first) accepted
      refine ⟨support,fun key h => mono key (oneStep.1 key h),?_⟩
      intro key member
      rcases List.mem_append.mp member with now | later
      · exact mono key (oneStep.2 key now)
      · exact created key later

private theorem transaction_presence (state result : State) (tx : Transaction)
    (supported : Supported state) (accepted : applyTransaction state tx = some result) :
    Supported result ∧ (∀ key, StoredInstance state key → StoredInstance result key) ∧
      (∀ block ∈ NotionCoreCreatorNetwork.createdBlocks tx, StoredInstance result (blockName block)) := by
  obtain ⟨support,mono,created⟩ := operations_presence state result (NotionCorePayload.operations tx) supported accepted
  refine ⟨support,mono,?_⟩
  intro block member
  apply created
  cases tx with
  | mk id payload => cases payload <;>
      simp [NotionCoreCreatorNetwork.createdBlocks] at member <;>
      simp_all [NotionCorePayload.operations,operationCreates]

theorem replay_presence (state result : State) (txs : List Transaction)
    (supported : Supported state) (accepted : replay state txs = some result) :
    Supported result ∧ (∀ key, StoredInstance state key → StoredInstance result key) ∧
      (∀ tx ∈ txs, ∀ block ∈ NotionCoreCreatorNetwork.createdBlocks tx,
        StoredInstance result (blockName block)) := by
  induction txs generalizing state with
  | nil => simp [replay] at accepted; subst result; exact ⟨supported,fun _ h => h,by simp⟩
  | cons tx rest ih =>
    cases first : applyTransaction state tx with
    | none => simp [replay,first] at accepted
    | some middle =>
      simp [replay,first] at accepted
      have oneStep :=  transaction_presence state middle tx supported first
      obtain ⟨support,mono,created⟩ := ih middle oneStep.1 accepted
      refine ⟨support,fun key h => mono key (oneStep.2.1 key h),?_⟩
      intro provider member block born
      rcases List.mem_cons.mp member with rfl | later
      · exact mono _ (oneStep.2.2 block born)
      · exact created provider later block born

theorem replay_created_instances (txs : List Transaction) (result : State)
    (accepted : replay {} txs = some result) :
    Supported result ∧ ∀ tx ∈ txs, ∀ block ∈ NotionCoreCreatorNetwork.createdBlocks tx,
      StoredInstance result (blockName block) := by
  have presence := replay_presence {} result txs (by simp [Supported,names]) accepted
  exact ⟨presence.1,presence.2.2⟩

/-- An earlier archived creator is present in the actual canonical prefix,
so next required instances exist without assuming the next operation succeeds. -/
theorem canonical_required_instance_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (inst : BlockKey)
    (required : inst ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    StoredInstance state (blockName inst) := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      version =
      pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactionsFor_runs,position,List.map_append,List.map_cons,same]
  obtain ⟨provider,published,earlier,born,_⟩ :=
    NotionCoreCreatorNetwork.replay_creator_provider_version reachable version closed member
      (pre.map reservation) (suffix.map reservation) runPosition (same ▸ required)
  obtain ⟨previous,inPre,runSame⟩ := List.mem_map.mp earlier
  obtain ⟨archived,archiveMember,previousEq,_⟩ := NotionCoreReconstruction.transactionsFor_received network version previous
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
  exact (replay_created_instances pre state accepted).2 previous inPre inst (transactionEq ▸ born)

/-- Registered peer receipts specialize an explicitly closed archive version. -/
theorem canonical_required_instance (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (inst : BlockKey)
    (required : inst ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    StoredInstance state (blockName inst) :=
  canonical_required_instance_version network reachable _
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix tx position state accepted inst required

#print axioms canonical_required_instance_version

private def seed := NotionCorePayload.bootstrap [97]
private def created : Transaction := ⟨⟨2,[65]⟩,.create (some .initial)⟩
private def fixture := replay {} [seed,created]

/-- Empty metadata-created instances persist despite having no text births. -/
theorem metadata_creator_control :
    fixture.map (fun state => state.instances.map Prod.fst) =
      some [0,blockName (.issued ⟨2,[65]⟩)] ∧
    fixture.map (fun state => state.instances.map Prod.fst) ≠ some [0] := by decide +kernel

#print axioms canonical_required_instance
#print axioms metadata_creator_control
#print axioms replay_created_instances
end Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence
