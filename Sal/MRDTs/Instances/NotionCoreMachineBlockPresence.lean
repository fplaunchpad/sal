import Sal.MRDTs.Instances.NotionCoreMachineCreators
import Sal.MRDTs.Instances.NotionCoreMachineCreatorPresence

/-! Displayed blocks persist and every executed creator is displayed. A
forest member leaves the forest only by merge, and then stays in the display
order as a tombstone. This derives canonical predecessor existence needed by
the independent create transition. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineBlockPresence
open NotionCoreMachine
open NotionCoreMachineCreators
open NotionCorePayload (Operation Transaction BlockKey reservation)

/-- Every block stays in the forest except a merge's source: a forest member
is removed only by merge. -/
theorem operation_kept (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result)
    (notMerge : ∀ source inst stop, op ≠ .merge source inst stop) :
    ∀ bid, bid ∈ names state.forest → bid ∈ names result.forest := by
  cases op with
  | create block after =>
    by_cases shown : blockName block ∈ state.display
    · have same : state = result := by simpa [applyOperation,shown] using accepted
      subst result
      exact fun _ member => member
    · simp only [applyOperation,shown,↓reduceIte,Option.some.injEq] at accepted
      subst result
      intro bid member
      simp only [apply_ite,putInstance_forest,ite_self]
      split <;> simp_all [names]
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted
      subst result
      simp
  | erase block inst targets =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    simp
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
          simp [equal]
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
        simp [same]
  | merge source inst stop => exact False.elim (notMerge source inst stop rfl)

/-- Blocks persist in the display order: a merged source stays there as a
tombstone. Only a fresh create adds a name. -/
theorem operation_display (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    ∀ bid, bid ∈ result.display ↔ bid ∈ state.display ∨ bid ∈ operationCreates op := by
  cases op with
  | create block after =>
    by_cases shown : blockName block ∈ state.display
    · have same : state = result := by simpa [applyOperation,shown] using accepted
      subst result
      intro bid
      simp only [operationCreates,List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (member | rfl)
        · exact member
        · exact shown
    · simp only [applyOperation,shown,↓reduceIte,Option.some.injEq] at accepted
      subst result
      intro bid
      rw [(NotionCoreDisplayOrder.insert_perm _ _ _).mem_iff]
      simp only [List.mem_cons,List.mem_filter,bne_iff_ne,ne_eq,operationCreates,List.not_mem_nil,or_false]
      constructor
      · rintro (rfl | ⟨member,_⟩)
        · exact Or.inr rfl
        · exact Or.inl member
      · rintro (member | rfl)
        · by_cases same : bid = blockName block
          · exact Or.inl same
          · exact Or.inr ⟨member,by simpa using same⟩
        · exact Or.inl rfl
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted
      subst result
      simp [operationCreates,putInstance_display]
  | erase block inst targets =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    simp [operationCreates,putInstance_display]
  | marker block inst id origin =>
    simp only [applyOperation] at accepted
    cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
    | none => simp [selected] at accepted
    | some rows =>
      simp only [selected] at accepted
      dsimp only [Bind.bind, Option.bind] at accepted
      split at accepted
      · contradiction
      · dsimp only at accepted
        split at accepted
        · simp at accepted
          subst result
          simp [operationCreates]
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
        simp [operationCreates]
  | merge source inst stop =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    simp [operationCreates]

/-- Every forest member is displayed. -/
def Covered (state : State) : Prop := ∀ bid ∈ names state.forest, bid ∈ state.display

theorem operation_covered (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) (covered : Covered state) : Covered result := by
  intro bid member
  rcases List.mem_append.mp (operation_names state result op accepted bid member) with old | fresh
  · exact (operation_display state result op accepted bid).mpr (Or.inl (covered bid old))
  · exact (operation_display state result op accepted bid).mpr (Or.inr fresh)

theorem operations_display (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) (covered : Covered state) :
    Covered result ∧
      ∀ bid, bid ∈ result.display ↔ bid ∈ state.display ∨ bid ∈ ops.flatMap operationCreates := by
  induction ops generalizing state with
  | nil =>
    have same : state = result := by simpa [applyOperations] using accepted
    subst result
    simp [covered]
  | cons op rest ih =>
    cases first : applyOperation state op with
    | none => simp [applyOperations,first] at accepted
    | some middle =>
      have later : applyOperations middle rest = some result := by simpa [applyOperations,first] using accepted
      obtain ⟨coveredResult,members⟩ := ih middle later (operation_covered state middle op first covered)
      refine ⟨coveredResult,fun bid => ?_⟩
      rw [members bid,operation_display state middle op first bid]
      simp only [List.flatMap_cons,List.mem_append]
      constructor
      · rintro ((old | fresh) | later)
        · exact Or.inl old
        · exact Or.inr (Or.inl fresh)
        · exact Or.inr (Or.inr later)
      · rintro (old | fresh | later)
        · exact Or.inl (Or.inl old)
        · exact Or.inl (Or.inr fresh)
        · exact Or.inr later

theorem transaction_display (state result : State) (tx : Transaction)
    (accepted : applyTransaction state tx = some result) (covered : Covered state) :
    Covered result ∧ ∀ bid, bid ∈ result.display ↔ bid ∈ state.display ∨
      bid ∈ (NotionCoreCreatorNetwork.createdBlocks tx).map blockName := by
  have translated : (NotionCorePayload.operations tx).flatMap operationCreates =
      (NotionCoreCreatorNetwork.createdBlocks tx).map blockName := by
    cases tx with
    | mk id payload => cases payload <;> simp [NotionCorePayload.operations,operationCreates,
        NotionCoreCreatorNetwork.createdBlocks,List.flatMap_map]
  simpa [translated] using operations_display state result (NotionCorePayload.operations tx) accepted covered

/-- Replayed blocks persist in the display order, merged or not. -/
theorem replay_display (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) (covered : Covered state) :
    Covered result ∧ ∀ bid, bid ∈ result.display ↔ bid ∈ state.display ∨
      ∃ tx ∈ txs, ∃ key ∈ NotionCoreCreatorNetwork.createdBlocks tx, blockName key = bid := by
  induction txs generalizing state with
  | nil =>
    have same : state = result := by simpa [replay] using accepted
    subst result
    simp [covered]
  | cons tx rest ih =>
    cases first : applyTransaction state tx with
    | none => simp [replay,first] at accepted
    | some middle =>
      have later : replay middle rest = some result := by simpa [replay,first] using accepted
      obtain ⟨coveredMiddle,step⟩ := transaction_display state middle tx first covered
      obtain ⟨coveredResult,members⟩ := ih middle later coveredMiddle
      refine ⟨coveredResult,fun bid => ?_⟩
      rw [members bid,step bid]
      simp only [List.mem_map,List.mem_cons]
      aesop

theorem canonical_required_block_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (inst : BlockKey)
    (required : inst ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    blockName inst ∈ state.display := by
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
  exact ((replay_display {} state pre accepted (by simp [Covered,names])).2 (blockName inst)).mpr
    (Or.inr ⟨previous,inPre,inst,transactionEq ▸ born,rfl⟩)

/-- Registered peer receipts specialize an explicitly closed archive version. -/
theorem canonical_required_block (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state) (inst : BlockKey)
    (required : inst ∈ NotionCoreCreatorNetwork.requiredBlocks tx.payload) :
    blockName inst ∈ state.display :=
  canonical_required_block_version network reachable _
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable (NotionCoreCreatorNetwork.payload_reachable reachable)) peer)
    pre suffix tx position state accepted inst required

#print axioms canonical_required_block_version

#print axioms canonical_required_block
#print axioms replay_display
#print axioms operation_kept
end Sal.MRDTs.Instances.NotionCoreMachineBlockPresence
