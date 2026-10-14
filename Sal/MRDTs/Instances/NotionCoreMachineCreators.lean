import Sal.MRDTs.Instances.NotionCoreCreatorNetwork

/-! Retrospective creator provenance for the actual partial machine replay.
Accepted execution is an input; this is not a progress theorem. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineCreators
open NotionCorePayload (BlockKey Transaction Operation)
open NotionCoreMachine
open NotionCoreSliceForest (Block Forest)

def names (forest : Forest) : List Nat := forest.map Block.id

theorem splitForest_names (physical : Nat → List NotionCoreSource.Atom)
    (marker : NotionCoreSpec.Address) (forest result : Forest)
    (accepted : NotionCoreSliceForest.splitForest physical marker forest = some result) :
    names result = names forest := by
  induction forest generalizing result with
  | nil => simp [NotionCoreSliceForest.splitForest] at accepted
  | cons block rest ih =>
    cases found : NotionCoreSliceForest.splitTree physical marker block.title with
    | some title =>
      simp [NotionCoreSliceForest.splitForest, found] at accepted
      subst result; rfl
    | none =>
      simp only [NotionCoreSliceForest.splitForest, found, Option.map_eq_some_iff] at accepted
      obtain ⟨tail, selected, equal⟩ := accepted
      subst result
      change block.id :: names tail = block.id :: names rest
      rw [ih tail selected]

theorem detachForest_names (marker : NotionCoreSpec.Address) (forest result : Forest)
    (child : NotionCoreSliceForest.Tree)
    (accepted : NotionCoreSliceForest.detachForest marker forest = some (result, child)) :
    names result = names forest := by
  induction forest generalizing result child with
  | nil => simp [NotionCoreSliceForest.detachForest] at accepted
  | cons block rest ih =>
    cases found : NotionCoreSliceForest.detachTree marker block.title with
    | some pair =>
      simp [NotionCoreSliceForest.detachForest, found] at accepted
      obtain ⟨equal, moved⟩ := accepted
      subst result; rfl
    | none =>
      simp only [NotionCoreSliceForest.detachForest, found, Option.map_eq_some_iff] at accepted
      obtain ⟨pair, selected, equal⟩ := accepted
      have left := congrArg Prod.fst equal
      dsimp at left
      rw [← left]
      change block.id :: names pair.1 = block.id :: names rest
      rw [ih pair.1 pair.2 selected]

@[simp] theorem appendToBlock_names (bid : Nat) (child : NotionCoreSliceForest.Tree) (forest : Forest) :
    names (NotionCoreSliceForest.appendToBlock bid child forest) = names forest := by
  simp only [names, NotionCoreSliceForest.appendToBlock, List.map_map]
  congr 1
  funext block
  dsimp only [Function.comp_def]
  split <;> rfl

@[simp] theorem putInstance_forest (state : State) (inst : Nat) (value : Instance) :
    (putInstance state inst value).forest = state.forest := by unfold putInstance; split <;> rfl

def operationCreates : Operation → List Nat
  | .create block _ => [blockName block]
  | _ => []

theorem operation_names (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    ∀ bid ∈ names result.forest, bid ∈ names state.forest ++ operationCreates op := by
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
      simp only [apply_ite, putInstance_forest, ite_self] at member
      split at member
      · exact List.mem_append_left _ member
      · simpa [names, operationCreates] using member
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
          simp [operationCreates, equal]
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
        simp [operationCreates, same]

theorem operations_names (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) :
    ∀ bid ∈ names result.forest, bid ∈ names state.forest ++ ops.flatMap operationCreates := by
  induction ops generalizing state with
  | nil =>
      simp [applyOperations] at accepted
      subst result
      simp
  | cons op rest ih =>
      cases first : applyOperation state op with
      | none => simp [applyOperations, first] at accepted
      | some middle =>
          simp [applyOperations, first] at accepted
          intro bid member
          have later := ih middle accepted bid member
          rcases List.mem_append.mp later with old | new
          · have prior := operation_names state middle op first bid old
            rcases List.mem_append.mp prior with old | new
            · exact List.mem_append_left _ old
            · simp only [List.flatMap_cons, List.mem_append]
              exact Or.inr (Or.inl new)
          · simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr (Or.inr new)

def transactionCreates (tx : Transaction) : List Nat :=
  (NotionCoreCreatorNetwork.createdBlocks tx).map blockName

private theorem decoded_creates (tx : Transaction) :
    (NotionCorePayload.operations tx).flatMap operationCreates = transactionCreates tx := by
  cases tx with
  | mk id payload => cases payload <;> simp [NotionCorePayload.operations, operationCreates,
      transactionCreates, NotionCoreCreatorNetwork.createdBlocks]

theorem transaction_names (state result : State) (tx : Transaction)
    (accepted : applyTransaction state tx = some result) :
    ∀ bid ∈ names result.forest, bid ∈ names state.forest ++ transactionCreates tx := by
  simpa only [decoded_creates] using operations_names state result (NotionCorePayload.operations tx) accepted

theorem replay_names (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) :
    ∀ bid ∈ names result.forest, bid ∈ names state.forest ++ txs.flatMap transactionCreates := by
  induction txs generalizing state with
  | nil =>
      simp [replay] at accepted
      subst result
      simp
  | cons tx rest ih =>
      cases first : applyTransaction state tx with
      | none => simp [replay, first] at accepted
      | some middle =>
          simp [replay, first] at accepted
          intro bid member
          have later := ih middle accepted bid member
          rcases List.mem_append.mp later with old | new
          · have prior := transaction_names state middle tx first bid old
            rcases List.mem_append.mp prior with old | new
            · exact List.mem_append_left _ old
            · simp only [List.flatMap_cons, List.mem_append]
              exact Or.inr (Or.inl new)
          · simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr (Or.inr new)

/-- Every actual resulting block has an actual decoder creator in the accepted
transaction sequence. Split and move phases cannot manufacture block IDs. -/
theorem replay_block_creator (txs : List Transaction) (result : State)
    (accepted : replay {} txs = some result) (block : Block) (member : block ∈ result.forest) :
    ∃ tx ∈ txs, ∃ key ∈ NotionCoreCreatorNetwork.createdBlocks tx, block.id = blockName key := by
  have source := replay_names {} result txs accepted block.id (List.mem_map.mpr ⟨block, member, rfl⟩)
  simp only [names, List.map_nil, List.nil_append] at source
  obtain ⟨tx, present, created⟩ := List.mem_flatMap.mp source
  obtain ⟨key, born, equal⟩ := List.mem_map.mp created
  exact ⟨tx, present, key, born, equal.symm⟩

/-- Tie retrospective machine provenance to a received typed transaction list.
The input links transaction membership to receipt, not to creator knowledge. -/
theorem replay_known_creator (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (result : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some result) (block : Block) (member : block ∈ result.forest) :
    ∃ key, block.id = blockName key ∧ NotionCoreCreatorNetwork.KnownCreator network session key := by
  obtain ⟨tx, present, key, created, encoded⟩ := replay_block_creator txs result accepted block member
  obtain ⟨entry, entryMember, same, receipt⟩ := received tx present
  exact ⟨key, encoded, entry, entryMember, same ▸ receipt, same ▸ created⟩


def instanceKeys (state : State) : List Nat := state.instances.map Prod.fst

private theorem putInstance_keys (state : State) (inst : Nat) (value : Instance) :
    ∀ key ∈ instanceKeys (putInstance state inst value), key ∈ instanceKeys state ++ [inst] := by
  unfold putInstance
  split
  · intro key member
    obtain ⟨pair, present, selected⟩ := List.mem_map.mp member
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp present
    split at same
    · subst pair
      simp_all [instanceKeys]
    · subst pair
      exact List.mem_append_left _ (List.mem_map.mpr ⟨old, oldMember, selected⟩)
  · simp [instanceKeys]

def operationInstances : Operation → List Nat
  | .create block _ => [blockName block]
  | .insert _ inst _ _ _ | .erase _ inst _ | .marker _ inst _ _ => [blockName inst]
  | .moveInto _ _ _ _ => []

private theorem operation_instance_keys (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) :
    ∀ key ∈ instanceKeys result, key ∈ instanceKeys state ++ operationInstances op := by
  cases op with
  | create block afterBlock =>
    simp only [applyOperation] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      intro key member
      exact List.mem_append_left _ member
    · simp only [Option.some.injEq] at accepted
      subst result
      simp only [instanceKeys, operationInstances]
      split
      · intro key member
        exact List.mem_append_left _ member
      · exact putInstance_keys state (blockName block) {}
  | insert block inst first origin atoms =>
    simp only [applyOperation] at accepted
    cases selected : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [selected] at accepted
    | some rows =>
      simp [selected] at accepted
      subst result
      exact putInstance_keys state (blockName inst) _
  | erase block inst targets =>
    simp only [applyOperation, Option.some.injEq] at accepted
    subst result
    exact putInstance_keys state (blockName inst) _
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
          exact putInstance_keys state (blockName inst) _
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
        simp [instanceKeys, operationInstances]

private theorem operations_instance_keys (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) :
    ∀ key ∈ instanceKeys result, key ∈ instanceKeys state ++ ops.flatMap operationInstances := by
  induction ops generalizing state with
  | nil => simp [applyOperations] at accepted; subst result; simp
  | cons op rest ih =>
      cases first : applyOperation state op with
      | none => simp [applyOperations, first] at accepted
      | some middle =>
        simp [applyOperations, first] at accepted
        intro key member
        rcases List.mem_append.mp (ih middle accepted key member) with old | new
        · rcases List.mem_append.mp (operation_instance_keys state middle op first key old) with old | new
          · exact List.mem_append_left _ old
          · simp only [List.flatMap_cons, List.mem_append]; exact Or.inr (Or.inl new)
        · simp only [List.flatMap_cons, List.mem_append]; exact Or.inr (Or.inr new)

def usedBlocks (tx : Transaction) : List BlockKey :=
  NotionCoreCreatorNetwork.createdBlocks tx ++ NotionCoreCreatorNetwork.requiredBlocks tx.payload

private theorem decoded_instances (tx : Transaction) :
    ∀ key ∈ (NotionCorePayload.operations tx).flatMap operationInstances,
      key ∈ (usedBlocks tx).map blockName := by
  cases tx with
  | mk id payload => cases payload <;> simp [NotionCorePayload.operations, operationInstances,
      usedBlocks, NotionCoreCreatorNetwork.createdBlocks, NotionCoreCreatorNetwork.requiredBlocks]

private theorem transaction_instance_keys (state result : State) (tx : Transaction)
    (accepted : applyTransaction state tx = some result) :
    ∀ key ∈ instanceKeys result, key ∈ instanceKeys state ++ (usedBlocks tx).map blockName := by
  intro key member
  rcases List.mem_append.mp (operations_instance_keys state result _ accepted key member) with old | new
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (decoded_instances tx key new)

private theorem replay_instance_keys (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) :
    ∀ key ∈ instanceKeys result, key ∈ instanceKeys state ++ txs.flatMap (fun tx => (usedBlocks tx).map blockName) := by
  induction txs generalizing state with
  | nil => simp [replay] at accepted; subst result; simp
  | cons tx rest ih =>
      cases first : applyTransaction state tx with
      | none => simp [replay, first] at accepted
      | some middle =>
        simp [replay, first] at accepted
        intro key member
        rcases List.mem_append.mp (ih middle accepted key member) with old | new
        · rcases List.mem_append.mp (transaction_instance_keys state middle tx first key old) with old | new
          · exact List.mem_append_left _ old
          · simp only [List.flatMap_cons, List.mem_append]; exact Or.inr (Or.inl new)
        · simp only [List.flatMap_cons, List.mem_append]; exact Or.inr (Or.inr new)

theorem replay_instance_used (txs : List Transaction) (result : State)
    (accepted : replay {} txs = some result) (inst : Nat) (member : inst ∈ instanceKeys result) :
    ∃ tx ∈ txs, ∃ key ∈ usedBlocks tx, inst = blockName key := by
  have source := replay_instance_keys {} result txs accepted inst member
  simp only [instanceKeys, List.map_nil, List.nil_append] at source
  obtain ⟨tx, present, inside⟩ := List.mem_flatMap.mp source
  obtain ⟨key, used, equal⟩ := List.mem_map.mp inside
  exact ⟨tx, present, key, used, equal.symm⟩


/-- Every instance touched by an accepted replay has a received creator when
emission carries creator provenance. This includes instances allocated by
insert/erase, not only title instances allocated by create. -/
theorem replay_known_instance_creator (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (result : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some result) (instName : Nat) (member : instName ∈ instanceKeys result) :
    ∃ key, blockName key = instName ∧ NotionCoreCreatorNetwork.KnownCreator network session key := by
  obtain ⟨tx, present, key, used, encoded⟩ := replay_instance_used txs result accepted instName member
  obtain ⟨entry, entryMember, same, receipt⟩ := received tx present
  refine ⟨key, encoded.symm, ?_⟩
  rcases List.mem_append.mp used with created | required
  · exact ⟨entry, entryMember, same ▸ receipt, same ▸ created⟩
  · have required' : key ∈ NotionCoreCreatorNetwork.requiredBlocks entry.tx.payload := same ▸ required
    obtain ⟨provider, providerMember, past, created⟩ :=
      NotionCoreCreatorNetwork.creator_provenance reachable entry entryMember key required'
    have issued := NotionCorePayloadNetwork.forget_reachable
      (NotionCoreCreatorNetwork.payload_reachable reachable)
    have entryRecord : entry.record ∈ (NotionCorePayloadNetwork.forget network).records :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    have receivedRun : entry.record.run ∈ (network.allocation.peers session).received := by
      change NotionCorePayload.reservation entry.tx ∈ (network.allocation.peers session).received
      rw [same]
      exact receipt
    have providerReceived := NotionCoreIssuance.peers_closed issued session entry.record entryRecord
      receivedRun (NotionCorePayload.reservation provider.tx) past
    exact ⟨provider, providerMember, providerReceived, created⟩

private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def cut : Transaction := ⟨⟨3,[66]⟩, .split .initial .initial (.item ⟨1,[65]⟩)⟩
/-- PASS+FAIL: actual replay creates the destination block, whereas its marker
belongs to the inherited initial text instance. No phantom block comes from
bootstrap's first text-item ID. -/
theorem split_creator_control :
    (replay {} [seed,cut]).map (fun state => names state.forest) =
      some [blockName .initial, blockName (.issued cut.id)] ∧
    (replay {} [seed,cut]).map (fun state => names state.forest) ≠
      some [blockName (.issued seed.id), blockName (.issued cut.id)] := by decide

/-- PASS+FAIL: metadata creation contributes a block even when it contributes
no text. Two identical accepted creations do not add another block. -/
theorem duplicate_create_control :
    let tx : Transaction := ⟨⟨1,[66]⟩, .create none⟩
    (replay {} [tx,tx]).map (fun state => names state.forest) = some [blockName (.issued tx.id)] ∧
    (replay {} [tx,tx]).map (fun state => names state.forest) ≠ some [] := by decide

/-- PASS+FAIL: the split marker updates the inherited instance; it does not
allocate a title instance named by bootstrap's first atom. -/
theorem instance_creator_control :
    (replay {} [seed,cut]).map instanceKeys =
      some [blockName .initial, blockName (.issued cut.id)] ∧
    (replay {} [seed,cut]).map instanceKeys ≠
      some [blockName .initial, blockName (.issued seed.id), blockName (.issued cut.id)] := by decide

#print axioms replay_block_creator
#print axioms replay_known_creator
#print axioms replay_known_instance_creator
end Sal.MRDTs.Instances.NotionCoreMachineCreators
