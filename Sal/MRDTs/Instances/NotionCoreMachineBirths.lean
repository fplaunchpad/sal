import Sal.MRDTs.Instances.NotionCoreMachineCreators

/-! Retrospective located item-birth provenance through actual machine
storage operations. Tombstones do not change identity or birth instance.
Accepted replay is an input; this file does not claim progress. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineBirths
open NotionRunAllocation (Id)
open NotionCorePayload (BlockKey Transaction Operation Birth birthId)
open NotionCoreParentMap (Row Table)
open NotionCoreMachine

def Stored (state : State) (inst : Nat) (id : Id) : Prop :=
  ∃ value, (inst,value) ∈ state.instances ∧ id ∈ value.rows.map (fun row => row.item.id)

theorem getInstance_stored (state : State) (inst : Nat) (id : Id)
    (member : id ∈ (getInstance state inst).rows.map (fun row => row.item.id)) : Stored state inst id := by
  cases found : state.instances.find? (fun pair => pair.1 == inst) with
  | none => simp [getInstance, found] at member
  | some pair =>
      have name : pair.1 = inst := by simpa using List.find?_some found
      have present := List.mem_of_find?_eq_some found
      simp only [getInstance, found, Option.map_some, Option.getD_some] at member
      exact ⟨pair.2, name ▸ present, member⟩

private theorem putInstance_stored (state : State) (inst : Nat) (value : Instance)
    (key : Nat) (id : Id) (member : Stored (putInstance state inst value) key id) :
    Stored state key id ∨ (key = inst ∧ id ∈ value.rows.map (fun row => row.item.id)) := by
  obtain ⟨stored, present, inside⟩ := member
  unfold putInstance at present
  split at present
  · obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp present
    split at equal
    · have pair := Prod.mk.inj equal
      exact Or.inr ⟨pair.1.symm, pair.2 ▸ inside⟩
    · subst old
      exact Or.inl ⟨stored, oldMember, inside⟩
  · rcases List.mem_append.mp present with old | fresh
    · exact Or.inl ⟨stored, old, inside⟩
    · have pair := Prod.mk.inj (List.mem_singleton.mp fresh)
      exact Or.inr ⟨pair.1, pair.2 ▸ inside⟩

private theorem integrate_ids (rows result : Table) (row : Row)
    (accepted : integrate rows row = some result) :
    ∀ id ∈ result.map (fun row => row.item.id), id ∈ rows.map (fun row => row.item.id) ∨ id = row.item.id := by
  unfold integrate at accepted
  cases found : NotionCoreParentMap.lookup rows row.item.id with
  | some old =>
      simp only [found] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst result
        intro id member; exact Or.inl member
      · contradiction
  | none =>
      simp only [found] at accepted
      split at accepted
      · contradiction
      · simp only [Option.some.injEq] at accepted
        subst result
        simp

private theorem integrateRows_ids (rows fresh result : Table)
    (accepted : integrateRows rows fresh = some result) :
    ∀ id ∈ result.map (fun row => row.item.id),
      id ∈ rows.map (fun row => row.item.id) ∨ id ∈ fresh.map (fun row => row.item.id) := by
  induction fresh generalizing rows with
  | nil => simp [integrateRows] at accepted; subst result; simp
  | cons row rest ih =>
      cases first : integrate rows row with
      | none => simp [integrateRows, first] at accepted
      | some middle =>
        simp [integrateRows, first] at accepted
        intro id member
        rcases ih middle accepted id member with old | new
        · rcases integrate_ids rows middle row first id old with old | same
          · exact Or.inl old
          · exact Or.inr (List.mem_cons.mpr (Or.inl same))
        · exact Or.inr (List.mem_cons_of_mem _ new)

def operationAddresses (op : Operation) : List (Nat × Id) :=
  (op.births (fun _ _ => false)).map (fun birth => (blockName birth.1, birthId birth))

private theorem inserted_addresses (block inst : BlockKey) (first : Id)
    (origin : NotionCoreOriginTree.Origin) (atoms : List Nat) (deleted : Id → Bool) (id : Id)
    (member : id ∈ (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms deleted)).map
      (fun row => row.item.id)) :
    (blockName inst, id) ∈ operationAddresses (.insert block inst first origin atoms) := by
  simp only [NotionCorePayload.runRows_ids, NotionCorePayload.textItems_ids] at member
  simp only [operationAddresses, Operation.births, List.map_map, Function.comp_def, birthId]
  change (blockName inst, id) ∈ (NotionCoreParentMap.runRows origin
    (NotionCorePayload.textItems first atoms (fun _ => false))).map (fun row => (blockName inst,row.item.id))
  obtain ⟨offset, present, same⟩ := List.mem_map.mp member
  apply List.mem_map.mpr
  have known : id ∈ (NotionCoreParentMap.runRows origin
      (NotionCorePayload.textItems first atoms (fun _ => false))).map (fun row => row.item.id) := by
    rw [NotionCorePayload.runRows_ids, NotionCorePayload.textItems_ids]
    exact List.mem_map.mpr ⟨offset, present, same⟩
  obtain ⟨row, present, same⟩ := List.mem_map.mp known
  exact ⟨row, present, by simp [same]⟩

private theorem operation_stored (state result : State) (op : Operation)
    (accepted : applyOperation state op = some result) (key : Nat) (id : Id)
    (member : Stored result key id) :
    Stored state key id ∨ (key,id) ∈ operationAddresses op := by
  cases op with
  | create block afterBlock =>
      simp only [applyOperation] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted; subst result; exact Or.inl member
      · simp only [Option.some.injEq] at accepted; subst result
        change Stored (if state.instances.any (fun pair => pair.1 == blockName block)
          then state else putInstance state (blockName block) {}) key id at member
        split at member
        · exact Or.inl member
        · rcases putInstance_stored state (blockName block) {} key id member with old | ⟨_, empty⟩
          · exact Or.inl old
          · simp at empty
  | insert block inst first origin atoms =>
      simp only [applyOperation] at accepted
      cases selected : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
      | none => simp [selected] at accepted
      | some rows =>
          simp [selected] at accepted; subst result
          rcases putInstance_stored state (blockName inst) _ key id member with old | ⟨rfl, inside⟩
          · exact Or.inl old
          · rcases integrateRows_ids _ _ rows selected id inside with old | fresh
            · exact Or.inl (getInstance_stored _ _ _ old)
            · exact Or.inr (inserted_addresses block inst first origin atoms _ id fresh)
  | erase block inst targets =>
      simp only [applyOperation, Option.some.injEq] at accepted; subst result
      rcases putInstance_stored state (blockName inst) _ key id member with old | ⟨rfl, inside⟩
      · exact Or.inl old
      · have previous : id ∈ (getInstance state (blockName inst)).rows.map (fun row => row.item.id) := by
          simpa [NotionCoreParentErase.erase, NotionCoreParentErase.eraseRow,
            List.map_map, Function.comp_def] using inside
        exact Or.inl (getInstance_stored _ _ _ previous)
  | marker block inst marker origin =>
      simp only [applyOperation] at accepted
      cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨marker,.split⟩,origin⟩ with
      | none => simp [selected] at accepted
      | some rows =>
          simp only [selected] at accepted
          dsimp only [Bind.bind, Option.bind] at accepted
          split at accepted
          · contradiction
          · dsimp only at accepted
            split at accepted
            · simp at accepted; subst result
              change Stored (putInstance state (blockName inst)
                {getInstance state (blockName inst) with rows := rows}) key id at member
              rcases putInstance_stored state (blockName inst) _ key id member with old | ⟨rfl, inside⟩
              · exact Or.inl old
              · rcases integrate_ids _ rows _ selected id inside with old | same
                · exact Or.inl (getInstance_stored _ _ _ old)
                · right
                  simpa [operationAddresses, Operation.births, birthId] using same
            · contradiction
  | moveInto block inst marker target =>
      simp only [applyOperation] at accepted
      split at accepted
      · contradiction
      · cases detached : NotionCoreSliceForest.detachForest
          (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
        | none => simp [detached] at accepted
        | some pair => simp [detached] at accepted; subst result; exact Or.inl member
  | merge source target =>
      simp only [applyOperation, Option.some.injEq] at accepted; subst result; exact Or.inl member

private theorem operations_stored (state result : State) (ops : List Operation)
    (accepted : applyOperations state ops = some result) (key : Nat) (id : Id)
    (member : Stored result key id) :
    Stored state key id ∨ (key,id) ∈ ops.flatMap operationAddresses := by
  induction ops generalizing state with
  | nil => simp [applyOperations] at accepted; subst result; exact Or.inl member
  | cons op rest ih =>
      cases first : applyOperation state op with
      | none => simp [applyOperations, first] at accepted
      | some middle =>
          simp [applyOperations, first] at accepted
          rcases ih middle accepted with old | fresh
          · rcases operation_stored state middle op first key id old with old | fresh
            · exact Or.inl old
            · exact Or.inr (List.mem_append_left _ fresh)
          · exact Or.inr (List.mem_append_right _ fresh)

def transactionAddresses (tx : Transaction) : List (Nat × Id) :=
  (NotionCorePayloadNetwork.birthAddresses tx).map (fun address => (blockName address.1,address.2))

private theorem decoded_addresses (tx : Transaction) :
    (NotionCorePayload.operations tx).flatMap operationAddresses = transactionAddresses tx := by
  simp only [transactionAddresses, NotionCorePayloadNetwork.birthAddresses,
    NotionCorePayload.births, List.map_flatMap, List.map_map, Function.comp_def]
  rfl

private theorem transaction_stored (state result : State) (tx : Transaction)
    (accepted : applyTransaction state tx = some result) (key : Nat) (id : Id)
    (member : Stored result key id) : Stored state key id ∨ (key,id) ∈ transactionAddresses tx := by
  simpa only [decoded_addresses] using operations_stored state result _ accepted key id member

private theorem replay_stored (state result : State) (txs : List Transaction)
    (accepted : replay state txs = some result) (key : Nat) (id : Id) (member : Stored result key id) :
    Stored state key id ∨ (key,id) ∈ txs.flatMap transactionAddresses := by
  induction txs generalizing state with
  | nil => simp [replay] at accepted; subst result; exact Or.inl member
  | cons tx rest ih =>
      cases first : applyTransaction state tx with
      | none => simp [replay, first] at accepted
      | some middle =>
          simp [replay, first] at accepted
          rcases ih middle accepted with old | fresh
          · rcases transaction_stored state middle tx first key id old with old | fresh
            · exact Or.inl old
            · exact Or.inr (List.mem_append_left _ fresh)
          · exact Or.inr (List.mem_append_right _ fresh)

/-- Actual stored identities have actual located decoded births, even after
arbitrary accepted duplicate insertions or tombstone updates. -/
theorem replay_row_birth (txs : List Transaction) (result : State)
    (accepted : replay {} txs = some result) (instName : Nat) (row : Row)
    (member : row ∈ (getInstance result instName).rows) :
    ∃ tx ∈ txs, ∃ inst, blockName inst = instName ∧
      (inst,row.item.id) ∈ NotionCorePayloadNetwork.birthAddresses tx := by
  have stored := getInstance_stored result instName row.item.id (List.mem_map.mpr ⟨row, member, rfl⟩)
  rcases replay_stored {} result txs accepted instName row.item.id stored with empty | born
  · simp [Stored] at empty
  · obtain ⟨tx, present, source⟩ := List.mem_flatMap.mp born
    obtain ⟨address, born, equal⟩ := List.mem_map.mp source
    have name := congrArg Prod.fst equal
    have id := congrArg Prod.snd equal
    change address.2 = row.item.id at id
    exact ⟨tx, present, address.1, name, id ▸ born⟩

/-- Finite raw traversal cannot manufacture an item absent from the parent
map. This holds without uniqueness, closure, or increasing-counter guards. -/
theorem traversal_row_member (fuel : Nat) (rows : Table) (origin : NotionCoreOriginTree.Origin)
    (item : NotionCoreOriginTree.Item) (member : item ∈ traversal fuel rows origin) :
    ∃ row ∈ rows, row.item = item := by
  induction fuel generalizing origin with
  | zero => simp [traversal] at member
  | succ fuel ih =>
      simp only [traversal, List.mem_flatMap] at member
      obtain ⟨id, child, present⟩ := member
      cases found : NotionCoreParentMap.lookup rows id with
      | none => simp [found] at present
      | some row =>
          simp only [found, List.mem_cons] at present
          rcases present with same | later
          · exact ⟨row, List.mem_of_find?_eq_some found, same.symm⟩
          · exact ih (.item id) later

/-- Receipt and actual replay storage supply located item knowledge. There is
no free item-provider, birth-tag, graph guard, or desired observation premise. -/
theorem replay_known_item (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (result : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some result) (inst : BlockKey) (id : Id)
    (member : id ∈ (getInstance result (blockName inst)).rows.map (fun row => row.item.id)) :
    NotionCorePayloadNetwork.Known network session (inst,id) := by
  obtain ⟨row, present, sameId⟩ := List.mem_map.mp member
  obtain ⟨tx, txMember, actualInst, name, born⟩ :=
    replay_row_birth txs result accepted (blockName inst) row present
  have sameInst : actualInst = inst := blockName_injective name
  have born' : (inst,id) ∈ NotionCorePayloadNetwork.birthAddresses tx := by
    simpa only [sameInst, sameId] using born
  obtain ⟨entry, entryMember, same, receipt⟩ := received tx txMember
  exact ⟨entry, entryMember, same ▸ receipt, same ▸ born'⟩

theorem replay_known_traversal_item (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (txs : List Transaction) (result : State)
    (received : ∀ tx ∈ txs, ∃ entry ∈ network.entries, entry.tx = tx ∧
      NotionCorePayload.reservation tx ∈ (network.allocation.peers session).received)
    (accepted : replay {} txs = some result) (inst : BlockKey) (fuel : Nat)
    (item : NotionCoreOriginTree.Item)
    (member : item ∈ traversal fuel (getInstance result (blockName inst)).rows .start) :
    NotionCorePayloadNetwork.Known network session (inst,item.id) := by
  obtain ⟨row, present, same⟩ := traversal_row_member fuel _ .start item member
  apply replay_known_item network session txs result received accepted inst item.id
  exact List.mem_map.mpr ⟨row, present, congrArg NotionCoreOriginTree.Item.id same⟩

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def marker : Id := ⟨4,[66]⟩
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def deletion : Transaction := ⟨⟨3,[66]⟩,.erase .initial [(.initial,[b])]⟩
private def cut : Transaction := ⟨marker,.split .initial .initial (.item b)⟩

/-- PASS+FAIL: an actual hidden-origin split retains both text births and its
marker in the inherited instance, rather than dropping the tombstoned parent. -/
theorem hidden_origin_birth_control :
    (replay {} [seed,deletion,cut]).map (fun state => (getInstance state (blockName .initial)).rows) =
      some [⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 true⟩,.item a⟩,⟨⟨marker,.split⟩,.item b⟩] ∧
    (replay {} [seed,deletion,cut]).map (fun state => (getInstance state (blockName .initial)).rows) ≠
      some [⟨⟨a,.text 97 false⟩,.start⟩] := by decide

/-- PASS+FAIL: the split destination's own instance remains physically empty;
the marker is a birth in the inherited instance, not the destination. -/
theorem marker_instance_control :
    (.initial,marker) ∈ NotionCorePayloadNetwork.birthAddresses cut ∧
    (.issued marker,marker) ∉ NotionCorePayloadNetwork.birthAddresses cut ∧
    (replay {} [seed,deletion,cut]).map (fun state => (getInstance state (blockName (.issued marker))).rows) = some [] := by
  exact ⟨by decide, by decide, by decide⟩

#print axioms replay_row_birth
#print axioms traversal_row_member
#print axioms replay_known_item
end Sal.MRDTs.Instances.NotionCoreMachineBirths
