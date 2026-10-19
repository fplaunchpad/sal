import Sal.MRDTs.Instances.NotionCoreMachineDocument
import Sal.MRDTs.Instances.NotionCoreMachineErase
import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates

/-! Actual erasure commutes with checked slice extraction and display-ordered
source-document materialization. Deletion retains every endpoint and parent;
the output transition is derived, not supplied as a projection equation. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentErase
open NotionCoreMachine
open NotionCoreMachineDocument
open NotionCoreSource (Atom eraseAtom)
open NotionCoreSpec (Address)
open NotionCorePayload (BlockKey Transaction)

@[simp] private theorem erase_address (targets : List Address) (atom : Atom) :
    (eraseAtom targets atom).address = atom.address := rfl

private theorem lookup_erase (targets : List Address) (atoms : List Atom) (address : Address) :
    NotionCorePartition.lookup (atoms.map (eraseAtom targets)) address =
      (NotionCorePartition.lookup atoms address).map (eraseAtom targets) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    by_cases selected : atom.address = address
    · simp [NotionCorePartition.lookup,selected]
    · simpa [NotionCorePartition.lookup,selected] using ih

private theorem extract_erase (targets : List Address) (atoms : List Atom)
    (start : Address) (stop : Option Address) :
    NotionCorePartition.extract (atoms.map (eraseAtom targets)) start stop =
      (NotionCorePartition.extract atoms start stop).map (eraseAtom targets) := by
  have ids : NotionCorePartition.extractIds (atoms.map (eraseAtom targets)) start stop =
      NotionCorePartition.extractIds atoms start stop := by
    simp [NotionCorePartition.extractIds,NotionCorePartition.ids,List.map_map,Function.comp_def]
  simp only [NotionCorePartition.extract,ids]
  generalize NotionCorePartition.extractIds atoms start stop = addresses
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
    cases address with
    | none => simpa using ih
    | some address =>
      simp only [List.filterMap_cons,Option.bind_some]
      rw [lookup_erase]
      cases found : NotionCorePartition.lookup atoms address <;> simp [ih]

private theorem physical_instance (state : State) (key : Nat) (atom : Atom)
    (member : atom ∈ physical state key) : atom.address.1 = key := by
  simp only [physical,NotionCorePhysicalReplay.physical,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨item,member,rfl⟩ <;> rfl

private theorem erase_untargeted (targets : List Address) (atom : Atom)
    (absent : atom.address ∉ targets) : eraseAtom targets atom = atom := by
  have excluded : targets.contains atom.address = false := by simpa using absent
  cases atom with
  | mk address kind =>
    cases kind with
    | split => rfl
    | text value deleted => simp only [eraseAtom,excluded,Bool.or_false]

/-- One fixed global address set describes erasure on every physical
instance; all other instances are unchanged because their names differ. -/
theorem erase_physical_global (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id)
    (accepted : applyOperation state (.erase block inst targets) = some result) :
    ∀ key, physical result key = (physical state key).map
      (eraseAtom (targets.map (NotionCorePhysicalReplay.address (blockName inst)))) := by
  intro key
  rw [(NotionCoreMachineErase.erase_physical state result block inst targets accepted).2.2 key]
  split
  · rename_i same
    rw [same]
  · rename_i distinct
    symm
    conv_rhs => rw [← List.map_id (physical state key)]
    apply List.map_congr_left
    intro atom member
    apply erase_untargeted
    intro selected
    obtain ⟨id,_,equal⟩ := List.mem_map.mp selected
    have instanceEq := congrArg Prod.fst equal
    exact distinct ((physical_instance state key atom member).symm.trans instanceEq.symm)

private theorem put_instance_present (state : State) (inst key : Nat) (value : Instance)
    (present : state.instances.any (fun entry => entry.1 == key) = true) :
    (putInstance state inst value).instances.any (fun entry => entry.1 == key) = true := by
  obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp present
  unfold putInstance
  split
  · apply List.any_eq_true.mpr
    refine ⟨if entry.1 == inst then (inst,value) else entry,List.mem_map.mpr ⟨entry,member,rfl⟩,?_⟩
    split <;> simp_all
  · apply List.any_eq_true.mpr
    exact ⟨entry,List.mem_append_left _ member,equal⟩

/-- Tombstones preserve literal endpoint checks and commute with the actual
raw extraction. Successful old extraction supplies its stored instance. -/
theorem sliceAtoms_erase (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (ref : NotionCoreSliceForest.Ref) (atoms : List Atom)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (extracted : sliceAtoms state ref = some atoms) :
    sliceAtoms result ref = some (atoms.map
      (eraseAtom (targets.map (NotionCorePhysicalReplay.address (blockName inst))))) := by
  let erased := eraseAtom (targets.map (NotionCorePhysicalReplay.address (blockName inst)))
  have oldAny : state.instances.any (fun entry => entry.1 == ref.start.1) = true := by
    by_contra absent
    have no : state.instances.any (fun entry => entry.1 == ref.start.1) = false := Bool.eq_false_iff.mpr absent
    simp [sliceAtoms,no] at extracted
  have resultEq : result = putInstance state (blockName inst)
      ⟨NotionCoreParentErase.erase targets (getInstance state (blockName inst)).rows,
       (getInstance state (blockName inst)).pending ++ targets⟩ := by
    simpa only [applyOperation,Option.some.injEq] using accepted.symm
  have newAny : result.instances.any (fun entry => entry.1 == ref.start.1) = true := by
    rw [resultEq]
    exact put_instance_present state _ _ _ oldAny
  have physicalEq : physical result ref.start.1 = (physical state ref.start.1).map erased :=
    erase_physical_global state result block inst targets accepted ref.start.1
  have idsEq : (physical result ref.start.1).map Atom.address = (physical state ref.start.1).map Atom.address := by
    rw [physicalEq]
    simp [erased,List.map_map,Function.comp_def]
  have extractEq : NotionCorePartition.extract (physical result ref.start.1) ref.start ref.stop =
      (NotionCorePartition.extract (physical state ref.start.1) ref.start ref.stop).map erased := by
    rw [physicalEq]
    exact extract_erase _ _ _ _
  have commute : sliceAtoms result ref = (sliceAtoms state ref).map (List.map erased) := by
    simp only [sliceAtoms,oldAny,newAny,idsEq,extractEq]
    cases first : ((physical state ref.start.1).map Atom.address).contains ref.start <;>
      simp only [Bool.not_false,Bool.not_true,Bool.false_or,Bool.false_eq_true,if_false,if_true]
    · rfl
    · cases ending : ref.stop with
      | none =>
        simp only [Bind.bind,Option.bind]
        split <;> rfl
      | some stop =>
        dsimp only
        cases last : ((physical state ref.start.1).map Atom.address).contains stop <;>
          simp_all only [Bool.false_eq_true,if_false,if_true,Bind.bind,Option.bind]
        · rfl
        · split <;> rfl
  rw [commute,extracted]
  rfl

private theorem mapM_transform {α β : Type} (xs : List α) (f g : α → Option β) (h : β → β)
    (transform : ∀ x value, f x = some value → g x = some (h value))
    (ys : List β) (before : xs.mapM f = some ys) : xs.mapM g = some (ys.map h) := by
  induction xs generalizing ys with
  | nil => simp at before; subst ys; rfl
  | cons head rest ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at before
    | some value =>
      cases later : rest.mapM f with
      | none => simp [List.mapM_cons,first,later] at before
      | some tail =>
        have equal : value :: tail = ys := by simpa [List.mapM_cons,first,later] using before
        subst ys
        have next := transform head value first
        have following := ih tail later
        simp [List.mapM_cons,next,following]

/-- Every slice of a materialized chain undergoes exactly the source erasure;
the block's name, instance and slice starts remain unchanged. -/
theorem materializeBlock_erase (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (stored : NotionCoreSliceForest.Block)
    (source : NotionCoreSource.Block)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (before : materializeBlock state stored = some source) :
    materializeBlock result stored = some (NotionCoreSourceDocument.eraseBlock
      (targets.map (NotionCorePhysicalReplay.address (blockName inst))) source) := by
  obtain ⟨extracted,name,instEq⟩ := materialized_slices state stored source before
  have after : NotionCoreMachineClient.materialize result stored.title = some
      (source.slices.map (NotionCoreSource.eraseSlice
        (targets.map (NotionCorePhysicalReplay.address (blockName inst))))) := by
    unfold NotionCoreMachineClient.materialize at extracted ⊢
    apply mapM_transform _ _ _ _ ?_ _ extracted
    intro ref slice selected
    cases atoms : sliceAtoms state ref with
    | none => simp [atoms] at selected
    | some found =>
      have sliceEq : slice = ⟨ref.start,found,ref.stop⟩ := by simpa [atoms] using selected.symm
      subst slice
      simp [sliceAtoms_erase state result block inst targets ref found accepted atoms,
        NotionCoreSource.eraseSlice]
  cases source
  simp only at name instEq
  subst name instEq
  simp [materializeBlock,after,NotionCoreSourceDocument.eraseBlock]

/-- Successful old materialization itself yields successful new
materialization with every active block erased by the same fixed addresses.
Neither a new materialization equation nor a chosen output doc is assumed. -/
theorem materializeDocument_erase (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (document : NotionCoreSourceDocument.Document)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (before : materializeDocument state = some document) :
    materializeDocument result = some (document.map (NotionCoreSourceDocument.eraseBlock
      (targets.map (NotionCorePhysicalReplay.address (blockName inst))))) := by
  have frames := NotionCoreMachineErase.erase_physical state result block inst targets accepted
  unfold materializeDocument at before ⊢
  rw [frames.2.1]
  apply mapM_transform state.display _ _ _ ?_ document before
  intro bid source extracted
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at extracted
    cases extracted
    rw [materializeEntry_tombstone result bid (by rw [frames.1]; exact found)]
    rfl
  | some stored =>
    rw [materializeEntry_stored state bid stored found] at extracted
    rw [materializeEntry_stored result bid stored (by rw [frames.1]; exact found)]
    exact materializeBlock_erase state result block inst targets stored source accepted extracted

/-- One erase operation per instance group erases every materialized block by
the concatenated addresses of all groups. -/
theorem materializeDocument_erase_groups (state result : State) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id))
    (document : NotionCoreSourceDocument.Document)
    (accepted : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result)
    (before : materializeDocument state = some document) :
    materializeDocument result = some (document.map (NotionCoreSourceDocument.eraseBlock
      (groups.flatMap fun group => group.2.map (NotionCorePhysicalReplay.address (blockName group.1))))) := by
  induction groups generalizing state document with
  | nil =>
    simp only [List.map_nil, applyOperations, Option.some.injEq] at accepted
    subst result
    rw [before]
    congr 1
    conv_lhs => rw [← List.map_id document]
    apply List.map_congr_left
    intro source _
    simp [NotionCoreSourceDocument.eraseBlock,
      show NotionCoreSource.eraseSlice [] = id from funext NotionCoreSource.eraseSlice_nil]
  | cons group rest ih =>
    cases first : applyOperation state (.erase block group.1 group.2) with
    | none => simp [applyOperations, first] at accepted
    | some middle =>
      have later : applyOperations middle (rest.map fun group => .erase block group.1 group.2) =
          some result := by simpa [applyOperations, first] using accepted
      have middleDocument := materializeDocument_erase state middle block group.1 group.2 document
        first before
      rw [ih middle _ later middleDocument]
      simp [List.map_map, Function.comp_def, NotionCoreSourceDocument.eraseBlock_eraseBlock]

/-- Every list of erase operations executes. -/
theorem erase_groups_total (state : State) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id)) :
    ∃ result, applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result := by
  induction groups generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons group rest ih =>
    obtain ⟨result, later⟩ := ih (putInstance state (blockName group.1)
      ⟨NotionCoreParentErase.erase group.2 (getInstance state (blockName group.1)).rows,
        (getInstance state (blockName group.1)).pending ++ group.2⟩)
    exact ⟨result, by simp [applyOperations, applyOperation, later]⟩

/-- Actual erase operation simulates the existing independent source delete
transition, with the after-document constructed from derived materialization. -/
theorem erase_source_step (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (document : NotionCoreSourceDocument.Document)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (before : materializeDocument state = some document) :
    ∃ after, materializeDocument result = some after ∧
      NotionCoreSourceDocument.step document
        (.delete (targets.map (NotionCorePhysicalReplay.address (blockName inst)))) = some after :=
  ⟨_,materializeDocument_erase state result block inst targets document accepted before,rfl⟩

/-- Projecting the derived after-document gives the natural semantic delete
command, rather than defining the sequential specification by machine replay. -/
theorem erase_spec_step (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (document : NotionCoreSourceDocument.Document)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (before : materializeDocument state = some document) :
    (materializeDocument result).map NotionCoreSourceDocument.project =
      NotionCoreSpec.step (NotionCoreSourceDocument.project document)
        (.delete (targets.map (NotionCorePhysicalReplay.address (blockName inst)))) := by
  rw [materializeDocument_erase state result block inst targets document accepted before]
  exact NotionCoreSourceDocument.project_delete document _

/-- One erase operation per instance group simulates one source delete per
group, each step guarded by the unchanged unique display names. -/
theorem erase_groups_execution (state : State) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id))
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (names : (document.map NotionCoreSource.Block.id).Nodup) :
    ∃ result after,
      applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document (groups.map fun group =>
        .delete (group.2.map (NotionCorePhysicalReplay.address (blockName group.1)))) after := by
  induction groups generalizing state document with
  | nil => exact ⟨state,document,rfl,materialized,.nil document⟩
  | cons group rest ih =>
    let middle := putInstance state (blockName group.1)
      ⟨NotionCoreParentErase.erase group.2 (getInstance state (blockName group.1)).rows,
        (getInstance state (blockName group.1)).pending ++ group.2⟩
    have operation : applyOperation state (.erase block group.1 group.2) = some middle := rfl
    have middleDocument := materializeDocument_erase state middle block group.1 group.2 document
      operation materialized
    have middleNames : ((document.map (NotionCoreSourceDocument.eraseBlock
        (group.2.map (NotionCorePhysicalReplay.address (blockName group.1))))).map
          NotionCoreSource.Block.id).Nodup := by
      simpa [List.map_map,Function.comp_def,NotionCoreSourceDocument.eraseBlock] using names
    obtain ⟨result,after,later,projected,run⟩ := ih middle _ middleDocument middleNames
    exact ⟨result,after,by simp [applyOperations,operation,later],projected,
      .cons ⟨names,True.intro⟩ rfl run⟩

/-- Canonical deletion executes an atomic source history update: one delete
per instance group. Every erase operation succeeds, so the old projection is
the only premise used; the source-history guards are derived from replay. -/
theorem canonical_erase_execution_version (network : NotionCorePayloadNetwork.State)
    (_reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (_closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (_position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (block : BlockKey) (groups : List (BlockKey × List NotionRunAllocation.Id))
    (payload : tx.payload = .erase block groups) :
    ∃ result after, applyTransaction state tx = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document (groups.map fun group =>
        .delete (group.2.map (NotionCorePhysicalReplay.address (blockName group.1)))) after := by
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) replayed
  have names : (document.map NotionCoreSource.Block.id).Nodup := by
    rw [materialized_ids state document materialized]
    exact aligned.2.1
  obtain ⟨result,after,operations,projected,run⟩ :=
    erase_groups_execution state block groups document materialized names
  exact ⟨result,after,by simpa [applyTransaction,NotionCorePayload.operations,payload] using operations,
    projected,run⟩

theorem canonical_erase_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (block : BlockKey) (groups : List (BlockKey × List NotionRunAllocation.Id))
    (payload : tx.payload = .erase block groups) :
    ∃ result after, applyTransaction state tx = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document (groups.map fun group =>
        .delete (group.2.map (NotionCorePhysicalReplay.address (blockName group.1)))) after :=
  canonical_erase_execution_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed (NotionCorePayloadNetwork.forget_reachable
      (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix tx position state replayed document materialized block groups payload

#print axioms canonical_erase_execution_version
#print axioms erase_groups_execution
#print axioms canonical_erase_execution

#print axioms sliceAtoms_erase
#print axioms materializeDocument_erase
#print axioms erase_source_step
#print axioms erase_spec_step
#print axioms materializeDocument_erase_groups

namespace SPOT
private def a : NotionRunAllocation.Id := ⟨1,[65]⟩
private def b : NotionRunAllocation.Id := ⟨2,[65]⟩
private def marker : NotionRunAllocation.Id := ⟨3,[65]⟩
private def fixture : State :=
  {instances := [(0,⟨[⟨⟨a,.text 97 false⟩,.start⟩,
      ⟨⟨b,.text 98 false⟩,.item a⟩,⟨⟨marker,.split⟩,.item b⟩],[]⟩)],
   forest := [⟨0,NotionCoreSliceForest.freshTitle 0⟩],display := [0]}
/-- Erasing a parent hides a but retains b. Targeting a split marker retains
that physical marker; this operation never removes endpoints or descendants. -/
theorem hidden_parent_control :
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc))) = some [(0,[98])] ∧
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc))) ≠ some [(0,[])] ∧
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc))) ≠ some [(0,[97,98])] := by decide +kernel

theorem marker_retained_control :
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => doc.flatMap (fun block => block.slices.flatMap fun slice =>
        slice.atoms.map Atom.address))) =
        some [NotionCorePhysicalReplay.address 0 a,NotionCorePhysicalReplay.address 0 b,
          NotionCorePhysicalReplay.address 0 marker] ∧
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => doc.flatMap (fun block => block.slices.flatMap fun slice =>
        slice.atoms.map Atom.address))) ≠
        some [NotionCorePhysicalReplay.address 0 b] := by decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineDocumentErase
