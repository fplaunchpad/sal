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

/-- A materialized block's active atoms undergo exactly the source erasure;
its owner, retained start, and own/attached root shape remain unchanged. -/
theorem materializeBlock_erase (state result : State) (block inst : BlockKey)
    (targets : List NotionRunAllocation.Id) (stored : NotionCoreSliceForest.Block)
    (source : NotionCoreSource.Block)
    (accepted : applyOperation state (.erase block inst targets) = some result)
    (before : materializeBlock state stored = some source) :
    materializeBlock result stored = some (NotionCoreSourceDocument.eraseBlock
      (targets.map (NotionCorePhysicalReplay.address (blockName inst))) source) := by
  cases extracted : sliceAtoms state (NotionCoreSliceForest.active stored.title) with
  | none => simp [materializeBlock,extracted] at before
  | some atoms =>
    have sourceEq : source = ⟨stored.id,if NotionCoreSliceForest.attached stored.title then .attached stored.id else .own,
        ⟨(NotionCoreSliceForest.active stored.title).start,atoms⟩⟩ := by
      simpa [materializeBlock,extracted] using before.symm
    have after := sliceAtoms_erase state result block inst targets _ atoms accepted extracted
    simp [materializeBlock,after,sourceEq,NotionCoreSourceDocument.eraseBlock,NotionCoreSource.eraseSlice]

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
  rw [frames.1]
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none => simp [found] at extracted
  | some stored =>
    have old : materializeBlock state stored = some source := by simpa [found] using extracted
    have changed := materializeBlock_erase state result block inst targets stored source accepted old
    simpa [found] using changed

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

/-- Honest canonical deletion executes an atomic source history update.
The old projection is the only materialization premise; target decoding and
all source-history guards are derived. -/
theorem canonical_erase_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (block inst : BlockKey) (targets : List NotionRunAllocation.Id)
    (payload : tx.payload = .erase block inst targets) :
    ∃ result after, applyTransaction state tx = some result ∧
      materializeDocument result = some after ∧
      NotionCoreSourceDocument.Execution document
        [.delete (targets.map (NotionCorePhysicalReplay.address (blockName inst)))] after := by
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct network reachable peer pre (tx :: suffix) position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans replayed)
  subst checked
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have stored := NotionCoreMachineCreatorPresence.canonical_required_instance network creators
    peer pre suffix tx position state replayed inst
    (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks])
  obtain ⟨result,operation,_⟩ := NotionCoreMachinePartitionUpdates.erase_operation_partitioned
    state block inst targets part stored
  have transaction : applyTransaction state tx = some result := by
    simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,operation]
  obtain ⟨after,projected,stepped⟩ := erase_source_step state result block inst targets document operation materialized
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names]) replayed
  have names : (document.map NotionCoreSource.Block.id).Nodup := by
    rw [materialized_ids state document materialized]
    exact aligned.2.nodup_iff.mpr aligned.1
  exact ⟨result,after,transaction,projected,
    .cons ⟨names,True.intro⟩ stepped (.nil after)⟩

#print axioms canonical_erase_execution

#print axioms sliceAtoms_erase
#print axioms materializeDocument_erase
#print axioms erase_source_step
#print axioms erase_spec_step

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
      (fun doc => doc.flatMap (fun block => block.active.atoms.map Atom.address))) =
        some [NotionCorePhysicalReplay.address 0 a,NotionCorePhysicalReplay.address 0 b,
          NotionCorePhysicalReplay.address 0 marker] ∧
    ((applyOperation fixture (.erase .initial .initial [a,marker]) >>= materializeDocument).map
      (fun doc => doc.flatMap (fun block => block.active.atoms.map Atom.address))) ≠
        some [NotionCorePhysicalReplay.address 0 b] := by decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineDocumentErase
