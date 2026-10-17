import Sal.MRDTs.Instances.NotionCoreStructuralCuts
import Sal.MRDTs.Instances.NotionCoreStructuralRows
import Sal.MRDTs.Instances.NotionCoreStructuralDisplay
import Sal.MRDTs.Instances.NotionCoreStructuralActiveText
import Sal.MRDTs.Instances.NotionCoreMachineBlockPresence

/-! Direct interval reconstruction from immutable facts. The actual interpreter
is the theorem's reference only, never called by the new computation. The
reconstruction covers the merge-free fragment: it selects one active record per
block, and the record set alone cannot say which blocks a merge absorbed. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralRender
open NotionCorePayload (BlockKey)
open NotionCoreStructuralFacts (State ofTransactions)
open NotionCoreStructuralCuts (records)
open NotionCoreIncrementalCounterexample (reconstructCells cutRecord cutRecords)
open NotionCorePartition (Cell Entry flatten)
open NotionCoreSource (Atom)

def instanceRecords (entries : List Entry) (inst : Nat) : List Entry :=
  entries.filter (fun entry => entry.start.1 == inst)

noncomputable def cells (facts : State) (inst : BlockKey) : List Cell :=
  reconstructCells (NotionCoreStructuralRows.physical facts inst)
    (instanceRecords (records facts) (NotionCoreMachine.blockName inst))

private theorem cellRefs_records (cells : List Cell) :
    (NotionCoreMachinePartition.cellRefs cells).map cutRecord = cells.map Cell.entry := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [NotionCoreMachinePartition.cellRefs,cutRecord,Cell.entry,ih]

/-- Direct cells equal every represented physical interval of the actual
honest reconstruction. The caller supplies neither owner lists, interval stops,
source structural invariants, replay success nor a desired observation. It
covers the merge-free fragment, where the record owners are exact. -/
theorem honest_cells (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (free : NotionCoreMergeFree.MergeFree network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      ∀ inst : BlockKey,
        (∃ entry ∈ state.instances, entry.1 = NotionCoreMachine.blockName inst) →
        ∃ represented, NotionCoreMachine.physical state (NotionCoreMachine.blockName inst) = flatten represented ∧
          cells (ofTransactions (NotionCoreReconstruction.transactionsFor network version)) inst = represented := by
  obtain ⟨state,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  obtain ⟨rowsState,rowsReplay,physicalEq⟩ := NotionCoreStructuralRows.honest_physical network reachable version closed
  have sameRows := Option.some.inj (rowsReplay.symm.trans accepted)
  subst rowsState
  obtain ⟨cutsState,cutsReplay,recordsEq⟩ := NotionCoreStructuralCuts.honest_records network reachable free version closed
  have sameCuts := Option.some.inj (cutsReplay.symm.trans accepted)
  subst cutsState
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    version closed _ [] (by simp) state accepted
  refine ⟨state,accepted,?_⟩
  intro inst existsInstance
  obtain ⟨represented,physicalFactor,referencePerm⟩ := part.partitions _ existsInstance
  refine ⟨represented,physicalFactor,?_⟩
  have filtered := recordsEq.filter (fun entry => entry.start.1 == NotionCoreMachine.blockName inst)
  have mapped := referencePerm.map cutRecord
  have together : (instanceRecords (records (ofTransactions (NotionCoreReconstruction.transactionsFor network version)))
      (NotionCoreMachine.blockName inst)).Perm (represented.map Cell.entry) := by
    apply filtered.trans
    simpa [instanceRecords,cutRecords,cutRecord,List.filter_map,cellRefs_records] using mapped
  unfold cells
  rw [physicalEq inst,physicalFactor]
  exact NotionCoreIncrementalCounterexample.reconstructCells_correct represented _ together
    (by simpa [physicalFactor] using unique (NotionCoreMachine.blockName inst))


noncomputable def recordText (facts : State) (entry : Entry) : Option (List Nat) := do
  let raw ← NotionCoreStructuralRows.physicalName facts entry.start.1
  let cell ← NotionCorePartition.findCell
    (reconstructCells raw (instanceRecords (records facts) entry.start.1)) entry.start
  pure (cell.slice.atoms.flatMap NotionCoreMachine.atomText)

noncomputable def activeEntry (facts : State) (bid : Nat) : Option Entry :=
  ((records facts).filter (fun entry => entry.owner == bid && entry.start.1 != bid)).head?.orElse
    (fun _ => ((records facts).filter (fun entry => entry.owner == bid)).head?)
noncomputable def blockText (facts : State) (bid : Nat) : Option (List Nat) :=
  activeEntry facts bid >>= recordText facts

/-- Direct reading of one immutable owner/start record recovers the exact
reference interval, including tombstones and retained marker anchors. -/
theorem recordText_ref (facts : State) (state : NotionCoreMachine.State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((NotionCoreMachine.physical state inst).map Atom.address).Nodup)
    (permutation : (records facts).Perm (cutRecords state.forest))
    (physicalEq : ∀ name, (∃ entry ∈ state.instances, entry.1 = name) →
      NotionCoreStructuralRows.physicalName facts name = some (NotionCoreMachine.physical state name))
    (owned : Nat × NotionCoreSliceForest.Ref)
    (member : owned ∈ NotionCoreForestRefs.ownedRefs state.forest) :
    recordText facts (cutRecord owned) =
      (NotionCoreMachine.sliceAtoms state owned.2).map (List.flatMap NotionCoreMachine.atomText) := by
  have existsInstance := part.refsExist owned member
  obtain ⟨all,factor,referencePerm⟩ := part.partitions owned.2.start.1 existsInstance
  have inCells : owned ∈ NotionCoreMachinePartition.cellRefs all :=
    referencePerm.mem_iff.mp (List.mem_filter.mpr ⟨member,by simp⟩)
  obtain ⟨before,cell,after,shape,equal⟩ := (NotionCoreMachinePartition.cellRefs_member all owned).mp inCells
  subst all
  have cellsPerm : (instanceRecords (records facts) owned.2.start.1).Perm ((before ++ cell :: after).map Cell.entry) := by
    have whole := permutation.filter (fun entry => entry.start.1 == owned.2.start.1)
    apply whole.trans
    simpa [instanceRecords,cutRecords,cutRecord,List.filter_map,cellRefs_records] using referencePerm.map cutRecord
  unfold recordText
  dsimp only [cutRecord]
  rw [physicalEq owned.2.start.1 existsInstance,factor]
  have recovered := NotionCoreIncrementalCounterexample.reconstructCells_correct
    (before ++ cell :: after) _ cellsPerm (by simpa [factor] using unique owned.2.start.1)
  simp only [Bind.bind,Option.bind]
  rw [recovered]
  rw [equal]
  have found := NotionCorePartition.findCell_of_member cell cell.slice.start
    (by simpa [factor] using unique owned.2.start.1) (by simp)
    (by simp [NotionCoreSource.Slice.traversal])
  have extracted := NotionCoreMachineSlices.sliceAtoms_cell state before after cell
    (by simpa [equal] using existsInstance) (by simpa [equal] using factor)
    (by simpa [equal] using unique owned.2.start.1)
  simp [found,extracted]


private def treeRecords (block : NotionCoreSliceForest.Block) : List Entry :=
  (NotionCoreSliceForest.preorderTree block.title).map (fun ref => cutRecord (block.id,ref))

private theorem filter_block (forest : NotionCoreSliceForest.Forest) (block : NotionCoreSliceForest.Block)
    (unique : (forest.map NotionCoreSliceForest.Block.id).Nodup) (member : block ∈ forest) :
    forest.filter (fun other => other.id == block.id) = [block] := by
  induction forest with
  | nil => simp at member
  | cons head rest ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | inside
    · have empty : rest.filter (fun other => other.id == block.id) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other member
        simp only [beq_iff_eq]
        intro same
        exact nd.1 (List.mem_map.mpr ⟨other,member,same⟩)
      simp [empty]
    · have distinct : head.id ≠ block.id := fun same =>
        nd.1 (List.mem_map.mpr ⟨block,inside,same.symm⟩)
      simp [distinct,ih nd.2 inside]

private theorem filter_records (forest : NotionCoreSliceForest.Forest) (bid : Nat) :
    (cutRecords forest).filter (fun entry => entry.owner == bid) =
      (forest.filter (fun block => block.id == bid)).flatMap treeRecords := by
  induction forest with
  | nil => rfl
  | cons block rest ih =>
    have own : (treeRecords block).filter (fun entry => entry.owner == bid) =
        if block.id == bid then treeRecords block else [] := by
      by_cases same : block.id = bid <;>
        simp [treeRecords,cutRecord,List.filter_map,same,Function.comp_def]
    have consEq : cutRecords (block :: rest) = treeRecords block ++ cutRecords rest := by
      simp [cutRecords,NotionCoreForestRefs.ownedRefs,treeRecords,List.map_append,List.map_map,Function.comp_def]
    rw [consEq,List.filter_append,own,ih]
    by_cases same : block.id = bid <;> simp [same]

private theorem owner_records (facts : State) (state : NotionCoreMachine.State)
    (permutation : (records facts).Perm (cutRecords state.forest))
    (block : NotionCoreSliceForest.Block)
    (unique : (state.forest.map NotionCoreSliceForest.Block.id).Nodup) (member : block ∈ state.forest) :
    ((records facts).filter (fun entry => entry.owner == block.id)).Perm (treeRecords block) := by
  have filtered := permutation.filter (fun entry => entry.owner == block.id)
  simpa [filter_records,filter_block state.forest block unique member] using filtered

private theorem activeEntry_normal (facts : State) (block : NotionCoreSliceForest.Block)
    (normal : NotionCoreSliceForest.Normal block.id block.title)
    (ownerPerm : ((records facts).filter (fun entry => entry.owner == block.id)).Perm (treeRecords block))
    (different : NotionCoreSliceForest.attached block.title = true →
      (NotionCoreSliceForest.active block.title).start.1 ≠ block.id) :
    activeEntry facts block.id = some (cutRecord (block.id,NotionCoreSliceForest.active block.title)) := by
  have foreign : ((records facts).filter (fun entry => entry.owner == block.id && entry.start.1 != block.id)).Perm
      ((treeRecords block).filter (fun entry => entry.start.1 != block.id)) := by
    simpa [List.filter_filter,Bool.and_comm] using ownerPerm.filter (fun entry => entry.start.1 != block.id)
  cases block with
  | mk bid title =>
    change NotionCoreSliceForest.Normal bid title at normal
    cases normal with
    | own stop =>
      have ownEq : (records facts).filter (fun entry => entry.owner == bid) =
          [cutRecord (bid,⟨(bid,.start),stop⟩)] := by
        simpa [treeRecords,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren] using ownerPerm
      have foreignEq : (records facts).filter (fun entry => entry.owner == bid && entry.start.1 != bid) = [] := by
        simpa [treeRecords,cutRecord,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren] using foreign
      simp [activeEntry,ownEq,foreignEq,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
    | attached ref =>
      have diff : ref.start.1 ≠ bid := different rfl
      have foreignEq : (records facts).filter (fun entry => entry.owner == bid && entry.start.1 != bid) = [cutRecord (bid,ref)] := by
        simpa [treeRecords,cutRecord,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
          NotionCoreSliceForest.titleRef,diff] using foreign
      simp [activeEntry,foreignEq,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]


/-- The direct record selector agrees with the actual active slice. Empty
inactive own-title records remain stored but are never selected for text. The
forest is flat, which is the merge-free shape: a merged block has several
active slices and no single record carries its text. -/
theorem activeEntry_actual (facts : State) (state : NotionCoreMachine.State)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (flat : NotionCoreStructuralCuts.Flat state.forest)
    (permutation : (records facts).Perm (cutRecords state.forest))
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest) :
    activeEntry facts block.id = some (cutRecord (block.id,NotionCoreSliceForest.active block.title)) := by
  apply activeEntry_normal facts block (flat block member).1
  · exact owner_records facts state permutation block shape.2.1 member
  · intro attached
    exact (NotionCoreStructuralCuts.flat_attached state shape flat block member attached).2

/-- The direct selected-record observation equals the actual active interval's
visible text. All endpoints are derived by scanning immutable boundary records.
It holds on the flat, merge-free shape. -/
theorem blockText_active (facts : State) (state : NotionCoreMachine.State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (flat : NotionCoreStructuralCuts.Flat state.forest)
    (unique : ∀ inst, ((NotionCoreMachine.physical state inst).map Atom.address).Nodup)
    (permutation : (records facts).Perm (cutRecords state.forest))
    (physicalEq : ∀ name, (∃ entry ∈ state.instances, entry.1 = name) →
      NotionCoreStructuralRows.physicalName facts name = some (NotionCoreMachine.physical state name))
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest) :
    blockText facts block.id =
      (NotionCoreMachine.sliceAtoms state (NotionCoreSliceForest.active block.title)).map
        (List.flatMap NotionCoreMachine.atomText) := by
  unfold blockText
  rw [activeEntry_actual facts state shape flat permutation block member]
  simp only [Bind.bind,Option.bind]
  apply recordText_ref facts state part unique permutation physicalEq
  apply List.mem_flatMap.mpr
  refine ⟨block,member,List.mem_map.mpr ⟨NotionCoreSliceForest.active block.title,?_,rfl⟩⟩
  have activeMem (bid : Nat) (tree : NotionCoreSliceForest.Tree) (normal : NotionCoreSliceForest.Normal bid tree) :
      NotionCoreSliceForest.active tree ∈ NotionCoreSliceForest.preorderTree tree := by
    cases normal <;> simp [NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.slice,
      NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren]
  exact activeMem block.id block.title (flat block member).1


/-- Whole document observation from structural parent/deletion/cut/create facts.
Creation links alone determine display order; no transaction replay is called. -/
noncomputable def observe (facts : State) : Option (List (Nat × List Nat)) :=
  (NotionCoreStructuralDisplay.displayFacts facts).mapM fun bid => do
    pure (bid, ← blockText facts bid)

private theorem option_mapM_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (equal : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have head := equal x (by simp)
    have tail := ih (fun y member => equal y (by simp [member]))
    simp [List.mapM_cons,head,tail]

/-- Every displayed block is stored in the forest. Only merge removes a block
from the forest, so this holds on the merge-free fragment. -/
def Stored (state : NotionCoreMachine.State) : Prop :=
  ∀ bid ∈ state.display, bid ∈ NotionCoreMachineCreators.names state.forest

theorem operation_stored (state result : NotionCoreMachine.State) (op : NotionCorePayload.Operation)
    (accepted : NotionCoreMachine.applyOperation state op = some result)
    (notMerge : ∀ source target, op ≠ .merge source target) (stored : Stored state) : Stored result := by
  intro bid member
  rcases (NotionCoreMachineBlockPresence.operation_display state result op accepted bid).mp member with old | fresh
  · exact NotionCoreMachineBlockPresence.operation_kept state result op accepted notMerge bid (stored bid old)
  · cases op with
    | create block after =>
      simp only [NotionCoreMachineCreators.operationCreates,List.mem_singleton] at fresh
      subst fresh
      by_cases shown : NotionCoreMachine.blockName block ∈ state.display
      · have same : state = result := by simpa [NotionCoreMachine.applyOperation,shown] using accepted
        subst result
        exact stored _ shown
      · simp only [NotionCoreMachine.applyOperation,shown,↓reduceIte,Option.some.injEq] at accepted
        subst result
        simp only [apply_ite,NotionCoreMachineCreators.putInstance_forest,ite_self,NotionCoreMachineCreators.names]
        split
        · next present =>
          obtain ⟨found,inside,equal⟩ := List.any_eq_true.mp present
          exact List.mem_map.mpr ⟨found,inside,by simpa using equal⟩
        · simp
    | _ => simp [NotionCoreMachineCreators.operationCreates] at fresh

theorem operations_stored (state result : NotionCoreMachine.State) (ops : List NotionCorePayload.Operation)
    (accepted : NotionCoreMachine.applyOperations state ops = some result)
    (notMerge : ∀ op ∈ ops, ∀ source target, op ≠ .merge source target) (stored : Stored state) :
    Stored result := by
  induction ops generalizing state with
  | nil =>
    have same : state = result := by simpa [NotionCoreMachine.applyOperations] using accepted
    exact same ▸ stored
  | cons op rest ih =>
    cases first : NotionCoreMachine.applyOperation state op with
    | none => simp [NotionCoreMachine.applyOperations,first] at accepted
    | some middle =>
      apply ih middle (by simpa [NotionCoreMachine.applyOperations,first] using accepted)
        (fun op' member => notMerge op' (by simp [member]))
      exact operation_stored state middle op first (notMerge op (by simp)) stored

theorem replay_stored (state result : NotionCoreMachine.State) (txs : List NotionCorePayload.Transaction)
    (accepted : NotionCoreMachine.replay state txs = some result)
    (free : ∀ tx ∈ txs, NotionCoreMergeFree.NotMerge tx) (stored : Stored state) : Stored result := by
  induction txs generalizing state with
  | nil =>
    have same : state = result := by simpa [NotionCoreMachine.replay] using accepted
    exact same ▸ stored
  | cons tx rest ih =>
    cases first : NotionCoreMachine.applyTransaction state tx with
    | none => simp [NotionCoreMachine.replay,first] at accepted
    | some middle =>
      apply ih middle (by simpa [NotionCoreMachine.replay,first] using accepted)
        (fun tx' member => free tx' (by simp [member]))
      apply operations_stored state middle _ first _ stored
      intro op member source target equal
      subst equal
      have notMerge := free tx (by simp)
      cases tx with
      | mk id payload =>
        cases payload <;> simp [NotionCorePayload.operations] at member
        exact notMerge _ _ rfl

theorem visible_stored (state : NotionCoreMachine.State) (stored : Stored state) :
    NotionCoreMachine.visible state = state.display := by
  apply List.filter_eq_self.mpr
  intro bid member
  simpa [NotionCoreMachineCreators.names,List.any_eq_true] using stored bid member

/-- The generic observation bridge needs structural completeness, exact physical
rows and create-link order, rather than a supplied desired query answer. The
forest is flat and every displayed block is stored, which is the merge-free
fragment. -/
theorem observe_actual (facts : State) (state : NotionCoreMachine.State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (flat : NotionCoreStructuralCuts.Flat state.forest)
    (stored : Stored state)
    (aligned : NotionCoreMachineDisplay.Aligned state)
    (unique : ∀ inst, ((NotionCoreMachine.physical state inst).map Atom.address).Nodup)
    (permutation : (records facts).Perm (cutRecords state.forest))
    (physicalEq : ∀ name, (∃ entry ∈ state.instances, entry.1 = name) →
      NotionCoreStructuralRows.physicalName facts name = some (NotionCoreMachine.physical state name))
    (displayEq : NotionCoreStructuralDisplay.displayFacts facts = state.display) :
    observe facts = NotionCoreMachine.render state := by
  unfold observe NotionCoreMachine.render
  rw [displayEq,visible_stored state stored]
  apply option_mapM_congr
  intro bid displayed
  obtain ⟨block,member,name⟩ := List.mem_map.mp (stored bid displayed)
  have found := NotionCoreMachineClient.find_block_member state.forest aligned.1 block member
  have titleMember : (block.id,block.title.slice) ∈ NotionCoreForestRefs.ownedRefs state.forest := by
    apply List.mem_flatMap.mpr
    refine ⟨block,member,List.mem_map.mpr ⟨block.title.slice,?_,rfl⟩⟩
    cases block.title; simp [NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.Tree.slice]
  have rootName (id : Nat) (tree : NotionCoreSliceForest.Tree) (normal : NotionCoreSliceForest.Normal id tree) :
      tree.slice.start.1 = id := by cases normal <;> rfl
  have titleExists : state.instances.any (fun entry => entry.1 == block.id) = true := by
    simpa [rootName block.id block.title (flat block member).1] using part.refsExist _ titleMember
  have empty : NotionCoreSliceForest.attached block.title = true →
      NotionCoreMachine.physical state block.id = NotionCoreSliceForest.emptyPhysical block.id := fun attached =>
    (NotionCoreStructuralCuts.flat_attached state shape flat block member attached).1
  have direct := blockText_active facts state part shape flat unique permutation physicalEq block member
  have actual := NotionCoreStructuralActiveText.blockText_active state block found (flat block member).1
    empty (fun _ => titleExists)
  have texts : blockText facts bid = NotionCoreMachine.blockText state bid := by
    rw [← name,direct,actual]
  rw [texts]

/-- Complete closed-version query correspondence, derived only from the
existing honest request/receipt protocol. It covers insertion, retained erasure,
splitting, concurrent late receipt and recursively synthesized closed versions,
on the merge-free fragment: a merge's effect depends on which blocks are alive
when it replays, which an order-free fact query cannot evaluate. -/
theorem honest_observe (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (free : NotionCoreMergeFree.MergeFree network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    observe (ofTransactions (NotionCoreReconstruction.transactionsFor network version)) =
      (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
        NotionCoreMachine.render) := by
  obtain ⟨state,accepted,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  obtain ⟨physicalState,physicalReplay,physicalTyped⟩ := NotionCoreStructuralRows.honest_physical network reachable version closed
  have samePhysical := Option.some.inj (physicalReplay.symm.trans accepted)
  subst physicalState
  obtain ⟨cutState,cutReplay,permutation⟩ := NotionCoreStructuralCuts.honest_records network reachable free version closed
  have sameCuts := Option.some.inj (cutReplay.symm.trans accepted)
  subst cutState
  have flat := (NotionCoreStructuralCuts.honest_records_prefix network reachable free version closed _ []
    (by simp) state accepted).1
  have stored := replay_stored {} state _ accepted (NotionCoreMergeFree.transactionsFor network free version)
    (by simp [Stored])
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network payloadReach
    version closed _ [] (by simp) state accepted
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state _
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  rw [observe_actual _ state part shape flat stored aligned unique permutation
    (NotionCoreStructuralRows.physicalName_existing _ state accepted _ physicalTyped)
    (NotionCoreStructuralDisplay.honest_display network reachable version state accepted)]
  rw [accepted]
  rfl


namespace SPOT
private def low : NotionCorePayload.Transaction :=
  ⟨⟨3,[66]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def high : NotionCorePayload.Transaction :=
  ⟨⟨3,[67]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def splitNetwork : NotionCorePayloadNetwork.State :=
  let copied := NotionCorePayloadNetwork.exchange
    (NotionCorePayloadNetwork.exchange (NotionCorePayloadNetwork.seeded [97,98]) [66] [65]) [67] [65]
  NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.emit copied [66] low.payload low) [67] high.payload high
private def merged : NotionCorePayloadNetwork.State := NotionCorePayloadNetwork.exchange splitNetwork [67] [66]
private def version : List NotionRunAllocation.Run := (merged.allocation.peers [67]).received
private def facts : State := ofTransactions (NotionCoreReconstruction.transactionsFor merged version)

/-- The whole direct query receives the lower-key split late. It preserves the
hand-derived empty high interval and b-owned low interval; it cannot echo the
high replica's former END ownership. -/
theorem late_split_observe_control :
    observe facts = some [(0,[97]),(NotionCoreMachine.blockName (.issued high.id),[]),
      (NotionCoreMachine.blockName (.issued low.id),[98])] ∧
    observe facts ≠ some [(0,[97]),(NotionCoreMachine.blockName (.issued high.id),[98]),
      (NotionCoreMachine.blockName (.issued low.id),[98])] := by
  have splitReach : NotionCoreMachineNetwork.Reach splitNetwork :=
    NotionCoreIncrementalCounterexample.honestly_issuable_splits.2.2
  have reach : NotionCoreMachineNetwork.Reach merged := .exchange [67] [66] splitReach
  have closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget merged).records version :=
    NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reach))) [67]
  have free : NotionCoreMergeFree.MergeFree merged := by
    simp only [merged,splitNetwork,NotionCoreMergeFree.exchange_iff,NotionCoreMergeFree.emit_iff]
    exact ⟨fun _ _ => by simp [high],fun _ _ => by simp [low],NotionCoreMergeFree.seeded _⟩
  have equal := honest_observe merged reach free version closed
  change observe facts = _ at equal
  rw [equal]
  have raw : ((merged.entries.map NotionCorePayloadNetwork.Entry.tx).filter
      (fun tx => NotionCorePayload.reservation tx ∈ version)) =
        [high,low,NotionCorePayload.bootstrap [97,98]] := by decide +kernel
  have ordered : NotionCoreReconstruction.transactionsFor merged version =
      [NotionCorePayload.bootstrap [97,98],low,high] := by
    unfold NotionCoreReconstruction.transactionsFor
    rw [raw]
    have session : ¬ ([67] : List Nat) < [66] := by decide
    simp [session,List.mergeSort,NotionCoreReconstruction.Ascending,NotionCoreSourceInvariant.Desc,
      NotionRunAllocation.Before,low,high,NotionCorePayload.bootstrap]
  rw [ordered]
  decide +kernel

#print axioms late_split_observe_control

private def seed : NotionCorePayload.Transaction := NotionCorePayload.bootstrap [97,98]
private def mergeBack : NotionCorePayload.Transaction := ⟨⟨4,[66]⟩,.merge (.issued low.id) .initial⟩

/-- A merge contributes no structural fact. -/
theorem merge_no_facts (txs : List NotionCorePayload.Transaction) :
    ofTransactions (txs ++ [mergeBack]) = ofTransactions txs := by
  simp [mergeBack,NotionCoreStructuralFacts.decode,NotionCoreStructuralFacts.decodeList,
    NotionCoreStructuralFacts.extra,NotionCorePayload.births,NotionCorePayload.operations,
    NotionCorePayload.Operation.births]

/-- The merge-free scope is forced. Splitting `ab` after `a` and merging the new
block back adds no fact, while replay moves `b` back into the first block; so
no query on the fact set agrees with replay on both archives. -/
theorem merge_outside_scope (query : State → Option (List (Nat × List Nat))) :
    (NotionCoreMachine.replay {} [seed,low] >>= NotionCoreMachine.render) =
      some [(0,[97]),(NotionCoreMachine.blockName (.issued low.id),[98])] ∧
    (NotionCoreMachine.replay {} [seed,low,mergeBack] >>= NotionCoreMachine.render) = some [(0,[97,98])] ∧
    (query (ofTransactions [seed,low]) ≠ (NotionCoreMachine.replay {} [seed,low] >>= NotionCoreMachine.render) ∨
      query (ofTransactions [seed,low,mergeBack]) ≠
        (NotionCoreMachine.replay {} [seed,low,mergeBack] >>= NotionCoreMachine.render)) := by
  have split : (NotionCoreMachine.replay {} [seed,low] >>= NotionCoreMachine.render) =
      some [(0,[97]),(NotionCoreMachine.blockName (.issued low.id),[98])] := by decide +kernel
  have merged : (NotionCoreMachine.replay {} [seed,low,mergeBack] >>= NotionCoreMachine.render) =
      some [(0,[97,98])] := by decide +kernel
  refine ⟨split,merged,?_⟩
  by_contra agree
  rw [not_or,not_not,not_not] at agree
  have same : ofTransactions [seed,low,mergeBack] = ofTransactions [seed,low] :=
    merge_no_facts [seed,low]
  have contra := agree.1.symm.trans (same ▸ agree.2)
  rw [split,merged] at contra
  simp [NotionCoreMachine.blockName] at contra

#print axioms merge_outside_scope

end SPOT

#print axioms observe_actual
#print axioms honest_observe
#print axioms activeEntry_actual
#print axioms blockText_active
#print axioms recordText_ref
#print axioms honest_cells
end Sal.MRDTs.Instances.NotionCoreStructuralRender
