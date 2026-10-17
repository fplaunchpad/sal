import Sal.MRDTs.Instances.NotionCoreRuntimeIndex
import Sal.MRDTs.Instances.NotionCoreStructuralMRDT

/-! Executable indexed query. Hash-map adapters supply direct lookup and origin
bucket callbacks; proof-only row enumeration never occurs in this query. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeQuery
open NotionCorePayload (BlockKey)
open NotionCoreParentMap (Table Row)
open NotionCoreOriginTree (Origin Item)
open NotionRunAllocation (Id)
open NotionCoreStructuralDisplay (Link creatorKey Ascending)
open NotionCorePartition (Entry)
open NotionCoreIncrementalCounterexample (cutRecord cutRecords)
open NotionCoreSource (Atom)

structure View where
  rows : BlockKey → Table
  lookup : BlockKey → Id → Option Row
  bucket : BlockKey → Origin → List Id
  fuel : BlockKey → Nat
  links : List Link
  records : List Entry

def traverse (view : View) (inst : BlockKey) : Nat → Origin → List Item
  | 0, _ => []
  | fuel + 1, origin => (view.bucket inst origin).flatMap fun id =>
      match view.lookup inst id with
      | none => []
      | some row => row.item :: traverse view inst fuel (.item id)

def physical (view : View) (inst : BlockKey) : List Atom :=
  NotionCorePhysicalReplay.physical (NotionCoreMachine.blockName inst)
    (traverse view inst (view.fuel inst) .start)
def physicalName (view : View) (name : Nat) : Option (List Atom) :=
  (NotionCoreMachineClient.decodeBlock name).map (physical view)
def display (view : View) : List Nat :=
  NotionCoreStructuralDisplay.displayLinks []
    (view.links.mergeSort (fun a b => decide (Ascending a b)))
def selectEntry (entries : List Entry) (bid : Nat) : Option Entry :=
  (entries.filter (fun entry => entry.owner == bid && entry.start.1 != bid)).head?.orElse
    (fun _ => (entries.filter (fun entry => entry.owner == bid)).head?)
def activeEntry (view : View) (bid : Nat) : Option Entry := selectEntry view.records bid
def recordText (view : View) (entry : Entry) : Option (List Nat) := do
  let raw ← physicalName view entry.start.1
  let cell ← NotionCorePartition.findCell
    (NotionCoreIncrementalCounterexample.reconstructCells raw
      (NotionCoreStructuralRender.instanceRecords view.records entry.start.1)) entry.start
  pure (cell.slice.atoms.flatMap NotionCoreMachine.atomText)
def blockText (view : View) (bid : Nat) : Option (List Nat) :=
  activeEntry view bid >>= recordText view
def observe (view : View) : Option NotionCoreHistory.View :=
  (display view).mapM fun bid => do pure (bid, ← blockText view bid)

/-- Finite keyed state invariants. These describe stored rows, bucket adjacency,
counts and immutable record enumeration, never a desired document answer. -/
structure Represents (view : View) (facts : NotionCoreStructuralFacts.State) : Prop where
  rowsUnique : ∀ inst, NotionCoreParentMap.Unique (view.rows inst)
  rowsSet : ∀ inst, (view.rows inst).toFinset = NotionCoreStructuralRows.rows facts inst
  lookupRows : ∀ inst id, view.lookup inst id = NotionCoreParentMap.lookup (view.rows inst) id
  buckets : ∀ inst origin, view.bucket inst origin = NotionCoreParentMap.sortedChildren (view.rows inst) origin
  count : ∀ inst, view.fuel inst = (view.rows inst).length
  links : view.links.Perm (NotionCoreStructuralDisplay.linkSet facts).toList
  records : view.records.Perm (NotionCoreStructuralCuts.records facts)
  recordStartsUnique : (view.records.map Entry.start).Nodup

theorem traverse_correct (view : View) (facts : NotionCoreStructuralFacts.State)
    (represented : Represents view facts) (inst : BlockKey) (fuel : Nat) (origin : Origin) :
    traverse view inst fuel origin = NotionCoreParentMap.traverse fuel (view.rows inst) origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
    simp only [traverse,NotionCoreParentMap.traverse,represented.buckets]
    apply congrArg (fun f => (NotionCoreParentMap.sortedChildren (view.rows inst) origin).flatMap f)
    funext id
    rw [represented.lookupRows]
    cases NotionCoreParentMap.lookup (view.rows inst) id <;> simp [ih]

theorem physical_correct (view : View) (facts : NotionCoreStructuralFacts.State)
    (represented : Represents view facts) (inst : BlockKey) :
    physical view inst = NotionCoreStructuralRows.physical facts inst := by
  have nd := List.Nodup.of_map (fun row : Row => row.item.id) (represented.rowsUnique inst)
  have permutation : (view.rows inst).Perm (NotionCoreStructuralRows.rows facts inst).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    simpa using represented.rowsSet inst
  have rightUnique : NotionCoreParentMap.Unique (NotionCoreStructuralRows.rows facts inst).toList :=
    (permutation.map (fun row : Row => row.item.id)).nodup_iff.mp (represented.rowsUnique inst)
  unfold physical NotionCoreStructuralRows.physical
  rw [represented.count,traverse_correct view facts represented]
  rw [permutation.length_eq]
  exact congrArg _ (NotionCoreStructuralRows.traverse_permutation _ _ permutation rightUnique _ _)

theorem physicalName_correct (view : View) (facts : NotionCoreStructuralFacts.State)
    (represented : Represents view facts) (name : Nat) :
    physicalName view name = NotionCoreStructuralRows.physicalName facts name := by
  unfold physicalName NotionCoreStructuralRows.physicalName
  cases NotionCoreMachineClient.decodeBlock name <;> simp [physical_correct view facts represented]

private theorem boundaryAt_member (entries : List Entry) (entry : Entry)
    (unique : (entries.map Entry.start).Nodup) (member : entry ∈ entries) :
    NotionCoreIncrementalCounterexample.boundaryAt entries entry.start = some entry := by
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | inside
    · simp [NotionCoreIncrementalCounterexample.boundaryAt]
    · have different : head.start ≠ entry.start := fun same =>
        nd.1 (List.mem_map.mpr ⟨entry,inside,same.symm⟩)
      simpa [NotionCoreIncrementalCounterexample.boundaryAt,different] using ih nd.2 inside

theorem boundaryAt_permutation (a b : List Entry) (permutation : a.Perm b)
    (unique : (b.map Entry.start).Nodup) (address : NotionCoreSpec.Address) :
    NotionCoreIncrementalCounterexample.boundaryAt a address =
      NotionCoreIncrementalCounterexample.boundaryAt b address := by
  cases found : NotionCoreIncrementalCounterexample.boundaryAt a address with
  | none =>
    symm
    apply List.find?_eq_none.mpr
    intro entry member
    exact List.find?_eq_none.mp found entry (permutation.mem_iff.mpr member)
  | some entry =>
    have named : entry.start = address := by simpa [NotionCoreIncrementalCounterexample.boundaryAt] using List.find?_some found
    have member : entry ∈ b := permutation.mem_iff.mp (List.mem_of_find?_eq_some found)
    simpa [named] using (boundaryAt_member b entry unique member).symm

theorem reconstructCells_permutation (raw : List Atom) (a b : List Entry)
    (permutation : a.Perm b) (unique : (b.map Entry.start).Nodup) :
    NotionCoreIncrementalCounterexample.reconstructCells raw a =
      NotionCoreIncrementalCounterexample.reconstructCells raw b := by
  unfold NotionCoreIncrementalCounterexample.reconstructCells NotionCoreIncrementalCounterexample.orderedRecords
  congr 1
  apply List.filterMap_congr
  intro atom member
  exact boundaryAt_permutation a b permutation unique atom.address

theorem recordText_correct (view : View) (facts : NotionCoreStructuralFacts.State)
    (represented : Represents view facts) (entry : Entry) :
    recordText view entry = NotionCoreStructuralRender.recordText facts entry := by
  have filtered : (NotionCoreStructuralRender.instanceRecords view.records entry.start.1).Perm
      (NotionCoreStructuralRender.instanceRecords (NotionCoreStructuralCuts.records facts) entry.start.1) :=
    by simpa [NotionCoreStructuralRender.instanceRecords] using represented.records.filter (fun item : Entry => item.start.1 == entry.start.1)
  have unique : ((NotionCoreStructuralRender.instanceRecords (NotionCoreStructuralCuts.records facts)
      entry.start.1).map Entry.start).Nodup := by
    have all := (represented.records.map Entry.start).nodup_iff.mp represented.recordStartsUnique
    exact all.sublist ((List.filter_sublist (p := fun item : Entry => item.start.1 == entry.start.1)).map Entry.start)
  unfold recordText NotionCoreStructuralRender.recordText
  rw [physicalName_correct view facts represented]
  cases NotionCoreStructuralRows.physicalName facts entry.start.1 with
  | none => rfl
  | some raw =>
    dsimp only [Bind.bind,Option.bind]
    rw [reconstructCells_permutation raw _ _ filtered unique]

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

private theorem owner_records (entries : List Entry) (state : NotionCoreMachine.State)
    (permutation : entries.Perm (cutRecords state.forest))
    (block : NotionCoreSliceForest.Block)
    (unique : (state.forest.map NotionCoreSliceForest.Block.id).Nodup) (member : block ∈ state.forest) :
    (entries.filter (fun entry => entry.owner == block.id)).Perm (treeRecords block) := by
  have filtered := permutation.filter (fun entry => entry.owner == block.id)
  simpa [filter_records,filter_block state.forest block unique member] using filtered

private theorem selectEntry_normal (entries : List Entry) (block : NotionCoreSliceForest.Block)
    (normal : NotionCoreSliceForest.Normal block.id block.title)
    (ownerPerm : (entries.filter (fun entry => entry.owner == block.id)).Perm (treeRecords block))
    (different : NotionCoreSliceForest.attached block.title = true →
      (NotionCoreSliceForest.active block.title).start.1 ≠ block.id) :
    selectEntry entries block.id = some (cutRecord (block.id,NotionCoreSliceForest.active block.title)) := by
  have foreign : (entries.filter (fun entry => entry.owner == block.id && entry.start.1 != block.id)).Perm
      ((treeRecords block).filter (fun entry => entry.start.1 != block.id)) := by
    simpa [List.filter_filter,Bool.and_comm] using ownerPerm.filter (fun entry => entry.start.1 != block.id)
  cases block with
  | mk bid title =>
    change NotionCoreSliceForest.Normal bid title at normal
    cases normal with
    | own stop =>
      have ownEq : entries.filter (fun entry => entry.owner == bid) =
          [cutRecord (bid,⟨(bid,.start),stop⟩)] := by
        simpa [treeRecords,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren] using ownerPerm
      have foreignEq : entries.filter (fun entry => entry.owner == bid && entry.start.1 != bid) = [] := by
        simpa [treeRecords,cutRecord,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren] using foreign
      simp [selectEntry,ownEq,foreignEq,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
    | attached ref =>
      have diff : ref.start.1 ≠ bid := different rfl
      have foreignEq : entries.filter (fun entry => entry.owner == bid && entry.start.1 != bid) = [cutRecord (bid,ref)] := by
        simpa [treeRecords,cutRecord,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
          NotionCoreSliceForest.titleRef,diff] using foreign
      simp [selectEntry,foreignEq,NotionCoreSliceForest.active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]




/-- The runtime record selector agrees with the structural one on a flat
forest, the merge-free shape in which every block has one active record. -/
theorem activeEntry_correct (view : View) (facts : NotionCoreStructuralFacts.State)
    (represented : Represents view facts) (state : NotionCoreMachine.State)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (flat : NotionCoreStructuralCuts.Flat state.forest)
    (factRecords : (NotionCoreStructuralCuts.records facts).Perm (cutRecords state.forest))
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest) :
    activeEntry view block.id = NotionCoreStructuralRender.activeEntry facts block.id := by
  rw [NotionCoreStructuralRender.activeEntry_actual facts state shape flat factRecords block member]
  apply selectEntry_normal view.records block (flat block member).1
  · exact owner_records view.records state (represented.records.trans factRecords) block shape.2.1 member
  · intro attached
    exact (NotionCoreStructuralCuts.flat_attached state shape flat block member attached).2

local instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy (creatorKey a) (creatorKey b) with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same.symm)
    · exact Or.inr (Or.inl reverse)
local instance : IsTrans Link Ascending where
  trans a b c ab bc :=
    (inferInstance : IsTrans Id NotionCoreSourceInvariant.Desc).trans
      (creatorKey c) (creatorKey b) (creatorKey a) bc ab

/-- Creator sorting uses the same executable mergeSort in the runtime and
structural model. Honest unique creator keys make its order unambiguous. -/
theorem display_correct (view : View) (txs : List NotionCorePayload.Transaction)
    (represented : Represents view (NotionCoreStructuralFacts.ofTransactions txs))
    (ordered : (txs.filterMap NotionCoreStructuralDisplay.creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b))) :
    display view = NotionCoreStructuralDisplay.displayFacts (NotionCoreStructuralFacts.ofTransactions txs) := by
  let canonical := txs.filterMap NotionCoreStructuralDisplay.creation
  have keyUnique : (canonical.map creatorKey).Nodup := by
    apply List.pairwise_map.mpr
    apply ordered.imp
    intro a b before same
    rw [same] at before
    exact NotionCoreSourceInvariant.before_irrefl _ before
  have unique : canonical.Nodup := List.Nodup.of_map creatorKey keyUnique
  have enumeration : view.links.Perm canonical := by
    have links := represented.links
    rw [NotionCoreStructuralDisplay.linkSet_transactions] at links
    exact links.trans (List.toFinset_toList unique)
  have permutation : (view.links.mergeSort (fun a b => decide (Ascending a b))).Perm canonical :=
    (List.mergeSort_perm _ _).trans enumeration
  have sorted : (view.links.mergeSort (fun a b => decide (Ascending a b))).Pairwise Ascending :=
    List.pairwise_mergeSort' Ascending _
  have actualKeys := (permutation.map creatorKey).nodup_iff.mpr keyUnique
  have actualOrdered : (view.links.mergeSort (fun a b => decide (Ascending a b))).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by
    apply (sorted.and (List.pairwise_map.mp actualKeys)).imp
    intro a b both
    rcases both.1 with before | equal
    · exact before
    · exact False.elim (both.2 equal.symm)
  have equal := permutation.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) actualOrdered ordered
  unfold display NotionCoreStructuralDisplay.displayFacts
  rw [NotionCoreStructuralDisplay.orderedLinks_transactions txs ordered,equal]

private theorem option_mapM_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (equal : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have head := equal x (by simp)
    have tail := ih (fun y member => equal y (by simp [member]))
    simp [List.mapM_cons,head,tail]

/-- Every transaction of the closed version carries no merge payload. This is
the scope of the structural renderer; transactions outside the version are
unconstrained. -/
def VersionFree (network : NotionCorePayloadNetwork.State) (version : List NotionRunAllocation.Run) : Prop :=
  ∀ tx ∈ NotionCoreReconstruction.transactionsFor network version, NotionCoreMergeFree.NotMerge tx

theorem versionFree_of_mergeFree (network : NotionCorePayloadNetwork.State)
    (free : NotionCoreMergeFree.MergeFree network) (version : List NotionRunAllocation.Run) :
    VersionFree network version :=
  NotionCoreMergeFree.transactionsFor network free version

/-- A version is merge-free when its transactions are, as a set, the image of
a merge-free list. -/
theorem versionFree_of_image {network : NotionCorePayloadNetwork.State}
    {version : List NotionRunAllocation.Run} {txs : List NotionCorePayload.Transaction}
    (free : ∀ tx ∈ txs, NotionCoreMergeFree.NotMerge tx)
    (image : txs.toFinset = (NotionCoreReconstruction.transactionsFor network version).toFinset) :
    VersionFree network version := by
  intro tx member
  apply free tx
  have : tx ∈ (NotionCoreReconstruction.transactionsFor network version).toFinset := by simpa using member
  rw [← image] at this
  simpa using this

private theorem replay_append (state : NotionCoreMachine.State) (a b : List NotionCorePayload.Transaction) :
    NotionCoreMachine.replay state (a ++ b) =
      (NotionCoreMachine.replay state a >>= fun next => NotionCoreMachine.replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,NotionCoreMachine.replay]
    cases NotionCoreMachine.applyTransaction state tx <;> simp [ih]

/-- Archive-derived cut records of every canonical prefix of a merge-free
closed version, which also keeps every prefix forest flat. -/
theorem records_prefix (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : VersionFree network version)
    (pre suffix : List NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : NotionCoreMachine.replay {} pre = some state) :
    NotionCoreStructuralCuts.Flat state.forest ∧
      cutRecords state.forest = pre.flatMap NotionCoreStructuralCuts.transactionRecords := by
  induction pre using List.reverseRecOn generalizing suffix state with
  | nil =>
    simp [NotionCoreMachine.replay] at accepted
    subst state
    exact ⟨NotionCoreStructuralCuts.flat_nil,rfl⟩
  | append_singleton pre tx ih =>
    have oldPosition : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix := by
      simpa [List.append_assoc] using position
    obtain ⟨old,oldReplay,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version
      network reachable version closed pre (tx::suffix) oldPosition
    have exec : NotionCoreMachine.applyTransaction old tx = some state := by
      simpa [replay_append,oldReplay,NotionCoreMachine.replay] using accepted
    have notMerge := free tx (by rw [oldPosition]; simp)
    obtain ⟨oldFlat,oldRecords⟩ := ih (tx::suffix) oldPosition old oldReplay
    obtain ⟨flatNext,records⟩ := NotionCoreStructuralCuts.canonical_records_step network reachable version
      closed pre suffix tx oldPosition old state oldReplay oldFlat notMerge exec
    refine ⟨flatNext,?_⟩
    rw [records,oldRecords]
    simp

/-- The unordered structural cut records of a merge-free closed version are a
permutation of the actual replay forest's records. -/
theorem records_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : VersionFree network version) :
    ∃ state, NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      (NotionCoreStructuralCuts.records (NotionCoreStructuralFacts.ofTransactions
        (NotionCoreReconstruction.transactionsFor network version))).Perm (cutRecords state.forest) := by
  obtain ⟨state,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  refine ⟨state,accepted,?_⟩
  have actual := (records_prefix network reachable version closed free _ [] (by simp) state accepted).2
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    version closed _ [] (by simp) state accepted
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact Finset.nodup_toList _
  · exact NotionCoreStructuralCuts.cutRecords_nodup state part unique
  · rw [actual]
    exact NotionCoreStructuralCuts.records_ofTransactions _

/-- The structural renderer agrees with reference replay on every merge-free
closed version of an honest network; merges elsewhere in the network do not
enter the version. -/
theorem honest_observe_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : VersionFree network version) :
    NotionCoreStructuralRender.observe (NotionCoreStructuralFacts.ofTransactions
        (NotionCoreReconstruction.transactionsFor network version)) =
      (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
        NotionCoreMachine.render) := by
  obtain ⟨state,accepted,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  obtain ⟨physicalState,physicalReplay,physicalTyped⟩ := NotionCoreStructuralRows.honest_physical network reachable version closed
  have samePhysical := Option.some.inj (physicalReplay.symm.trans accepted)
  subst physicalState
  obtain ⟨cutState,cutReplay,permutation⟩ := records_version network reachable version closed free
  have sameCuts := Option.some.inj (cutReplay.symm.trans accepted)
  subst cutState
  have flat := (records_prefix network reachable version closed free _ [] (by simp) state accepted).1
  have stored := NotionCoreStructuralRender.replay_stored {} state _ accepted free
    (by simp [NotionCoreStructuralRender.Stored])
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network payloadReach
    version closed _ [] (by simp) state accepted
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state _
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  rw [NotionCoreStructuralRender.observe_actual _ state part shape flat stored aligned unique permutation
    (NotionCoreStructuralRows.physicalName_existing _ state accepted _ physicalTyped)
    (NotionCoreStructuralDisplay.honest_display network reachable version state accepted)]
  rw [accepted]
  rfl

/-- Executable callbacks, counts, creation links and cut maps refine the
checked structural renderer on every merge-free honest closed archive version.
Nothing in this computation enumerates a Finset or executes a transaction
interpreter. It covers the merge-free fragment, the scope of the structural
renderer it refines. -/
theorem observe_correct (view : View) (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : VersionFree network version)
    (represented : Represents view (NotionCoreStructuralFacts.ofTransactions
      (NotionCoreReconstruction.transactionsFor network version))) :
    observe view = NotionCoreStructuralRender.observe (NotionCoreStructuralFacts.ofTransactions
      (NotionCoreReconstruction.transactionsFor network version)) := by
  let txs := NotionCoreReconstruction.transactionsFor network version
  let facts := NotionCoreStructuralFacts.ofTransactions txs
  obtain ⟨state,accepted,_,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  obtain ⟨cutsState,cutsReplay,recordsPerm⟩ := records_version network reachable version closed free
  have same := Option.some.inj (cutsReplay.symm.trans accepted)
  subst cutsState
  have flat := (records_prefix network reachable version closed free _ [] (by simp) state accepted).1
  have stored := NotionCoreStructuralRender.replay_stored {} state _ accepted free
    (by simp [NotionCoreStructuralRender.Stored])
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)
  have ordered : (txs.filterMap NotionCoreStructuralDisplay.creation).Pairwise
      (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) := by
    apply NotionCoreStructuralDisplay.creationLinks_ordered _ (NotionCoreReconstruction.transactionsFor_ordered network payloadReach version)
    intro tx member link selected
    apply NotionCoreStructuralDisplay.creation_key tx link ?_ selected
    intro atoms payload
    obtain ⟨entry,published,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx member
    have exactTx := NotionCoreRootCreators.archived_bootstrap network payloadReach entry published atoms (same ▸ payload)
    have txEq : tx = NotionCorePayload.bootstrap atoms := same.symm.trans exactTx
    simp only [txEq,NotionCorePayload.bootstrap]
  unfold observe NotionCoreStructuralRender.observe
  rw [display_correct view txs represented ordered]
  apply option_mapM_congr
  intro bid displayed
  rw [NotionCoreStructuralDisplay.honest_display network reachable version state accepted] at displayed
  obtain ⟨block,member,name⟩ := List.mem_map.mp (stored bid displayed)
  have selected := activeEntry_correct view facts represented state shape flat recordsPerm block member
  have textEq : blockText view bid = NotionCoreStructuralRender.blockText facts bid := by
    unfold blockText NotionCoreStructuralRender.blockText
    rw [← name,selected]
    cases NotionCoreStructuralRender.activeEntry facts block.id with
    | none => rfl
    | some entry => simpa only [Bind.bind,Option.bind] using recordText_correct view facts represented entry
  rw [textEq]

#print axioms display_correct
#print axioms observe_correct
#print axioms honest_observe_version
#print axioms physical_correct
#print axioms recordText_correct
end Sal.MRDTs.Instances.NotionCoreRuntimeQuery
