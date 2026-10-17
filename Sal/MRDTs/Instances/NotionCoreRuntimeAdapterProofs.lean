import Sal.MRDTs.Instances.NotionCoreRuntimeAdapter

namespace Sal.MRDTs.Instances.NotionCoreRuntimeAdapter
open NotionCorePartition (Entry)
open NotionCoreMachine (blockName)

open NotionCoreRuntimeState
open NotionCoreStructuralFacts (Fact)
open NotionCorePayload (BlockKey)
open NotionCoreParentMap (Row)
open NotionRunAllocation (Id)

private theorem keyAddress_injective : Function.Injective
    (fun key : NotionCoreRuntimeTypes.ItemKey =>
      NotionCorePhysicalReplay.address (blockName key.1) key.2) := by
  intro a b equal
  have block := NotionCoreMachine.blockName_injective (congrArg Prod.fst equal)
  have item := NotionCorePhysicalReplay.localId_injective (congrArg Prod.snd equal)
  exact Prod.ext block item

theorem recordStarts_unique (state : State) : ((cutEntries state).map Entry.start).Nodup := by
  have createdKeys : (state.created.toList.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact state.created.distinct_keys_toList.imp (fun h => by simpa using h)
  have cutKeys : (state.cuts.toList.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact state.cuts.distinct_keys_toList.imp (fun h => by simpa using h)
  have left : (state.created.toList.map (fun pair => (blockName pair.1,NotionCoreSpec.LocalId.start))).Nodup := by
    have mapped := createdKeys.map (f := fun key : BlockKey => (blockName key,NotionCoreSpec.LocalId.start)) (fun a b equal => NotionCoreMachine.blockName_injective (congrArg Prod.fst equal))
    simpa only [List.map_map,Function.comp_def] using mapped
  have right : (state.cuts.toList.map (fun pair => NotionCorePhysicalReplay.address (blockName pair.1.1) pair.1.2)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using cutKeys.map keyAddress_injective
  have separate : List.Disjoint
      (state.created.toList.map (fun pair => (blockName pair.1,NotionCoreSpec.LocalId.start)))
      (state.cuts.toList.map (fun pair => NotionCorePhysicalReplay.address (blockName pair.1.1) pair.1.2)) := by
    apply List.disjoint_left.mpr
    intro address left right
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp left
    obtain ⟨b,_,equal⟩ := List.mem_map.mp right
    have impossible := congrArg Prod.snd equal
    simp [NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId] at impossible
  simpa [cutEntries,List.map_append,List.map_map,Function.comp_def] using List.nodup_append'.mpr ⟨left,right,separate⟩

@[simp] private theorem filterMap_none {α β : Type} (xs : List α) :
    xs.filterMap (fun _ => (none : Option β)) = [] := by
  induction xs <;> simp [*]

private theorem records_list (facts : List Fact) :
    (NotionCoreStructuralCuts.records facts.toFinset).toFinset =
      (facts.filterMap NotionCoreStructuralCuts.factRecord).toFinset := by
  ext entry
  simp [NotionCoreStructuralCuts.records,List.mem_filterMap]

theorem records_set (state : State) :
    (cutEntries state).toFinset = (NotionCoreStructuralCuts.records (abstract state)).toFinset := by
  rw [abstract,records_list]
  have filtered : (factsList state).filterMap NotionCoreStructuralCuts.factRecord =
      state.cuts.toList.map (fun pair => (⟨blockName pair.2,NotionCorePhysicalReplay.address (blockName pair.1.1) pair.1.2⟩ : Entry)) ++
      state.created.toList.map (fun pair => (⟨blockName pair.1,(blockName pair.1,.start)⟩ : Entry)) := by
    simp [factsList,List.filterMap_map,NotionCoreStructuralCuts.factRecord,Function.comp_def]
  rw [filtered]
  unfold cutEntries
  exact List.toFinset_eq_of_perm _ _ List.perm_append_comm

theorem records_permutation (state : State) :
    (cutEntries state).Perm (NotionCoreStructuralCuts.records (abstract state)) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact List.Nodup.of_map Entry.start (recordStarts_unique state)
  · exact Finset.nodup_toList _
  · exact records_set state

theorem links_permutation (state : State) :
    (creatorLinks state).Perm (NotionCoreStructuralDisplay.linkSet (abstract state)).toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · apply List.Nodup.of_map Prod.fst
    apply List.pairwise_map.mpr
    exact state.created.distinct_keys_toList.imp (fun h => by simpa [creatorLinks] using h)
  · exact Finset.nodup_toList _
  · ext link
    rcases link with ⟨block,after⟩
    simp [Std.HashMap.mem_toList_iff_getElem?_eq_some,creatorLinks,NotionCoreStructuralDisplay.linkSet_membership,abstract,factsList,List.mem_map,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some,Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem births_set (state : State) (inst : BlockKey) :
    (birthsAt state inst).toFinset = NotionCoreStructuralRows.births (abstract state) inst := by
  ext row
  simp [birthsAt,NotionCoreStructuralRows.mem_births,abstract,factsList,List.mem_map,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some,List.mem_filterMap,Prod.exists,
    Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem targets_set (state : State) (inst : BlockKey) :
    (targetsAt state inst).toFinset = NotionCoreStructuralRows.targets (abstract state) inst := by
  ext id
  simp [targetsAt,NotionCoreStructuralRows.mem_targets,abstract,factsList,List.mem_map,Prod.exists,Std.HashSet.mem_toList,List.mem_filterMap,Prod.exists,
    Std.HashSet.mem_toList]

private theorem eraseRow_members (a b : List Id) (same : ∀ id, id ∈ a ↔ id ∈ b) (row : Row) :
    NotionCoreParentErase.eraseRow a row = NotionCoreParentErase.eraseRow b row := by
  rcases row with ⟨⟨id,kind⟩,origin⟩
  cases kind <;> simp [NotionCoreParentErase.eraseRow,NotionCoreParentErase.eraseItem,same]
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

theorem rows_set (state : State) (inst : BlockKey) :
    (rowsAt state inst).toFinset = NotionCoreStructuralRows.rows (abstract state) inst := by
  unfold rowsAt NotionCoreParentErase.erase NotionCoreStructuralRows.rows
  have mapEq : ((birthsAt state inst).map (NotionCoreParentErase.eraseRow (targetsAt state inst))).toFinset =
      (birthsAt state inst).toFinset.image (NotionCoreParentErase.eraseRow (targetsAt state inst)) := by
    ext row; simp
  rw [mapEq,births_set]
  apply Finset.image_congr
  intro row member
  apply eraseRow_members
  intro id
  rw [← targets_set]
  simp

theorem tombstone_eq (state : State) (inst : BlockKey) (row : Row) :
    tombstone state inst row = NotionCoreParentErase.eraseRow (targetsAt state inst) row := by
  have flags : state.erased.contains (inst,row.item.id) = decide (row.item.id ∈ targetsAt state inst) := by
    apply Bool.eq_iff_iff.mpr
    simp [targetsAt,List.mem_filterMap,Prod.exists,Std.HashSet.mem_toList]
  rcases row with ⟨⟨id,kind⟩,origin⟩
  cases kind <;> simp [tombstone,NotionCoreParentErase.eraseRow,NotionCoreParentErase.eraseItem,flags]
  congr 1
  exact decide_eq_decide.mpr Iff.rfl


theorem births_unique (state : State) (keys : RowKeys state) (inst : BlockKey) :
    NotionCoreParentMap.Unique (birthsAt state inst) := by
  have strengthened : state.births.toList.Pairwise (fun a b =>
      a.1 ≠ b.1 ∧ a.2.item.id = a.1.2 ∧ b.2.item.id = b.1.2) := by
    apply state.births.distinct_keys_toList.imp_of_mem
    intro a b ha hb different
    exact ⟨by simpa using different,
      keys a.1.1 a.1.2 a.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp ha),
      keys b.1.1 b.1.2 b.2 (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hb)⟩
  unfold NotionCoreParentMap.Unique birthsAt
  apply List.pairwise_map.mpr
  apply strengthened.filterMap
  intro a b relation row found row' found' equal
  split at found <;> simp_all only [Option.some.injEq,reduceCtorEq]
  split at found' <;> simp_all only [Option.some.injEq,reduceCtorEq]
  apply relation.1
  exact Prod.ext (by simp_all) (relation.2.1.symm.trans relation.2.2)

theorem rows_unique (state : State) (keys : RowKeys state) (inst : BlockKey) :
    NotionCoreParentMap.Unique (rowsAt state inst) :=
  NotionCoreParentErase.erase_unique _ _ (births_unique state keys inst)

theorem birth_lookup (state : State) (keys : RowKeys state) (inst : BlockKey) (id : Id) :
    birthAt state inst id = NotionCoreParentMap.lookup (birthsAt state inst) id := by
  cases found : birthAt state inst id with
  | none =>
    symm
    apply List.find?_eq_none.mpr
    intro row member
    have source : ∃ key : Id, state.births[(inst,key)]? = some row := by
      simpa [birthsAt,List.mem_filterMap,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some] using member
    obtain ⟨key,present⟩ := source
    have named := keys inst key row present
    intro hit
    have same : row.item.id = id := by simpa using hit
    have keyEq : key = id := named.symm.trans same
    rw [keyEq] at present
    change birthAt state inst id = some row at present
    rw [found] at present
    contradiction
  | some row =>
    have source : state.births[(inst,id)]? = some row := found
    have named := keys inst id row source
    have member : row ∈ birthsAt state inst := by
      simp [birthsAt,List.mem_filterMap,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some]
      exact ⟨id,source⟩
    simpa [named] using (NotionCoreParentMap.lookup_member _ row (births_unique state keys inst) member).symm

theorem lookup_rows (state : State) (keys : RowKeys state) (inst : BlockKey) (id : Id) :
    lookupAt state inst id = NotionCoreParentMap.lookup (rowsAt state inst) id := by
  unfold lookupAt rowsAt
  rw [NotionCoreMachineErase.lookup_erase,← birth_lookup state keys]
  apply congrArg (fun f => (birthAt state inst id).map f)
  funext row
  exact tombstone_eq state inst row

theorem buckets_rows (state : State) (buckets : Buckets state) (inst : BlockKey)
    (origin : NotionCoreOriginTree.Origin) :
    childrenAt state inst origin = NotionCoreParentMap.sortedChildren (rowsAt state inst) origin := by
  rw [buckets inst origin]
  simp [rowsAt,NotionCoreParentMap.sortedChildren,NotionCoreMachineErase.childIds_erase]

theorem counts_rows (state : State) (counts : Counts state) (inst : BlockKey) :
    countAt state inst = (rowsAt state inst).length := by
  simpa [rowsAt,NotionCoreParentErase.erase] using counts inst

/-- Concrete keyed storage and retained bucket invariants discharge every
hypothesis of executable query refinement. -/
theorem represents (state : State) (valid : Valid state) :
    NotionCoreRuntimeQuery.Represents (toView state) (abstract state) where
  rowsUnique := rows_unique state valid.1
  rowsSet := rows_set state
  lookupRows := lookup_rows state valid.1
  buckets := buckets_rows state valid.2.1
  count := counts_rows state valid.2.2
  links := links_permutation state
  records := records_permutation state
  recordStartsUnique := recordStarts_unique state

/-- The native hash-map query has the verified structural MRDT's exact answer
for merge-free honest closed-version images. Its premises constrain
storage/protocol, not an observation or a chosen final document. It covers the
merge-free fragment, the scope of the structural renderer. -/
theorem observeState_correct (state : State) (valid : Valid state)
    (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (free : NotionCoreRuntimeQuery.VersionFree network version)
    (image : abstract state = NotionCoreStructuralFacts.ofTransactions
      (NotionCoreReconstruction.transactionsFor network version)) :
    observeState state = NotionCoreStructuralRender.observe (abstract state) := by
  unfold observeState
  rw [image]
  apply NotionCoreRuntimeQuery.observe_correct _ network reachable version closed free
  exact image ▸ represents state valid

#print axioms represents
#print axioms observeState_correct
end Sal.MRDTs.Instances.NotionCoreRuntimeAdapter
