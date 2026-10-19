import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
import Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress

/-! Whole split/detach/move restores the partition. The containing reference
is cut in two; the moved suffix chain, including the new right reference, is
re-owned by the fresh destination, whose empty title remains represented. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCoreSliceForest
open NotionCoreForestRefs (ownedRefs leftRef rightRef)
open NotionCoreMachinePartition (Partitioned cellRefs)
open NotionCoreMachine

private theorem cellRefs_cut (before after : List NotionCorePartition.Cell)
    (cell : NotionCorePartition.Cell) (marker : Address) (target : Nat) (left right : List Atom) :
    ∃ prefixRefs,
      cellRefs (before ++ cell :: after) = prefixRefs ++
        (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after ∧
      cellRefs (before ++ [⟨cell.owner,⟨cell.slice.start,left,some marker⟩⟩,⟨target,⟨marker,right,cell.slice.stop⟩⟩] ++ after) =
        prefixRefs ++ (cell.owner,⟨cell.slice.start,some marker⟩) ::
          (target,⟨marker,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after := by
  induction before with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons head rest ih =>
    obtain ⟨refs,old,new⟩ := ih
    let endpoint := (rest ++ cell :: after).head?.map (fun next => next.slice.start)
    have same : (rest ++ ([⟨cell.owner,⟨cell.slice.start,left,some marker⟩⟩,⟨target,⟨marker,right,cell.slice.stop⟩⟩] : List NotionCorePartition.Cell) ++ after).head?.map
        (fun next => next.slice.start) = endpoint := by cases rest <;> rfl
    refine ⟨(head.owner,⟨head.slice.start,endpoint⟩) :: refs,?_,?_⟩
    · simp only [List.cons_append,cellRefs,old]
      rfl
    · simp only [List.cons_append,cellRefs,same,new]

private theorem extractIds_cell (before after : List NotionCorePartition.Cell)
    (cell : NotionCorePartition.Cell)
    (unique : ((NotionCorePartition.flatten (before ++ cell :: after)).map Atom.address).Nodup) :
    NotionCorePartition.extractIds (NotionCorePartition.flatten (before ++ cell :: after)) cell.slice.start
      (after.head?.map (fun next => next.slice.start)) = NotionCorePartition.ids cell.slice.atoms := by
  have factor : NotionCorePartition.flatten (before ++ cell :: after) =
      (NotionCorePartition.flatten before ++ NotionCorePartition.boundary cell.slice.start :: cell.slice.atoms) ++
        NotionCorePartition.flatten after := by
    simp [NotionCorePartition.flatten,NotionCorePartition.Cell.physical,List.append_assoc]
  rw [factor] at unique ⊢
  apply NotionCorePartition.extractIds_factor _ _ _ _ _ ?_ unique
  cases after with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | cons next rest => exact Or.inr ⟨next.slice.start,next.slice.atoms ++ NotionCorePartition.flatten rest,rfl,rfl⟩

/-- The actual strict endpoint scan and the physical marker kind recover the
cut inside the represented cell. No selected final cell or suffix is supplied. -/
theorem containing_cell_cut (state : NotionCoreMachine.State) (refs : List Ref)
    (covers : NotionCoreMachinePartition.Covers state refs)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (ref : Ref) (marker : Address) (member : ref ∈ refs)
    (contained : contains (physical state) ref marker = true)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1) :
    ∃ before cell after left right,
      physical state marker.1 = NotionCorePartition.flatten (before ++ cell :: after) ∧
      ref = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩ ∧
      cell.slice.atoms = left ++ NotionCorePartition.boundary marker :: right ∧
      (refs.filter (fun ref => ref.start.1 == marker.1)).Perm
        ((cellRefs (before ++ cell :: after)).map Prod.snd) := by
  obtain ⟨cells,physicalEq,permutation⟩ := covers.partitions ref.start.1 (covers.refsExist ref member)
  have matched := permutation.mem_iff.mp (List.mem_filter.mpr ⟨member,by simp⟩)
  obtain ⟨owned,ownedMember,ownedRef⟩ := List.mem_map.mp matched
  obtain ⟨before,cell,after,shape,equal⟩ := (NotionCoreMachinePartition.cellRefs_member cells owned).mp ownedMember
  have factor := shape ▸ physicalEq
  have conditions : ref.start.1 = marker.1 ∧
      (NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop).contains (some marker) = true := by
    simpa only [contains,Bool.and_eq_true,decide_eq_true_eq] using contained
  have sameInst := conditions.1
  have scanned : some marker ∈ NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop := by
    exact List.contains_iff_mem.mp conditions.2
  have endpoint : ref = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩ := by
    rw [← ownedRef, equal]
  have localUnique : ((NotionCorePartition.flatten (before ++ cell :: after)).map Atom.address).Nodup := by
    rw [← factor]; exact unique ref.start.1
  rw [factor,endpoint,extractIds_cell before after cell localUnique] at scanned
  obtain ⟨atom,atomMember,address⟩ := List.mem_map.mp scanned
  have addressEq : atom.address = marker := Option.some.inj address
  have rawMember : atom ∈ physical state marker.1 := by
    rw [← sameInst,factor]
    apply List.mem_flatMap.mpr
    exact ⟨cell,by simp,by simp [NotionCorePartition.Cell.physical,atomMember]⟩
  have found := NotionCorePartition.lookup_member (physical state marker.1) atom (unique _) rawMember
  have foundMarker := NotionCorePartition.lookup_member (physical state marker.1)
    (NotionCorePartition.boundary marker) (unique _) literal
  rw [addressEq] at found
  have atomEq : atom = NotionCorePartition.boundary marker := Option.some.inj (found.symm.trans foundMarker)
  have markerMember : NotionCorePartition.boundary marker ∈ cell.slice.atoms := atomEq ▸ atomMember
  obtain ⟨left,right,atoms⟩ := List.append_of_mem markerMember
  exact ⟨before,cell,after,left,right,by simpa only [sameInst] using factor,endpoint,atoms,
    by simpa only [shape,sameInst] using permutation⟩

/-- Cutting an interior physical boundary retains the same traversal while
adding exactly the right interval. -/
theorem cut_cells (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (marker : Address) (owner : Nat) (left right : List Atom)
    (atoms : cell.slice.atoms = left ++ NotionCorePartition.boundary marker :: right) :
    let next : List NotionCorePartition.Cell := before ++
      [⟨cell.owner,⟨cell.slice.start,left,some marker⟩⟩,⟨owner,⟨marker,right,cell.slice.stop⟩⟩] ++ after
    NotionCorePartition.flatten next = NotionCorePartition.flatten (before ++ cell :: after) ∧
      ∃ prefixRefs,
        cellRefs (before ++ cell :: after) = prefixRefs ++
          (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after ∧
        cellRefs next = prefixRefs ++ (cell.owner,⟨cell.slice.start,some marker⟩) ::
          (owner,⟨marker,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after := by
  dsimp only
  refine ⟨?_,cellRefs_cut before after cell marker owner left right⟩
  simp [NotionCorePartition.flatten,NotionCorePartition.Cell.physical,atoms,List.append_assoc]

private theorem perm_replace {α : Type} {a b c d : List α} {old : α} (new : List α)
    (permutation : (a ++ old :: b).Perm (c ++ old :: d)) :
    (a ++ new ++ b).Perm (c ++ new ++ d) := by
  have removed : (a ++ b).Perm (c ++ d) :=
    (List.perm_middle.symm.trans (permutation.trans List.perm_middle)).cons_inv
  have shift : ∀ x y : List α, (x ++ new ++ y).Perm (new ++ (x ++ y)) := fun x y => by
    rw [List.append_assoc]
    exact List.perm_append_comm_assoc x new y
  exact (shift a b).trans ((removed.append_left new).trans (shift c d).symm)

/-- Replacing a containing reference by its two halves preserves coverage;
the cut is derived by scanning the marker. Owners play no part. -/
theorem cut_covers (state : NotionCoreMachine.State) (before after : List Ref) (ref : Ref)
    (marker : Address)
    (covers : NotionCoreMachinePartition.Covers state (before ++ ref :: after))
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (contained : contains (physical state) ref marker = true)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1) :
    NotionCoreMachinePartition.Covers state
      (before ++ leftRef ref marker :: rightRef ref marker :: after) := by
  have conditions : ref.start.1 = marker.1 ∧
      (NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop).contains (some marker) = true := by
    simpa only [contains,Bool.and_eq_true,decide_eq_true_eq] using contained
  have sameInst := conditions.1
  have sourceExists := covers.refsExist ref (by simp)
  constructor
  · intro owned member
    simp only [List.mem_append,List.mem_cons] at member
    rcases member with previous | rfl | rfl | later
    · exact covers.refsExist owned (by simp [previous])
    · exact sourceExists
    · simpa only [rightRef,sameInst] using sourceExists
    · exact covers.refsExist owned (by simp [later])
  · intro inst existsInstance
    by_cases same : inst = marker.1
    · subst inst
      obtain ⟨cells,cell,tail,left,right,factor,refEq,atoms,permutation⟩ :=
        containing_cell_cut state _ covers unique ref marker (by simp) contained literal
      obtain ⟨physicalSame,prefixRefs,oldCells,nextCells⟩ := cut_cells cells tail cell marker cell.owner
        left right atoms
      refine ⟨cells ++ [⟨cell.owner,⟨cell.slice.start,left,some marker⟩⟩,⟨cell.owner,⟨marker,right,cell.slice.stop⟩⟩] ++ tail,
        factor.trans physicalSame.symm,?_⟩
      have refSelected : (ref.start.1 == marker.1) = true := by simp [sameInst]
      have leftSelected : ((leftRef ref marker).start.1 == marker.1) = true := by simp [leftRef, sameInst]
      have rightSelected : ((rightRef ref marker).start.1 == marker.1) = true := by simp [rightRef]
      rw [oldCells, List.filter_append, List.filter_cons_of_pos (p := fun ref : Ref => ref.start.1 == marker.1) refSelected,
        List.map_append, List.map_cons] at permutation
      rw [nextCells, List.filter_append, List.filter_cons_of_pos (p := fun ref : Ref => ref.start.1 == marker.1) leftSelected,
        List.filter_cons_of_pos (p := fun ref : Ref => ref.start.1 == marker.1) rightSelected, List.map_append, List.map_cons, List.map_cons]
      have oldRef : ((cell.owner, (⟨cell.slice.start, tail.head?.map (fun next => next.slice.start)⟩ : Ref)) :
          Nat × Ref).2 = ref := refEq.symm
      rw [oldRef] at permutation
      have replaced := perm_replace [leftRef ref marker, rightRef ref marker] permutation
      have leftEq : leftRef ref marker = ⟨cell.slice.start, some marker⟩ := by simp [leftRef, refEq]
      have rightEq : rightRef ref marker = ⟨marker, tail.head?.map (fun next => next.slice.start)⟩ := by
        simp [rightRef, refEq]
      rw [leftEq, rightEq] at replaced ⊢
      simpa [List.append_assoc] using replaced
    · obtain ⟨cells,factor,permutation⟩ := covers.partitions inst existsInstance
      refine ⟨cells,factor,?_⟩
      have absent : (ref.start.1 == inst) = false := by simp [sameInst,Ne.symm same]
      have markerAbsent : (marker.1 == inst) = false := by simp [Ne.symm same]
      simpa [leftRef,rightRef,absent,markerAbsent,List.filter_append,List.filter_cons] using permutation

/-- Actual atomic split progress: partition coverage supplies a containing
reference, and on a chain forest detachment of the fresh right node succeeds. -/
theorem atomicSplit_progress (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) (chains : ∀ block ∈ forest, Chain block.title) (fresh : FreshMarker forest marker)
    (empty : physical target = emptyPhysical target)
    (witness : ∃ block ∈ forest, ∃ ref ∈ preorderTree block.title, contains physical ref marker = true) :
    ∃ result, atomicSplit physical marker target forest = some result := by
  obtain ⟨divided,split⟩ := NotionCoreMachineRouting.splitForest_progress physical marker forest witness
  obtain ⟨before,block,after,pre,ref,post,title,moved,_,_,_,_,_,_,_,detached⟩ :=
    splitForest_detach physical marker forest divided chains fresh split
  rw [atomicSplit_route physical marker target forest empty]
  have pair : splitDetach physical marker forest =
      some (before ++ {block with title := title} :: after, moved) := by
    simp [splitDetach, split, detached]
  rw [pair]
  exact ⟨_, rfl⟩

/-- Exact reference rewriting of an atomic split. The containing reference is
cut; the right half and every reference of the suffix after it change owner to
the fresh destination, behind its empty title root. -/
theorem atomicSplit_refs (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest result : Forest) (chains : ∀ block ∈ forest, Chain block.title)
    (fresh : FreshMarker forest marker) (freshTarget : target ∉ forest.map Block.id)
    (empty : physical target = emptyPhysical target)
    (accepted : atomicSplit physical marker target forest = some result) :
    ∃ before owner pre ref post after,
      ownedRefs (forest ++ [⟨target,freshTitle target⟩]) =
        before ++ (pre ++ ref :: post).map (owner,·) ++ after ++ [(target,titleRef target)] ∧
      contains physical ref marker = true ∧
      ownedRefs result = before ++ (pre ++ [leftRef ref marker]).map (owner,·) ++ after ++
        (target,titleRef target) :: (target,rightRef ref marker) :: post.map (target,·) := by
  obtain ⟨lead,block,tail,pre,ref,post,title,moved,shape,old,inside,_,titleEq,_,movedEq,resultEq⟩ :=
    atomicSplit_result physical marker target forest result chains fresh freshTarget empty accepted
  refine ⟨ownedRefs lead,block.id,pre,ref,post,ownedRefs tail,?_,inside,?_⟩
  · simp [shape,ownedRefs,old,freshTitle,preorderTree,preorderChildren,List.append_assoc]
  · subst resultEq
    simp [ownedRefs,titleEq,preorderTree,preorderChildren,movedEq,List.append_assoc]

/-- Whole atomic split restores every instance's represented endpoint table.
The source interval is recovered from raw physical coverage and actual forest
search; owners of the moved suffix are recomputed from the result forest. -/
theorem atomicSplit_partitioned (state : NotionCoreMachine.State) (forest : Forest)
    (marker : Address) (target : Nat)
    (shape : state.forest = forest ++ [⟨target,freshTitle target⟩])
    (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (chains : ∀ block ∈ forest, Chain block.title) (fresh : FreshMarker forest marker)
    (freshTarget : target ∉ forest.map Block.id)
    (empty : physical state target = emptyPhysical target)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = marker.1)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1)
    (newBoundary : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker) :
    ∃ result, atomicSplit (physical state) marker target forest = some result ∧
      Partitioned {state with forest := result} := by
  have present : marker ∈ (physical state marker.1).map Atom.address :=
    List.mem_map.mpr ⟨NotionCorePartition.boundary marker,literal,rfl⟩
  obtain ⟨block,member,ref,refMember,contained⟩ :=
    NotionCoreMachinePartition.containing_tree_ref state partitioned unique marker existsInstance present newBoundary
  have witness : ∃ block ∈ forest, ∃ ref ∈ preorderTree block.title,
      contains (physical state) ref marker = true := by
    rw [shape] at member
    rcases List.mem_append.mp member with old | newest
    · exact ⟨block,old,ref,refMember,contained⟩
    · have equal := List.mem_singleton.mp newest
      subst block
      have refEq : ref = titleRef target := by simpa [freshTitle,preorderTree,preorderChildren] using refMember
      rw [refEq,empty_title_rejects _ target marker empty] at contained
      contradiction
  obtain ⟨result,executed⟩ := atomicSplit_progress (physical state) marker target forest chains fresh empty witness
  refine ⟨result,executed,?_⟩
  obtain ⟨lead,block,tail,pre,ref,post,title,moved,blocks,old,inside,_,titleEq,_,movedEq,resultEq⟩ :=
    atomicSplit_result (physical state) marker target forest result chains fresh freshTarget empty executed
  have covers := NotionCoreMachinePartition.covers_of_partitioned partitioned
  have oldRefs : forestRefs state.forest = (forestRefs lead ++ pre) ++ ref ::
      (post ++ forestRefs tail ++ [titleRef target]) := by
    rw [shape,blocks]
    simp [forestRefs,old,freshTitle,preorderTree,preorderChildren,List.append_assoc]
  rw [oldRefs] at covers
  have cut := cut_covers state _ _ ref marker covers unique inside literal
  apply NotionCoreMachinePartition.partitioned_of_covers _ _ _ unique
  apply NotionCoreMachinePartition.covers_perm cut
  subst resultEq
  have newRefs : forestRefs ((lead ++ {block with title := title} :: tail) ++
      [⟨target,.node (titleRef target) (.cons moved .nil)⟩]) =
      (forestRefs lead ++ pre) ++ leftRef ref marker ::
        (forestRefs tail ++ titleRef target :: rightRef ref marker :: post) := by
    simp [forestRefs,titleEq,preorderTree,preorderChildren,movedEq,List.append_assoc]
  rw [newRefs]
  refine List.Perm.append_left _ (List.Perm.cons _ ?_)
  have moved : (forestRefs tail ++ titleRef target :: rightRef ref marker :: post).Perm
      (rightRef ref marker :: post ++ (forestRefs tail ++ [titleRef target])) := by
    have step : forestRefs tail ++ titleRef target :: rightRef ref marker :: post =
        (forestRefs tail ++ [titleRef target]) ++ (rightRef ref marker :: post) := by simp
    rw [step]
    exact List.perm_append_comm
  simpa [List.append_assoc] using moved

#print axioms atomicSplit_partitioned
#print axioms atomicSplit_refs
#print axioms containing_cell_cut

namespace SPOT
private def inherited : Address := (10,.event (0,1))
private def marker : Address := (10,.event (0,2))
private def raw (inst : Nat) : List Atom :=
  if inst = 10 then [NotionCorePartition.boundary (10,.start),
    NotionCorePartition.boundary inherited,NotionCorePartition.boundary marker]
  else emptyPhysical inst
private def old : Forest :=
  [⟨10,.node ⟨(10,.start),some inherited⟩ .nil⟩,
   ⟨11,.node (titleRef 11) (.cons (.node ⟨inherited,none⟩ .nil) .nil)⟩]
private def moved : Forest :=
  [⟨10,.node ⟨(10,.start),some inherited⟩ .nil⟩,
   ⟨11,.node (titleRef 11) (.cons (.node ⟨inherited,some marker⟩ .nil) .nil)⟩,
   ⟨12,.node (titleRef 12) (.cons (.node ⟨marker,none⟩ .nil) .nil)⟩]

/-- Hand-derived repeated split: the inherited leaf is shortened, the new
leaf receives owner 12, and both empty title roots remain present. -/
theorem attached_split_control :
    atomicSplit raw marker 12 old = some moved ∧
    atomicSplit raw marker 12 old ≠ some (old ++ [⟨12,freshTitle 12⟩]) := by decide

/-- The tempting intermediate result has two references with owner 11 in
instance 10; only the complete detach/move restores unique ownership. -/
theorem moved_refs_control :
    (ownedRefs moved).filter (fun owned => owned.2.start.1 == 10) =
      [(10,⟨(10,.start),some inherited⟩),(11,⟨inherited,some marker⟩),(12,⟨marker,none⟩)] ∧
    (ownedRefs moved).filter (fun owned => owned.2.start.1 == 10) ≠
      [(10,⟨(10,.start),some inherited⟩),(11,⟨inherited,some marker⟩),(11,⟨marker,none⟩)] := by decide
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
