import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
import Sal.MRDTs.Instances.NotionCoreMachineMarkerProgress

/-! Whole split/detach/move restores owner uniqueness after the transient tree
split duplicates its owner's two endpoint references. The raw marker is already
physical, and the fresh destination's empty title must remain represented. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCoreSliceForest
open NotionCoreForestRefs (ownedRefs leftRef rightRef)
open NotionCoreMachinePartition (Partitioned cellRefs)
open NotionCoreMachine

private theorem split_detach_context (physical : Nat → List Atom) (marker : Address)
    (forest divided : Forest) (normal : NormalForest forest) (fresh : FreshMarker forest marker)
    (inactive : ∀ block ∈ forest, attached block.title = true → contains physical (titleRef block.id) marker = false)
    (split : splitForest physical marker forest = some divided) :
    ∃ before source after, forest = before ++ source :: after ∧
      contains physical (active source.title) marker = true ∧
      detachForest marker divided = some
        (before ++ {source with title := cutActive source.title marker} :: after,
         .node ⟨marker,(active source.title).stop⟩ .nil) := by
  induction forest generalizing divided with
  | nil => simp [splitForest] at split
  | cons block rest ih =>
    have headNormal := normal block (by simp)
    have tailNormal : NormalForest rest := fun found member => normal found (List.mem_cons_of_mem _ member)
    have tailFresh : FreshMarker rest marker := fun found member => fresh found (List.mem_cons_of_mem _ member)
    have tailInactive : ∀ found ∈ rest, attached found.title = true → contains physical (titleRef found.id) marker = false :=
      fun found member => inactive found (List.mem_cons_of_mem _ member)
    cases selected : splitTree physical marker block.title with
    | some title =>
      simp only [splitForest,selected,Option.some.injEq] at split
      subst divided
      have detached := splitTree_detach physical block.id block.title title marker headNormal
        (fresh block (by simp)) (inactive block (by simp)) selected
      exact ⟨[],block,rest,rfl,detached.2,by simp [detachForest,detached.1]⟩
    | none =>
      simp only [splitForest,selected,Option.map_eq_some_iff] at split
      obtain ⟨tail,selectedTail,equal⟩ := split
      subst divided
      obtain ⟨before,source,after,shape,contained,detached⟩ :=
        ih tail tailNormal tailFresh tailInactive selectedTail
      have headNone := detach_normal_none block.id block.title marker headNormal (fresh block (by simp))
      exact ⟨block :: before,source,after,by simp [shape],contained,
        by simp [detachForest,headNone,detached]⟩

private theorem append_fresh (forest : Forest) (target : Nat) (child : Tree)
    (fresh : target ∉ forest.map Block.id) :
    appendToBlock target child (forest ++ [⟨target,freshTitle target⟩]) =
      forest ++ [⟨target,appendRoot (freshTitle target) child⟩] := by
  simp only [appendToBlock,List.map_append,List.map_cons,List.map_nil]
  have untouched : forest.map (fun block => if block.id = target then {block with title := appendRoot block.title child} else block) = forest := by
    induction forest with
    | nil => rfl
    | cons block rest ih =>
      have absent : block.id ≠ target ∧ target ∉ rest.map Block.id := by simpa [eq_comm] using fresh
      simp only [List.map_cons,if_neg absent.1]
      rw [ih absent.2]
  simp [untouched]

/-- The moved subtree is a leaf and its old owner/ref are recovered from
literal recursive search and detachment. No chosen output forest is assumed. -/
theorem atomicSplit_context (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) (normal : NormalForest forest) (fresh : FreshMarker forest marker)
    (freshTarget : target ∉ forest.map Block.id)
    (inactive : ∀ block ∈ forest, attached block.title = true → contains physical (titleRef block.id) marker = false)
    (empty : physical target = emptyPhysical target)
    (witness : ∃ block ∈ forest, ∃ ref ∈ preorderTree block.title, contains physical ref marker = true) :
    ∃ before source after, forest = before ++ source :: after ∧
      contains physical (active source.title) marker = true ∧
      atomicSplit physical marker target forest = some
        ((before ++ {source with title := cutActive source.title marker} :: after) ++
          [⟨target,.node (titleRef target) (.cons (.node ⟨marker,(active source.title).stop⟩ .nil) .nil)⟩]) := by
  obtain ⟨divided,split⟩ := NotionCoreMachineRouting.splitForest_progress physical marker forest witness
  obtain ⟨before,source,after,shape,contained,detached⟩ :=
    split_detach_context physical marker forest divided normal fresh inactive split
  have selected : splitDetach physical marker forest = some
      (before ++ {source with title := cutActive source.title marker} :: after,
       .node ⟨marker,(active source.title).stop⟩ .nil) := by simp [splitDetach,split,detached]
  have freshRemaining : target ∉ (before ++ {source with title := cutActive source.title marker} :: after).map Block.id := by
    simpa [shape] using freshTarget
  refine ⟨before,source,after,shape,contained,?_⟩
  rw [atomicSplit_route physical marker target forest empty,selected]
  simp only [Option.map_some,append_fresh _ target _ freshRemaining]
  rfl

/-- Exact endpoint replacement and final reownership, including the fresh
title root already appended to the input forest. The leaf endpoint is moved
past forest-map enumeration; physical cells need only a permutation. -/
theorem atomicSplit_refs (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : Forest) (normal : NormalForest forest) (fresh : FreshMarker forest marker)
    (freshTarget : target ∉ forest.map Block.id)
    (inactive : ∀ block ∈ forest, attached block.title = true → contains physical (titleRef block.id) marker = false)
    (empty : physical target = emptyPhysical target)
    (witness : ∃ block ∈ forest, ∃ ref ∈ preorderTree block.title, contains physical ref marker = true) :
    ∃ result before owner ref after,
      atomicSplit physical marker target forest = some result ∧
      ownedRefs (forest ++ [⟨target,freshTitle target⟩]) = before ++ (owner,ref) :: after ∧
      contains physical ref marker = true ∧
      ownedRefs result = (before ++ (owner,leftRef ref marker) :: after) ++ [(target,rightRef ref marker)] := by
  obtain ⟨lead,source,suffix,shape,contained,executed⟩ :=
    atomicSplit_context physical marker target forest normal fresh freshTarget inactive empty witness
  have sourceMember : source ∈ forest := by rw [shape]; simp
  have sourceNormal := normal source sourceMember
  rcases source with ⟨owner,title⟩
  change Normal owner title at sourceNormal
  cases sourceNormal with
  | own stop =>
    refine ⟨_,ownedRefs lead,owner,⟨(owner,.start),stop⟩,
      ownedRefs suffix ++ [(target,titleRef target)],executed,?_,contained,?_⟩
    all_goals simp [shape,ownedRefs,preorderTree,preorderChildren,active,cutActive,freshTitle,titleRef,leftRef,rightRef,
      Tree.children,Tree.slice,List.append_assoc]
  | attached slice =>
    refine ⟨_,ownedRefs lead ++ [(owner,titleRef owner)],owner,slice,
      ownedRefs suffix ++ [(target,titleRef target)],executed,?_,contained,?_⟩
    all_goals simp [shape,ownedRefs,preorderTree,preorderChildren,active,cutActive,freshTitle,titleRef,leftRef,rightRef,
      Tree.children,Tree.slice,List.append_assoc]

private theorem cellRefs_owners (cells : List NotionCorePartition.Cell) :
    (cellRefs cells).map Prod.fst = cells.map NotionCorePartition.Cell.owner := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [cellRefs,ih]

private theorem replace_perm {α : Type} [DecidableEq α] (a b c d : List α) (old left right : α)
    (permutation : (a ++ old :: b).Perm (c ++ old :: d))
    (uniqueA : (a ++ old :: b).Nodup) (uniqueC : (c ++ old :: d).Nodup) :
    ((a ++ left :: b) ++ [right]).Perm (c ++ left :: right :: d) := by
  have absentA : old ∉ a := fun member =>
    (List.nodup_cons.mp (List.nodup_middle.mp uniqueA)).1 (List.mem_append_left _ member)
  have absentC : old ∉ c := fun member =>
    (List.nodup_cons.mp (List.nodup_middle.mp uniqueC)).1 (List.mem_append_left _ member)
  have erased := permutation.erase old
  rw [List.erase_append_right _ absentA,List.erase_append_right _ absentC] at erased
  simp only [List.erase_cons_head] at erased
  have lifted := ((erased.cons left).cons right)
  have source : ((a ++ left :: b) ++ [right]).Perm (right :: left :: (a ++ b)) :=
    (List.perm_append_comm.append_left []).trans ((List.perm_middle (a := left)).cons right)
  have target : (c ++ left :: right :: d).Perm (right :: left :: (c ++ d)) := by
    have moved : (c ++ left :: right :: d).Perm (left :: (c ++ right :: d)) := List.perm_middle
    exact moved.trans ((List.perm_middle (a := right)).cons left) |>.trans (List.Perm.swap _ _ _)
  exact source.trans (lifted.trans target.symm)

private theorem cellRefs_cut (before after : List NotionCorePartition.Cell)
    (cell : NotionCorePartition.Cell) (marker : Address) (target : Nat) (left right : List Atom) :
    ∃ prefixRefs,
      cellRefs (before ++ cell :: after) = prefixRefs ++
        (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after ∧
      cellRefs (before ++ [⟨cell.owner,⟨cell.slice.start,left⟩⟩,⟨target,⟨marker,right⟩⟩] ++ after) =
        prefixRefs ++ (cell.owner,⟨cell.slice.start,some marker⟩) ::
          (target,⟨marker,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after := by
  induction before with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons head rest ih =>
    obtain ⟨refs,old,new⟩ := ih
    let endpoint := (rest ++ cell :: after).head?.map (fun next => next.slice.start)
    have same : (rest ++ ([⟨cell.owner,⟨cell.slice.start,left⟩⟩,⟨target,⟨marker,right⟩⟩] : List NotionCorePartition.Cell) ++ after).head?.map
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
theorem containing_cell_cut (state : NotionCoreMachine.State) (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (owner : Nat) (ref : Ref) (marker : Address)
    (member : (owner,ref) ∈ ownedRefs state.forest)
    (contained : contains (physical state) ref marker = true)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1) :
    ∃ before cell after left right,
      physical state marker.1 = NotionCorePartition.flatten (before ++ cell :: after) ∧
      (owner,ref) = (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) ∧
      cell.slice.atoms = left ++ NotionCorePartition.boundary marker :: right ∧
      ((before ++ cell :: after).map NotionCorePartition.Cell.owner).Nodup ∧
      ((ownedRefs state.forest).filter (fun owned => owned.2.start.1 == marker.1)).Perm
        (cellRefs (before ++ cell :: after)) := by
  obtain ⟨cells,physicalEq,owners,permutation⟩ := partitioned.partitions ref.start.1
    (partitioned.refsExist (owner,ref) member)
  have matched := permutation.mem_iff.mp (List.mem_filter.mpr ⟨member,by simp⟩)
  obtain ⟨before,cell,after,shape,equal⟩ := (NotionCoreMachinePartition.cellRefs_member cells (owner,ref)).mp matched
  have factor := shape ▸ physicalEq
  have conditions : ref.start.1 = marker.1 ∧
      (NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop).contains (some marker) = true := by
    simpa only [contains,Bool.and_eq_true,decide_eq_true_eq] using contained
  have sameInst := conditions.1
  have scanned : some marker ∈ NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop := by
    exact List.contains_iff_mem.mp conditions.2
  have endpoint : ref = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩ := congrArg Prod.snd equal
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
  exact ⟨before,cell,after,left,right,by simpa only [sameInst] using factor,equal,atoms,shape ▸ owners,
    by simpa only [shape,sameInst] using permutation⟩

/-- Cutting an interior physical boundary retains the same traversal while
adding exactly the freshly reowned right interval. -/
theorem cut_cells (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (marker : Address) (target : Nat) (left right : List Atom)
    (atoms : cell.slice.atoms = left ++ NotionCorePartition.boundary marker :: right)
    (owners : ((before ++ cell :: after).map NotionCorePartition.Cell.owner).Nodup)
    (fresh : target ∉ (before ++ cell :: after).map NotionCorePartition.Cell.owner) :
    let next : List NotionCorePartition.Cell := before ++
      [⟨cell.owner,⟨cell.slice.start,left⟩⟩,⟨target,⟨marker,right⟩⟩] ++ after
    NotionCorePartition.flatten next = NotionCorePartition.flatten (before ++ cell :: after) ∧
      (next.map NotionCorePartition.Cell.owner).Nodup ∧
      ∃ prefixRefs,
        cellRefs (before ++ cell :: after) = prefixRefs ++
          (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after ∧
        cellRefs next = prefixRefs ++ (cell.owner,⟨cell.slice.start,some marker⟩) ::
          (target,⟨marker,after.head?.map (fun next => next.slice.start)⟩) :: cellRefs after := by
  dsimp only
  refine ⟨?_,?_,cellRefs_cut before after cell marker target left right⟩
  · simp [NotionCorePartition.flatten,NotionCorePartition.Cell.physical,atoms,List.append_assoc]
  · have middle : ((before.map NotionCorePartition.Cell.owner ++ [cell.owner]) ++
        target :: after.map NotionCorePartition.Cell.owner).Nodup := by
      apply List.nodup_middle.mpr
      apply List.nodup_cons.mpr
      constructor
      · simpa [List.map_append,List.map_cons,List.append_assoc] using fresh
      · simpa [List.map_append,List.map_cons,List.append_assoc] using owners
    simpa [List.map_append,List.map_cons,List.append_assoc] using middle

/-- Exact reference substitution follows from uniqueness and the old
permutation; it does not assume the desired next endpoint table. -/
theorem cut_refs_permutation (beforeRefs afterRefs : List (Nat × Ref))
    (before after : List NotionCorePartition.Cell) (cell : NotionCorePartition.Cell)
    (marker : Address) (target : Nat) (left right : List Atom)
    (permutation : (beforeRefs ++
      (cell.owner,⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩) :: afterRefs).Perm
      (cellRefs (before ++ cell :: after)))
    (owners : ((before ++ cell :: after).map NotionCorePartition.Cell.owner).Nodup) :
    ((beforeRefs ++ (cell.owner,(⟨cell.slice.start,some marker⟩ : Ref)) :: afterRefs) ++
      [(target,(⟨marker,after.head?.map (fun next => next.slice.start)⟩ : Ref))]).Perm
      (cellRefs (before ++ ([⟨cell.owner,⟨cell.slice.start,left⟩⟩,⟨target,⟨marker,right⟩⟩] : List NotionCorePartition.Cell) ++ after)) := by
  obtain ⟨prefixRefs,old,next⟩ := cellRefs_cut before after cell marker target left right
  have unique : (cellRefs (before ++ cell :: after)).Nodup := by
    apply List.Nodup.of_map Prod.fst
    rw [cellRefs_owners]
    exact owners
  rw [old] at permutation unique
  rw [next]
  exact replace_perm beforeRefs afterRefs prefixRefs (cellRefs after) _ _ _ permutation
    (permutation.nodup_iff.mpr unique) unique

/-- Reference replacement is sufficient to restore the complete physical
partition; the cut and the moved interval are derived by scanning the marker. -/
theorem reference_cut_partitioned (state : NotionCoreMachine.State) (result : Forest)
    (marker : Address) (target owner : Nat) (ref : Ref)
    (beforeRefs afterRefs : List (Nat × Ref))
    (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (old : ownedRefs state.forest = beforeRefs ++ (owner,ref) :: afterRefs)
    (next : ownedRefs result = (beforeRefs ++ (owner,leftRef ref marker) :: afterRefs) ++
      [(target,rightRef ref marker)])
    (contained : contains (physical state) ref marker = true)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1)
    (fresh : ∀ owned ∈ ownedRefs state.forest, owned.2.start.1 = marker.1 → owned.1 ≠ target) :
    Partitioned {state with forest := result} := by
  have conditions : ref.start.1 = marker.1 ∧
      (NotionCorePartition.extractIds (physical state ref.start.1) ref.start ref.stop).contains (some marker) = true := by
    simpa only [contains,Bool.and_eq_true,decide_eq_true_eq] using contained
  have sameInst := conditions.1
  have selected : (owner,ref) ∈ ownedRefs state.forest := by rw [old]; simp
  have sourceExists := partitioned.refsExist (owner,ref) selected
  constructor
  · intro owned member
    rw [next] at member
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((previous | rfl | later) | rfl)
    · exact partitioned.refsExist owned (by rw [old]; simp [previous])
    · exact sourceExists
    · exact partitioned.refsExist owned (by rw [old]; simp [later])
    · simpa only [rightRef,sameInst] using sourceExists
  · intro inst existsInstance
    by_cases same : inst = marker.1
    · subst inst
      obtain ⟨before,cell,after,left,right,factor,equal,atoms,owners,permutation⟩ :=
        containing_cell_cut state partitioned unique owner ref marker selected contained literal
      have freshOwner : target ∉ (before ++ cell :: after).map NotionCorePartition.Cell.owner := by
        intro member
        obtain ⟨found,foundMember,foundOwner⟩ := List.mem_map.mp member
        obtain ⟨lead,tail,shape⟩ := List.append_of_mem foundMember
        have ownMember := (NotionCoreMachinePartition.cellRefs_member (before ++ cell :: after)
          (found.owner,⟨found.slice.start,tail.head?.map (fun next => next.slice.start)⟩)).mpr
            ⟨lead,found,tail,shape,rfl⟩
        have oldMember := permutation.mem_iff.mpr ownMember
        have decoded := List.mem_filter.mp oldMember
        have belongs : found.slice.start.1 = marker.1 := by simpa using decoded.2
        exact fresh _ decoded.1 belongs foundOwner
      obtain ⟨physicalSame,nextOwners,refs,oldCells,nextCells⟩ := cut_cells before after cell marker target left right atoms owners freshOwner
      refine ⟨before ++ [⟨cell.owner,⟨cell.slice.start,left⟩⟩,⟨target,⟨marker,right⟩⟩] ++ after,
        factor.trans physicalSame.symm,nextOwners,?_⟩
      have refEq : ref = ⟨cell.slice.start,after.head?.map (fun next => next.slice.start)⟩ := congrArg Prod.snd equal
      have ownerEq : owner = cell.owner := congrArg Prod.fst equal
      have cellInst : cell.slice.start.1 = marker.1 := by simpa only [refEq] using sameInst
      rw [old,List.filter_append,List.filter_cons] at permutation
      simp only [sameInst,beq_self_eq_true,ite_true] at permutation
      have changed := cut_refs_permutation
        (beforeRefs.filter (fun owned => owned.2.start.1 == marker.1))
        (afterRefs.filter (fun owned => owned.2.start.1 == marker.1))
        before after cell marker target left right (by simpa only [refEq,ownerEq] using permutation) owners
      simpa [next,leftRef,rightRef,sameInst,cellInst,refEq,ownerEq] using changed
    · obtain ⟨cells,factor,owners,permutation⟩ := partitioned.partitions inst existsInstance
      refine ⟨cells,factor,owners,?_⟩
      have absent : (ref.start.1 == inst) = false := by simp [sameInst,Ne.symm same]
      have markerAbsent : (marker.1 == inst) = false := by simp [Ne.symm same]
      simpa [next,old,leftRef,rightRef,absent,markerAbsent] using permutation

/-- Whole atomic split restores every instance's represented endpoint table.
The source interval is recovered from raw physical coverage and actual forest
search, and the right cell is reowned only after detachment and move. -/
theorem atomicSplit_partitioned (state : NotionCoreMachine.State) (forest : Forest)
    (marker : Address) (target : Nat)
    (shape : state.forest = forest ++ [⟨target,freshTitle target⟩])
    (partitioned : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (normal : NormalForest forest) (fresh : FreshMarker forest marker)
    (freshTarget : target ∉ forest.map Block.id)
    (inactive : ∀ block ∈ forest, attached block.title = true →
      contains (physical state) (titleRef block.id) marker = false)
    (empty : physical state target = emptyPhysical target)
    (distinct : marker.1 ≠ target)
    (existsInstance : ∃ entry ∈ state.instances, entry.1 = marker.1)
    (literal : NotionCorePartition.boundary marker ∈ physical state marker.1)
    (newBoundary : ∀ owned ∈ ownedRefs state.forest, owned.2.start ≠ marker) :
    ∃ result, atomicSplit (physical state) marker target forest = some result ∧
      Partitioned {state with forest := result} := by
  have present : marker ∈ (physical state marker.1).map Atom.address :=
    List.mem_map.mpr ⟨NotionCorePartition.boundary marker,literal,rfl⟩
  obtain ⟨block,member,ref,refMember,contained⟩ :=
    NotionCoreMachinePartition.containing_tree_ref state partitioned unique marker existsInstance present newBoundary
  rw [shape] at member
  rcases List.mem_append.mp member with old | newest
  · obtain ⟨result,before,owner,sourceRef,after,executed,oldRefs,inside,nextRefs⟩ :=
      atomicSplit_refs (physical state) marker target forest normal fresh freshTarget inactive empty
        ⟨block,old,ref,refMember,contained⟩
    refine ⟨result,executed,reference_cut_partitioned state result marker target owner sourceRef before after
      partitioned unique (by simpa only [shape] using oldRefs) nextRefs inside literal ?_⟩
    rw [shape]
    exact NotionCoreMachineMarkerProgress.fresh_target_ref_owner forest target marker.1 freshTarget distinct
  · have equal := List.mem_singleton.mp newest
    subst block
    have refEq : ref = titleRef target := by simpa [freshTitle,preorderTree,preorderChildren] using refMember
    rw [refEq,empty_title_rejects _ target marker empty] at contained
    contradiction

#print axioms atomicSplit_partitioned
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
