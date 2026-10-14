import Sal.MRDTs.Instances.NotionCoreMachine

/-! Actual marker routing progress from a structurally contained physical
marker. Deriving the containing slice from joint partition coverage is separate. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineRouting
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCoreSource.Endpoint
open NotionCoreSliceForest (Ref Tree Children Forest)
open NotionCoreMachine

private theorem beforeEnd_member (xs : List (Option Address)) (stop marker : Option Address)
    (member : marker ∈ beforeEnd stop xs) : marker ∈ xs ∧ xs.idxOf marker < xs.idxOf stop := by
  induction xs with
  | nil => simp [beforeEnd] at member
  | cons head rest ih =>
    by_cases ends : head = stop
    · simp [beforeEnd, ends] at member
    · simp only [beforeEnd, if_neg ends, List.mem_cons] at member
      rcases member with same | later
      · subst marker
        simp only [List.mem_cons, true_or, List.idxOf_cons, beq_self_eq_true, cond_true]
        have no : (head == stop) = false := Bool.eq_false_iff.mpr (by simpa using ends)
        simp [no]
      · obtain ⟨present, before⟩ := ih later
        refine ⟨List.mem_cons_of_mem _ present, ?_⟩
        have no : (head == stop) = false := Bool.eq_false_iff.mpr (by simpa using ends)
        by_cases same : head = marker
        · simp only [List.idxOf_cons, no, cond_false]
          simp [same]
        · have noMarker : (head == marker) = false := Bool.eq_false_iff.mpr (by simpa using same)
          simp only [List.idxOf_cons, no, noMarker, cond_false]
          omega

/-- A raw endpoint scan containing a marker gives its strict physical index
bounds. Duplicate markers before START would falsify the lower bound. -/
theorem extract_member_indices (xs : List (Option Address)) (start stop marker : Option Address)
    (unique : xs.Nodup) (startPresent : start ∈ xs) (ordered : xs.idxOf start < xs.idxOf stop)
    (member : marker ∈ extract start stop xs) :
    marker ∈ xs ∧ xs.idxOf start < xs.idxOf marker ∧ xs.idxOf marker < xs.idxOf stop := by
  induction xs with
  | nil => simp at startPresent
  | cons head rest ih =>
    have nd := List.nodup_cons.mp unique
    by_cases begins : head = start
    · subst head
      simp only [extract, afterStart, if_true] at member
      obtain ⟨present, before⟩ := beforeEnd_member rest stop marker member
      have noMarker : (start == marker) = false := Bool.eq_false_iff.mpr (by
        intro equal
        have equal' : start = marker := by simpa using equal
        exact nd.1 (equal' ▸ present))
      have noStop : (start == stop) = false := Bool.eq_false_iff.mpr (by
        intro equal
        have equal' : start = stop := by simpa using equal
        simp [equal'] at ordered)
      refine ⟨List.mem_cons_of_mem _ present, ?_, ?_⟩
      · simp [List.idxOf_cons, noMarker]
      · simp only [List.idxOf_cons, noMarker, noStop, cond_false]; omega
    · have noStart : (head == start) = false := Bool.eq_false_iff.mpr (by simpa using begins)
      have noStop : (head == stop) = false := Bool.eq_false_iff.mpr (by
        intro same; simp [List.idxOf_cons, noStart, same] at ordered)
      have startTail : start ∈ rest := (List.mem_cons.mp startPresent).resolve_left (Ne.symm begins)
      have orderTail : rest.idxOf start < rest.idxOf stop := by
        simp only [List.idxOf_cons, noStart, noStop, cond_false] at ordered
        omega
      have memberTail : marker ∈ extract start stop rest := by
        simpa only [extract, afterStart, if_neg begins] using member
      obtain ⟨present, lower, upper⟩ := ih nd.2 startTail orderTail memberTail
      have noMarker : (head == marker) = false := Bool.eq_false_iff.mpr (by
        intro equal
        have equal' : head = marker := by simpa using equal
        exact nd.1 (equal' ▸ present))
      refine ⟨List.mem_cons_of_mem _ present, ?_, ?_⟩
      all_goals simp only [List.idxOf_cons, noStart, noStop, noMarker, cond_false]; omega

private theorem idx_map_some (ids : List Address) (address : Address) :
    (ids.map some).idxOf (some address) = ids.idxOf address := by
  induction ids with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : head = address
    · simp [same]
    · have no : (head == address) = false := Bool.eq_false_iff.mpr (by simpa using same)
      have noSome : (some head == some address) = false := Bool.eq_false_iff.mpr (by simpa using same)
      simp only [List.map_cons, List.idxOf_cons, no, noSome, cond_false, ih]

private theorem token_some_index (ids : List Address) (address : Address) (member : address ∈ ids) :
    (ids.map some ++ [none]).idxOf (some address) = ids.idxOf address := by
  rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨address,member,rfl⟩),idx_map_some]

private theorem token_end_index (ids : List Address) :
    (ids.map some ++ [none]).idxOf none = ids.length := by
  rw [List.idxOf_append_of_notMem (by simp)]
  simp

private theorem token_unique (ids : List Address) (unique : ids.Nodup) :
    (ids.map some ++ [none]).Nodup := by
  apply List.nodup_append'.mpr
  exact ⟨unique.map (Option.some_injective _),by simp,
    List.disjoint_left.mpr (by intro token member selected; simp only [List.mem_singleton] at selected; subst token; simp at member)⟩

def stopIndex (ids : List Address) : Option Address → Nat
  | none => ids.length
  | some stop => ids.idxOf stop

/-- Source strict containment is derived from actual endpoint scans, not an
assumed interval position or a desired materialized split equation. -/
theorem contains_indices (state : State) (ref : Ref) (marker : Address)
    (valid : validBounds state ref = true)
    (unique : ((physical state ref.start.1).map Atom.address).Nodup)
    (contained : NotionCoreSliceForest.contains (physical state) ref marker = true) :
    let ids := (physical state ref.start.1).map Atom.address
    ref.start.1 = marker.1 ∧ marker ∈ ids ∧ ids.idxOf ref.start < ids.idxOf marker ∧
      ids.idxOf marker < stopIndex ids ref.stop := by
  let ids := (physical state ref.start.1).map Atom.address
  have has : ref.start.1 = marker.1 ∧ some marker ∈ NotionCorePartition.extractIds
      (physical state ref.start.1) ref.start ref.stop := by
    simpa only [NotionCoreSliceForest.contains, Bool.and_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] using contained
  have validParts :
      (state.instances.any (fun entry => entry.1 == ref.start.1) = true ∧ ref.start ∈ ids) ∧
      (match ref.stop with
      | none => ids.idxOf ref.start < ids.length
      | some finish => finish ∈ ids ∧ ids.idxOf ref.start < ids.idxOf finish) := by
    cases stop : ref.stop <;>
      simpa only [validBounds,stop,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq] using valid
  have start : ref.start ∈ ids := validParts.1.2
  have physicalTokens : NotionCorePartition.ids (physical state ref.start.1) ++ [none] = ids.map some ++ [none] := by
    simp [ids,NotionCorePartition.ids,List.map_map,Function.comp_def]
  have ordered : (ids.map some ++ [none]).idxOf (some ref.start) < (ids.map some ++ [none]).idxOf ref.stop := by
    rw [token_some_index ids ref.start start]
    cases stop : ref.stop with
    | none =>
        rw [token_end_index]
        simpa only [stop] using validParts.2
    | some finish =>
        have bounds : finish ∈ ids ∧ ids.idxOf ref.start < ids.idxOf finish := by
          simpa only [stop] using validParts.2
        rw [token_some_index ids finish bounds.1]
        exact bounds.2
  have extracted : some marker ∈ extract (some ref.start) ref.stop (ids.map some ++ [none]) := by
    simpa only [NotionCorePartition.extractIds,physicalTokens] using has.2
  obtain ⟨present,lower,upper⟩ := extract_member_indices (ids.map some ++ [none])
    (some ref.start) ref.stop (some marker) (token_unique ids unique)
    (List.mem_append_left _ (List.mem_map.mpr ⟨ref.start,start,rfl⟩)) ordered extracted
  have member : marker ∈ ids := by simpa using present
  rw [token_some_index ids ref.start start,token_some_index ids marker member] at lower
  rw [token_some_index ids marker member] at upper
  refine ⟨has.1,member,lower,?_⟩
  cases stop : ref.stop with
  | none => simpa only [stop,stopIndex,token_end_index] using upper
  | some finish =>
      have stopMember : finish ∈ ids := by
        have bounds : finish ∈ ids ∧ ids.idxOf ref.start < ids.idxOf finish := by
          simpa only [stop] using validParts.2
        exact bounds.1
      simpa only [stop,stopIndex,token_some_index ids finish stopMember] using upper


theorem split_ref_bounds (state : State) (ref : Ref) (marker : Address)
    (valid : validBounds state ref = true)
    (unique : ((physical state ref.start.1).map Atom.address).Nodup)
    (contained : NotionCoreSliceForest.contains (physical state) ref marker = true) :
    validBounds state ⟨ref.start,some marker⟩ = true ∧ validBounds state ⟨marker,ref.stop⟩ = true := by
  obtain ⟨same,member,lower,upper⟩ := contains_indices state ref marker valid unique contained
  have allocated : state.instances.any (fun entry => entry.1 == ref.start.1) = true := by
    cases stop : ref.stop <;> simp only [validBounds,stop,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq] at valid
    all_goals exact valid.1.1
  have startMember : ref.start ∈ (physical state ref.start.1).map Atom.address := by
    cases stop : ref.stop <;> simp only [validBounds,stop,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq] at valid
    all_goals exact valid.1.2
  constructor
  · simpa only [validBounds,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq] using
      And.intro (And.intro allocated startMember) (And.intro member lower)
  · cases stop : ref.stop with
    | none =>
        simpa only [validBounds,stop,← same,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq,stopIndex] using
          And.intro (And.intro allocated member) upper
    | some finish =>
        have finishMember : finish ∈ (physical state ref.start.1).map Atom.address := by
          simp only [validBounds,stop,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq] at valid
          exact valid.2.1
        simpa only [validBounds,stop,← same,Bool.and_eq_true,List.contains_iff_mem,decide_eq_true_eq,stopIndex] using
          And.intro (And.intro allocated member) (And.intro finishMember upper)

def ValidTree (state : State) (tree : Tree) : Prop :=
  ∀ ref ∈ NotionCoreSliceForest.preorderTree tree, validBounds state ref = true

def ValidChildren (state : State) (children : Children) : Prop :=
  ∀ ref ∈ NotionCoreSliceForest.preorderChildren children, validBounds state ref = true

private theorem splitNode_valid (state : State) (tree : Tree) (marker : Address)
    (valid : ValidTree state tree)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (contained : NotionCoreSliceForest.contains (physical state) tree.slice marker = true) :
    ValidTree state (NotionCoreSliceForest.splitNode marker tree) := by
  cases tree with
  | node ref children =>
      have old : validBounds state ref = true := valid ref (by simp [NotionCoreSliceForest.preorderTree])
      have divided := split_ref_bounds state ref marker old (unique ref.start.1) contained
      intro selected member
      simp only [NotionCoreSliceForest.splitNode,NotionCoreSliceForest.preorderTree,
        NotionCoreSliceForest.preorderChildren,List.append_nil,List.mem_cons] at member
      rcases member with rfl | rfl | child
      · exact divided.1
      · exact divided.2
      · exact valid selected (List.mem_cons_of_mem _ child)


mutual
private theorem splitTree_valid (state : State) (marker : Address) (tree result : Tree)
    (valid : ValidTree state tree) (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (accepted : NotionCoreSliceForest.splitTree (physical state) marker tree = some result) : ValidTree state result := by
  cases tree with
  | node ref children =>
    by_cases selected : NotionCoreSliceForest.contains (physical state) ref marker = true
    · simp only [NotionCoreSliceForest.splitTree,if_pos selected,Option.some.injEq] at accepted
      subst result
      exact splitNode_valid state _ marker valid unique selected
    · simp only [NotionCoreSliceForest.splitTree,if_neg selected,Option.map_eq_some_iff] at accepted
      obtain ⟨next,childAccepted,equal⟩ := accepted
      subst result
      have childValid : ValidChildren state children := fun target member => valid target (List.mem_cons_of_mem _ member)
      have newValid := splitChildren_valid state marker children next childValid unique childAccepted
      intro target member
      rcases List.mem_cons.mp member with rfl | child
      · exact valid target (by simp [NotionCoreSliceForest.preorderTree])
      · exact newValid target child
private theorem splitChildren_valid (state : State) (marker : Address) (children result : Children)
    (valid : ValidChildren state children) (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (accepted : NotionCoreSliceForest.splitChildren (physical state) marker children = some result) : ValidChildren state result := by
  cases children with
  | nil => simp [NotionCoreSliceForest.splitChildren] at accepted
  | cons tree rest =>
    have treeValid : ValidTree state tree := fun ref member => valid ref (List.mem_append_left _ member)
    have restValid : ValidChildren state rest := fun ref member => valid ref (List.mem_append_right _ member)
    cases first : NotionCoreSliceForest.splitTree (physical state) marker tree with
    | some next =>
      simp only [NotionCoreSliceForest.splitChildren,first,Option.some.injEq] at accepted
      subst result
      intro ref member
      rcases List.mem_append.mp member with head | tail
      · exact splitTree_valid state marker tree next treeValid unique first ref head
      · exact restValid ref tail
    | none =>
      simp only [NotionCoreSliceForest.splitChildren,first,Option.map_eq_some_iff] at accepted
      obtain ⟨next,restAccepted,equal⟩ := accepted
      subst result
      intro ref member
      rcases List.mem_append.mp member with head | tail
      · exact treeValid ref head
      · exact splitChildren_valid state marker rest next restValid unique restAccepted ref tail
end

mutual
theorem splitTree_progress (physical : Nat → List Atom) (marker : Address) (tree : Tree)
    (witness : ∃ ref ∈ NotionCoreSliceForest.preorderTree tree,
      NotionCoreSliceForest.contains physical ref marker = true) :
    ∃ result, NotionCoreSliceForest.splitTree physical marker tree = some result := by
  cases tree with
  | node ref children =>
    by_cases selected : NotionCoreSliceForest.contains physical ref marker = true
    · exact ⟨NotionCoreSliceForest.splitNode marker (.node ref children),by simp [NotionCoreSliceForest.splitTree,selected]⟩
    · obtain ⟨target,member,contained⟩ := witness
      rcases List.mem_cons.mp member with rfl | child
      · exact (selected contained).elim
      · obtain ⟨next,accepted⟩ := splitChildren_progress physical marker children ⟨target,child,contained⟩
        exact ⟨.node ref next,by simp [NotionCoreSliceForest.splitTree,selected,accepted]⟩
theorem splitChildren_progress (physical : Nat → List Atom) (marker : Address) (children : Children)
    (witness : ∃ ref ∈ NotionCoreSliceForest.preorderChildren children,
      NotionCoreSliceForest.contains physical ref marker = true) :
    ∃ result, NotionCoreSliceForest.splitChildren physical marker children = some result := by
  cases children with
  | nil => simp [NotionCoreSliceForest.preorderChildren] at witness
  | cons tree rest =>
    cases first : NotionCoreSliceForest.splitTree physical marker tree with
    | some next => exact ⟨.cons next rest,by simp [NotionCoreSliceForest.splitChildren,first]⟩
    | none =>
      obtain ⟨ref,member,contained⟩ := witness
      rcases List.mem_append.mp member with head | tail
      · obtain ⟨next,accepted⟩ := splitTree_progress physical marker tree ⟨ref,head,contained⟩
        rw [first] at accepted; contradiction
      · obtain ⟨next,accepted⟩ := splitChildren_progress physical marker rest ⟨ref,tail,contained⟩
        exact ⟨.cons tree next,by simp [NotionCoreSliceForest.splitChildren,first,accepted]⟩
end

theorem splitForest_progress (physical : Nat → List Atom) (marker : Address) (forest : Forest)
    (witness : ∃ block ∈ forest, ∃ ref ∈ NotionCoreSliceForest.preorderTree block.title,
      NotionCoreSliceForest.contains physical ref marker = true) :
    ∃ result, NotionCoreSliceForest.splitForest physical marker forest = some result := by
  induction forest with
  | nil => simp at witness
  | cons block rest ih =>
    cases first : NotionCoreSliceForest.splitTree physical marker block.title with
    | some title => exact ⟨{block with title := title} :: rest,by simp [NotionCoreSliceForest.splitForest,first]⟩
    | none =>
      obtain ⟨selected,member,ref,inside,contained⟩ := witness
      rcases List.mem_cons.mp member with rfl | tail
      · obtain ⟨title,accepted⟩ := splitTree_progress physical marker selected.title ⟨ref,inside,contained⟩
        rw [first] at accepted; contradiction
      · obtain ⟨next,accepted⟩ := ih ⟨selected,tail,ref,inside,contained⟩
        exact ⟨block :: next,by simp [NotionCoreSliceForest.splitForest,first,accepted]⟩

private theorem splitForest_valid (state : State) (marker : Address) (forest result : Forest)
    (valid : ∀ block ∈ forest, ValidTree state block.title)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (accepted : NotionCoreSliceForest.splitForest (physical state) marker forest = some result) :
    ∀ block ∈ result, ValidTree state block.title := by
  induction forest generalizing result with
  | nil => simp [NotionCoreSliceForest.splitForest] at accepted
  | cons block rest ih =>
    have rootValid := valid block (by simp)
    have tailValid : ∀ block ∈ rest, ValidTree state block.title := fun block member => valid block (List.mem_cons_of_mem _ member)
    cases first : NotionCoreSliceForest.splitTree (physical state) marker block.title with
    | some title =>
      simp only [NotionCoreSliceForest.splitForest,first,Option.some.injEq] at accepted
      subst result
      intro selected member
      rcases List.mem_cons.mp member with rfl | tail
      · exact splitTree_valid state marker block.title title rootValid unique first
      · exact tailValid selected tail
    | none =>
      simp only [NotionCoreSliceForest.splitForest,first,Option.map_eq_some_iff] at accepted
      obtain ⟨next,restAccepted,equal⟩ := accepted
      subst result
      intro selected member
      rcases List.mem_cons.mp member with rfl | tail
      · exact rootValid
      · exact ih next tailValid restAccepted selected tail

/-- Actual recursive search succeeds and its checked forest endpoint bounds
hold. The containing-ref witness is structural; joint partition coverage must
derive it after marker insertion. -/
theorem splitForest_checked_progress (state : State) (marker : Address)
    (bounds : validForestBounds state = true)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (witness : ∃ block ∈ state.forest, ∃ ref ∈ NotionCoreSliceForest.preorderTree block.title,
      NotionCoreSliceForest.contains (physical state) ref marker = true) :
    ∃ forest, NotionCoreSliceForest.splitForest (physical state) marker state.forest = some forest ∧
      validForestBounds {state with forest := forest} = true := by
  obtain ⟨forest,accepted⟩ := splitForest_progress (physical state) marker state.forest witness
  have valid : ∀ block ∈ state.forest, ValidTree state block.title := by
    simpa only [validForestBounds,List.all_eq_true,ValidTree] using bounds
  have preserved := splitForest_valid state marker state.forest forest valid unique accepted
  refine ⟨forest,accepted,?_⟩
  simpa only [validForestBounds,List.all_eq_true,ValidTree,validBounds,physical,getInstance] using preserved


private def a : NotionRunAllocation.Id := ⟨1,[65]⟩
private def b : NotionRunAllocation.Id := ⟨2,[65]⟩
private def markerId : NotionRunAllocation.Id := ⟨3,[66]⟩
private def marker : Address := NotionCorePhysicalReplay.address 0 markerId
private def transient : State :=
  ⟨[(0,⟨[⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 true⟩,.item a⟩,
    ⟨⟨markerId,.split⟩,.item a⟩],[]⟩)], [⟨0,NotionCoreSliceForest.freshTitle 0⟩],[0]⟩
private def routed : Forest :=
  [⟨0,.node ⟨(0,.start),some marker⟩ (.cons (.node ⟨marker,none⟩ .nil) .nil)⟩]

/-- PASS+FAIL: routing after actual physical marker insertion splits the root
and preserves its right slice containing a tombstone; it does not discard it. -/
theorem routed_bounds_control :
    NotionCoreSliceForest.splitForest (physical transient) marker transient.forest = some routed ∧
    validForestBounds {transient with forest := routed} = true ∧
    NotionCoreSliceForest.splitForest (physical transient) marker transient.forest ≠
      some [⟨0,.node ⟨(0,.start),some marker⟩ .nil⟩] := by decide

/-- PASS+FAIL: source containment is strict at both endpoint boundaries. -/
theorem strict_boundary_control :
    NotionCoreSliceForest.contains (physical transient) ⟨(0,.start),none⟩ marker = true ∧
    NotionCoreSliceForest.contains (physical transient) ⟨marker,none⟩ marker ≠ true ∧
    NotionCoreSliceForest.contains (physical transient) ⟨(0,.start),some marker⟩ marker ≠ true := by decide

/-- PASS+FAIL: duplicated marker identity before START falsifies the tempting
unguarded index implication. The checked theorem requires physical uniqueness. -/
theorem duplicate_boundary_control :
    let xs := [some marker,some ((0,.start) : Address),some marker,none]
    some marker ∈ extract (some ((0,.start) : Address)) none xs ∧
    ¬ xs.idxOf (some ((0,.start) : Address)) < xs.idxOf (some marker) := by decide

#print axioms contains_indices
#print axioms splitForest_checked_progress
end Sal.MRDTs.Instances.NotionCoreMachineRouting
