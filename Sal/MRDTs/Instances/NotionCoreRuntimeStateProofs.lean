import Sal.MRDTs.Instances.NotionCoreRuntimeState

namespace Sal.MRDTs.Instances.NotionCoreRuntimeState
open NotionCoreRuntimeTypes (ItemKey OriginKey)
open NotionCorePayload (BlockKey Transaction)
open NotionCoreParentMap (Row Table)
open NotionCoreOriginTree (Origin)
open NotionRunAllocation (Id)
open NotionCoreStructuralFacts (Fact decodeList)

theorem abstract_birth (s : State) (inst : BlockKey) (row : Row) :
    Fact.birth inst row ∈ abstract s ↔ ∃ id : Id, s.births[(inst,id)]? = some row := by
  simp [abstract,factsList,List.mem_map,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem abstract_erased (s : State) (inst : BlockKey) (id : Id) :
    Fact.erased inst id ∈ abstract s ↔ (inst,id) ∈ s.erased := by
  simp [abstract,factsList,List.mem_map,Prod.exists,Std.HashSet.mem_toList]

theorem abstract_cut (s : State) (inst : BlockKey) (id : Id) (target : BlockKey) :
    Fact.cut inst id target ∈ abstract s ↔ s.cuts[(inst,id)]? = some target := by
  simp [abstract,factsList,List.mem_map,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem abstract_created (s : State) (block : BlockKey) (after : Option BlockKey) :
    Fact.created block after ∈ abstract s ↔ s.created[block]? = some after := by
  simp [abstract,factsList,List.mem_map,Prod.exists,Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem birth_exact {s : State} (keys : RowKeys s) (inst : BlockKey) (row : Row) :
    Fact.birth inst row ∈ abstract s ↔ s.births[(inst,row.item.id)]? = some row := by
  rw [abstract_birth]
  constructor
  · rintro ⟨id,found⟩
    rw [keys inst id row found]
    exact found
  · exact fun found => ⟨row.item.id,found⟩

theorem insertFact_rowKeys {s next : State} (keys : RowKeys s) (fact : Fact)
    (accepted : insertFact s fact = .ok next) : RowKeys next := by
  cases fact with
  | birth inst row =>
      cases found : s.births[(inst,row.item.id)]? with
      | none =>
          simp [insertFact,found] at accepted
          subst next
          intro key id value lookup
          simp only [Std.HashMap.getElem?_insert] at lookup
          by_cases hit : (inst,row.item.id) == (key,id)
          · simp only [hit,if_pos] at lookup
            have same : (inst,row.item.id) = (key,id) := by simpa using hit
            have valueEq := Option.some.inj lookup
            simpa [← valueEq] using congrArg Prod.snd same
          · simp only [hit] at lookup
            exact keys key id value lookup
      | some old =>
          by_cases same : old = row
          · simp [insertFact,found,same] at accepted
            subst next
            exact keys
          · simp [insertFact,found,same] at accepted
  | erased inst id =>
      simp [insertFact] at accepted
      subst next
      exact keys
  | cut inst id owner =>
      cases found : s.cuts[(inst,id)]? with
      | none => simp [insertFact,found] at accepted; subst next; exact keys
      | some old =>
          by_cases same : old = owner
          · simp [insertFact,found,same] at accepted; subst next; exact keys
          · simp [insertFact,found,same] at accepted
  | created block afterBlock =>
      cases found : s.created[block]? with
      | none => simp [insertFact,found] at accepted; subst next; exact keys
      | some old =>
          by_cases same : old = afterBlock
          · simp [insertFact,found,same] at accepted; subst next; exact keys
          · simp [insertFact,found,same] at accepted

private theorem birth_insert_abstract (s : State) (inst : BlockKey) (row : Row)
    (absent : s.births[(inst,row.item.id)]? = none) (children counts) :
    abstract {s with births := s.births.insert (inst,row.item.id) row,children := children,counts := counts} =
      insert (Fact.birth inst row) (abstract s) := by
  ext fact
  cases fact with
  | birth key value =>
      simp only [abstract_birth,Finset.mem_insert,Fact.birth.injEq]
      simp only [Std.HashMap.getElem?_insert]
      constructor
      · rintro ⟨id,found⟩
        by_cases hit : (inst,row.item.id) == (key,id)
        · simp only [hit,if_pos,Option.some.injEq] at found
          have same : (inst,row.item.id) = (key,id) := by simpa using hit
          exact Or.inl ⟨(congrArg Prod.fst same).symm,found.symm⟩
        · simp only [hit] at found
          exact Or.inr ⟨id,found⟩
      · rintro (⟨rfl,rfl⟩ | ⟨id,found⟩)
        · exact ⟨value.item.id,by simp⟩
        · have different : (inst,row.item.id) ≠ (key,id) := by
            intro same
            have contradiction := same ▸ absent
            rw [found] at contradiction
            contradiction
          exact ⟨id,by simpa [different] using found⟩
  | erased key id => simp [abstract_erased]
  | cut key id owner => simp [abstract_cut]
  | created key afterBlock => simp [abstract_created]

private theorem cut_insert_abstract (s : State) (inst : BlockKey) (id : Id) (owner : BlockKey)
    (absent : s.cuts[(inst,id)]? = none) :
    abstract {s with cuts := s.cuts.insert (inst,id) owner} = insert (Fact.cut inst id owner) (abstract s) := by
  ext fact
  cases fact with
  | birth key row => simp [abstract_birth]
  | erased key marker => simp [abstract_erased]
  | cut key marker target =>
      by_cases hit : (inst,id) = (key,marker)
      · have hi := congrArg Prod.fst hit
        have hd := congrArg Prod.snd hit
        simp only at hi hd
        subst key
        subst marker
        simp [abstract_cut,absent,eq_comm]
      · have noKey : ¬ (key = inst ∧ marker = id) := fun h => hit (Prod.ext h.1.symm h.2.symm)
        simp [abstract_cut,Std.HashMap.getElem?_insert,hit]
        intro hi hd _
        exact (noKey ⟨hi,hd⟩).elim
  | created key afterBlock => simp [abstract_created]

private theorem created_insert_abstract (s : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (absent : s.created[block]? = none) :
    abstract {s with created := s.created.insert block afterBlock} = insert (Fact.created block afterBlock) (abstract s) := by
  ext fact
  cases fact with
  | birth key row => simp [abstract_birth]
  | erased key marker => simp [abstract_erased]
  | cut key marker target => simp [abstract_cut]
  | created key previous =>
      by_cases hit : block = key
      · subst key
        simp [abstract_created,absent,eq_comm]
      · simp [abstract_created,Std.HashMap.getElem?_insert,hit,beq_iff_eq,Ne.symm hit]

theorem insertFact_abstract {s next : State} (fact : Fact)
    (accepted : insertFact s fact = .ok next) : abstract next = insert fact (abstract s) := by
  cases fact with
  | birth inst row =>
      cases found : s.births[(inst,row.item.id)]? with
      | none =>
          simp [insertFact,found] at accepted
          subst next
          exact birth_insert_abstract s inst row found _ _
      | some old =>
          by_cases same : old = row
          · simp [insertFact,found,same] at accepted
            subst next
            symm
            apply Finset.insert_eq_of_mem
            exact (abstract_birth s inst row).mpr ⟨row.item.id,by simpa [same] using found⟩
          · simp [insertFact,found,same] at accepted
  | erased inst id =>
      simp [insertFact] at accepted
      subst next
      ext fact
      cases fact with
      | birth key row => simp [abstract_birth]
      | erased key marker =>
          simp only [abstract_erased,Finset.mem_insert,Fact.erased.injEq,Std.HashSet.mem_insert,beq_iff_eq,Prod.mk.injEq]
          tauto
      | cut key marker target => simp [abstract_cut]
      | created key previous => simp [abstract_created]
  | cut inst id owner =>
      cases found : s.cuts[(inst,id)]? with
      | none => simp [insertFact,found] at accepted; subst next; exact cut_insert_abstract s inst id owner found
      | some old =>
          by_cases same : old = owner
          · simp [insertFact,found,same] at accepted
            subst next
            symm
            apply Finset.insert_eq_of_mem
            exact (abstract_cut s inst id owner).mpr (by simpa [same] using found)
          · simp [insertFact,found,same] at accepted
  | created block afterBlock =>
      cases found : s.created[block]? with
      | none => simp [insertFact,found] at accepted; subst next; exact created_insert_abstract s block afterBlock found
      | some old =>
          by_cases same : old = afterBlock
          · simp [insertFact,found,same] at accepted
            subst next
            symm
            apply Finset.insert_eq_of_mem
            exact (abstract_created s block afterBlock).mpr (by simpa [same] using found)
          · simp [insertFact,found,same] at accepted

private theorem map_insert_new {K V : Type} [BEq K] [Hashable K] [LawfulBEq K]
    (m : Std.HashMap K V) (key : K) (value : V) (absent : m[key]? = none) :
    (m.insert key value).toList.Perm ((key,value) :: m.toList) := by
  have filtered : m.toList.filter (fun p => !(key == p.1)) = m.toList := by
    apply List.filter_eq_self.mpr
    intro p member
    have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member
    have different : key ≠ p.1 := by
      intro same
      rw [← same,absent] at found
      contradiction
    simp [different]
  simpa [filtered] using (Std.HashMap.toList_insert_perm (m := m) (k := key) (v := value))

private theorem birthsAt_insert (s : State) (inst : BlockKey) (row : Row)
    (absent : s.births[(inst,row.item.id)]? = none) (key : BlockKey) :
    (birthsAt {s with births := s.births.insert (inst,row.item.id) row} key).Perm
      (if inst = key then row :: birthsAt s key else birthsAt s key) := by
  have enumerated := (map_insert_new s.births (inst,row.item.id) row absent).filterMap
    (fun p => if p.1.1 = key then some p.2 else none)
  by_cases same : inst = key <;> simpa [birthsAt,same] using enumerated

private theorem insert_bucket (ids : List Id) (id : Id) :
    (NotionCoreSourceInvariant.sortChildren ids).orderedInsert NotionCoreSourceInvariant.Desc id =
      NotionCoreSourceInvariant.sortChildren (id :: ids) := by
  simp only [NotionCoreSourceInvariant.sortChildren,List.mergeSort_eq_insertionSort,List.insertionSort_cons]

private theorem birth_insert_buckets (s : State) (inst : BlockKey) (row : Row)
    (absent : s.births[(inst,row.item.id)]? = none) (buckets : Buckets s) :
    Buckets {s with births := s.births.insert (inst,row.item.id) row, children := s.children.insert (inst,row.origin) ((childrenAt s inst row.origin).orderedInsert NotionCoreSourceInvariant.Desc row.item.id), counts := s.counts.insert inst (countAt s inst + 1)} := by
  let next : State := {s with births := s.births.insert (inst,row.item.id) row, children := s.children.insert (inst,row.origin) ((childrenAt s inst row.origin).orderedInsert NotionCoreSourceInvariant.Desc row.item.id), counts := s.counts.insert inst (countAt s inst + 1)}
  intro key origin
  have perm : (birthsAt next key).Perm (if inst = key then row :: birthsAt s key else birthsAt s key) :=
    birthsAt_insert s inst row absent key
  have childPerm := perm.filterMap (fun r => if r.origin = origin then some r.item.id else none)
  change (NotionCoreParentMap.childIds (birthsAt next key) origin).Perm
    (NotionCoreParentMap.childIds (if inst = key then row :: birthsAt s key else birthsAt s key) origin) at childPerm
  have sorted : NotionCoreParentMap.sortedChildren (birthsAt next key) origin =
      NotionCoreSourceInvariant.sortChildren
        (NotionCoreParentMap.childIds (if inst = key then row :: birthsAt s key else birthsAt s key) origin) :=
    NotionCoreSourceInvariant.sort_permutation childPerm
  change childrenAt next key origin = NotionCoreParentMap.sortedChildren (birthsAt next key) origin
  rw [sorted]
  by_cases sameInst : inst = key
  · subst key
    by_cases sameOrigin : row.origin = origin
    · subst origin
      have rhs : NotionCoreParentMap.childIds (if inst = inst then row :: birthsAt s inst else birthsAt s inst) row.origin =
          row.item.id :: NotionCoreParentMap.childIds (birthsAt s inst) row.origin := by
        simp [NotionCoreParentMap.childIds]
      rw [rhs]
      change ((s.children.insert (inst,row.origin) _)[(inst,row.origin)]?).getD [] = _
      simp only [Std.HashMap.getElem?_insert_self,Option.getD_some]
      rw [buckets inst row.origin]
      exact insert_bucket _ _
    · have rhs : NotionCoreParentMap.childIds (if inst = inst then row :: birthsAt s inst else birthsAt s inst) origin =
          NotionCoreParentMap.childIds (birthsAt s inst) origin := by simp [NotionCoreParentMap.childIds,sameOrigin]
      rw [rhs]
      have different : (inst,row.origin) ≠ (inst,origin) := by simp [sameOrigin]
      simpa [next,childrenAt,Std.HashMap.getElem?_insert,different] using buckets inst origin
  · have rhs : NotionCoreParentMap.childIds (if inst = key then row :: birthsAt s key else birthsAt s key) origin =
        NotionCoreParentMap.childIds (birthsAt s key) origin := by simp [sameInst]
    rw [rhs]
    have different : (inst,row.origin) ≠ (key,origin) := by simp [sameInst]
    simpa [next,childrenAt,Std.HashMap.getElem?_insert,different] using buckets key origin

private theorem birth_insert_counts (s : State) (inst : BlockKey) (row : Row)
    (absent : s.births[(inst,row.item.id)]? = none) (counts : Counts s) (children) :
    Counts {s with births := s.births.insert (inst,row.item.id) row, children := children,counts := s.counts.insert inst (countAt s inst + 1)} := by
  let next : State := {s with births := s.births.insert (inst,row.item.id) row, children := children,counts := s.counts.insert inst (countAt s inst + 1)}
  intro key
  have perm : (birthsAt next key).Perm (if inst = key then row :: birthsAt s key else birthsAt s key) :=
    birthsAt_insert s inst row absent key
  have length := perm.length_eq
  have count := counts key
  unfold countAt at count
  by_cases same : inst = key
  · subst key
    simpa [next,countAt,Std.HashMap.getElem?_insert,count] using length.symm
  · simpa [next,countAt,Std.HashMap.getElem?_insert,same,count] using length.symm

theorem empty_valid : Valid empty := by
  refine ⟨?_,?_,?_⟩
  · intro inst id row found
    simp [empty] at found
  · intro inst origin
    simp [empty,childrenAt,birthsAt,NotionCoreParentMap.sortedChildren,
      NotionCoreParentMap.childIds,NotionCoreSourceInvariant.sortChildren]
  · intro inst
    simp [empty,countAt,birthsAt]

@[simp] theorem empty_abstract : abstract empty = ∅ := by simp [abstract,factsList,empty]

theorem insertFact_valid {s next : State} (valid : Valid s) (fact : Fact)
    (accepted : insertFact s fact = .ok next) : Valid next := by
  have keysNext := insertFact_rowKeys valid.1 fact accepted
  cases fact with
  | birth inst row =>
      cases found : s.births[(inst,row.item.id)]? with
      | none =>
          simp [insertFact,found] at accepted
          subst next
          exact ⟨keysNext,birth_insert_buckets s inst row found valid.2.1,
            birth_insert_counts s inst row found valid.2.2 _⟩
      | some old =>
          by_cases same : old = row
          · simp [insertFact,found,same] at accepted; subst next; exact valid
          · simp [insertFact,found,same] at accepted
  | erased inst id =>
      simp [insertFact] at accepted
      subst next
      exact valid
  | cut inst id owner =>
      cases found : s.cuts[(inst,id)]? with
      | none => simp [insertFact,found] at accepted; subst next; exact valid
      | some old =>
          by_cases same : old = owner
          · simp [insertFact,found,same] at accepted; subst next; exact valid
          · simp [insertFact,found,same] at accepted
  | created block afterBlock =>
      cases found : s.created[block]? with
      | none => simp [insertFact,found] at accepted; subst next; exact valid
      | some old =>
          by_cases same : old = afterBlock
          · simp [insertFact,found,same] at accepted; subst next; exact valid
          · simp [insertFact,found,same] at accepted

theorem batch_valid {s next : State} (valid : Valid s) (facts : List Fact)
    (accepted : facts.foldlM insertFact s = .ok next) : Valid next := by
  induction facts generalizing s with
  | nil => change Except.ok s = Except.ok next at accepted; cases accepted; exact valid
  | cons fact rest ih =>
      cases first : insertFact s fact with
      | error reason =>
          simp only [List.foldlM_cons,first] at accepted
          change Except.error reason = Except.ok next at accepted
          contradiction
      | ok middle =>
          apply ih (insertFact_valid valid fact first)
          simpa [List.foldlM_cons,first] using accepted

theorem batch_abstract {s next : State} (facts : List Fact)
    (accepted : facts.foldlM insertFact s = .ok next) :
    abstract next = abstract s ∪ facts.toFinset := by
  induction facts generalizing s with
  | nil => change Except.ok s = Except.ok next at accepted; cases accepted; simp
  | cons fact rest ih =>
      cases first : insertFact s fact with
      | error reason =>
          simp only [List.foldlM_cons,first] at accepted
          change Except.error reason = Except.ok next at accepted
          contradiction
      | ok middle =>
          have tail : rest.foldlM insertFact middle = .ok next := by
            simpa [List.foldlM_cons,first] using accepted
          rw [ih tail,insertFact_abstract fact first]
          simp

theorem receive_valid {s next : State} (valid : Valid s) (tx : Transaction)
    (accepted : receive s tx = .ok next) : Valid next := batch_valid valid (decodeList tx) accepted

theorem receive_abstract {s next : State} (tx : Transaction)
    (accepted : receive s tx = .ok next) :
    abstract next = abstract s ∪ NotionCoreStructuralFacts.decode tx := batch_abstract (decodeList tx) accepted

theorem merge_valid {left right next : State} (valid : Valid left)
    (accepted : merge left right = .ok next) : Valid next := batch_valid valid (factsList right) accepted

theorem merge_abstract {left right next : State} (accepted : merge left right = .ok next) :
    abstract next = abstract left ∪ abstract right := batch_abstract (factsList right) accepted

/-- The optimized single-value maps reject conflicting immutable keys.
This structural condition states exactly the domain required for progress,
without assuming any intended document observation. -/
def Compatible (facts : Finset Fact) : Prop :=
  (∀ inst (a b : Row), Fact.birth inst a ∈ facts → Fact.birth inst b ∈ facts →
    a.item.id = b.item.id → a = b) ∧
  (∀ inst id a b, Fact.cut inst id a ∈ facts → Fact.cut inst id b ∈ facts → a = b) ∧
  (∀ block a b, Fact.created block a ∈ facts → Fact.created block b ∈ facts → a = b)

theorem Compatible.mono {a b : Finset Fact} (compatible : Compatible b) (subset : a ⊆ b) : Compatible a := by
  refine ⟨?_,?_,?_⟩
  · intro inst x y hx hy same; exact compatible.1 inst x y (subset hx) (subset hy) same
  · intro inst id x y hx hy; exact compatible.2.1 inst id x y (subset hx) (subset hy)
  · intro block x y hx hy; exact compatible.2.2 block x y (subset hx) (subset hy)

theorem insertFact_total (s : State) (keys : RowKeys s) (fact : Fact)
    (compatible : Compatible (insert fact (abstract s))) :
    ∃ next, insertFact s fact = .ok next := by
  cases fact with
  | birth inst row =>
      cases found : s.births[(inst,row.item.id)]? with
      | none => exact ⟨_,by simp [insertFact,found]; rfl⟩
      | some old =>
          have oldMember : Fact.birth inst old ∈ insert (Fact.birth inst row) (abstract s) :=
            Finset.mem_insert_of_mem ((abstract_birth s inst old).mpr ⟨row.item.id,found⟩)
          have equal : old = row := compatible.1 inst old row oldMember (Finset.mem_insert_self _ _)
            (keys inst row.item.id old found)
          exact ⟨s,by simp [insertFact,found,equal]⟩
  | erased inst id => exact ⟨_,rfl⟩
  | cut inst id target =>
      cases found : s.cuts[(inst,id)]? with
      | none => exact ⟨_,by simp [insertFact,found]; rfl⟩
      | some old =>
          have oldMember : Fact.cut inst id old ∈ insert (Fact.cut inst id target) (abstract s) :=
            Finset.mem_insert_of_mem ((abstract_cut s inst id old).mpr found)
          have equal := compatible.2.1 inst id old target oldMember (Finset.mem_insert_self _ _)
          exact ⟨s,by simp [insertFact,found,equal]⟩
  | created block afterBlock =>
      cases found : s.created[block]? with
      | none => exact ⟨_,by simp [insertFact,found]; rfl⟩
      | some old =>
          have oldMember : Fact.created block old ∈ insert (Fact.created block afterBlock) (abstract s) :=
            Finset.mem_insert_of_mem ((abstract_created s block old).mpr found)
          have equal := compatible.2.2 block old afterBlock oldMember (Finset.mem_insert_self _ _)
          exact ⟨s,by simp [insertFact,found,equal]⟩

theorem batch_total (s : State) (valid : Valid s) (facts : List Fact)
    (compatible : Compatible (abstract s ∪ facts.toFinset)) :
    ∃ next, facts.foldlM insertFact s = .ok next := by
  induction facts generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons fact rest ih =>
      have headCompatible : Compatible (insert fact (abstract s)) := compatible.mono (by
        intro f member
        rcases Finset.mem_insert.mp member with rfl | old
        · exact Finset.mem_union_right _ (by simp)
        · exact Finset.mem_union_left _ old)
      obtain ⟨middle,first⟩ := insertFact_total s valid.1 fact headCompatible
      have same : abstract middle ∪ rest.toFinset = abstract s ∪ (fact :: rest).toFinset := by
        rw [insertFact_abstract fact first]
        simp
      obtain ⟨next,tail⟩ := ih middle (insertFact_valid valid fact first) (by simpa [same] using compatible)
      exact ⟨next,by simpa [List.foldlM_cons,first] using tail⟩

theorem receive_total (s : State) (valid : Valid s) (tx : Transaction)
    (compatible : Compatible (abstract s ∪ NotionCoreStructuralFacts.decode tx)) :
    ∃ next, receive s tx = .ok next := batch_total s valid (decodeList tx) compatible

theorem merge_total (left right : State) (valid : Valid left)
    (compatible : Compatible (abstract left ∪ abstract right)) :
    ∃ next, merge left right = .ok next := batch_total left valid (factsList right) compatible

#print axioms receive_total
#print axioms merge_total
#print axioms receive_abstract
#print axioms merge_abstract
#print axioms receive_valid
#print axioms merge_valid
#print axioms insertFact_abstract
end Sal.MRDTs.Instances.NotionCoreRuntimeState
