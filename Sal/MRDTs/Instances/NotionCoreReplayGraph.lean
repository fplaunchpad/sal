import Sal.MRDTs.Instances.NotionCorePayloadParents

/-! Graph properties of actual payload-derived replay tables. No graph
uniqueness or rank predicate is supplied by the caller. -/
namespace Sal.MRDTs.Instances.NotionCoreReplayGraph
open NotionRunAllocation (Id Run Session)
open NotionCorePayload
open NotionCorePayloadNetwork
open NotionCorePayloadParents
open NotionCoreParentMap (Row Table)

def allIds (entries : List Entry) (deleted : BlockKey → Id → Bool) : List Id :=
  entries.flatMap fun entry => (births entry.tx deleted).map birthId

theorem all_births_unique {state : State} (reachable : Reach state)
    (deleted : BlockKey → Id → Bool) : (allIds state.entries deleted).Nodup := by
  induction reachable with
  | init => simp [initial, allIds]
  | bootstrap atoms => simpa [seeded, allIds] using birth_ids_unique (bootstrap atoms) deleted
  | exchange target source _ ih => exact ih
  | gap session ticks _ ih => exact ih
  | @emit state session payload tx reachable prepared known ih =>
      exact List.nodup_append'.mpr ⟨birth_ids_unique tx deleted, ih,
        prepared_births_fresh reachable prepared deleted⟩

private theorem selectedIds_sublist (inst : BlockKey) (values : List Birth) :
    ((values.filterMap fun birth => if birth.1 = inst then some birth.2 else none).map
      (fun row => row.item.id)).Sublist (values.map birthId) := by
  induction values with
  | nil => exact .slnil
  | cons value rest ih =>
      by_cases same : value.1 = inst
      · simpa [same, birthId] using List.Sublist.cons₂ value.2.item.id ih
      · simpa [same] using List.Sublist.cons (birthId value) ih

private theorem prefixIds_sublist (entries : List Entry) (pre : List Run) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    ((prefixRows entries pre inst deleted).map (fun row => row.item.id)).Sublist (allIds entries deleted) := by
  induction entries with
  | nil => exact .slnil
  | cons entry rest ih =>
      by_cases selected : reservation entry.tx ∈ pre
      · simpa [prefixRows, allIds, selected] using
          (selectedIds_sublist inst (births entry.tx deleted)).append ih
      · simpa [prefixRows, allIds, selected] using
          (List.nil_sublist ((births entry.tx deleted).map birthId)).append ih

theorem prefix_unique {state : State} (reachable : Reach state) (pre : List Run)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Unique (prefixRows state.entries pre inst deleted) :=
  (prefixIds_sublist state.entries pre inst deleted).nodup (all_births_unique reachable deleted)

theorem entry_counter_positive {state : State} (reachable : Reach state) :
    ∀ entry ∈ state.entries, 0 < entry.tx.id.counter := by
  induction reachable with
  | init => simp [initial]
  | bootstrap atoms => simp [seeded, bootstrap]
  | exchange target source _ ih => exact ih
  | gap session ticks _ ih => exact ih
  | @emit state session payload tx reachable prepared known ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · have same := congrArg NotionCoreIssuance.Record.run (prepare_record prepared)
        have counter := congrArg (fun run : Run => run.first.counter) same
        simp only [record, reservation, NotionRunAllocation.reserve] at counter
        change tx.id.counter = ((forget state).allocation.peers session).clock + 1 at counter
        change 0 < tx.id.counter
        omega
      · exact ih entry member

theorem prefix_increasing {state : State} (reachable : Reach state) (pre : List Run)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Increasing (prefixRows state.entries pre inst deleted) := by
  intro row member
  obtain ⟨entry, present, selected, born⟩ := (prefix_row_member _ _ _ _ _).mp member
  obtain ⟨offset, within, id, origin⟩ := birth_parent entry.tx deleted (inst, row) born
  change row.item.id = offsetId entry.tx.id offset at id
  change row.origin = parentAt entry.tx.id (payloadOrigin entry.tx.payload) offset at origin
  rw [origin, parentAt]
  split
  · rename_i zero
    subst offset
    cases same : payloadOrigin entry.tx.payload with
    | start => simpa [NotionCoreParentMap.originCounter, id, offsetId] using
        entry_counter_positive reachable entry present
    | item old =>
        have reference := external_reference entry.tx.payload old same
        have before := NotionCoreIssuance.reference_counter_before (forget_reachable reachable)
          (List.mem_map.mpr ⟨entry, present, rfl⟩) reference
        simpa [NotionCoreParentMap.originCounter, id, offsetId, Entry.record, record, reservation] using before
  · rename_i positive
    simp only [NotionCoreParentMap.originCounter, id, offsetId]
    omega

private theorem runRows_origin (origin : NotionCoreOriginTree.Origin)
    (items : List NotionCoreOriginTree.Item) (row : Row)
    (member : row ∈ NotionCoreParentMap.runRows origin items) :
    row.origin = origin ∨ ∃ item ∈ items, row.origin = .item item.id := by
  induction items generalizing origin with
  | nil => simp [NotionCoreParentMap.runRows] at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · rcases ih (.item first.id) member with same | ⟨item, present, same⟩
        · exact Or.inr ⟨first, by simp, same⟩
        · exact Or.inr ⟨item, List.mem_cons_of_mem _ present, same⟩

theorem located_birth_parent (tx : Transaction) (deleted : BlockKey → Id → Bool)
    (inst : BlockKey) (row : Row) (born : (inst, row) ∈ births tx deleted)
    (old : Id) (parent : row.origin = .item old) :
    (inst, old) ∈ locatedReferences tx.payload ∨
      (inst, old) ∈ birthAddresses tx := by
  cases tx with
  | mk first payload =>
    cases payload with
    | bootstrap atoms =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_map] at born
      obtain ⟨r, present, pair⟩ := born
      have instKeys := congrArg Prod.fst pair
      have rows := congrArg Prod.snd pair
      dsimp at instKeys rows
      subst inst
      subst row
      rcases runRows_origin .start _ r present with same | ⟨item, member, same⟩
      · rw [parent] at same; contradiction
      · have equal : item.id = old := NotionCoreOriginTree.Origin.item.inj (same.symm.trans parent)
        right
        rw [← birthAddresses_deleted ⟨first, .bootstrap atoms⟩ deleted]
        simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.append_nil, List.map_map, birthId]
        change (_, old) ∈ (NotionCoreParentMap.runRows _ _).map (fun r => (_, birthId (_, r)))
        rw [runRows_addresses]
        exact List.mem_map.mpr ⟨item, member, by simp [equal]⟩
    | insert block instKey origin atoms =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_map] at born
      obtain ⟨r, present, pair⟩ := born
      have instKeys := congrArg Prod.fst pair
      have rows := congrArg Prod.snd pair
      dsimp at instKeys rows
      subst inst
      subst row
      rcases runRows_origin origin _ r present with same | ⟨item, member, same⟩
      · left
        have equal : origin = .item old := same.symm.trans parent
        simp [locatedReferences, originReference, equal]
      · have equal : item.id = old := NotionCoreOriginTree.Origin.item.inj (same.symm.trans parent)
        right
        rw [← birthAddresses_deleted ⟨first, .insert block instKey origin atoms⟩ deleted]
        simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.map_map, birthId]
        change (_, old) ∈ (NotionCoreParentMap.runRows _ _).map (fun r => (_, birthId (_, r)))
        rw [runRows_addresses]
        exact List.mem_map.mpr ⟨item, member, by simp [equal]⟩
    | split block instKey origin =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_singleton] at born
      have instKeys := congrArg Prod.fst born
      have rows := congrArg Prod.snd born
      dsimp at instKeys rows
      subst inst
      subst row
      left
      change origin = .item old at parent
      simp [locatedReferences, originReference, parent]
    | create afterBlock => simp [births, operations, Operation.births] at born
    | erase block groups => simp at born
    | merge source target => simp [births, operations, Operation.births] at born

/-- Closure for every prefix of a canonical whole-version replay. External
parent providers are derived from reception provenance; internal predecessors
are births of the same included transaction. -/
theorem prefix_closed {state : State} (reachable : Reach state) (peer : Session)
    (pre suffix : List Run)
    (prefixEq : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received = pre ++ suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Closed (prefixRows state.entries pre inst deleted) := by
  intro row member
  obtain ⟨entry, present, selected, born⟩ := (prefix_row_member _ _ _ _ _).mp member
  cases parent : row.origin with
  | start => trivial
  | item old =>
      rcases located_birth_parent entry.tx deleted inst row born old parent with external | internal
      · obtain ⟨before, after, same⟩ := List.append_of_mem selected
        have position : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received =
            before ++ reservation entry.tx :: (after ++ suffix) := by
          rw [prefixEq, same]; simp [List.append_assoc]
        obtain ⟨provider, providerMember, prior, birth, bound⟩ :=
          replay_located_provider reachable peer present before (after ++ suffix) position external
        rw [← birthAddresses_deleted provider.tx deleted] at birth
        obtain ⟨value, bornProvider, addressEq⟩ := List.mem_map.mp birth
        have instEq := congrArg Prod.fst addressEq
        have idEq := congrArg Prod.snd addressEq
        refine List.mem_map.mpr ⟨value.2, ?_, ?_⟩
        · apply (prefix_row_member _ _ _ _ _).mpr
          refine ⟨provider, providerMember, ?_, ?_⟩
          · rw [same]; exact List.mem_append_left _ prior
          · have valueEq : (inst, value.2) = value := Prod.ext instEq.symm rfl
            exact valueEq ▸ bornProvider
        · exact idEq
      · rw [← birthAddresses_deleted entry.tx deleted] at internal
        obtain ⟨value, bornSame, addressEq⟩ := List.mem_map.mp internal
        have instEq := congrArg Prod.fst addressEq
        have idEq := congrArg Prod.snd addressEq
        refine List.mem_map.mpr ⟨value.2, ?_, idEq⟩
        apply (prefix_row_member _ _ _ _ _).mpr
        refine ⟨entry, present, selected, ?_⟩
        have valueEq : (inst, value.2) = value := Prod.ext instEq.symm rfl
        exact valueEq ▸ bornSame


theorem prefix_graph {state : State} (reachable : Reach state) (peer : Session)
    (pre suffix : List Run)
    (prefixEq : NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received = pre ++ suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    NotionCoreParentMap.Unique (prefixRows state.entries pre inst deleted) ∧
    NotionCoreParentMap.Increasing (prefixRows state.entries pre inst deleted) ∧
    NotionCoreParentMap.Closed (prefixRows state.entries pre inst deleted) :=
  ⟨prefix_unique reachable pre inst deleted, prefix_increasing reachable pre inst deleted,
    prefix_closed reachable peer pre suffix prefixEq inst deleted⟩

theorem canonical_graph {state : State} (reachable : Reach state) (peer : Session)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    let rows := prefixRows state.entries
      (NotionCoreIssuance.replay (forget state) (state.allocation.peers peer).received) inst deleted
    NotionCoreParentMap.Unique rows ∧ NotionCoreParentMap.Increasing rows ∧ NotionCoreParentMap.Closed rows :=
  prefix_graph reachable peer _ [] (by simp) inst deleted

private def a : Id := ⟨1, [65]⟩
private def b : Id := ⟨2, [65]⟩
private def marker : Id := ⟨3, [66]⟩
private def seed : Transaction := bootstrap [97, 98]
private def cut : Transaction := ⟨marker, .split .initial .initial (.item b)⟩
private def archive : List Entry := [⟨cut, [reservation seed]⟩, ⟨seed, []⟩]

/-- PASS+FAIL: archive enumeration is newest first, while a canonical prefix
includes only bootstrap. Its second character points to its first, not START. -/
theorem prefix_rows_control :
    prefixRows archive [reservation seed] .initial (fun _ _ => false) =
      [⟨⟨a, .text 97 false⟩, .start⟩, ⟨⟨b, .text 98 false⟩, .item a⟩] ∧
    prefixRows archive [reservation seed] .initial (fun _ _ => false) ≠
      [⟨⟨a, .text 97 false⟩, .start⟩, ⟨⟨b, .text 98 false⟩, .start⟩] := by decide

/-- PASS+FAIL: the full prefix adds the marker's external edge. Tombstoning
its parent preserves the physical edge and the parent's run predecessor. -/
theorem tombstone_rows_control :
    prefixRows archive [reservation seed, reservation cut] .initial (fun _ id => decide (id = b)) =
      [⟨⟨marker, .split⟩, .item b⟩, ⟨⟨a, .text 97 false⟩, .start⟩,
       ⟨⟨b, .text 98 true⟩, .item a⟩] ∧
    prefixRows archive [reservation seed, reservation cut] (.issued marker) (fun _ _ => false) ≠
      [⟨⟨marker, .split⟩, .item b⟩] := by decide

#print axioms all_births_unique
#print axioms prefix_graph
#print axioms canonical_graph
end Sal.MRDTs.Instances.NotionCoreReplayGraph
