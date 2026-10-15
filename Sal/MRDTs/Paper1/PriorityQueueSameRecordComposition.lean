import Sal.MRDTs.Paper1.PriorityQueueSameRecordSpec
import Sal.MRDTs.Paper1.PriorityQueueSameRecordOrdering
import Sal.MRDTs.Paper1.ProjectedCriterion
import Mathlib.Data.List.Nodup

/-! Compose independent per-element histories. Distinct elements commute in
the ordinary priority-map language, so concatenation preserves every required
specification-visibility edge, including for whole-map maximum queries. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord

def keyHistory (keys : List Nat) (word : Nat → List Event) : List Event :=
  keys.flatMap word

theorem keyHistory_enumerates (keys : List Nat) (word : Nat → List Event)
    (E : Set Event) (uniqueKeys : keys.Nodup)
    (covered : ∀ e ∈ E, elementOf e.op ∈ keys)
    (perKey : ∀ x ∈ keys, listPermOf (word x) {e | e ∈ E ∧ elementOf e.op = x}) :
    listPermOf (keyHistory keys word) E := by
  constructor
  · apply List.nodup_flatMap.mpr
    refine ⟨fun x hx => (perKey x hx).1, ?_⟩
    apply uniqueKeys.imp_of_mem
    intro x y hx hy different
    apply List.disjoint_left.mpr
    intro e ex ey
    have xx := ((perKey x hx).2 e).mp ex
    have yy := ((perKey y hy).2 e).mp ey
    exact different (xx.2.symm.trans yy.2)
  · intro e
    simp only [keyHistory,List.mem_flatMap]
    constructor
    · rintro ⟨x,hx,he⟩
      exact (((perKey x hx).2 e).mp he).1
    · intro he
      exact ⟨elementOf e.op,covered e he,
        ((perKey _ (covered e he)).2 e).mpr ⟨he,rfl⟩⟩

theorem keyHistory_respects (keys : List Nat) (word : Nat → List Event)
    (C : ReplayContext D.toUpdateSig) (uniqueKeys : keys.Nodup)
    (sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x)
    (ordered : ∀ x ∈ keys, respects (word x) C.vis) :
    respects (keyHistory keys word) (projectedSpecVisibility id spec C) := by
  induction keys with
  | nil => exact List.Pairwise.nil
  | cons x keys ih =>
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp uniqueKeys
    change List.Pairwise _ (word x ++ keys.flatMap word)
    apply List.pairwise_append.mpr
    refine ⟨?_,?_,?_⟩
    · exact (ordered x (by simp)).imp (fun {_ _} h edge => h edge.1)
    · exact ih unique (fun y hy => sameKey y (by simp [hy]))
        (fun y hy => ordered y (by simp [hy]))
    · intro a ha b hb edge
      obtain ⟨y,hy,hby⟩ := List.mem_flatMap.mp hb
      have ax := sameKey x (by simp) a ha
      have by' := sameKey y (by simp [hy]) b hby
      have equal := conflict_same_key b a edge.2
      have yx : y = x := by simpa only [ax,by'] using equal
      exact fresh (yx ▸ hy)

private theorem filter_single_key (events : List Event) (x y : Nat)
    (sameKey : ∀ e ∈ events, elementOf e.op = y) :
    events.filter (fun e => elementOf e.op = x) = if x = y then events else [] := by
  by_cases equal : x = y
  · rw [if_pos equal]
    apply List.filter_eq_self.mpr
    intro e he
    simp [sameKey e he,equal]
  · rw [if_neg equal]
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [sameKey e he,Ne.symm equal]

theorem keyHistory_filter (keys : List Nat) (word : Nat → List Event)
    (uniqueKeys : keys.Nodup)
    (sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x) (x : Nat) :
    (keyHistory keys word).filter (fun e => elementOf e.op = x) =
      if x ∈ keys then word x else [] := by
  induction keys with
  | nil => simp [keyHistory]
  | cons y keys ih =>
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp uniqueKeys
    change ((word y ++ keyHistory keys word).filter _) = _
    rw [List.filter_append,filter_single_key _ x y (sameKey y (by simp)),
      ih unique (fun z hz => sameKey z (by simp [hz]))]
    by_cases equal : x = y
    · subst x
      simp [fresh]
    · simp [equal]

theorem keyHistory_cell (keys : List Nat) (word : Nat → List Event)
    (uniqueKeys : keys.Nodup)
    (sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x) (x : Nat) :
    ((keyHistory keys word).foldl seqStep model.initial).2 x =
      if x ∈ keys then ((word x).foldl seqStep model.initial).2 x else none := by
  rw [seqFold_filter_cell,keyHistory_filter keys word uniqueKeys sameKey x]
  split <;> simp_all [model]

/-- Per-element final cell agreements determine the entire ordinary map, hence
also its maximum, empty and membership observations. -/
theorem keyHistory_state (keys : List Nat) (word : Nat → List Event)
    (uniqueKeys : keys.Nodup)
    (sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x)
    (target : SeqState) (consistent : SeqConsistent target)
    (present : ∀ x ∈ keys, ((word x).foldl seqStep model.initial).2 x = target.2 x)
    (absent : ∀ x ∉ keys, target.2 x = none) :
    (keyHistory keys word).foldl seqStep model.initial = target := by
  apply seqState_ext (seqConsistent_fold _ _ seqConsistent_initial) consistent
  intro x
  rw [keyHistory_cell keys word uniqueKeys sameKey x]
  by_cases member : x ∈ keys
  · simp [member,present x member]
  · simp [member,absent x member]

theorem project_consistent (s : State) : SeqConsistent (project s) := by
  intro x
  change x ∈ elements s ↔ priority s x ≠ none
  simpa only [not_not] using (not_congr (priority_none_iff s x)).symm

theorem keyHistory_query (keys : List Nat) (word : Nat → List Event)
    (uniqueKeys : keys.Nodup)
    (sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x)
    (s : State)
    (present : ∀ x ∈ keys, ((word x).foldl seqStep model.initial).2 x = priority s x)
    (absent : ∀ x ∉ keys, priority s x = none) (q : Query) :
    seqRead ((keyHistory keys word).foldl seqStep model.initial) q = read s q := by
  rw [keyHistory_state keys word uniqueKeys sameKey (project s)
    (project_consistent s) present absent]
  exact (observe_project s q).symm

/-- Assemble per-element existence proofs into one history explaining every
query. The hypotheses expose exactly the remaining execution-specific work. -/
theorem assemble_key_histories (keys : List Nat) (E : Set Event) (s : State)
    (C : ReplayContext D.toUpdateSig) (uniqueKeys : keys.Nodup)
    (covered : ∀ e ∈ E, elementOf e.op ∈ keys)
    (perKey : ∀ x ∈ keys, ∃ events,
      listPermOf events {e | e ∈ E ∧ elementOf e.op = x} ∧
      respects events C.vis ∧
      (events.foldl seqStep model.initial).2 x = priority s x)
    (absent : ∀ x ∉ keys, priority s x = none) :
    ∃ events, listPermOf events E ∧
      respects events (projectedSpecVisibility id spec C) ∧
      ∀ q, seqRead (events.foldl seqStep model.initial) q = read s q := by
  classical
  let word (x : Nat) := if hx : x ∈ keys then (perKey x hx).choose else []
  have properties : ∀ x ∈ keys,
      listPermOf (word x) {e | e ∈ E ∧ elementOf e.op = x} ∧
      respects (word x) C.vis ∧
      ((word x).foldl seqStep model.initial).2 x = priority s x := by
    intro x hx
    simpa only [word,dif_pos hx] using (perKey x hx).choose_spec
  have sameKey : ∀ x ∈ keys, ∀ e ∈ word x, elementOf e.op = x := by
    intro x hx e he
    exact (((properties x hx).1.2 e).mp he).2
  refine ⟨keyHistory keys word,
    keyHistory_enumerates keys word E uniqueKeys covered (fun x hx => (properties x hx).1),
    keyHistory_respects keys word C uniqueKeys sameKey (fun x hx => (properties x hx).2.1),?_⟩
  exact keyHistory_query keys word uniqueKeys sameKey s (fun x hx => (properties x hx).2.2) absent

#print axioms keyHistory_enumerates
#print axioms keyHistory_respects
#print axioms keyHistory_query
#print axioms assemble_key_histories

end Sal.MRDTs.Paper1.PriorityQueueSameRecord
