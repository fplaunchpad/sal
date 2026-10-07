import Sal.MRDTs.Paper1.SpecificationVisibility

/-!
# The active criterion admits a sequential no-op-removal bug

This is the one-element specialization of the manuscript's OR-set mutation:
add retains its timestamp, removal is the identity, and three-way merge is
unchanged. The actual run is add, remove, query. The criterion may explain its
wrong answer by reversing the two updates because concrete commutation makes
its entire linearization relation empty.
-/
namespace Sal.MRDTs.Paper1.CriterionCounterexample
open Foundation
open Classical

inductive Update where
  | add
  | remove
  deriving DecidableEq, Repr

def mutate (s : Finset Timestamp) (e : Op Update) : Finset Timestamp :=
  match e.op with
  | .add => insert e.time s
  | .remove => s

@[reducible] def D : MRDTSig where
  State := Finset Timestamp
  dec_state := inferInstance
  init := ∅
  AppOp := Update
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := mutate
  merge l a b := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)
  query s _ := decide s.Nonempty

def emptyPolicy : OperationPolicy Update where
  before _ _ := False

def setMachine : DeterministicSpec Update Unit Bool where
  State := Bool
  initial := false
  update _ op := match op with
    | .add => true
    | .remove => false
  query present _ := present

def spec : HistorySpec Update Unit Bool := setMachine.toSpec

def addEvent : Op Update := (1, 0, .add)
def removeEvent : Op Update := (2, 0, .remove)

theorem all_commute (a b : Op Update) : D.toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨ta, ra, oa⟩
  rcases b with ⟨tb, rb, ob⟩
  cases oa <;> cases ob <;>
    simp [D, mutate, Op.op, Op.time, Finset.insert_comm]

theorem restrictedLaws : RestrictedLaws D.toUpdateSig emptyPolicy where
  noncomm_exact a b := by simp [emptyPolicy, all_commute a b]
  no_chain := by simp [emptyPolicy]
  conditional_commutation := by simp [emptyPolicy]

/-- The full order is empty, including its visibility disjunct. -/
theorem paperOrder_empty (C : ReplayContext D.toUpdateSig)
    (E : Set (Op Update)) (a b : Op Update) :
    ¬ paperOrder emptyPolicy C E a b := by
  simp [paperOrder, emptyPolicy, all_commute a b]

/-- Removal contributes no retained timestamp; add contributes its event time. -/
theorem fold_mem_adds (ops : List (Op Update)) (t : Timestamp) :
    t ∈ applySeq D.toUpdateSig D.init ops ↔
      ∃ e ∈ ops, e.op = .add ∧ e.time = t := by
  induction ops using List.reverseRecOn with
  | nil => simp [applySeq, D]
  | append_singleton ops e ih =>
      rw [applySeq_append_single]
      rcases e with ⟨et, er, eo⟩
      cases eo <;>
        simp [D, mutate, Op.op, Op.time, List.mem_append, ih]
      all_goals grind

/-- The canonical state depends only on addition events, never their order. -/
theorem canonical_mem_adds {C : ReplayContext D.toUpdateSig}
    {E : Set (Op Update)} {s : D.State}
    (h : @IsCanonicalState D.toUpdateSig emptyPolicy.lift C E s) (t : Timestamp) :
    t ∈ s ↔ ∃ e ∈ E, e.op = .add ∧ e.time = t := by
  obtain ⟨π, hp, _, hf⟩ := h
  rw [← hf, fold_mem_adds]
  exact ⟨fun ⟨e, he, hop, ht⟩ => ⟨e, (hp.2 e).mp he, hop, ht⟩,
    fun ⟨e, he, hop, ht⟩ => ⟨e, (hp.2 e).mpr he, hop, ht⟩⟩

/-- The unchanged OR-set merge satisfies Join even when removals do nothing.
Timestamp uniqueness makes the retained-add image preserve intersections. -/
theorem mutant_join : @Join D emptyPolicy.lift := by
  letI : ReplayPolicy D.toUpdateSig := emptyPolicy.lift
  intro C E1 E2 s0 s1 s2 _ _ hs1 hs2 _ _ h0 h1 h2
  have hbase : s0 = s1 ∩ s2 := by
    ext t
    rw [canonical_mem_adds h0, Finset.mem_inter,
      canonical_mem_adds h1, canonical_mem_adds h2]
    constructor
    · rintro ⟨e, he, hop, ht⟩
      exact ⟨⟨e, he.1, hop, ht⟩, ⟨e, he.2, hop, ht⟩⟩
    · rintro ⟨⟨e1, he1, hop1, ht1⟩, ⟨e2, he2, hop2, ht2⟩⟩
      have heq : e1 = e2 := C.ts_unique (hs1 e1 he1) (hs2 e2 he2) (ht1.trans ht2.symm)
      exact ⟨e1, ⟨he1, heq ▸ he2⟩, hop1, ht1⟩
  have hmerge : D.merge s0 s1 s2 = s1 ∪ s2 := by
    rw [hbase]
    ext t
    simp only [D, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hh1 := h1
  have hh2 := h2
  obtain ⟨π1, hp1, _, _⟩ := hh1
  obtain ⟨π2, hp2, _, _⟩ := hh2
  let π := π1 ++ π2.filter (fun e => decide (e ∉ π1))
  have hp : listPermOf π (E1 ∪ E2) := listPermOf_union hp1 hp2
  have hr : respects π (@loOn D.toUpdateSig emptyPolicy.lift C (E1 ∪ E2)) := by
    unfold respects
    apply List.pairwise_of_forall
    intro a b
    exact fun hab => paperOrder_empty C (E1 ∪ E2) b a
      ((paperOrder_iff_loOn restrictedLaws C _ b a).mpr hab)
  have hc : @IsCanonicalState D.toUpdateSig emptyPolicy.lift C (E1 ∪ E2)
      (applySeq D.toUpdateSig D.init π) := ⟨π, hp, hr, rfl⟩
  have hstate : applySeq D.toUpdateSig D.init π = s1 ∪ s2 := by
    ext t
    rw [canonical_mem_adds hc, Finset.mem_union,
      canonical_mem_adds h1, canonical_mem_adds h2]
    constructor
    · rintro ⟨e, he1 | he2, hop, ht⟩
      · exact Or.inl ⟨e, he1, hop, ht⟩
      · exact Or.inr ⟨e, he2, hop, ht⟩
    · rintro (⟨e, he, hop, ht⟩ | ⟨e, he, hop, ht⟩)
      · exact ⟨e, Or.inl he, hop, ht⟩
      · exact ⟨e, Or.inr he, hop, ht⟩
  exact ⟨π, hp, hr, hstate.trans hmerge.symm⟩

private def isRemove (e : Op Update) : Bool := match e.op with
  | .remove => true
  | .add => false

private def removalsFirst (π : List (Op Update)) : List (Op Update) :=
  π.filter isRemove ++ π.filter (fun e => !isRemove e)

private theorem remove_fold (ops : List (Op Update))
    (h : ∀ e ∈ ops, e.op = .remove) :
    (ops.map Op.op).foldl setMachine.update false = false := by
  induction ops with
  | nil => rfl
  | cons e ops ih =>
      have hop := h e (by simp)
      change (ops.map Op.op).foldl setMachine.update (setMachine.update false e.op) = false
      rw [hop]
      exact ih (fun x hx => h x (by simp [hx]))

private theorem add_fold (ops : List (Op Update))
    (h : ∀ e ∈ ops, e.op = .add) (initial : Bool) :
    (ops.map Op.op).foldl setMachine.update initial = if ops = [] then initial else true := by
  induction ops generalizing initial with
  | nil => rfl
  | cons e ops ih =>
      have hop := h e (by simp)
      change (ops.map Op.op).foldl setMachine.update (setMachine.update initial e.op) = true
      rw [hop]
      simpa using ih (fun x hx => h x (by simp [hx])) true

/-- Reversing causal removes is sufficient for every history, not just the
small counterexample: the ordinary set then observes all retained additions. -/
private theorem removalsFirst_accepted (π : List (Op Update)) :
    spec.admits (projectedUpdates (D := D) (removalsFirst π) ++
      [.query () (D.query (applySeq D.toUpdateSig D.init π) ())]) := by
  let removals := π.filter isRemove
  let additions := π.filter (fun e => !isRemove e)
  have hr : ∀ e ∈ removals, e.op = .remove := by
    intro e he
    have hh := (List.mem_filter.mp he).2
    cases h : e.op <;> simp [isRemove, h] at hh ⊢
  have ha : ∀ e ∈ additions, e.op = .add := by
    intro e he
    have hh := (List.mem_filter.mp he).2
    cases h : e.op <;> simp [isRemove, h] at hh ⊢
  have hnon : (applySeq D.toUpdateSig D.init π).Nonempty ↔ additions ≠ [] := by
    rw [List.ne_nil_iff_length_pos]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨e, he, hop, _⟩ := (fold_mem_adds π t).mp ht
      apply List.length_pos_of_mem (a := e)
      exact List.mem_filter.mpr ⟨he, by simp [isRemove, hop]⟩
    · intro hp
      obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hp
      have hop := ha e he
      exact ⟨e.time, (fold_mem_adds π e.time).mpr
        ⟨e, (List.mem_filter.mp he).1, hop, rfl⟩⟩
  have labels : projectedUpdates (D := D) (removalsFirst π) =
      DeterministicSpec.updateLabels (Q := Unit) (V := Bool)
        ((removalsFirst π).map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map]
  rw [labels, spec, setMachine.updates_query_iff]
  change decide (applySeq D.toUpdateSig D.init π).Nonempty =
    ((removals ++ additions).map Op.op).foldl setMachine.update false
  rw [List.map_append, List.foldl_append, remove_fold removals hr, add_fold additions ha]
  by_cases hempty : additions = []
  · have hfalse : ¬ (applySeq D.toUpdateSig D.init π).Nonempty :=
      fun h => hnon.mp h hempty
    simp [hempty, hfalse]
  · simp [hempty, hnon.mpr hempty]

/-- Every raw reachable store has a canonical replay witness at every version. -/
theorem raw_replay_witness {C : Configuration D}
    (reach : (labeledTS D).ReachableFrom (initConfig D) C) :
    @HasReplayWitness D emptyPolicy.lift C := by
  letI : ReplayPolicy D.toUpdateSig := emptyPolicy.lift
  exact replayWitness_of_join mutant_join C reach

/-- The mutant converges on every raw execution, including historical versions. -/
theorem raw_store_convergence {C : Configuration D}
    (reach : (labeledTS D).ReachableFrom (initConfig D) C)
    {v w : Version} {s t : D.State} {E : Set (Op Update)}
    (hv : C.ver v = some (s, E)) (hw : C.ver w = some (t, E)) : s = t := by
  have hs := raw_replay_witness reach v s E hv
  have ht := raw_replay_witness reach w t E hw
  ext timestamp
  exact (canonical_mem_adds hs timestamp).trans (canonical_mem_adds ht timestamp).symm

/-- The literal criterion accepts the mutant in every raw execution, even
though its natural sequential behavior fails the independent set language. -/
theorem mutant_rawRA : RAImplementation D emptyPolicy spec := by
  apply raImplementation_of_reachable
  intro C reach r v s E _ hver q
  obtain ⟨π, hp, _, hf⟩ := raw_replay_witness reach v s E hver
  have hperm := List.filter_append_perm isRemove π
  have hp' : listPermOf (removalsFirst π) E :=
    ⟨hperm.nodup_iff.mpr hp.1, fun e => (hperm.mem_iff (a := e)).trans (hp.2 e)⟩
  refine ⟨removalsFirst π, hp', ?_, ?_⟩
  · unfold respects
    apply List.pairwise_of_forall
    exact fun a b => paperOrder_empty _ _ b a
  · cases q
    simpa [hf] using removalsFirst_accepted π

/-- Equal event sets determine the same state across separate raw executions. -/
theorem raw_cross_store_convergence {C C' : Configuration D}
    (reach : (labeledTS D).ReachableFrom (initConfig D) C)
    (reach' : (labeledTS D).ReachableFrom (initConfig D) C')
    {v w : Version} {s t : D.State} {E : Set (Op Update)}
    (hv : C.ver v = some (s, E)) (hw : C'.ver w = some (t, E)) : s = t := by
  have hs := raw_replay_witness reach v s E hv
  have ht := raw_replay_witness reach' w t E hw
  ext timestamp
  exact (canonical_mem_adds hs timestamp).trans (canonical_mem_adds ht timestamp).symm

/-- Canonical correctness also holds for every raw virtual-base execution. -/
theorem canonical_reachableV {C : Configuration D}
    (reach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C) :
    @CanonicalConfig D emptyPolicy.lift C := by
  letI : ReplayPolicy D.toUpdateSig := emptyPolicy.lift
  exact canonicalConfig_reachableV mutant_join reach

/-- Equal event sets converge even in the widened raw execution semantics. -/
theorem virtual_store_convergence {C : Configuration D}
    (reach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C)
    {v w : Version} {s t : D.State} {E : Set (Op Update)}
    (hv : C.ver v = some (s, E)) (hw : C.ver w = some (t, E)) : s = t := by
  letI : ReplayPolicy D.toUpdateSig := emptyPolicy.lift
  have canonical := canonical_reachableV reach
  ext timestamp
  exact (canonical_mem_adds (canonical.canonical v s E hv) timestamp).trans
    (canonical_mem_adds (canonical.canonical w t E hw) timestamp).symm

private def version1 (v : Version) : Option (D.State × Set (Op Update)) :=
  if v = 0 then some (∅, ∅) else if v = 1 then some ({1}, {addEvent}) else none
private def version2 (v : Version) : Option (D.State × Set (Op Update)) :=
  if v = 2 then some ({1}, {addEvent, removeEvent}) else version1 v
private def heads (v : Version) (r : Replica) : Option Version :=
  if r = 0 then some v else none
private def parents1 (v : Version) : List Version := if v = 1 then [0] else []
private def parents2 (v : Version) : List Version := if v = 2 then [1] else parents1 v

private theorem events1 {r : Replica} {E : Set (Op Update)}
    (h : headEventsFrom version1 (heads 1) r = some E) : E = {addEvent} := by
  by_cases hr : r = 0
  · subst r; simpa [headEventsFrom, version1, heads] using h.symm
  · simp [headEventsFrom, heads, hr] at h

private theorem events2 {r : Replica} {E : Set (Op Update)}
    (h : headEventsFrom version2 (heads 2) r = some E) :
    E = {addEvent, removeEvent} := by
  by_cases hr : r = 0
  · subst r; simpa [headEventsFrom, version2, heads] using h.symm
  · simp [headEventsFrom, heads, hr] at h

private theorem version1_cases {v : Version} {s : D.State} {E : Set (Op Update)}
    (h : version1 v = some (s, E)) :
    (v = 0 ∧ s = ∅ ∧ E = ∅) ∨ (v = 1 ∧ s = {1} ∧ E = {addEvent}) := by
  by_cases h0 : v = 0
  · simp [version1, h0] at h; exact Or.inl ⟨h0, h.1.symm, h.2.symm⟩
  · by_cases h1 : v = 1
    · simp [version1, h1] at h; exact Or.inr ⟨h1, h.1.symm, h.2.symm⟩
    · simp [version1, h0, h1] at h

/-- Real configuration after a single add, with the root retained. -/
def afterAdd : Configuration D where
  vis _ _ := False
  ver := version1
  head := heads 1
  parents := parents1
  parents_lt := by intro v p h; simp [parents1] at h; rcases h with ⟨rfl, rfl⟩; decide
  ver_init := by simp [version1]
  head_alloc := by intro r v h; simp [heads] at h; rcases h with ⟨rfl, rfl⟩; simp [version1]
  vis_src := by simp
  vis_tgt := by simp
  vis_causal := by simp
  timestamps_distinct := by
    intro a b r E r' E' hE ha hE' hb hne
    change a ∈ E at ha; change b ∈ E' at hb
    rw [events1 hE] at ha; rw [events1 hE'] at hb
    simp only [Set.mem_singleton_iff] at ha hb
    exact (hne (ha.trans hb.symm)).elim
  causal_mono := by simp
  vis_total_same_replica := by
    intro a b r E r' E' hE ha hE' hb hne _
    change a ∈ E at ha; change b ∈ E' at hb
    rw [events1 hE] at ha; rw [events1 hE'] at hb
    simp only [Set.mem_singleton_iff] at ha hb
    exact (hne (ha.trans hb.symm)).elim
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET hg hv1 hv2 hvT
    rcases version1_cases hv1 with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;>
      rcases version1_cases hv2 with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;>
      rcases version1_cases hvT with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    all_goals first
      | (solve | simp)
      | (solve | have hh := reaches_le (by intro v p h; simp [parents1] at h; rcases h with ⟨rfl, rfl⟩; decide) hg.1; norm_num at *)
      | (solve | have hh := reaches_le (by intro v p h; simp [parents1] at h; rcases h with ⟨rfl, rfl⟩; decide) hg.2.1; norm_num at *)
      | (solve | have hh := reaches_le (by intro v p h; simp [parents1] at h; rcases h with ⟨rfl, rfl⟩; decide) (hg.2.2 1 Relation.ReflTransGen.refl Relation.ReflTransGen.refl); norm_num at *)

private theorem version2_cases {v : Version} {s : D.State} {E : Set (Op Update)}
    (h : version2 v = some (s, E)) :
    (v = 0 ∧ s = ∅ ∧ E = ∅) ∨
    (v = 1 ∧ s = {1} ∧ E = {addEvent}) ∨
    (v = 2 ∧ s = {1} ∧ E = {addEvent, removeEvent}) := by
  by_cases h2 : v = 2
  · simp [version2, h2] at h; exact Or.inr (Or.inr ⟨h2, h.1.symm, h.2.symm⟩)
  · simp only [version2, if_neg h2] at h
    rcases version1_cases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem parents2_lt : ∀ v p, p ∈ parents2 v → p < v := by
  intro v p h
  by_cases h2 : v = 2
  · subst v; simp [parents2] at h; subst p; decide
  · simp [parents2, parents1, h2] at h; rcases h with ⟨rfl, rfl⟩; decide

private theorem events_mono {v w : Version} {sv sw : D.State}
    {Ev Ew : Set (Op Update)} (hv : version2 v = some (sv, Ev))
    (hw : version2 w = some (sw, Ew)) (hvw : v ≤ w) : Ev ⊆ Ew := by
  rcases version2_cases hv with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;>
    rcases version2_cases hw with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;>
    first | (solve | simp) | (solve | norm_num at *)

private theorem reaches2_of_le {v w : Version} (hv : v ≤ 2) (hw : w ≤ 2)
    (hvw : v ≤ w) : Reaches parents2 v w := by
  interval_cases v <;> interval_cases w
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by simp [parents2, parents1])
  · exact (Relation.ReflTransGen.single (show 0 ∈ parents2 1 by simp [parents2, parents1])).trans
      (Relation.ReflTransGen.single (show 1 ∈ parents2 2 by simp [parents2]))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by simp [parents2])
  · exact Relation.ReflTransGen.refl

/-- The actual removal keeps the add's entry and records the causal edge. -/
def afterRemove : Configuration D where
  vis a b := a = addEvent ∧ b = removeEvent
  ver := version2
  head := heads 2
  parents := parents2
  parents_lt := parents2_lt
  ver_init := by simp [version2, version1]
  head_alloc := by intro r v h; simp [heads] at h; rcases h with ⟨rfl, rfl⟩; simp [version2]
  vis_src := by rintro a b ⟨rfl, rfl⟩; exact ⟨0, {addEvent, removeEvent}, by simp [headEventsFrom, heads, version2], by change addEvent ∈ ({addEvent, removeEvent} : Set (Op Update)); simp⟩
  vis_tgt := by rintro a b ⟨rfl, rfl⟩; exact ⟨0, {addEvent, removeEvent}, by simp [headEventsFrom, heads, version2], by change removeEvent ∈ ({addEvent, removeEvent} : Set (Op Update)); simp⟩
  vis_causal := by
    rintro a b r E ⟨rfl, rfl⟩ hE _; change addEvent ∈ E; rw [events2 hE]; simp
  timestamps_distinct := by
    intro a b r E r' E' hE ha hE' hb hne
    change a ∈ E at ha; change b ∈ E' at hb
    rw [events2 hE] at ha; rw [events2 hE'] at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [addEvent, removeEvent] at *
  causal_mono := by rintro a b ⟨rfl, rfl⟩; decide
  vis_total_same_replica := by
    intro a b r E r' E' hE ha hE' hb hne _
    change a ∈ E at ha; change b ∈ E' at hb
    rw [events2 hE] at ha; rw [events2 hE'] at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [addEvent, removeEvent] at *
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET hg hv1 hv2 hvT
    have ht1 := reaches_le parents2_lt hg.1
    have ht2 := reaches_le parents2_lt hg.2.1
    have h1 : v1 ≤ 2 := by rcases version2_cases hv1 with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
    have h2 : v2 ≤ 2 := by rcases version2_cases hv2 with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
    have ht : vT = min v1 v2 := by
      have hm := hg.2.2 (min v1 v2)
        (reaches2_of_le ((min_le_left _ _).trans h1) h1 (min_le_left _ _))
        (reaches2_of_le ((min_le_right _ _).trans h2) h2 (min_le_right _ _))
      have hmt := reaches_le parents2_lt hm
      exact Nat.le_antisymm (Nat.le_min.mpr ⟨ht1, ht2⟩) hmt
    have hE1 := events_mono hvT hv1 ht1
    have hE2 := events_mono hvT hv2 ht2
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨hE1 hx, hE2 hx⟩
    · intro x hx
      by_cases hh : v1 ≤ v2
      · have hv : vT = v1 := ht.trans (min_eq_left hh)
        rw [hv, hv1, Option.some.injEq, Prod.mk.injEq] at hvT
        exact hvT.2 ▸ hx.1
      · have hv : vT = v2 := ht.trans (min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hh)))
        rw [hv, hv2, Option.some.injEq, Prod.mk.injEq] at hvT
        exact hvT.2 ▸ hx.2



/-- The first state is reached by the actual operational add rule. -/
theorem add_step : Step D (initConfig D) (.apply 1 0 .add) afterAdd := by
  apply Step.apply (D := D) (v := 0) (s := ∅) (ev := ∅) (vnew := 1)
  · simp [initConfig]
  · simp [initConfig, D]
  · intro e he
    rcases he with ⟨r, E, hE, he⟩
    unfold Configuration.headEvents headEventsFrom at hE
    by_cases hr : r = 0
    · simp [initConfig, hr] at hE; subst E; exact he.elim
    · simp [initConfig, hr] at hE
  · intro v s E hv e he
    by_cases h0 : v = 0
    · simp [initConfig, h0] at hv; rw [← hv.2] at he; exact he.elim
    · simp [initConfig, h0] at hv
  · simp [initConfig]
  · decide
  · funext a b
    apply propext
    change False ↔ (False ∨ ((a ∈ (∅ : Set (Op Update))) ∧ b = (1, 0, .add)))
    simp
  · funext v
    by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;>
      simp_all [afterAdd, version1, initConfig, D, mutate, Op.op, Op.time, addEvent]
  · funext r; by_cases hr : r = 0 <;> simp [afterAdd, heads, initConfig, hr]
  · funext v; simp [afterAdd, parents1, initConfig]

/-- The second rule really applies removal at the add's head. -/
theorem remove_step : Step D afterAdd (.apply 2 0 .remove) afterRemove := by
  apply Step.apply (D := D) (v := 1) (s := {1}) (ev := {addEvent}) (vnew := 2)
  · simp [afterAdd, heads]
  · simp [afterAdd, version1]
  · intro e he
    rcases he with ⟨r, E, hE, he⟩
    have hE' : headEventsFrom version1 (heads 1) r = some E := hE
    change e ∈ E at he
    rw [events1 hE'] at he
    simp only [Set.mem_singleton_iff] at he; subst e; decide
  · intro v s E hv e he
    have hv' : version1 v = some (s, E) := hv
    rcases version1_cases hv' with ⟨_, _, hE⟩ | ⟨_, _, hE⟩
    · rw [hE] at he; exact he.elim
    · rw [hE] at he
      simp only [Set.mem_singleton_iff] at he; subst e; decide
  · simp [afterAdd, version1]
  · decide
  · funext a b
    apply propext
    change (a = addEvent ∧ b = removeEvent) ↔
      (False ∨ ((a ∈ ({addEvent} : Set (Op Update))) ∧ b = (2, 0, .remove)))
    simp [removeEvent]
  · funext v
    simp [afterAdd, afterRemove, version2, D, mutate, Op.op, removeEvent, Set.pair_comm]
  · funext r; by_cases hr : r = 0 <;> simp [afterAdd, afterRemove, heads, hr]
  · funext v; simp [afterAdd, afterRemove, parents1, parents2]

theorem query_step : Step D afterRemove (.query 0 () true) afterRemove := by
  apply Step.query (D := D) (s := {1})
  · simp [Configuration.headState, headStateFrom, afterRemove, heads, version2]
  · decide

/-- A fully explicit reachable trace records the erroneous answer. -/
theorem bad_execution : (labeledTS D).Execution (initConfig D)
    [(.apply 1 0 .add, afterAdd), (.apply 2 0 .remove, afterRemove),
      (.query 0 () true, afterRemove)] :=
  .cons add_step (.cons remove_step (.cons query_step (.nil _)))

def issuance : Issuance D where
  CanIssue _ _ := True

private theorem honest_afterAdd : MintHonest D issuance.CanIssue afterAdd := by
  intro e he
  refine ⟨[], ?_, by simp [respects], True.intro⟩
  simp [listPermOf, afterAdd]

private theorem honest_afterRemove : MintHonest D issuance.CanIssue afterRemove := by
  intro e he
  obtain ⟨r, E, hE, he⟩ := he
  have hE' : headEventsFrom version2 (heads 2) r = some E := hE
  change e ∈ E at he
  rw [events2 hE'] at he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl
  · refine ⟨[], ?_, by simp [respects], True.intro⟩
    simp [listPermOf, afterRemove, addEvent, removeEvent]
  · refine ⟨[addEvent], ?_, by simp [respects], True.intro⟩
    constructor
    · simp
    · intro a
      simp only [List.mem_singleton]
      change (a = addEvent) ↔
        (a ∈ afterRemove.events ∧ a = addEvent ∧ removeEvent = removeEvent)
      have ha : addEvent ∈ afterRemove.events :=
        ⟨0, {addEvent, removeEvent}, by simp [Configuration.headEvents, headEventsFrom,
          afterRemove, heads, version2], by change addEvent ∈ ({addEvent, removeEvent} : Set (Op Update)); simp⟩
      simp only [and_true]
      exact ⟨fun h => ⟨h ▸ ha, h⟩, fun h => h.2⟩

/-- The counterexample also survives the retained issuance discipline. -/
theorem bad_mintCertified : MintCertifiedReach D issuance afterRemove := by
  have first : MintCertifiedReach D issuance afterAdd := .step .init
    (MintCertifiedReach.mintHonest (.init : MintCertifiedReach D issuance (initConfig D)))
    (.apply (v := 0) (s := (∅ : Finset Timestamp)) (by simp [initConfig]) (by simp [initConfig, D]) True.intro add_step)
    honest_afterAdd
  exact .step first honest_afterAdd
    (.apply (v := 1) (s := ({1} : Finset Timestamp)) (by simp [afterAdd, heads]) (by simp [afterAdd, version1]) True.intro remove_step)
    honest_afterRemove

/-- PASS pin: the natural causal history returns false in the set spec. -/
theorem causal_history_admitted :
    spec.admits [.update .add, .update .remove, .query () false] := by
  exact (setMachine.updates_query_iff [.add, .remove] () false).mpr rfl

/-- FAIL pin: the natural causal history cannot explain the implementation's true. -/
theorem causal_history_rejects_true :
    ¬ spec.admits [.update .add, .update .remove, .query () true] := by
  intro h
  have hh := (setMachine.updates_query_iff [.add, .remove] () true).mp h
  exact Bool.noConfusion hh

/-- The active definition nevertheless accepts the final configuration. -/
theorem wrong_answer_ra_linearizable :
    RALinearizable D emptyPolicy spec afterRemove := by
  intro r v s E hhead hver q
  have hhead' : heads 2 r = some v := hhead
  simp [heads] at hhead'
  rcases hhead' with ⟨rfl, rfl⟩
  have hver' : version2 2 = some (s, E) := hver
  simp [version2] at hver'
  rcases hver' with ⟨hs, hE⟩
  rw [← hs, ← hE]
  refine ⟨[removeEvent, addEvent], ?_, ?_, ?_⟩
  · simp [listPermOf, addEvent, removeEvent, or_comm]
  · simp [respects, paperOrder_empty]
  · cases q
    exact (setMachine.updates_query_iff [.remove, .add] () true).mpr rfl

/-- The accepting witness explicitly reverses an actual visibility edge. -/
theorem accepting_witness_violates_visibility :
    afterRemove.vis addEvent removeEvent ∧
    ¬ respects [removeEvent, addEvent] afterRemove.vis := by
  simp [afterRemove, respects, addEvent, removeEvent]

theorem fold_history_sound_fails : ¬ FoldHistorySound D spec := by
  intro h
  exact causal_history_rejects_true (h [addEvent, removeEvent] ())

private theorem enumeration_pair {π : List (Op Update)}
    (h : listPermOf π {addEvent, removeEvent}) :
    π = [addEvent, removeEvent] ∨ π = [removeEvent, addEvent] := by
  have hp : π.Perm [addEvent, removeEvent] := by
    apply (List.perm_ext_iff_of_nodup h.1 (by simp [addEvent, removeEvent])).mpr
    intro e
    simpa using h.2 e
  have hlen : π.length = 2 := by simpa using hp.length_eq
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := (h.2 a).mp (by simp)
  have hb := (h.2 b).mp (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp [listPermOf] at h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · simp [listPermOf] at h

theorem initial_ra_linearizable : RALinearizable D emptyPolicy spec (initConfig D) := by
  intro r v s E hhead hver q
  simp [initConfig] at hhead
  rcases hhead with ⟨rfl, rfl⟩
  simp [initConfig, D] at hver
  rcases hver with ⟨hs, hE⟩
  rw [← hs, ← hE]
  refine ⟨[], by simp [listPermOf], by simp [respects], ?_⟩
  cases q
  exact (setMachine.updates_query_iff [] () false).mpr rfl

theorem afterAdd_ra_linearizable : RALinearizable D emptyPolicy spec afterAdd := by
  intro r v s E hhead hver q
  have hhead' : heads 1 r = some v := hhead
  simp [heads] at hhead'
  rcases hhead' with ⟨rfl, rfl⟩
  have hver' : version1 1 = some (s, E) := hver
  simp [version1] at hver'
  rcases hver' with ⟨hs, hE⟩
  rw [← hs, ← hE]
  refine ⟨[addEvent], by simp [listPermOf], by simp [respects], ?_⟩
  cases q
  exact (setMachine.updates_query_iff [.add] () true).mpr rfl

/-- Every configuration in the actual bad execution satisfies the active criterion. -/
theorem bad_ra_execution : RAExecution D emptyPolicy spec (initConfig D)
    [(.apply 1 0 .add, afterAdd), (.apply 2 0 .remove, afterRemove),
      (.query 0 () true, afterRemove)] := by
  constructor
  · exact initial_ra_linearizable
  · intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl | rfl
    · exact afterAdd_ra_linearizable
    · exact wrong_answer_ra_linearizable
    · exact wrong_answer_ra_linearizable

/-- An independent query suffix distinguishes the two update orders. -/
theorem spec_add_remove_do_not_commute : ¬ spec.Commutes .add .remove := by
  intro h
  have hx := (h [] [.query () true]).mpr
    ((setMachine.updates_query_iff [.remove, .add] () true).mpr rfl)
  exact causal_history_rejects_true hx

theorem specification_conflicts_coverage_fails : ¬ SpecificationConflictsCovered D spec := by
  intro covered
  have conflict : ¬ spec.Commutes addEvent.op removeEvent.op :=
    spec_add_remove_do_not_commute
  exact covered addEvent removeEvent conflict (all_commute addEvent removeEvent)

/-- The appendix candidate rejects the same reachable wrong answer. -/
theorem wrong_answer_not_specification_ra :
    ¬ SpecificationRALinearizable D emptyPolicy spec afterRemove := by
  intro h
  obtain ⟨π, hp, _, hspecvis, haccept⟩ := h 0 2 {1} {addEvent, removeEvent}
    (by simp [afterRemove, heads]) (by simp [afterRemove, version2]) ()
  rcases enumeration_pair hp with rfl | rfl
  · exact causal_history_rejects_true haccept
  · have hv : specVisibility spec afterRemove.replayContext addEvent removeEvent :=
      ⟨⟨rfl, rfl⟩, spec_add_remove_do_not_commute⟩
    exact (List.pairwise_cons.mp hspecvis).1 addEvent (by simp) hv

/-- Exact comparison of the active definition and the separately stated candidate. -/
theorem criteria_differ_on_reachable_mutation :
    MintCertifiedReach D issuance afterRemove ∧
    RALinearizable D emptyPolicy spec afterRemove ∧
    ¬ SpecificationRALinearizable D emptyPolicy spec afterRemove :=
  ⟨bad_mintCertified, wrong_answer_ra_linearizable, wrong_answer_not_specification_ra⟩

#print axioms mutant_rawRA
#print axioms raw_cross_store_convergence
#print axioms mutant_join
#print axioms raw_store_convergence
#print axioms canonical_reachableV
#print axioms virtual_store_convergence
#print axioms wrong_answer_ra_linearizable
#print axioms bad_execution
#print axioms bad_ra_execution
#print axioms criteria_differ_on_reachable_mutation
end Sal.MRDTs.Paper1.CriterionCounterexample
