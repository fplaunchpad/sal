import Sal.MRDTs.Paper1.RGAEventSpec

/-! Native RGA client requests use positions; generated messages use identities.
This module preserves the original issuer and identified history languages.
It proves local ordinary-list effects under explicit view assumptions, not a
concurrent positional-list certificate. The corrected source issuer reserves identifier 0 exclusively for the root.
-/
namespace Sal.MRDTs.Paper1.RGA.Client
open Foundation Instances.RGA

inductive Request where
  | insert (index : Nat)
  | delete (index : Nat)
  deriving DecidableEq

def step (view : List Nat) (stamp : Nat) : Request → List Nat
  | .insert index => view.take index ++ stamp :: view.drop index
  | .delete index => view.take index ++ view.drop (index + 1)

def anchorAt (view : List Nat) (index : Nat) : Nat :=
  if index = 0 then 0 else view.getD (index - 1) 0

/-- The clock/replica are supplied by the replication layer, not the client.
Bounds reject malformed positions. No new freshness or live-parent restriction
is imposed on the existing issuer by this preparation function. -/
def prepare (view : List Nat) (stamp replica : Nat) : Request → Option (Op RGAOp)
  | .insert index =>
      if index ≤ view.length then
        let anchor := anchorAt view index
        if (anchor = 0 ∧ 0 < stamp) ∨ anchor < stamp then some (stamp,replica,.addAfter anchor) else none
      else none
  | .delete index =>
      if index < view.length then some (stamp,replica,.remove (view.getD index 0)) else none

/-- A complete materialized view relates visible IDs to the original Boolean
birth/grave state, without changing its update or issuance predicate. -/
def LiveView (s : RGAM.State) (view : List Nat) : Prop :=
  ∀ id, id ∈ view ↔ s.2 id = false ∧ ∃ anchor, s.1 (id,anchor) = true

def Fresh (s : RGAM.State) (stamp : Nat) : Prop :=
  (∀ anchor, s.1 (stamp,anchor) = false) ∧ s.2 stamp = false

private theorem getD_mem (view : List Nat) (index : Nat) (h : index < view.length) :
    view.getD index 0 ∈ view := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_mem h

private theorem getD_at (view : List Nat) (index : Nat) (h : index < view.length) :
    view.getD index 0 = view[index] := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  rfl

theorem prepared_canIssue {s : RGAM.State} {view : List Nat}
    (observed : LiveView s view) {stamp replica : Nat} (fresh : Fresh s stamp)
    {request : Request} {event : Op RGAOp}
    (prepared : prepare view stamp replica request = some event) : applicable event s := by
  cases request with
  | insert index =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      split at prepared
      next clock =>
        cases prepared
        refine ⟨?_,fresh.1,fresh.2⟩
        rcases clock with root | newer
        · exact Or.inl root
        · by_cases root : anchorAt view index = 0
          · exact Or.inl ⟨root,Nat.zero_lt_of_lt newer⟩
          · have indexPositive : index ≠ 0 := by intro h; simp [anchorAt,h] at root
            have member : anchorAt view index ∈ view := by
              simp only [anchorAt,if_neg indexPositive]
              exact getD_mem view (index-1) (by omega)
            obtain ⟨live,born⟩ := (observed _).mp member
            exact Or.inr ⟨live,newer,born⟩
      next => simp at prepared
    next => simp at prepared
  | delete index =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      cases prepared
      obtain ⟨live,born⟩ := (observed _).mp (getD_mem view index bound)
      exact ⟨born,live⟩
    next => simp at prepared

/-- Every source-issuable message has a corresponding positional request
in a complete view. Arbitrary caller clocks still must satisfy the original source guard. -/
theorem covers_original_issuer {s : RGAM.State} {view : List Nat}
    (observed : LiveView s view) {event : Op RGAOp} (issued : applicable event s) :
    ∃ request, prepare view event.1 event.2.1 request = some event := by
  rcases event with ⟨stamp,replica,op⟩
  cases op with
  | addAfter anchor =>
    rcases issued.1 with root | ⟨live,newer,born⟩
    · obtain ⟨rfl,positive⟩ := root
      exact ⟨.insert 0,by simp [prepare,anchorAt,positive]⟩
    · have member : anchor ∈ view := (observed anchor).mpr ⟨live,born⟩
      obtain ⟨index,bound,eq⟩ := List.mem_iff_getElem.mp member
      refine ⟨.insert (index+1),?_⟩
      have selected : anchorAt view (index+1) = anchor := by
        have positive : index+1 ≠ 0 := by omega
        rw [anchorAt,if_neg positive,Nat.add_sub_cancel,getD_at view index bound]
        exact eq
      simp [prepare,selected,newer,show index+1 ≤ view.length by omega]
  | remove id =>
    have member : id ∈ view := (observed id).mpr ⟨issued.2,issued.1⟩
    obtain ⟨index,bound,eq⟩ := List.mem_iff_getElem.mp member
    refine ⟨.delete index,?_⟩
    simp [prepare,bound,getD_at view index bound,eq]

private theorem insertAfter_positional (view : List Nat) (unique : view.Nodup)
    (noRoot : 0 ∉ view) (stamp index : Nat) (bound : index ≤ view.length) :
    insertAfter (anchorAt view index) stamp view = step view stamp (.insert index) := by
  induction view generalizing index with
  | nil => have hz : index = 0 := by simp at bound; exact bound
           subst index; rfl
  | cons head tail ih =>
    obtain ⟨headFresh,tailUnique⟩ := List.nodup_cons.mp unique
    have headNonzero : head ≠ 0 := by intro h; exact noRoot (by simp [h])
    have tailNoRoot : 0 ∉ tail := fun h => noRoot (List.mem_cons_of_mem _ h)
    cases index with
    | zero => rfl
    | succ index =>
      cases index with
      | zero => simp [anchorAt,insertAfter,step,headNonzero]
      | succ index =>
        have selected : tail.getD index 0 ∈ tail := getD_mem tail index (by simp at bound; omega)
        have diff : head ≠ tail.getD index 0 := fun h => headFresh (h ▸ selected)
        have nonzero : tail.getD index 0 ≠ 0 := fun h => tailNoRoot (h ▸ selected)
        have previous := ih tailUnique tailNoRoot (index+1) (by simp at bound; omega)
        simp only [List.getD_eq_getElem?_getD] at diff nonzero
        simpa [anchorAt,insertAfter,step,diff,nonzero,List.getD_cons_succ] using congrArg (List.cons head) previous

private theorem delete_positional (view : List Nat) (unique : view.Nodup)
    (index : Nat) (bound : index < view.length) :
    view.filter (· ≠ view.getD index 0) = step view 0 (.delete index) := by
  rw [getD_at view index bound]
  have filters : view.filter (· ≠ view[index]) = view.filter (· != view[index]) := by
    congr 1
    funext x
    by_cases h : x = view[index] <;> simp [h]
  rw [filters,← unique.erase_eq_filter,unique.erase_getElem index bound,List.eraseIdx_eq_take_drop_succ]
  rfl

/-- Local ordinary-list refinement through the strict identified machine.
The generic view lemma states zero exclusion; certified_no_root discharges it
for every state in the corrected source certified domain. -/
theorem prepared_refines_identified {view : List Nat} (unique : view.Nodup)
    (noRoot : 0 ∉ view) {allocated : Finset Nat} {stamp replica : Nat}
    (fresh : stamp ∉ allocated) {request : Request} {event : Op RGAOp}
    (prepared : prepare view stamp replica request = some event) :
    ∃ allocated', EventSpec.machine.transition (view,allocated) (.update event)
      (step view stamp request,allocated') := by
  cases request with
  | insert index =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      split at prepared
      next clock =>
        cases prepared
        refine ⟨insert stamp allocated,?_⟩
        rw [EventSpec.insertion_uses_timestamp]
        refine ⟨⟨?_,fresh⟩,?_,?_⟩
        · rcases clock with root | newer
          · exact root.2
          · exact Nat.zero_lt_of_lt newer
        · by_cases root : index = 0
          · left; simp [anchorAt,root]
          · right; simp only [anchorAt,if_neg root]
            exact getD_mem view (index-1) (by omega)
        · rw [insertAfter_positional view unique noRoot stamp index bound]
      next => simp at prepared
    next => simp at prepared
  | delete index =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      cases prepared
      refine ⟨allocated,?_⟩
      rw [EventSpec.deletion_uses_target]
      rw [delete_positional view unique index bound]
      rfl
    next => simp at prepared

/-- Certified raw apply forces its clock above every observed event through
configuration coherence, independently of the application's issuer guard. -/
theorem apply_clock_above_observed {C C' : Configuration RGAM} {stamp replica : Nat}
    {op : RGAOp} (one : Step RGAM C (.apply stamp replica op) C') :
    ∀ e, ∀ v s E, C.head replica = some v → C.ver v = some (s,E) →
      e ∈ E → e.1 < stamp := by
  cases one with
  | apply headAt versionAt freshTime freshStore freshVersion rank C' vis ver head parents =>
    intro e v s E hh hv he
    have sameV := Option.some.inj (headAt.symm.trans hh)
    subst v
    have same := Option.some.inj (versionAt.symm.trans hv)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact C'.causal_mono (by rw [vis]; exact Or.inr ⟨he,rfl⟩)

theorem corrected_root_guard_control :
    applicable (1,0,.addAfter 0) RGAM.init ∧
    ¬ applicable (0,0,.addAfter 0) RGAM.init ∧
    prepare [] 1 0 (.insert 0) = some (1,0,.addAfter 0) ∧
    prepare [] 0 0 (.insert 0) = none := by simp [applicable,RGAM,prepare,anchorAt]

theorem root_boundary_control :
    ¬ applicable (0,0,.addAfter 0) RGAM.init ∧
    prepare [0] 1 0 (.insert 1) = some (1,0,.addAfter 0) ∧
    insertAfter 0 1 [0] = [1,0] ∧ step [0] 1 (.insert 1) = [0,1] ∧
    insertAfter 0 1 [0] ≠ step [0] 1 (.insert 1) := by
  simp [applicable,RGAM,prepare,anchorAt,insertAfter,step]

theorem client_controls :
    prepare [4,6] 9 0 (.insert 1) = some (9,0,.addAfter 4) ∧
    insertAfter 4 9 [4,6] = [4,9,6] ∧ insertAfter 4 9 [4,6] ≠ [4,6,9] ∧
    prepare [4,6] 9 0 (.delete 1) = some (9,0,.remove 6) ∧
    prepare [4,6] 9 0 (.insert 3) = none ∧ prepare [] 9 0 (.delete 0) = none := by decide

/-! A dropped-guard raw first insertion can allocate the root identifier.
The following one-step raw configuration pins that dropped-guard boundary. -/
def zeroEvent : Op RGAOp := (0,0,.addAfter 0)
noncomputable def zeroState : RGAM.State := RGAM.update RGAM.init zeroEvent
private noncomputable def zeroVer (v : Version) : Option (RGAM.State × Set (Op RGAOp)) :=
  if v = 0 then some (RGAM.init,∅) else if v = 1 then some (zeroState,{zeroEvent}) else none
private def zeroHead (r : Replica) : Option Version := if r = 0 then some 1 else none
private def zeroParents (v : Version) : List Version := if v = 1 then [0] else []
private theorem zero_rank : ∀ v p, p ∈ zeroParents v → p < v := by
  intro v p h
  by_cases hv : v = 1 <;> simp [zeroParents,hv] at h
  subst v; subst p; decide
private theorem zero_observed {r : Replica} {E : Set (Op RGAOp)}
    (h : headEventsFrom zeroVer zeroHead r = some E) {e : Op RGAOp} (he : e ∈ E) :
    e = zeroEvent := by
  by_cases hr : r = 0
  · subst r
    simp [headEventsFrom,zeroHead,zeroVer] at h
    subst E
    exact he
  · simp [headEventsFrom,zeroHead,hr] at h
private theorem zero_version_cases {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (h : zeroVer v = some (s,E)) :
    (v = 0 ∧ s = RGAM.init ∧ E = ∅) ∨ (v = 1 ∧ s = zeroState ∧ E = {zeroEvent}) := by
  by_cases hv : v = 0
  · simp [zeroVer,hv] at h
    exact Or.inl ⟨hv,h.1.symm,h.2.symm⟩
  · by_cases h1 : v = 1
    · simp [zeroVer,hv,h1] at h
      exact Or.inr ⟨h1,h.1.symm,h.2.symm⟩
    · simp [zeroVer,hv,h1] at h

noncomputable def zeroConfig : Configuration RGAM where
  vis := fun _ _ => False
  ver := zeroVer
  head := zeroHead
  parents := zeroParents
  parents_lt := zero_rank
  ver_init := by simp [zeroVer]
  head_alloc := by
    intro r v h
    by_cases hr : r = 0
    · simp [zeroHead,hr] at h
      subst v; simp [zeroVer]
    · simp [zeroHead,hr] at h
  vis_src := fun h => h.elim
  vis_tgt := fun h => h.elim
  vis_causal := fun h => h.elim
  timestamps_distinct := by
    intro a b r E r' E' ha he hb he' different
    exact (different ((zero_observed ha he).trans (zero_observed hb he').symm)).elim
  causal_mono := fun h => h.elim
  vis_total_same_replica := by
    intro a b r E r' E' ha he hb he' different same
    exact (different ((zero_observed ha he).trans (zero_observed hb he').symm)).elim
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET gca hv1 hv2 hvT
    rcases zero_version_cases hv1 with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals rcases zero_version_cases hv2 with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals rcases zero_version_cases hvT with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals try simp
    all_goals try (simp only [IsGCA] at gca)
    all_goals try (exact (Nat.not_succ_le_zero 0 (reaches_le zero_rank gca.1)).elim)
    all_goals try (exact (Nat.not_succ_le_zero 0 (reaches_le zero_rank gca.2.1)).elim)
    exact (Nat.not_succ_le_zero 0 (reaches_le zero_rank (gca.2.2 1 .refl .refl))).elim

private theorem init_no_events : (initConfig RGAM).events = ∅ := by
  ext e
  constructor
  · rintro ⟨r,E,h,he⟩
    by_cases hr : r = 0
    · simp [Configuration.headEvents,headEventsFrom,initConfig,hr] at h
      subst E; exact he
    · simp [Configuration.headEvents,headEventsFrom,initConfig,hr] at h
  · intro h; exact h.elim

theorem zero_step : Step RGAM (initConfig RGAM) (.apply 0 0 (.addAfter 0)) zeroConfig := by
  apply Step.apply (v := 0) (s := RGAM.init) (ev := ∅) (vnew := 1)
  · simp [initConfig]
  · simp [initConfig]
  · intro e he
    rw [init_no_events] at he
    exact he.elim
  · intro w sw Ew hw e he
    by_cases h0 : w = 0
    · simp [initConfig,h0] at hw
      obtain ⟨rfl,rfl⟩ := hw
      exact he.elim
    · simp [initConfig,h0] at hw
  · simp [initConfig]
  · decide
  · ext a b; change False ↔ False ∨ ((∅ : Set (Op RGAOp)) a ∧ b = _); simp only [false_or]; constructor <;> intro h; exact h.elim; exact h.1.elim
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1
    all_goals simp [zeroConfig,zeroVer,zeroState,zeroEvent,initConfig,h0,h1]
  · funext r
    by_cases hr : r = 0 <;> simp [zeroConfig,zeroHead,initConfig,hr]
  · rfl

theorem zero_actual_read : read zeroState = [0] := by
  have h := read_eq_sequence_of_birthGraveRel (birthGraveSound [zeroEvent])
  simpa [zeroState,zeroEvent,applySeq,SequentialMachine.run,birthGraveMachine,
    Instances.RGA.sequence,insertAfter] using h

theorem zero_successor_actual_read :
    read (RGAM.update zeroState (1,0,.addAfter 0)) = [1,0] := by
  have h := read_eq_sequence_of_birthGraveRel
    (birthGraveSound [zeroEvent,(1,0,.addAfter 0)])
  have seq : Instances.RGA.sequence ⟨{(1,0),(0,0)},∅⟩ = [1,0] := by
    let q : Finset (Nat × Nat) := {(1,0),(0,0)}
    have length : q.toList.length = 2 := by simp [q]
    obtain ⟨a,b,order⟩ := List.length_eq_two.mp length
    have ha : a ∈ q := by rw [← Finset.mem_toList,order]; simp
    have hb : b ∈ q := by rw [← Finset.mem_toList,order]; simp
    have different : a ≠ b := by have h := q.nodup_toList; rw [order] at h; simpa using h
    simp only [q,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals try exact (different rfl).elim
    all_goals simp [Instances.RGA.sequence,← show q = {(1,0),(0,0)} from rfl,order,insertAfter]
    all_goals simp [List.mergeSort,List.merge,insertAfter]
  simpa [zeroState,zeroEvent,applySeq,SequentialMachine.run,birthGraveMachine,seq] using h

theorem certified_insert_positive {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) {t r anchor : Nat}
    (member : (t,r,.addAfter anchor) ∈ C.events) : 0 < t := by
  obtain ⟨past,_,_,guard⟩ := exec.mintHonest _ member
  rcases guard.1 with root | earlier
  · exact root.2
  · exact Nat.zero_lt_of_lt earlier.2.1

private theorem insertAfter_no_root (view : List Nat) (noRoot : 0 ∉ view)
    (anchor stamp : Nat) (positive : 0 < stamp) : 0 ∉ insertAfter anchor stamp view := by
  induction view with
  | nil => simp [insertAfter,Nat.ne_of_gt positive,Ne.symm (Nat.ne_of_gt positive)]
  | cons head tail ih =>
    have headNonzero : head ≠ 0 := fun h => noRoot (by simp [h])
    have tailNoRoot : 0 ∉ tail := fun h => noRoot (List.mem_cons_of_mem _ h)
    by_cases root : anchor = 0 <;> by_cases same : head = anchor
    all_goals simp_all [insertAfter,Ne.symm (Nat.ne_of_gt positive)]

private theorem list_run_no_root (ops : List (Op RGAOp))
    (positive : ∀ t r a, (t,r,.addAfter a) ∈ ops → 0 < t) :
    ¬ List.Mem 0 (listSpec.run ops) := by
  induction ops using List.reverseRecOn with
  | nil => change ¬ List.Mem 0 []; intro h; cases h
  | append_singleton ops e ih =>
    have old : ∀ t r a, (t,r,.addAfter a) ∈ ops → 0 < t :=
      fun t r a h => positive t r a (List.mem_append_left _ h)
    rw [SequentialSpec.run_append_single]
    rcases e with ⟨t,r,op⟩
    cases op with
    | addAfter a => exact insertAfter_no_root _ (ih old) a t (positive t r a (by simp))
    | remove id => exact fun h => ih old (List.mem_of_mem_filter h)

theorem certified_no_root {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (version : C.ver v = some (s,E)) : 0 ∉ read s := by
  have replay : HasReplayWitness C := by
    cases exec with
    | ordinary reach => exact replayAdequacy.sound reach
    | virtual reach => exact replayAdequacy.soundV reach
  obtain ⟨ops,perm,_,fold⟩ := replay v s E version
  have wf := versionWellFormed_of_execution exec version
  have href := canonical_refines_list perm wf
  have state := (canonical_fold ops).trans fold
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) = listSpec.run (canonical ops) at href
  rw [state] at href
  rw [href]
  apply list_run_no_root
  intro t r a h
  have good := exec.canonicalConfig (fun _ _ => Instances.RGA.join _)
  apply certified_insert_positive exec
  exact good.version_events_supported v s E version _ ((canonical_listPermOf perm).2 _ |>.mp h)

theorem prepared_refines_certified {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) {v : Version} {s : RGAM.State}
    {E : Set (Op RGAOp)} (version : C.ver v = some (s,E))
    (unique : (read s).Nodup) {allocated : Finset Nat} {stamp replica : Nat}
    (fresh : stamp ∉ allocated) {request : Request} {event : Op RGAOp}
    (prepared : prepare (read s) stamp replica request = some event) :
    ∃ allocated', EventSpec.machine.transition (read s,allocated) (.update event)
      (step (read s) stamp request,allocated') := by
  exact prepared_refines_identified unique (certified_no_root exec version) fresh prepared

#print axioms prepared_refines_certified
#print axioms certified_no_root
/-- Counterfactual raw trace admitted only after dropping the root-ID guard.
It is not an execution certified by the corrected source issuer. -/
theorem dropped_guard_root_boundary :
    Step RGAM (initConfig RGAM) (.apply 0 0 (.addAfter 0)) zeroConfig ∧
    ¬ applicable zeroEvent RGAM.init ∧ read zeroState = [0] ∧
    read (RGAM.update zeroState (1,0,.addAfter 0)) = [1,0] ∧
    read (RGAM.update zeroState (1,0,.addAfter 0)) ≠ step [0] 1 (.insert 1) := by
  refine ⟨zero_step,root_boundary_control.1,zero_actual_read,zero_successor_actual_read,?_⟩
  rw [zero_successor_actual_read]; decide

#print axioms dropped_guard_root_boundary
#print axioms zero_successor_actual_read
#print axioms zero_actual_read

#print axioms prepared_canIssue
#print axioms covers_original_issuer
#print axioms prepared_refines_identified
end Sal.MRDTs.Paper1.RGA.Client
