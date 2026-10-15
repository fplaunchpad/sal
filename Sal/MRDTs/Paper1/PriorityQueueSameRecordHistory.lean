import Sal.MRDTs.Paper1.PriorityQueueSameRecordAggregate
import Sal.MRDTs.Paper1.PriorityQueueSameRecordOrdering
import Sal.MRDTs.Paper1.PriorityQueueSameRecordComposition
import Sal.MRDTs.Framework.Base.FiniteOrder

/-! Construction of ordinary per-element explaining orders. The independent
priority map contains no insertion metadata; snapshots are used only to prove
which ordinary explaining order may be selected. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord
open Classical

def Targets (tag : Instances.PublishedAddWinsPriorityQueue.Tag) (e : Event) : Prop :=
  match e.op with | .inc x _ observed => tag.1 = x ∧ tag.2 ∈ observed | _ => False

instance targetsDecidable (tag : Instances.PublishedAddWinsPriorityQueue.Tag) (e : Event) :
    Decidable (Targets tag e) := by unfold Targets; cases e.op <;> infer_instance

theorem targets_iff (x t : Nat) (e : Event) :
    Targets (x,t) e ↔ ∃ n observed, e.op = .inc x n observed ∧ t ∈ observed := by
  rcases e with ⟨et,er,op⟩
  cases op <;> simp [Targets,Op.op] <;> grind

private theorem targets_attachment (x t : Nat) (e : Event) (targeted : Targets (x,t) e) :
    ∃ n, ((x,t),e.time,n) ∈ (step {} e).increments := by
  obtain ⟨n,observed,op,seen⟩ := (targets_iff x t e).mp targeted
  rcases e with ⟨et,er,payload⟩
  change payload = .inc x n observed at op
  subst payload
  refine ⟨n,?_⟩
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨t,seen,rfl⟩

private theorem targets_key (x t : Nat) (e : Event) (targeted : Targets (x,t) e) :
    elementOf e.op = x := by
  obtain ⟨n,observed,op,_⟩ := (targets_iff x t e).mp targeted
  simp only [op,elementOf]

private theorem targeted_amount (tag : Instances.PublishedAddWinsPriorityQueue.Tag) (e : Event) :
    incrementAmountFor tag e = if Targets tag e then incrementAmount e else 0 := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [incrementAmountFor,incrementAmount,Targets,Op.op]

theorem target_sum (events : List Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    (events.map (incrementAmountFor tag)).sum =
      ((events.filter (fun e => decide (Targets tag e))).map incrementAmount).sum := by
  induction events with
  | nil => rfl
  | cons e events ih =>
    by_cases targeted : Targets tag e <;>
      simp [List.filter_cons,targeted_amount,targeted,ih]

def FinalSegment (birth : Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) (e : Event) : Bool :=
  decide (e = birth ∨ Targets tag e)

/-- A live birth and its attached increments can be moved to a final segment
while preserving every same-element visibility edge. -/
theorem present_order (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (x t : Nat) (v : Int)
    (localEvents : List Event)
    (localEnum : listPermOf localEvents {e ∈ E | elementOf e.op = x})
    (ordered : respects localEvents C.vis)
    (birth : Event) (birthMember : birth ∈ E)
    (born : ((x,t),v) ∈ (step {} birth).births)
    (alive : (x,t) ∉ (applySeq D.toUpdateSig D.init events).removed) :
    ∃ pre rest, (pre ++ birth :: rest).Perm localEvents ∧
      respects (pre ++ birth :: rest) C.vis ∧
      (∀ e ∈ pre, ¬ Targets (x,t) e) ∧
      (∀ e ∈ rest, Targets (x,t) e) := by
  have birthOp := (birth_effect_iff birth x t v).mp born
  have birthKey : elementOf birth.op = x := by simp [birthOp.1,elementOf]
  have birthLocal : birth ∈ localEvents := (localEnum.2 birth).mpr ⟨birthMember,birthKey⟩
  have birthNotTargeted : ¬ Targets (x,t) birth := by simp [Targets,birthOp.1]
  let selected := FinalSegment birth (x,t)
  have first : selected birth = true := by simp [selected,FinalSegment]
  have before : ∀ e ∈ localEvents, selected e = true → e ≠ birth → C.vis birth e := by
    intro e he yes different
    have targeted : Targets (x,t) e := by
      simpa [selected,FinalSegment,different] using yes
    exact attached_increment_visible C honest trans birth e (supported birth birthMember)
      (supported e ((localEnum.2 e).mp he).1) x t v born (targets_attachment x t e targeted)
  have forward : ∀ a ∈ localEvents, ∀ b ∈ localEvents,
      selected a = true → C.vis a b → selected b = true := by
    intro a ha b hb yes edge
    have aSelected : a = birth ∨ Targets (x,t) a := by simpa [selected,FinalSegment] using yes
    have birthBefore : C.vis birth b := by
      rcases aSelected with rfl | targeted
      · exact edge
      · exact trans (attached_increment_visible C honest trans birth a (supported birth birthMember)
          (supported a ((localEnum.2 a).mp ha).1) x t v born (targets_attachment x t a targeted)) edge
    have bE := (localEnum.2 b).mp hb
    have targeted := (targets_iff x t b).mpr (surviving_birth_successor C honest trans events E enumerated
      supported closed birth b bE.1 birthBefore x t v born alive bE.2)
    simp [selected,FinalSegment,targeted]
  obtain ⟨rest,perm,order,suffix⟩ := exists_partitioned_order selected localEvents C.vis ordered birth
    birthLocal first forward before
  refine ⟨localEvents.filter (fun e => !selected e),rest,perm,order,?_,?_⟩
  · intro e he targeted
    have no := (List.mem_filter.mp he).2
    simp [selected,FinalSegment,targeted] at no
  · intro e he
    have selectedE := (List.mem_filter.mp (show e ∈ localEvents.filter selected by rw [suffix]; simp [he])).2
    have different : e ≠ birth := by
      intro equal
      subst e
      have nodup := localEnum.1.filter selected
      rw [suffix] at nodup
      exact (List.nodup_cons.mp nodup).1 he
    simpa [selected,FinalSegment,different] using selectedE

private theorem target_sums_same (a b : List Event)
    (ha : a.Nodup) (hb : b.Nodup) (tag : Instances.PublishedAddWinsPriorityQueue.Tag)
    (same : ∀ e, e ∈ a ∧ Targets tag e ↔ e ∈ b ∧ Targets tag e) :
    (a.map (incrementAmountFor tag)).sum = (b.map (incrementAmountFor tag)).sum := by
  rw [target_sum,target_sum]
  have perm : (a.filter (fun e => decide (Targets tag e))).Perm
      (b.filter (fun e => decide (Targets tag e))) := by
    apply (List.perm_ext_iff_of_nodup (ha.filter _) (hb.filter _)).mpr
    intro e
    simpa only [List.mem_filter,decide_eq_true_eq] using same e
  exact (perm.map incrementAmount).sum_eq

private theorem no_target_sum (events : List Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag)
    (none : ∀ e ∈ events, ¬ Targets tag e) : (events.map (incrementAmountFor tag)).sum = 0 := by
  induction events with
  | nil => rfl
  | cons e events ih =>
    simp only [List.map_cons,List.sum_cons,targeted_amount,if_neg (none e List.mem_cons_self)]
    rw [ih (fun e he => none e (List.mem_cons_of_mem _ he)),zero_add]

/-- The constructed present-element order replays the independent ordinary
cell to exactly the repaired concrete priority, with all required causal edges
within that element preserved. -/
theorem present_replay (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (distinct : events.Pairwise (fun a b => a.time ≠ b.time))
    (x t : Nat) (v : Int)
    (localEvents : List Event)
    (localEnum : listPermOf localEvents {e ∈ E | elementOf e.op = x})
    (ordered : respects localEvents C.vis)
    (birth : Event) (birthMember : birth ∈ E)
    (born : ((x,t),v) ∈ (step {} birth).births)
    (alive : (x,t) ∉ (applySeq D.toUpdateSig D.init events).removed) :
    ∃ replay, listPermOf replay {e ∈ E | elementOf e.op = x} ∧ respects replay C.vis ∧
      (replay.foldl seqStep model.initial).2 x =
        some (v + Instances.PublishedAddWinsPriorityQueue.acquired
          (applySeq D.toUpdateSig D.init events) (x,t)) := by
  obtain ⟨pre,rest,perm,order,preNone,restTargets⟩ := present_order C honest trans events E enumerated
    supported closed x t v localEvents localEnum ordered birth birthMember born alive
  have replayEnum : listPermOf (pre ++ birth :: rest) {e ∈ E | elementOf e.op = x} :=
    ⟨perm.symm.nodup localEnum.1,fun e => perm.mem_iff.trans (localEnum.2 e)⟩
  have bornOp := (birth_effect_iff birth x t v).mp born
  have birthNoTarget : ¬ Targets (x,t) birth := by simp [Targets,bornOp.1]
  have amountSame := target_sums_same events (pre ++ birth :: rest) enumerated.1 replayEnum.1 (x,t) (by
    intro e
    rw [enumerated.2,replayEnum.2]
    constructor
    · rintro ⟨member,targeted⟩
      exact ⟨⟨member,targets_key x t e targeted⟩,targeted⟩
    · rintro ⟨⟨member,_⟩,targeted⟩
      exact ⟨member,targeted⟩)
  have restAmount : rest.map (incrementAmountFor (x,t)) = rest.map incrementAmount := by
    apply List.map_congr_left
    intro e he
    exact (targeted_amount _ e).trans (if_pos (restTargets e he))
  have sumEq : (events.map (incrementAmountFor (x,t))).sum = (rest.map incrementAmount).sum := by
    rw [amountSame,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      no_target_sum pre (x,t) preNone,targeted_amount,if_neg birthNoTarget,restAmount]
    simp
  refine ⟨pre ++ birth :: rest,replayEnum,order,?_⟩
  rw [seqFold_cell,List.foldl_append,List.foldl_cons]
  have increments : ∀ e ∈ rest, ∃ amount observed, e.op = .inc x amount observed := by
    intro e he
    obtain ⟨n,observed,op,_⟩ := (targets_iff x t e).mp (restTargets e he)
    exact ⟨n,observed,op⟩
  rw [cellFold_increments rest _ x increments]
  simp only [cellUpdate,bornOp.1,ite_true,Option.map_some]
  rw [acquired_fold events distinct,sumEq]

def IsRemove (x : Nat) (e : Event) : Prop := ∃ observed, e.op = .remove x observed

instance isRemoveDecidable (x : Nat) (e : Event) : Decidable (IsRemove x e) := by
  unfold IsRemove
  cases h : e.op <;> simp <;> infer_instance

/-- A nonempty absent-element event set has an actual remover. An Inc cannot
supply a spurious witness because its issuer must already have a visible Add. -/
private theorem absent_has_remove (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (x : Nat) (absent : priority (applySeq D.toUpdateSig D.init events) x = none)
    (localEvents : List Event) (localEnum : listPermOf localEvents {e ∈ E | elementOf e.op = x})
    (nonempty : localEvents ≠ []) : ∃ r ∈ localEvents, IsRemove x r := by
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil localEvents nonempty
  have inE := (localEnum.2 e).mp he
  rcases e with ⟨t,rep,op⟩
  cases op with
  | add y v =>
    obtain ⟨member,same⟩ := inE
    change y = x at same
    subst y
    obtain ⟨r,hr,_,removed⟩ := absent_birth_has_remover C honest trans events E enumerated
      supported x absent (t,rep,.add x v) member v rfl
    have key : elementOf r.op = x := by obtain ⟨O,op⟩ := removed; simp [op,elementOf]
    exact ⟨r,(localEnum.2 r).mpr ⟨hr,key⟩,removed⟩
  | remove y observed =>
    obtain ⟨member,same⟩ := inE
    change y = x at same
    subst y
    exact ⟨(t,rep,.remove x observed),he,observed,rfl⟩
  | inc y n observed =>
    obtain ⟨member,same⟩ := inE
    change y = x at same
    subst y
    obtain ⟨birth,_,before,v,add⟩ := honest_inc_prior_birth C honest trans
      (t,rep,.inc x n observed) (supported _ member) x n observed rfl
    have birthInE := closed birth _ before member
    obtain ⟨r,hr,_,removed⟩ := absent_birth_has_remover C honest trans events E enumerated
      supported x absent birth birthInE v add
    have key : elementOf r.op = x := by obtain ⟨O,op⟩ := removed; simp [op,elementOf]
    exact ⟨r,(localEnum.2 r).mpr ⟨hr,key⟩,removed⟩

/-- Every absent element has a causal ordinary explaining order. It ends in a
maximal removal followed only by updates incapable of inserting that element;
ordinary absent Inc and Remove are explicitly no-ops. -/
theorem absent_replay (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (x : Nat) (absent : priority (applySeq D.toUpdateSig D.init events) x = none)
    (localEvents : List Event)
    (localEnum : listPermOf localEvents {e ∈ E | elementOf e.op = x})
    (ordered : respects localEvents C.vis) :
    ∃ replay, listPermOf replay {e ∈ E | elementOf e.op = x} ∧ respects replay C.vis ∧
      (replay.foldl seqStep model.initial).2 x = none := by
  by_cases empty : localEvents = []
  · exact ⟨localEvents,localEnum,ordered,by simp [empty,model]⟩
  obtain ⟨someRemove,member,isRemove⟩ := absent_has_remove C honest trans events E enumerated
    supported closed x absent localEvents localEnum empty
  let removals := localEvents.toFinset.filter (fun e => IsRemove x e)
  have nonempty : removals.Nonempty := ⟨someRemove,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr member,isRemove⟩⟩
  obtain ⟨r,hr,maxTime⟩ := Finset.exists_max_image removals Op.time nonempty
  obtain ⟨rLocal,rRemove⟩ := Finset.mem_filter.mp hr
  have rMember := List.mem_toFinset.mp rLocal
  have maximal : ∀ q ∈ E, (∃ observed, q.op = .remove x observed) → ¬ C.vis r q := by
    intro q hq remove edge
    have qKey : elementOf q.op = x := by obtain ⟨O,op⟩ := remove; simp [op,elementOf]
    have qMember := (localEnum.2 q).mpr ⟨hq,qKey⟩
    have max := maxTime q (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr qMember,remove⟩)
    exact not_lt_of_ge max (C.causal_mono edge)
  let selected : Event → Bool := fun e => decide (e = r ∨ C.vis r e)
  have first : selected r = true := by simp [selected]
  have before : ∀ e ∈ localEvents, selected e = true → e ≠ r → C.vis r e := by
    intro e he yes different
    simpa [selected,different] using yes
  have forward : ∀ a ∈ localEvents, ∀ b ∈ localEvents,
      selected a = true → C.vis a b → selected b = true := by
    intro a ha b hb yes edge
    have chosen : a = r ∨ C.vis r a := by simpa [selected] using yes
    have before : C.vis r b := by
      rcases chosen with rfl | earlier
      · exact edge
      · exact trans earlier edge
    simp [selected,before]
  obtain ⟨rest,perm,order,suffix⟩ := exists_partitioned_order selected localEvents C.vis ordered r rMember
    first forward before
  have noAdd : ∀ e ∈ rest, ∀ v, e.op ≠ .add x v := by
    intro e he v add
    have selectedE := (List.mem_filter.mp (show e ∈ localEvents.filter selected by rw [suffix]; simp [he])).2
    have different : e ≠ r := by
      intro eq
      subst e
      have nodup := localEnum.1.filter selected
      rw [suffix] at nodup
      exact (List.nodup_cons.mp nodup).1 he
    have after : C.vis r e := by simpa [selected,different] using selectedE
    have eMember : e ∈ localEvents := (List.mem_filter.mp (show e ∈ localEvents.filter selected by rw [suffix]; simp [he])).1
    exact absent_no_add_after_maximal_remove C honest trans events E enumerated supported x absent r maximal
      e ((localEnum.2 e).mp eMember).1 v add after
  obtain ⟨observed,rOp⟩ := rRemove
  refine ⟨localEvents.filter (fun e => !selected e) ++ r :: rest,
    ⟨perm.symm.nodup localEnum.1,fun e => perm.mem_iff.trans (localEnum.2 e)⟩,order,?_⟩
  rw [seqFold_cell,List.foldl_append,List.foldl_cons]
  simp only [cellUpdate,rOp,ite_true]
  exact cellFold_absent rest x noAdd

/-- A causal per-element explanation exists for every finite honest causal cut,
with the concrete value matched by ordinary total priority-map operations. -/
theorem per_key_replay (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (irrefl : ∀ e : Event, ¬ C.vis e e)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (distinct : events.Pairwise (fun a b => a.time ≠ b.time)) (x : Nat) :
    ∃ replay, listPermOf replay {e ∈ E | elementOf e.op = x} ∧ respects replay C.vis ∧
      (replay.foldl seqStep model.initial).2 x = priority (applySeq D.toUpdateSig D.init events) x := by
  let keyEvents := events.filter (fun e => elementOf e.op = x)
  have keyEnum : listPermOf keyEvents {e ∈ E | elementOf e.op = x} := by
    refine ⟨enumerated.1.filter _,?_⟩
    intro e
    simp only [keyEvents,List.mem_filter,decide_eq_true_eq,enumerated.2,Set.mem_setOf_eq]
  obtain ⟨localEvents,perm,ordered⟩ := exists_respecting_perm (R := C.vis) (fun {a b c} hab hbc => trans hab hbc) irrefl keyEvents
  have localEnum : listPermOf localEvents {e ∈ E | elementOf e.op = x} :=
    ⟨perm.nodup keyEnum.1,fun e => perm.symm.mem_iff.trans (keyEnum.2 e)⟩
  cases answer : priority (applySeq D.toUpdateSig D.init events) x with
  | none =>
    obtain ⟨replay,enum,order,value⟩ := absent_replay C honest trans events E enumerated
      supported closed x answer localEvents localEnum ordered
    exact ⟨replay,enum,order,by simpa only [answer] using value⟩
  | some p =>
    obtain ⟨t,v,known,alive,value,_⟩ := priority_selected_record _ x p answer
    rcases (fold_births D.init events ((x,t),v)).mp known with empty | ⟨birth,hb,born⟩
    · exact False.elim (Finset.notMem_empty _ empty)
    · obtain ⟨replay,enum,order,ordinary⟩ := present_replay C honest trans events E enumerated
        supported closed distinct x t v localEvents localEnum ordered birth ((enumerated.2 birth).mp hb) born alive
      exact ⟨replay,enum,order,by simpa only [answer,← value] using ordinary⟩

private theorem outside_keys_none (events : List Event) (E : Set Event)
    (enumerated : listPermOf events E) (keys : List Nat)
    (covered : ∀ e ∈ E, elementOf e.op ∈ keys) (x : Nat) (outside : x ∉ keys) :
    priority (applySeq D.toUpdateSig D.init events) x = none := by
  apply (priority_none_iff _ x).mpr
  intro live
  obtain ⟨⟨⟨y,t⟩,v⟩,hb,key⟩ := Finset.mem_image.mp live
  obtain ⟨born,_⟩ := Finset.mem_filter.mp hb
  change y = x at key
  subst y
  rcases (fold_births D.init events ((x,t),v)).mp born with empty | ⟨birth,member,born⟩
  · exact Finset.notMem_empty _ empty
  · have op := ((birth_effect_iff birth x t v).mp born).1
    have key : elementOf birth.op = x := by simp [op,elementOf]
    exact outside (key ▸ covered birth ((enumerated.2 birth).mp member))

/-- Full-query independent ordinary-history adequacy. Honest issuance is used
only at actual mint snapshots. Explaining prefixes use the explicitly total
ordinary Add/Inc/Remove semantics, and preserve every specification-conflicting
visibility edge. One explaining order matches ALL queries of the stored view. -/
theorem historyAdequacy : EventExecutionHistoryAdequacy D policy spec generation := by
  intro C execution version state E stored q
  have reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C := by
    cases execution with
    | ordinary ordinary => exact ordinary.toV
    | virtual recursive => exact recursive
  have good := canonicalVersions reach
  have honest := reach.mintHonest
  obtain ⟨events,enumerated,_,folded⟩ := good.canonical version state E stored
  have supported := good.version_events_supported version state E stored
  have closed := good.version_events_causal version state E stored
  have distinct : events.Pairwise (fun a b => a.time ≠ b.time) := by
    apply enumerated.1.imp_of_mem
    intro a b ha hb different sameTime
    exact different (C.replayContext.ts_unique (supported a ((enumerated.2 a).mp ha))
      (supported b ((enumerated.2 b).mp hb)) sameTime)
  let keys := (events.map (fun e => elementOf e.op)).toFinset.toList
  have unique : keys.Nodup := Finset.nodup_toList _
  have covered : ∀ e ∈ E, elementOf e.op ∈ keys := by
    intro e he
    apply Finset.mem_toList.mpr
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e,(enumerated.2 e).mpr he,rfl⟩
  have perKey : ∀ x ∈ keys, ∃ replay,
      listPermOf replay {e | e ∈ E ∧ elementOf e.op = x} ∧ respects replay C.vis ∧
      (replay.foldl seqStep model.initial).2 x = priority state x := by
    intro x hx
    simpa only [folded] using per_key_replay C honest good.vis_trans good.vis_irrefl events E enumerated
      supported closed distinct x
  obtain ⟨replay,enum,visible,observes⟩ := assemble_key_histories keys E state C.replayContext unique covered
    perKey (fun x hx => by simpa only [folded] using outside_keys_none events E enumerated keys covered x hx)
  have permutation : replay.Perm events := by
    apply (List.perm_ext_iff_of_nodup enum.1 enumerated.1).mpr
    intro e
    exact (enum.2 e).trans (enumerated.2 e).symm
  have same : applySeq D.toUpdateSig D.init replay = state := by
    exact (applySeq_perm_of_all_comm (D' := D.toUpdateSig) effects_commute permutation D.init).trans folded
  refine ⟨replay,enum,?_,visible,?_⟩
  · exact enum.1.imp (fun {_ _} _ => paperOrder_false_of_all_commute effects_commute C.replayContext E _ _)
  · change model.toSpec.admits (DeterministicSpec.updateLabels replay ++
      [.query q (read (applySeq D.toUpdateSig D.init replay) q)])
    rw [model.updates_query_iff]
    change read (applySeq D.toUpdateSig D.init replay) q = seqRead (replay.foldl seqStep model.initial) q
    rw [same]
    exact (observes q).symm

#print axioms present_replay
#print axioms absent_replay
#print axioms per_key_replay
#print axioms historyAdequacy

end Sal.MRDTs.Paper1.PriorityQueueSameRecord
