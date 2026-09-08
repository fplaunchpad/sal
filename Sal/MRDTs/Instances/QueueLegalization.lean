import Sal.MRDTs.Instances.QueueContract

/-! Constructive legalization of the queue's concurrent histories. -/
namespace Sal.MRDTs.Instances.Queue

open Sal.MRDTs.Foundation
open Classical

def deqsOf (ops : List (Op QOp)) (tag : ℕ) : List (Op QOp) :=
  ops.filter (fun d => !qIsEnq d && decide (qTag d = tag))

def removedEnqs (ops : List (Op QOp)) : List (Op QOp) :=
  ((ops.filter qIsEnq).filter (fun e => decide (e.1 ∈ qDeqTags ops))).mergeSort
    (fun a b => a.1 ≤ b.1)

def survivingEnqs (ops : List (Op QOp)) : List (Op QOp) :=
  ops.filter (fun e => qIsEnq e && !decide (e.1 ∈ qDeqTags ops))

def dequeueBlock (ops : List (Op QOp)) (e : Op QOp) : List (Op QOp) :=
  e :: deqsOf ops e.1

/-- Removed elements are processed one at a time, followed by survivors in
the order supplied by the implementation's replay witness. -/
def legalize (ops : List (Op QOp)) : List (Op QOp) :=
  (removedEnqs ops).flatMap (dequeueBlock ops) ++ survivingEnqs ops

theorem mem_deqsOf {ops : List (Op QOp)} {tag : ℕ} {d : Op QOp} :
    d ∈ deqsOf ops tag ↔ d ∈ ops ∧ d.2.2 = .deq tag := by
  obtain ⟨ts, r, op⟩ := d
  cases op <;> simp [deqsOf, qIsEnq, qTag]

theorem mem_removedEnqs {ops : List (Op QOp)} {e : Op QOp} :
    e ∈ removedEnqs ops ↔ e ∈ ops ∧ qIsEnq e = true ∧ e.1 ∈ qDeqTags ops := by
  simp [removedEnqs, List.mem_mergeSort, and_comm]

theorem mem_survivingEnqs {ops : List (Op QOp)} {e : Op QOp} :
    e ∈ survivingEnqs ops ↔ e ∈ ops ∧ qIsEnq e = true ∧ e.1 ∉ qDeqTags ops := by
  simp [survivingEnqs]

theorem deqsOf_nonempty {ops : List (Op QOp)} {tag : ℕ}
    (h : tag ∈ qDeqTags ops) : deqsOf ops tag ≠ [] := by
  obtain ⟨d, hd, hdi, ht⟩ := mem_qDeqTags.mp h
  have hd' : d ∈ deqsOf ops tag := by
    apply mem_deqsOf.mpr
    obtain ⟨ts, r, op⟩ := d
    cases op <;> simp_all [qIsEnq, qTag]
  intro hempty
  simp [hempty] at hd'

theorem block_mem {ops : List (Op QOp)} {e x : Op QOp} :
    x ∈ dequeueBlock ops e ↔ x = e ∨ x ∈ ops ∧ x.2.2 = .deq e.1 := by
  simp [dequeueBlock, mem_deqsOf]

theorem block_tag {ops : List (Op QOp)} {e x : Op QOp}
    (he : qIsEnq e = true) (hx : x ∈ dequeueBlock ops e) : qTag x = e.1 := by
  rcases block_mem.mp hx with rfl | ⟨_, hx⟩
  · obtain ⟨ts, r, op⟩ := x
    cases op <;> simp_all [qIsEnq, qTag]
  · simp [qTag, hx]

theorem legalize_perm {ops : List (Op QOp)} (hwf : QWf ops)
    (hbirth : ∀ d ∈ ops, qIsEnq d = false →
      ∃ e ∈ ops, qIsEnq e = true ∧ e.1 = qTag d) :
    (legalize ops).Perm ops := by
  have hrnd : (removedEnqs ops).Nodup := by
    apply (List.mergeSort_perm _ _).symm.nodup
    exact hwf.nd.filter _ |>.filter _
  have hbnd : ∀ e ∈ removedEnqs ops, (dequeueBlock ops e).Nodup := by
    intro e he
    have heq := (mem_removedEnqs.mp he).2.1
    apply List.nodup_cons.mpr
    refine ⟨?_, hwf.nd.filter _⟩
    intro h
    have hd := (mem_deqsOf.mp h).2
    simp [qIsEnq, hd] at heq
  have hdis : (removedEnqs ops).Pairwise
      (fun a b => List.Disjoint (dequeueBlock ops a) (dequeueBlock ops b)) := by
    apply hrnd.imp_of_mem
    intro a b ha hb hne
    apply List.disjoint_left.mpr
    intro x hxa hxb
    have hat := mem_removedEnqs.mp ha
    have hbt := mem_removedEnqs.mp hb
    exact hne (hwf.enq_uniq a hat.1 b hbt.1 hat.2.1 hbt.2.1
      ((block_tag hat.2.1 hxa).symm.trans (block_tag hbt.2.1 hxb)))
  have hflatnd := List.nodup_flatMap.mpr ⟨hbnd, hdis⟩
  have hsnd : (survivingEnqs ops).Nodup := hwf.nd.filter _
  have hcross : List.Disjoint ((removedEnqs ops).flatMap (dequeueBlock ops))
      (survivingEnqs ops) := by
    apply List.disjoint_left.mpr
    intro x hx hs
    obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx
    have hes := mem_removedEnqs.mp he
    have hxs := mem_survivingEnqs.mp hs
    rcases block_mem.mp hxe with rfl | ⟨_, hd⟩
    · exact hxs.2.2 hes.2.2
    · simp [qIsEnq, hd] at hxs
  apply List.perm_ext_iff_of_nodup
    (List.nodup_append.mpr ⟨hflatnd, hsnd,
      fun a ha b hb hab => List.disjoint_left.mp hcross ha (hab.symm ▸ hb)⟩) hwf.nd |>.mpr
  intro x
  constructor
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx
      rcases block_mem.mp hxe with rfl | ⟨hx, _⟩
      · exact (mem_removedEnqs.mp he).1
      · exact hx
    · exact (mem_survivingEnqs.mp hx).1
  · intro hx
    by_cases hi : qIsEnq x = true
    · by_cases hd : x.1 ∈ qDeqTags ops
      · exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨x, mem_removedEnqs.mpr ⟨hx, hi, hd⟩, List.mem_cons_self⟩)
      · exact List.mem_append_right _ (mem_survivingEnqs.mpr ⟨hx, hi, hd⟩)
    · have hi' : qIsEnq x = false := Bool.eq_false_iff.mpr hi
      obtain ⟨e, he, hei, het⟩ := hbirth x hx hi'
      have hd : e.1 ∈ qDeqTags ops := mem_qDeqTags.mpr ⟨x, hx, hi', het.symm⟩
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨e, mem_removedEnqs.mpr ⟨he, hei, hd⟩, ?_⟩
      apply block_mem.mpr
      right
      obtain ⟨ts, r, op⟩ := x
      cases op <;> simp_all [qIsEnq, qTag]

theorem deqs_empty_legal (ds : List (Op QOp)) (born : List ℕ) (tag : ℕ)
    (hb : tag ∈ born) (hd : ∀ d ∈ ds, d.2.2 = .deq tag)
    (tail : List (Op QOp)) :
    clientLegalAux born [] (ds ++ tail) = clientLegalAux born [] tail := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hop := hd d List.mem_cons_self
    simp [clientLegalAux, hop, hb, clientStep,
      ih (fun e he => hd e (List.mem_cons_of_mem _ he))]

theorem deqs_empty_fold (ds : List (Op QOp)) (tag : ℕ)
    (hd : ∀ d ∈ ds, d.2.2 = .deq tag) : ds.foldl clientStep [] = [] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp [List.foldl_cons, clientStep, hd d List.mem_cons_self,
      ih (fun e he => hd e (List.mem_cons_of_mem _ he))]

theorem block_legal {ops : List (Op QOp)} {e : Op QOp}
    (he : qIsEnq e = true) (hd : e.1 ∈ qDeqTags ops)
    (born : List ℕ) (tail : List (Op QOp)) (hfresh : e.1 ∉ born) :
    clientLegalAux born [] (dequeueBlock ops e ++ tail) =
      clientLegalAux (e.1 :: born) [] tail := by
  obtain ⟨ts, r, op⟩ := e
  cases op with
  | deq tag => simp [qIsEnq] at he
  | enq value =>
    obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil (deqsOf_nonempty hd)
    have hAll : ∀ x ∈ d :: ds, x.2.2 = .deq ts := by
      intro x hx
      exact (mem_deqsOf.mp (hds ▸ hx)).2
    simp [dequeueBlock, hds, clientLegalAux, clientStep, hfresh,
      hAll d List.mem_cons_self,
      deqs_empty_legal ds (ts :: born) ts (by simp)
        (fun x hx => hAll x (List.mem_cons_of_mem _ hx)) tail]

theorem block_fold {ops : List (Op QOp)} {e : Op QOp}
    (he : qIsEnq e = true) (hd : e.1 ∈ qDeqTags ops) :
    (dequeueBlock ops e).foldl clientStep [] = [] := by
  obtain ⟨ts, r, op⟩ := e
  cases op with
  | deq tag => simp [qIsEnq] at he
  | enq value =>
    obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil (deqsOf_nonempty hd)
    have hAll : ∀ x ∈ d :: ds, x.2.2 = .deq ts := by
      intro x hx
      exact (mem_deqsOf.mp (hds ▸ hx)).2
    simp [dequeueBlock, hds, List.foldl_cons, clientStep,
      hAll d List.mem_cons_self,
      deqs_empty_fold ds ts (fun x hx => hAll x (List.mem_cons_of_mem _ hx))]

theorem enqs_legal (es : List (Op QOp)) (born : List ℕ) (s : QState)
    (hi : ∀ e ∈ es, qIsEnq e = true) (hnd : (es.map Prod.fst).Nodup)
    (hf : ∀ e ∈ es, e.1 ∉ born) : clientLegalAux born s es = true := by
  induction es generalizing born s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | deq target => simpa [qIsEnq] using hi _ List.mem_cons_self
    | enq value =>
      have hfresh := hf _ List.mem_cons_self
      have htail := List.nodup_cons.mp hnd
      have hrec := ih (ts :: born) (s ++ [(ts, value)])
        (fun e he => hi e (List.mem_cons_of_mem _ he)) htail.2 (by
          intro e he
          simp only [List.mem_cons, not_or]
          exact ⟨fun ht => htail.1 (ht ▸ List.mem_map.mpr ⟨e, he, rfl⟩),
            hf e (List.mem_cons_of_mem _ he)⟩)
      simp [clientLegalAux, clientStep, hfresh, hrec]

theorem enqs_fold (es : List (Op QOp)) (s : QState)
    (hi : ∀ e ∈ es, qIsEnq e = true) :
    es.foldl clientStep s = s ++ es.map (fun e => (e.1, qVal e)) := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | deq target => simpa [qIsEnq] using hi _ List.mem_cons_self
    | enq value =>
      simp [List.foldl_cons, clientStep, qVal, List.append_assoc,
        ih _ (fun e he => hi e (List.mem_cons_of_mem _ he))]

theorem groups_legal (ops removed survivors : List (Op QOp)) (born : List ℕ)
    (hr : ∀ e ∈ removed, qIsEnq e = true ∧ e.1 ∈ qDeqTags ops)
    (hs : ∀ e ∈ survivors, qIsEnq e = true)
    (hnd : ((removed ++ survivors).map Prod.fst).Nodup)
    (hf : ∀ e ∈ removed ++ survivors, e.1 ∉ born) :
    clientLegalAux born [] (removed.flatMap (dequeueBlock ops) ++ survivors) = true := by
  induction removed generalizing born with
  | nil => exact enqs_legal survivors born [] hs hnd hf
  | cons e es ih =>
    have hri := hr e List.mem_cons_self
    have hndi := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, List.append_assoc,
      block_legal hri.1 hri.2 born _ (hf e (by simp))]
    apply ih (e.1 :: born) (fun a ha => hr a (List.mem_cons_of_mem _ ha)) hndi.2
    intro a ha
    simp only [List.mem_cons, not_or]
    refine ⟨fun ht => hndi.1 (ht ▸ List.mem_map.mpr ⟨a, ha, rfl⟩), ?_⟩
    exact hf a (List.mem_cons_of_mem _ ha)

theorem groups_fold (ops removed : List (Op QOp))
    (hr : ∀ e ∈ removed, qIsEnq e = true ∧ e.1 ∈ qDeqTags ops) :
    (removed.flatMap (dequeueBlock ops)).foldl clientStep [] = [] := by
  induction removed with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, List.foldl_append, block_fold (hr e List.mem_cons_self).1
      (hr e List.mem_cons_self).2]
    exact ih (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem enqueue_partition_perm (ops : List (Op QOp)) :
    (removedEnqs ops ++ survivingEnqs ops).Perm (ops.filter qIsEnq) := by
  have hsort := List.mergeSort_perm
    ((ops.filter qIsEnq).filter (fun e => decide (e.1 ∈ qDeqTags ops)))
    (fun a b => decide (a.1 ≤ b.1))
  have hs : survivingEnqs ops =
      (ops.filter qIsEnq).filter (fun e => !decide (e.1 ∈ qDeqTags ops)) := by
    simp [survivingEnqs, List.filter_filter, Bool.and_comm]
  rw [hs]
  exact (hsort.append_right _).trans (List.filter_append_perm _ _)

theorem legalize_legal {ops : List (Op QOp)} (hwf : QWf ops) :
    clientSpec.Legal (legalize ops) := by
  have hp := enqueue_partition_perm ops
  have hnd := hp.symm.nodup (hwf.nd.filter qIsEnq)
  have htagnd : ((removedEnqs ops ++ survivingEnqs ops).map Prod.fst).Nodup := by
    apply List.Nodup.map_on _ hnd
    intro a ha b hb ht
    have ha' := List.mem_filter.mp (hp.mem_iff.mp ha)
    have hb' := List.mem_filter.mp (hp.mem_iff.mp hb)
    exact hwf.enq_uniq a ha'.1 b hb'.1 ha'.2 hb'.2 ht
  exact groups_legal ops (removedEnqs ops) (survivingEnqs ops) []
    (fun _ he => (mem_removedEnqs.mp he).2)
    (fun _ he => (mem_survivingEnqs.mp he).2.1) htagnd (by simp)

theorem legalize_fold (ops : List (Op QOp)) :
    clientSpec.run (legalize ops) = qCanonList ops := by
  change (legalize ops).foldl clientStep [] = _
  rw [legalize, List.foldl_append, groups_fold ops (removedEnqs ops)
    (fun _ he => (mem_removedEnqs.mp he).2), enqs_fold]
  · simp only [List.nil_append]
    unfold survivingEnqs qCanonList
    congr 2
    funext e
    obtain ⟨ts, r, op⟩ := e
    cases op <;> simp [qIsEnq, qTag]
  · exact fun _ he => (mem_survivingEnqs.mp he).2.1

theorem surviving_map (ops : List (Op QOp)) :
    (survivingEnqs ops).map (fun e => (e.1, qVal e)) = qCanonList ops := by
  unfold survivingEnqs qCanonList
  congr 2
  funext e
  obtain ⟨ts, r, op⟩ := e
  cases op <;> simp [qIsEnq, qTag]

/-- The missing FIFO obligation: if `a` is visible to the enqueue of the
head removed by `d`, then `a` has already been dequeued in `d`'s past.
This follows from head issuance, not merely observed-target issuance. -/
theorem head_predecessor_dequeued {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {a b d : Op QOp} (ha : a ∈ C.events) (hb : b ∈ C.events) (hd : d ∈ C.events)
    (hai : qIsEnq a = true) (_hbi : qIsEnq b = true)
    (hdd : d.2.2 = .deq b.1) (hab : C.vis a b) :
    qDeqIn {e ∈ C.events | C.vis e d} a.1 := by
  by_contra hnot
  have hm := exec.mintHonest
  have hh := qHonest_of_mint C hm
  have hcfg : CanonicalConfig C := exec.canonicalConfig
    (fun C hm => q_join_at (qGood_core (qHonest_of_mint C hm)))
  obtain ⟨birth, hbirth, hbd, ht, _⟩ := hh d hd b.1 hdd
  have hbeq : birth = b := C.replayContext.ts_unique hbirth hb ht
  rw [hbeq] at hbd
  have had : C.vis a d := hcfg.vis_trans hab hbd
  obtain ⟨ops, hp, hr, hg⟩ := hm d hd
  have hwf := q_wf_of_causal_enum hh (fun _ he => he.1) hp hr
  change qApplicable d (applySeq Q.toUpdateSig Q.init ops) at hg
  unfold qApplicable at hg
  rw [hdd, q_fold_canon ops hwf] at hg
  obtain ⟨value, rest, hhead⟩ := hg
  have harem : a ∈ survivingEnqs ops := mem_survivingEnqs.mpr
    ⟨(hp.2 a).mpr ⟨ha, had⟩, hai, fun ht => hnot ((qDeqTags_perm hp).mp ht)⟩
  have hresp : respects (survivingEnqs ops) C.vis :=
    hr.sublist (List.filter_sublist (p := fun e => qIsEnq e && !decide (e.1 ∈ qDeqTags ops)))
  rw [← surviving_map] at hhead
  cases hs : survivingEnqs ops with
  | nil => simp [hs] at hhead
  | cons first tail =>
    have hfmem : first ∈ survivingEnqs ops := by simp [hs]
    have hfops := (mem_survivingEnqs.mp hfmem).1
    have hfirstTag : first.1 = b.1 := by
      rw [hs] at hhead
      exact congrArg (fun p : ℕ × ℕ => p.1) (List.cons.inj hhead).1
    have hfirst : first = b := C.replayContext.ts_unique
      ((hp.2 first).mp hfops).1 hb hfirstTag
    rw [hs, List.mem_cons] at harem
    rcases harem with h | h
    · have : a = b := h.trans hfirst
      exact hcfg.vis_irrefl b (by simpa only [this] using hab)
    · rw [hs] at hresp
      exact (List.pairwise_cons.mp hresp).1 a h (hfirst ▸ hab)

theorem survivor_not_vis_removed {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {E : Set (Op QOp)} (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {a b : Op QOp} (ha : a ∈ E) (hb : b ∈ E)
    (hai : qIsEnq a = true) (hbi : qIsEnq b = true)
    (has : ¬ qDeqIn E a.1) (hbr : qDeqIn E b.1) : ¬ C.vis a b := by
  intro hab
  obtain ⟨d, hd, hdi, hdt⟩ := hbr
  have hop : d.2.2 = .deq b.1 := by
    obtain ⟨ts, r, op⟩ := d
    cases op <;> simp_all [qIsEnq, qTag]
  obtain ⟨earlier, he, hei, het⟩ := head_predecessor_dequeued exec
    (hin a ha) (hin b hb) (hin d hd) hai hbi hop hab
  exact has ⟨earlier, hclosed earlier d he.2 hd, hei, het⟩

theorem lo_source_enq {C : Configuration Q} (hh : QHonest C)
    {E : Set (Op QOp)} {a b : Op QOp}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (h : loOn C.replayContext E a b) : qIsEnq a = true := by
  obtain ⟨ats, ar, ao⟩ := a
  cases ao with
  | enq value => rfl
  | deq target =>
    obtain ⟨bts, br, bo⟩ := b
    cases bo with
    | deq other =>
      simp [loOn, UpdateSig.rc, ReplayPolicy.Before, QReplayPolicy, rc, qRcOrder] at h
    | enq value =>
      rcases h with ⟨hv, hc⟩ | ⟨_, _, hdir, _⟩
      · have ht : bts = target := by
          by_contra hn
          simp [UpdateSig.rc, ReplayPolicy.Before, QReplayPolicy, rc, qRcOrder, hn] at hc
        obtain ⟨birth, hbirth, hba, htag, _⟩ := hh _ ha target rfl
        have heq : birth = (bts, br, .enq value) :=
          C.replayContext.ts_unique hbirth hb (htag.trans ht.symm)
        rw [heq] at hba
        exact False.elim (Nat.lt_asymm (C.causal_mono hv) (C.causal_mono hba))
      · have : False := by
          change (if bts = target then RcRes.Snd_then_fst else RcRes.Either) =
            RcRes.Fst_then_snd at hdir
          split at hdir <;> contradiction
        exact this.elim

theorem lo_to_deq_tag {C : Configuration Q} {E : Set (Op QOp)}
    {a b : Op QOp} (hai : qIsEnq a = true) {tag : ℕ}
    (hbd : b.2.2 = .deq tag) (h : loOn C.replayContext E a b) : a.1 = tag := by
  obtain ⟨ats, ar, ao⟩ := a
  cases ao with
  | deq target => simp [qIsEnq] at hai
  | enq value =>
    by_contra hn
    rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;>
      simp [UpdateSig.rc, ReplayPolicy.Before, QReplayPolicy, rc, qRcOrder, hbd, hn] at hc

theorem lo_into_removed_vis {C : Configuration Q} (hh : QHonest C)
    {E : Set (Op QOp)} (hin : ∀ e ∈ E, e ∈ C.events)
    {a b : Op QOp} (hb : b ∈ E) (hbi : qIsEnq b = true)
    (hremoved : qDeqIn E b.1) (h : loOn C.replayContext E a b) : C.vis a b := by
  rcases h with h | ⟨_, _, _, hno⟩
  · exact h.1
  · obtain ⟨d, hd, hdi, hdt⟩ := hremoved
    have hdd : d.2.2 = .deq b.1 := by
      obtain ⟨ts, r, op⟩ := d
      cases op <;> simp_all [qIsEnq, qTag]
    obtain ⟨birth, hbirth, hv, ht, _⟩ := hh d (hin d hd) b.1 hdd
    have heq : birth = b := C.replayContext.ts_unique hbirth (hin b hb) ht
    rw [heq] at hv
    apply False.elim
    apply hno
    refine ⟨d, hd, hv, Or.inl ?_⟩
    obtain ⟨ts, r, op⟩ := b
    cases op with
    | deq target => simp [qIsEnq] at hbi
    | enq value =>
      simp [UpdateSig.rc, ReplayPolicy.Before, QReplayPolicy, rc, qRcOrder, hdd]

theorem removed_strict_sorted {ops : List (Op QOp)} (hwf : QWf ops) :
    (removedEnqs ops).Pairwise (fun a b => a.1 < b.1) := by
  have hle : (removedEnqs ops).Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : Op QOp => decide (a.1 ≤ b.1))
        (by intro a b c hab hbc; exact decide_eq_true (Nat.le_trans
          (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (by intro a b; simpa only [Bool.or_eq_true, decide_eq_true_eq] using
          Nat.le_total a.1 b.1)
        ((ops.filter qIsEnq).filter (fun e => decide (e.1 ∈ qDeqTags ops)))
  have hnd : (removedEnqs ops).Nodup :=
    (List.mergeSort_perm _ _).symm.nodup ((hwf.nd.filter _).filter _)
  have hboth := hle.and hnd
  apply hboth.imp_of_mem
  intro a b ha hb h
  have ha' := mem_removedEnqs.mp ha
  have hb' := mem_removedEnqs.mp hb
  have hne : a.1 ≠ b.1 := fun ht => h.2
    (hwf.enq_uniq a ha'.1 b hb'.1 ha'.2.1 hb'.2.1 ht)
  exact Nat.lt_of_le_of_ne h.1 hne

theorem legalize_respects {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    {E : Set (Op QOp)} {ops : List (Op QOp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (hp : listPermOf ops E) (hwf : QWf ops)
    (hr : respects ops (loOn C.replayContext E)) :
    respects (legalize ops) (loOn C.replayContext E) := by
  have hh := qHonest_of_mint C exec.mintHonest
  have hmem : ∀ e ∈ ops, e ∈ C.events := fun e he => hin e ((hp.2 e).mp he)
  have hbmem : ∀ e ∈ removedEnqs ops, ∀ x ∈ dequeueBlock ops e, x ∈ ops := by
    intro e he x hx
    rcases block_mem.mp hx with rfl | ⟨hx, _⟩
    · exact (mem_removedEnqs.mp he).1
    · exact hx
  have hblock : ∀ e ∈ removedEnqs ops,
      respects (dequeueBlock ops e) (loOn C.replayContext E) := by
    intro e he
    unfold dequeueBlock respects
    apply List.pairwise_cons.mpr
    constructor
    · intro d hd hedge
      have hdi := (mem_deqsOf.mp hd).2
      have hi := lo_source_enq hh (hmem d (mem_deqsOf.mp hd).1)
        (hmem e (mem_removedEnqs.mp he).1) hedge
      simp [qIsEnq, hdi] at hi
    · apply List.pairwise_of_forall_mem_list
      intro a ha b hb hedge
      have hi := lo_source_enq hh (hmem b (mem_deqsOf.mp hb).1)
        (hmem a (mem_deqsOf.mp ha).1) hedge
      simp [qIsEnq, (mem_deqsOf.mp hb).2] at hi
  have hbetween : (removedEnqs ops).Pairwise
      (fun e f => ∀ a ∈ dequeueBlock ops e, ∀ b ∈ dequeueBlock ops f,
        ¬ loOn C.replayContext E b a) := by
    apply (removed_strict_sorted hwf).imp_of_mem
    intro e f he hf hlt a ha b hb hedge
    have hei := mem_removedEnqs.mp he
    have hfi := mem_removedEnqs.mp hf
    have hbi := lo_source_enq hh (hmem b (hbmem f hf b hb))
      (hmem a (hbmem e he a ha)) hedge
    have hbf : b = f := by
      rcases block_mem.mp hb with h | ⟨_, h⟩
      · exact h
      · simp [qIsEnq, h] at hbi
    subst b
    rcases block_mem.mp ha with rfl | ⟨ha, had⟩
    · have hv := lo_into_removed_vis hh hin ((hp.2 a).mp hei.1) hei.2.1
        ((qDeqTags_perm hp).mp hei.2.2) hedge
      exact Nat.lt_asymm hlt (C.causal_mono hv)
    · have ht := lo_to_deq_tag hfi.2.1 had hedge
      exact (Nat.ne_of_lt hlt) ht.symm
  unfold legalize respects
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_flatMap.mpr ⟨hblock, hbetween⟩,
    hr.sublist (List.filter_sublist (p := fun e => qIsEnq e && !decide (e.1 ∈ qDeqTags ops))), ?_⟩
  intro a ha b hb hedge
  obtain ⟨e, he, hae⟩ := List.mem_flatMap.mp ha
  have hei := mem_removedEnqs.mp he
  have hbi := mem_survivingEnqs.mp hb
  rcases block_mem.mp hae with rfl | ⟨ha, had⟩
  · have hv := lo_into_removed_vis hh hin ((hp.2 a).mp hei.1) hei.2.1
      ((qDeqTags_perm hp).mp hei.2.2) hedge
    exact survivor_not_vis_removed exec hin hclosed
      ((hp.2 b).mp hbi.1) ((hp.2 a).mp hei.1) hbi.2.1 hei.2.1
      (fun hd => hbi.2.2 ((qDeqTags_perm hp).mpr hd))
      ((qDeqTags_perm hp).mp hei.2.2) hv
  · have ht := lo_to_deq_tag hbi.2.1 had hedge
    exact hbi.2.2 (ht.symm ▸ hei.2.2)

/-- Every certified queue version has a legal abstract FIFO witness, with
the same event identities, the sole public order, and exact tagged contents. -/
theorem queue_legal_witness {C : Configuration Q}
    (exec : CertifiedExecution Q generation C)
    (replay : @HasReplayWitness Q rc C)
    {v : Version} {s : QState} {E : Set (Op QOp)}
    (hver : C.ver v = some (s, E)) :
    ∃ ops, listPermOf ops E ∧ respects ops (loOn C.replayContext E) ∧
      clientSpec.Legal ops ∧ clientSpec.run ops = s := by
  have hh := qHonest_of_mint C exec.mintHonest
  have hcfg : CanonicalConfig C := exec.canonicalConfig
    (fun C hm => q_join_at (qGood_core (qHonest_of_mint C hm)))
  have hin := hcfg.version_events_supported v s E hver
  have hclosed := hcfg.version_events_causal v s E hver
  obtain ⟨ops, hp, hr, hfold⟩ := replay v s E hver
  have hwf := q_wf_of_enum (qHonest_core hh) hin (fun a b hv _ hb => hclosed a b hv hb) hp hr
  have hbirth : ∀ d ∈ ops, qIsEnq d = false →
      ∃ e ∈ ops, qIsEnq e = true ∧ e.1 = qTag d := by
    intro d hd hdi
    obtain ⟨e, he, hei, het, _⟩ := q_deq_enq_mem (qHonest_core hh) hin
      (fun a b hv _ hb => hclosed a b hv hb) d ((hp.2 d).mp hd) hdi
    exact ⟨e, (hp.2 e).mpr he, hei, het⟩
  have hperm := legalize_perm hwf hbirth
  refine ⟨legalize ops, ⟨hperm.symm.nodup hp.1, fun e => hperm.mem_iff.trans (hp.2 e)⟩,
    legalize_respects exec hin hclosed hp hwf hr, legalize_legal hwf, ?_⟩
  rw [legalize_fold, ← q_fold_canon ops hwf]
  exact hfold

def clientSequentialCorrectness : SequentialCorrectnessCertificate Q generation rc clientSpec Eq where
  sound C exec replay := by
    intro v s E hver
    obtain ⟨ops, hp, hr, hl, hs⟩ := queue_legal_witness exec replay hver
    exact ⟨ops, hp, hr, hl, hs.symm, fun _ => congrArg List.head? hs.symm⟩

noncomputable def verified : VerifiedMRDT Q where
  issuance := generation
  rc := rc
  replayAdequacy := replayAdequacy
  Spec := clientSpec
  Rel := Eq
  sequentialCorrectness := clientSequentialCorrectness

theorem queue_spec_linearizable {C : Configuration Q}
    (h : MintCertifiedReach Q generation C) :
    IsSpecLinearizable Q rc clientSpec Eq C := verified.correct h

theorem queue_spec_linearizableV {C : Configuration Q}
    (h : MintCertifiedReachV Q (canonicalVirtualMergeBase Q) generation C) :
    IsSpecLinearizable Q rc clientSpec Eq C := verified.correctV h

#print axioms queue_legal_witness
#print axioms verified
#print axioms queue_spec_linearizable
#print axioms queue_spec_linearizableV

end Sal.MRDTs.Instances.Queue
