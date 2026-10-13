import Sal.MRDTs.Paper1.AnchoredQueue

namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA Sal.EmbedRGA

theorem descendant_below_anchor (pref : List Bool) (d : Nat) (positive : 1 ≤ d) :
    keyLt (key (pref ++ unaryCode.enc d)) (key pref) = true := by
  rw [key_append,key_def pref,keyLt_append_left]
  obtain ⟨b,bs,eq⟩ : ∃ b bs, unaryCode.enc d = b :: bs := by
    cases h : unaryCode.enc d with
    | nil => exact False.elim (enc_ne_nil unaryCode positive h)
    | cons b bs => exact ⟨b,bs,rfl⟩
  rw [eq,key_def]
  cases b <;> simp [sym,keyLt]

/-- Same-tail siblings use descending Lamport delta, hence descending fresh
identity when their observed anchor agrees. No delivery-order tie breaking. -/
theorem newer_sibling_before (pref : List Bool) {d e : Nat}
    (olderPositive : 1 ≤ e) (newer : e < d) :
    keyLt (key (pref ++ unaryCode.enc e))
      (key (pref ++ unaryCode.enc d)) = true := by
  rw [key_append,key_append,keyLt_append_left]
  obtain ⟨q,u,v,he,hd⟩ := enc_first_diff unaryCode olderPositive (by omega) newer
  rw [he,hd,key_append,key_append,keyLt_append_left]
  simp [key_def,keyLt,sym]

/-- Every live record precedes or equals the last observed record. -/
theorem sorted_last {s : State} (sorted : ESorted s) {last : ERec Nat}
    (observed : s.getLast? = some last) {r : ERec Nat} (member : r ∈ s) :
    r = last ∨ keyLt (key last.2.2) (key r.2.2) = true := by
  induction s with
  | nil => simp at observed
  | cons a xs ih =>
      rcases List.pairwise_cons.mp sorted with ⟨before,rest⟩
      cases xs with
      | nil => simp_all
      | cons b bs =>
          simp only [List.getLast?_cons_cons] at observed
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inr (before last (List.mem_of_getLast? observed))
          · exact ih rest observed member

/-- Fresh tail allocation appends in the coordinate order. This is the
representation fact used to derive FIFO causality from the original mint. -/
theorem issued_enqueue_after_live {s : State} (sorted : ESorted s)
    {t replica value anchor : Nat} {pref : List Bool}
    (issued : CanIssue (t,replica,enq value anchor pref) s)
    {r : ERec Nat} (member : r ∈ s) :
    keyLt (key (pref ++ unaryCode.enc (t-anchor))) (key r.2.2) = true := by
  obtain ⟨time,empty | last⟩ := issued
  · simp [empty.1] at member
  · obtain ⟨⟨a,v,p⟩,observed,eq⟩ := Option.map_eq_some_iff.mp last
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have child := descendant_below_anchor p (t-a) (by omega)
    rcases sorted_last sorted observed member with rfl | before
    · exact child
    · exact keyLt_trans child before

private theorem insert_at_end {new : ERec Nat} {s : State}
    (after : ∀ r ∈ s, keyLt (key new.2.2) (key r.2.2) = true) :
    eInsert new s = s ++ [new] := by
  induction s with
  | nil => rfl
  | cons a xs ih =>
      have no := keyLt_asymm (after a List.mem_cons_self)
      simp only [eInsert,no,Bool.false_eq_true,if_false,List.cons_append]
      rw [ih (fun r hr => after r (List.mem_cons_of_mem a hr))]

/-- A fresh originally issued enqueue has plain append behavior on a valid
materialized issuer list; arbitrary replay delivery still uses sorted insertion. -/
theorem issued_enqueue_appends {s : State} (sorted : ESorted s)
    {t replica value anchor : Nat} {pref : List Bool}
    (issued : CanIssue (t,replica,enq value anchor pref) s)
    (fresh : t ∉ eIds s) :
    Q.update s (t,replica,enq value anchor pref) =
      s ++ [(t,value,pref ++ unaryCode.enc (t-anchor))] := by
  change eUpdate unaryCode s (t,replica,.ins value pref anchor) = _
  simp only [eUpdate,if_neg fresh]
  exact insert_at_end (fun r hr => issued_enqueue_after_live sorted issued hr)

/-- A live head cannot have a distinct earlier live record. -/
theorem issued_dequeue_no_earlier_live {s : State} (sorted : ESorted s)
    {t replica target : Nat} (issued : CanIssue (t,replica,deq target) s)
    {head : ERec Nat} (observed : s.head? = some head)
    {r : ERec Nat} (member : r ∈ s) (different : r ≠ head) :
    keyLt (key head.2.2) (key r.2.2) ≠ true := by
  cases s with
  | nil => simp at observed
  | cons a xs =>
      simp only [List.head?_cons,Option.some.injEq] at observed
      subst a
      rcases List.mem_cons.mp member with same | member
      · exact False.elim (different same)
      · have before := (List.pairwise_cons.mp sorted).1 r member
        rw [keyLt_asymm before]
        decide

/-- Head-only original issuance is a real FIFO pop, while effect delivery
remains idempotent filter-by-identity on arbitrary replay scratch states. -/
theorem issued_dequeue_pops {s : State} (unique : (eIds s).Nodup)
    {t replica target : Nat} (issued : CanIssue (t,replica,deq target) s) :
    Q.update s (t,replica,deq target) = s.tail := by
  cases s with
  | nil => simp [CanIssue,deq] at issued
  | cons a xs =>
      have same : a.1 = target := by simpa [CanIssue,deq] using issued
      have absent : target ∉ eIds xs := by
        have absent' : a.1 ∉ eIds xs := (List.nodup_cons.mp unique).1
        rw [same] at absent'
        exact absent'
      change (a :: xs).filter (fun r => decide (r.1 ≠ target)) = xs
      simp only [List.filter_cons,same,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,
        if_false]
      apply List.filter_eq_self.mpr
      intro r hr
      simp only [decide_eq_true_eq]
      intro eq
      exact absent (List.mem_map.mpr ⟨r,hr,eq⟩)

#print axioms issued_enqueue_after_live
end Sal.MRDTs.Paper1.AnchoredQueue
