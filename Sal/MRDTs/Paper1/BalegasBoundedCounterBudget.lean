import Sal.MRDTs.Paper1.BalegasBoundedCounterEvent

/-! The scalar lower bound follows from conservation of the sum of escrow
balances. These statements concern legal sequential histories; the execution
bridge must establish their premises for each replicated history. -/
namespace Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
open Foundation Instances.BalegasBoundedCounter
open Classical

def Conserved (n : Nat) (K : Int) (s : Accounts) : Prop :=
  s.value = K + (Finset.range n).sum s.balance

theorem initial_conserved (n : Nat) (K : Int) : Conserved n K (initialAccounts K) := by
  simp [Conserved,initialAccounts]

theorem step_conserved {n : Nat} {K : Int} {s : Accounts} {e : Event}
    (h : Conserved n K s) (valid : validIssuer n e) :
    Conserved n K (accountStep s e) := by
  rcases e with ⟨ts,rep,op⟩
  have hr : rep ∈ Finset.range n := Finset.mem_range.mpr valid.1
  change s.value = K + ∑ r ∈ Finset.range n, s.balance r at h
  cases op with
  | increment amount =>
    simp [Conserved,accountStep,credit,debit,scalarDelta,Op.op,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,hr] at h ⊢
    omega
  | decrement amount =>
    simp [Conserved,accountStep,credit,debit,scalarDelta,Op.op,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,hr] at h ⊢
    omega
  | transfer amount target =>
    have ht : target ∈ Finset.range n := Finset.mem_range.mpr valid.2.1
    simp [Conserved,accountStep,credit,debit,scalarDelta,Op.op,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,hr,ht] at h ⊢
    omega

theorem scalar_lower_bound {n : Nat} {K : Int} {s : Accounts}
    (conserved : Conserved n K s) (safe : ∀ r, 0 ≤ s.balance r) : K ≤ s.value := by
  have hs : 0 ≤ (Finset.range n).sum s.balance := Finset.sum_nonneg (fun r _ => safe r)
  unfold Conserved at conserved
  omega

def Legal (n : Nat) : Accounts → List Event → Prop
  | _, [] => True
  | s, e :: rest => validIssuer n e ∧ affordable s e ∧ Legal n (accountStep s e) rest

theorem legal_run_safe {n : Nat} {K : Int} {ops : List Event}
    (legal : Legal n (initialAccounts K) ops) :
    (∀ r, 0 ≤ (run K ops).balance r) ∧ Conserved n K (run K ops) ∧ K ≤ (run K ops).value := by
  have aux : ∀ s : Accounts, (∀ r, 0 ≤ s.balance r) → Conserved n K s → Legal n s ops →
      (∀ r, 0 ≤ (ops.foldl accountStep s).balance r) ∧ Conserved n K (ops.foldl accountStep s) := by
    clear legal
    induction ops with
    | nil => intro s hs hc _; exact ⟨hs,hc⟩
    | cons e rest ih =>
      intro s hs hc hl
      exact ih (accountStep s e) (accountStep_nonnegative hs hl.2.1)
        (step_conserved hc hl.1) hl.2.2
  obtain ⟨hs,hc⟩ := aux (initialAccounts K) (by simp [initialAccounts]) (initial_conserved n K) legal
  exact ⟨hs,hc,scalar_lower_bound hc hs⟩
theorem legal_history_accepts {n : Nat} {K : Int} {ops : List Event}
    (legal : Legal n (initialAccounts K) ops) (q : Query) :
    (spec n K).admits (ops.map SeqLabel.update ++ [.query q (accountQuery (run K ops) q)]) := by
  have aux : ∀ (s : Accounts), Legal n s ops →
      Runs (machine n K).transition s (ops.map SeqLabel.update) (ops.foldl accountStep s) := by
    clear legal
    induction ops with
    | nil => intro s _; exact .nil s
    | cons e rest ih =>
      intro s hl
      exact .cons ⟨rfl,hl.1,hl.2.1⟩ (ih (accountStep s e) hl.2.2)
  refine ⟨run K ops,?_⟩
  exact (aux (initialAccounts K) legal).append (.cons ⟨rfl,rfl⟩ (.nil _))

theorem causal_legal {n : Nat} {K : Int} [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D n K) (fun e s => applicable n s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis) :
    Legal n (initialAccounts K) ops := by
  have allvalid : ∀ e ∈ C.events, validIssuer n e := by
    intro e he
    obtain ⟨_,_,hg⟩ := honest e he
    exact applicable_valid hg
  have hi : ∀ e ∈ C.events, ∃ past : List Event,
      listPermOf past {x ∈ C.events | C.vis x e} ∧ affordable (run K past) e := by
    intro e he
    obtain ⟨sp,⟨past,hpp,_,hfp⟩,hg⟩ := honest e he
    refine ⟨past,hpp,?_⟩
    have vp : ∀ x ∈ past, validIssuer n x := fun x hx => allvalid x ((hpp.2 x).mp hx).1
    change applySeq (D n K).toUpdateSig initial past = sp at hfp
    rw [run_refines vp,hfp]
    exact applicable_affordable hg
  have funded := causal_prefix_affordable hG hi hv hp hc
  have valid : ∀ e ∈ ops, validIssuer n e := fun e he =>
    allvalid e (hG.version_events_supported v s E hv e ((hp.2 e).mp he))
  have aux : ∀ pre rest : List Event, ops = pre ++ rest → Legal n (run K pre) rest := by
    intro pre rest
    induction rest generalizing pre with
    | nil => intro _; trivial
    | cons e rest ih =>
      intro hs
      have hvE : e ∈ ops := by rw [hs]; simp
      refine ⟨valid e hvE,funded pre e rest hs,?_⟩
      have ha : run K (pre ++ [e]) = accountStep (run K pre) e := by
        simp [run,List.foldl_append]
      rw [← ha]
      apply ih
      simpa [List.append_assoc] using hs
  exact aux [] ops rfl

theorem causal_history_accepts {n : Nat} {K : Int} [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D n K) (fun e s => applicable n s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis) (q : Query) :
    (spec n K).admits (ops.map SeqLabel.update ++ [.query q (query n K s q)]) := by
  have legal := causal_legal hG honest hv hp hc
  have valid : ∀ e ∈ ops, validIssuer n e := by
    intro e he
    obtain ⟨_,_,hg⟩ := honest e (hG.version_events_supported v s E hv e ((hp.2 e).mp he))
    exact applicable_valid hg
  have hf : applySeq (D n K).toUpdateSig initial ops = s := by
    obtain ⟨other,hpo,_,ho⟩ := hG.canonical v s E hv
    have perm : ops.Perm other := List.perm_ext_iff_of_nodup hp.1 hpo.1 |>.mpr (by
      intro x; exact (hp.2 x).trans (hpo.2 x).symm)
    exact (applySeq_perm_of_all_comm (all_comm n K) perm _).trans ho
  have accepted := legal_history_accepts legal q
  simpa [run_refines valid,hf,← query_refines] using accepted

theorem causal_legal_on {n : Nat} {K : Int} [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D n K) (fun e s => applicable n s e) C)
    {E : Set Event} (hEev : ∀ e ∈ E, e ∈ C.events)
    (hEcl : ∀ x y, C.vis x y → y ∈ E → x ∈ E)
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis) :
    Legal n (initialAccounts K) ops := by
  have allvalid : ∀ e ∈ C.events, validIssuer n e := by
    intro e he
    obtain ⟨_,_,hg⟩ := honest e he
    exact applicable_valid hg
  have hi : ∀ e ∈ C.events, ∃ past : List Event,
      listPermOf past {x ∈ C.events | C.vis x e} ∧ affordable (run K past) e := by
    intro e he
    obtain ⟨sp,⟨past,hpp,_,hfp⟩,hg⟩ := honest e he
    refine ⟨past,hpp,?_⟩
    have vp : ∀ x ∈ past, validIssuer n x := fun x hx => allvalid x ((hpp.2 x).mp hx).1
    change applySeq (D n K).toUpdateSig initial past = sp at hfp
    rw [run_refines vp,hfp]
    exact applicable_affordable hg
  have funded := causal_prefix_affordable_on hG hi hEev hEcl hp hc
  have valid : ∀ e ∈ ops, validIssuer n e := fun e he =>
    allvalid e (hEev e ((hp.2 e).mp he))
  have aux : ∀ pre rest : List Event, ops = pre ++ rest → Legal n (run K pre) rest := by
    intro pre rest
    induction rest generalizing pre with
    | nil => intro _; trivial
    | cons e rest ih =>
      intro hs
      have hvE : e ∈ ops := by rw [hs]; simp
      refine ⟨valid e hvE,funded pre e rest hs,?_⟩
      have ha : run K (pre ++ [e]) = accountStep (run K pre) e := by
        simp [run,List.foldl_append]
      rw [← ha]
      apply ih
      simpa [List.append_assoc] using hs
  exact aux [] ops rfl

theorem causal_history_bounds {n : Nat} {K : Int} [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D n K) (fun e s => applicable n s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis)
    (hf : applySeq (D n K).toUpdateSig initial ops = s) :
    (∀ r, 0 ≤ localRights n s r) ∧ K ≤ value n K s ∧ Conserved n K (project n K s) := by
  have legal := causal_legal hG honest hv hp hc
  have valid : ∀ e ∈ ops, validIssuer n e := by
    intro e he
    obtain ⟨_,_,hg⟩ := honest e (hG.version_events_supported v s E hv e ((hp.2 e).mp he))
    exact applicable_valid hg
  obtain ⟨hs,hcon,hval⟩ := legal_run_safe legal
  have hr : run K ops = project n K s := by rw [run_refines valid,hf]
  rw [hr] at hs hcon hval
  exact ⟨hs,hval,hcon⟩

#print axioms causal_history_accepts
#print axioms causal_history_bounds
#print axioms causal_legal_on

end Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
