import Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent

/-! Finite-support capacity conservation for the corrected candidate.
Transfers redistribute existing rights; allocation consumes them. -/
namespace Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent
open Foundation Instances.TransferableBoundedCounter.Corrected
open Classical

/-- All accounts touched by the event, independent of its amount. -/
def touched (e : Event) : Finset Nat := match e.op with
  | .transfer _ target | .rebalance _ target => {e.2.1,target}
  | .allocate _ => {e.2.1}
  | .participants _ => ∅

def support (owner : Nat) (ops : List Event) : Finset Nat :=
  insert owner (ops.foldr (fun e K => touched e ∪ K) ∅)

def totalRights (K : Finset Nat) (s : Accounts) : Int :=
  K.sum s.balance + K.sum s.consumed

/-- A single request conserves available plus consumed rights. Membership
changes have no budget effect. Self-transfers conserve rights as well. -/
theorem accountStep_conserves {K : Finset Nat} {e : Event} (s : Accounts)
    (h : touched e ⊆ K) : totalRights K (accountStep s e) = totalRights K s := by
  rcases e with ⟨ts,rep,op⟩
  cases op with
  | participants ids => simp [totalRights,accountStep,step,Op.op]
  | allocate n =>
    have hr : rep ∈ K := h (by simp [touched,Op.op])
    simp [totalRights,accountStep,step,Op.op,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,hr]
  | transfer n target =>
    have hr : rep ∈ K := h (by simp [touched,Op.op])
    have ht : target ∈ K := h (by simp [touched,Op.op])
    simp [totalRights,accountStep,step,Op.op,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,hr,ht]
  | rebalance n target =>
    have hr : rep ∈ K := h (by simp [touched,Op.op])
    have ht : target ∈ K := h (by simp [touched,Op.op])
    simp [totalRights,accountStep,step,Op.op,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,hr,ht]

theorem run_conserves {capacity owner : Nat} {ops : List Event} {K : Finset Nat}
    (ho : owner ∈ K) (ht : ∀ e ∈ ops, touched e ⊆ K) :
    totalRights K (run capacity owner ops) = capacity := by
  have aux : ∀ s : Accounts, totalRights K (ops.foldl accountStep s) = totalRights K s := by
    induction ops with
    | nil => intro s; rfl
    | cons e rest ih =>
      intro s
      change totalRights K (rest.foldl accountStep (accountStep s e)) = _
      rw [ih (fun x hx => ht x (by simp [hx]))]
      exact accountStep_conserves s (ht e (by simp))
  rw [run,aux]
  simp [totalRights,initialAccounts,initialBalance,ho]

/-- The global allocation bound follows from conservation and nonnegative
remaining balances, on any finite carrier covering the request history. -/
theorem allocation_budget {capacity owner : Nat} {ops : List Event} {K : Finset Nat}
    (ho : owner ∈ K) (ht : ∀ e ∈ ops, touched e ⊆ K)
    (safe : ∀ r, 0 ≤ (run capacity owner ops).balance r) :
    K.sum (run capacity owner ops).consumed ≤ capacity := by
  have hcons := run_conserves (capacity := capacity) ho ht
  have hbal : 0 ≤ K.sum (run capacity owner ops).balance :=
    Finset.sum_nonneg (fun r _ => safe r)
  unfold totalRights at hcons
  omega

#print axioms accountStep_conserves
#print axioms allocation_budget
theorem owner_mem_support (owner : Nat) (ops : List Event) : owner ∈ support owner ops := by
  simp [support]

theorem touched_subset_support {owner : Nat} {ops : List Event} {e : Event} (he : e ∈ ops) :
    touched e ⊆ support owner ops := by
  have aux : ∀ ops : List Event, ∀ e ∈ ops,
      touched e ⊆ ops.foldr (fun x K => touched x ∪ K) ∅ := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih e he) Finset.subset_union_right
  exact Finset.Subset.trans (aux ops e he) (Finset.subset_insert _ _)

theorem accountStep_outside {K : Finset Nat} {e : Event} {r : Nat}
    (s : Accounts) (h : touched e ⊆ K) (hr : r ∉ K) :
    (accountStep s e).balance r = s.balance r ∧
    (accountStep s e).consumed r = s.consumed r := by
  have hn : r ∉ touched e := fun hm => hr (h hm)
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp [touched,Op.op] at hn
  all_goals simp_all [accountStep,step,Op.op]

theorem run_outside {capacity owner : Nat} {ops : List Event} {K : Finset Nat}
    (ho : owner ∈ K) (ht : ∀ e ∈ ops, touched e ⊆ K) {r : Nat} (hr : r ∉ K) :
    (run capacity owner ops).balance r = 0 ∧ (run capacity owner ops).consumed r = 0 := by
  have aux : ∀ s : Accounts, (ops.foldl accountStep s).balance r = s.balance r ∧
      (ops.foldl accountStep s).consumed r = s.consumed r := by
    induction ops with
    | nil => intro s; exact ⟨rfl,rfl⟩
    | cons e rest ih =>
      intro s
      have htail := ih (fun x hx => ht x (by simp [hx])) (accountStep s e)
      have hhead := accountStep_outside s (ht e (by simp)) hr
      exact ⟨htail.1.trans hhead.1,htail.2.trans hhead.2⟩
  have ne : r ≠ owner := fun eq => hr (eq ▸ ho)
  simpa [run,initialAccounts,initialBalance,ne] using aux (initialAccounts capacity owner)

/-- Complete finite-support global budget: no account outside the carrier
has any consumed rights, and total consumption never exceeds initial capacity. -/
theorem history_capacity_bound {capacity owner : Nat} {ops : List Event}
    (safe : ∀ r, 0 ≤ (run capacity owner ops).balance r) :
    (support owner ops).sum (run capacity owner ops).consumed ≤ capacity ∧
      ∀ r ∉ support owner ops, (run capacity owner ops).consumed r = 0 := by
  refine ⟨allocation_budget (owner_mem_support owner ops)
    (fun e he => touched_subset_support he) safe, ?_⟩
  intro r hr
  exact (run_outside (owner_mem_support owner ops)
    (fun e he => touched_subset_support he) hr).2

#print axioms history_capacity_bound
theorem causal_history_budget {capacity owner : Nat}
    [EventOrder (D capacity owner).toUpdateSig]
    {C : Configuration (D capacity owner)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D capacity owner) (fun e s => applicable owner s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis)
    (hf : applySeq (D capacity owner).toUpdateSig (initial capacity owner) ops = s) :
    Nonnegative s ∧ (support owner ops).sum s.allocations ≤ capacity ∧
      (∀ r ∉ support owner ops, s.allocations r = 0) ∧
      totalRights (support owner ops) (project s) = capacity := by
  have hpref :=  prefix_inv_of_causal_witness (initial_nonnegative capacity owner)
    (safetyStep capacity owner) hG honest hv hp hc
  have hs : Nonnegative s := by
    rw [← hf]; exact hpref ops [] (by simp)
  have hr : run capacity owner ops = project s := by rw [run_refines,hf]
  have hb := history_capacity_bound (capacity := capacity) (owner := owner) (ops := ops) (by
    intro r; rw [hr]; exact hs r)
  rw [hr] at hb
  refine ⟨hs,hb.1,hb.2,?_⟩
  rw [← hr]
  exact run_conserves (owner_mem_support owner ops) (fun e he => touched_subset_support he)

private theorem honest_of_mint {capacity owner : Nat} {C : Configuration (D capacity owner)}
    (h : MintHonest (D capacity owner) (fun e s => applicable owner s e) C) :
    HonestAppOn (D capacity owner) (fun e s => applicable owner s e) C := by
  intro e he
  obtain ⟨past,hp,hc,hg⟩ := h e he
  exact ⟨applySeq (D capacity owner).toUpdateSig (D capacity owner).init past,
    ⟨past,hp,hc,rfl⟩,hg⟩

/-- Every stored ordinary/recursive-virtual version has nonnegative balances,
finite support, conserved total capacity, and bounded global allocations. -/
theorem versions_budgetV {capacity owner : Nat} {C : Configuration (D capacity owner)}
    (reach : MintCertifiedReachV (D capacity owner) (canonicalVirtualMergeBase (D capacity owner))
      (generation capacity owner) C) :
    ∀ v s E, C.ver v = some (s,E) → ∃ ops : List Event,
      listPermOf ops E ∧ respects ops C.vis ∧ Nonnegative s ∧
      (support owner ops).sum s.allocations ≤ capacity ∧
      (∀ r ∉ support owner ops, s.allocations r = 0) ∧
      totalRights (support owner ops) (project s) = capacity := by
  have hG := canonicalConfig_of_mintCertifiedV (fun _ _ => join capacity owner _) reach
  have hCC := causalCanonical_of_all_comm_replayOrder_either (all_comm capacity owner)
    (fun _ _ => rfl) hG
  intro v s E hv
  obtain ⟨ops,hp,hc,_,hf⟩ := hCC v s E hv
  exact ⟨ops,hp,hc,causal_history_budget hG (honest_of_mint reach.mintHonest) hv hp hc hf⟩

theorem versions_budget {capacity owner : Nat} {C : Configuration (D capacity owner)}
    (reach : MintCertifiedReach (D capacity owner) (generation capacity owner) C) :
    ∀ v s E, C.ver v = some (s,E) → ∃ ops : List Event,
      listPermOf ops E ∧ respects ops C.vis ∧ Nonnegative s ∧
      (support owner ops).sum s.allocations ≤ capacity ∧
      (∀ r ∉ support owner ops, s.allocations r = 0) ∧
      totalRights (support owner ops) (project s) = capacity :=
  versions_budgetV reach.toV

#print axioms versions_budgetV
theorem accountStep_consumed_nonnegative {s : Accounts} (h : ∀ r, 0 ≤ s.consumed r)
    (e : Event) : ∀ r, 0 ≤ (accountStep s e).consumed r := by
  intro r
  have hr := h r
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [accountStep,Op.op]
  all_goals (try split_ifs) <;> omega

theorem run_consumed_nonnegative (capacity owner : Nat) (ops : List Event) :
    ∀ r, 0 ≤ (run capacity owner ops).consumed r := by
  have aux : ∀ s : Accounts, (∀ r, 0 ≤ s.consumed r) →
      ∀ r, 0 ≤ (ops.foldl accountStep s).consumed r := by
    induction ops with
    | nil => intro s hs; exact hs
    | cons e rest ih =>
      intro s hs
      exact ih (accountStep s e) (accountStep_consumed_nonnegative hs e)
  exact aux (initialAccounts capacity owner) (fun _ => le_refl 0)

theorem versions_allocations_nonnegativeV {capacity owner : Nat}
    {C : Configuration (D capacity owner)}
    (reach : MintCertifiedReachV (D capacity owner) (canonicalVirtualMergeBase (D capacity owner))
      (generation capacity owner) C) :
    VersionsSatisfy (fun s : State => ∀ r, 0 ≤ s.allocations r) C := by
  have hG := canonicalConfig_of_mintCertifiedV (fun _ _ => join capacity owner _) reach
  intro v s E hv
  obtain ⟨ops,_,_,hf⟩ := hG.canonical v s E hv
  change applySeq (D capacity owner).toUpdateSig (initial capacity owner) ops = s at hf
  have hr : run capacity owner ops = project s := by rw [run_refines,hf]
  have nonneg := run_consumed_nonnegative capacity owner ops
  rw [hr] at nonneg
  exact nonneg

#print axioms versions_allocations_nonnegativeV
end Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent
