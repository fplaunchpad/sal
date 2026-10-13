import Sal.MRDTs.Instances.TransferableBoundedCounterCorrected
import Sal.MRDTs.Paper1.BoundedCounterEvent

/-! Independent nonnegative account semantics for the corrected additive
candidate. Prepared rebalance labels have transfer semantics; the abstract
machine does not repeat extrema selection at replay time. -/
namespace Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent
open Foundation Instances.TransferableBoundedCounter.Corrected
open Classical

abbrev Event := Op Action
abbrev Balance := Nat → Int

def step (balance : Balance) (e : Event) : Balance := fun r => match e.op with
  | .participants _ => balance r
  | .allocate n => balance r - if r = e.2.1 then (n : Int) else 0
  | .transfer n target | .rebalance n target =>
    balance r + (if r = target then (n : Int) else 0) -
      (if r = e.2.1 then (n : Int) else 0)

def initialBalance (capacity owner : Nat) : Balance :=
  fun r => if r = owner then capacity else 0

structure Accounts where
  balance : Balance
  consumed : Nat → Int

def initialAccounts (capacity owner : Nat) : Accounts :=
  ⟨initialBalance capacity owner, fun _ => 0⟩

def accountStep (s : Accounts) (e : Event) : Accounts :=
  ⟨step s.balance e, fun r => s.consumed r + match e.op with
    | .allocate n => if r = e.2.1 then n else 0
    | _ => 0⟩

def accountQuery (s : Accounts) : Query → Int
  | .available r => s.balance r
  | .reserved r => s.balance r + s.consumed r
  | .allocated r => s.consumed r

def affordable (balance : Balance) (e : Event) : Prop := match e.op with
  | .participants _ => True
  | .allocate n | .transfer n _ | .rebalance n _ => (n : Int) ≤ balance e.2.1

def machine (capacity owner : Nat) : HistoryMachine Event Query Int where
  State := Accounts
  initial := initialAccounts capacity owner
  transition s label next := match label with
    | .update e => next = accountStep s e ∧ (∀ r, 0 ≤ next.balance r) ∧ affordable s.balance e
    | .query q answer => next = s ∧ answer = accountQuery s q

def spec (capacity owner : Nat) := (machine capacity owner).toSpec

def Nonnegative (s : State) : Prop := ∀ r, 0 ≤ available s r

theorem initial_nonnegative (capacity owner : Nat) :
    Nonnegative (initial capacity owner) := by
  intro r; simp [available, initial]; split_ifs <;> (try simp_all only) <;> omega

theorem step_refines (s : State) (e : Event) :
    available (update s e) = step (available s) e := by
  funext r
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [update, step, available, bump, Op.op]
  all_goals split_ifs <;> (try simp_all only) <;> omega

theorem guarded_update_nonnegative {owner : Nat} {s : State} {e : Event}
    (inv : Nonnegative s) (guard : applicable owner s e) :
    Nonnegative (update s e) := by
  intro r
  rw [step_refines]
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [step, Op.op] at *
  · exact inv r
  · simp only [applicable, Op.op] at guard
    have hr := inv r
    have hs := inv rep
    split_ifs <;> (try simp_all only) <;> omega
  · simp only [applicable, Op.op] at guard
    have hr := inv r
    have hs := inv rep
    split_ifs <;> (try simp_all only) <;> omega
  · simp only [applicable, Op.op] at guard
    have hr := inv r
    have hs := inv rep
    split_ifs <;> (try simp_all only) <;> omega

def credit (r : Nat) (e : Event) : Int := match e.op with
  | .transfer n target | .rebalance n target => if r = target then n else 0
  | _ => 0

def debit (r : Nat) (e : Event) : Int := match e.op with
  | .allocate n | .transfer n _ | .rebalance n _ => if r = e.2.1 then n else 0
  | _ => 0

theorem credit_nonnegative (r : Nat) (e : Event) : 0 ≤ credit r e := by
  rcases e with ⟨ts,rep,op⟩; cases op <;> simp only [credit, Op.op]
  all_goals try split_ifs
  all_goals omega

theorem debit_support {r : Nat} {e : Event} (h : debit r e ≠ 0) : e.2.1 = r := by
  rcases e with ⟨ts,rep,op⟩; cases op <;> simp [debit, Op.op] at h
  all_goals exact h.1.symm

theorem available_update (s : State) (e : Event) (r : Nat) :
    available (update s e) r = available s r + credit r e - debit r e := by
  rw [step_refines]
  rcases e with ⟨ts,rep,op⟩; cases op <;> simp [step, credit, debit, Op.op]

theorem available_fold (capacity owner : Nat) (ops : List Event) (r : Nat) :
    available (applySeq (D capacity owner).toUpdateSig (initial capacity owner) ops) r =
      initialBalance capacity owner r + (ops.map (credit r)).sum - (ops.map (debit r)).sum := by
  have general : ∀ (s : State), available (applySeq (D capacity owner).toUpdateSig s ops) r =
      available s r + (ops.map (credit r)).sum - (ops.map (debit r)).sum := by
    induction ops with
    | nil => intro s; simp [applySeq]
    | cons e rest ih =>
      intro s
      change available (applySeq (D capacity owner).toUpdateSig (update s e) rest) r = _
      rw [ih, available_update]
      simp only [List.map_cons, List.sum_cons]
      omega
  simpa [available, initial, initialBalance] using general (initial capacity owner)

/-- The source's accumulated debits are unchanged by independent events;
credits from other sources can only increase. -/
theorem available_prefix_ge_past {capacity owner : Nat}
    [EventOrder (D capacity owner).toUpdateSig]
    {C : Configuration (D capacity owner)} {E S : Set Event} {e : Event}
    (hEev : ∀ a ∈ E, a ∈ C.events) (hSsub : S ⊆ E) (heE : e ∈ E)
    (heS : e ∉ S) (hfut : ∀ x ∈ S, ¬ C.vis e x)
    (hpast : ∀ x, C.vis x e → x ∈ S)
    {ρS ρP : List Event} (hpS : listPermOf ρS S)
    (hpP : listPermOf ρP {x ∈ C.events | C.vis x e}) :
    available (applySeq (D capacity owner).toUpdateSig (initial capacity owner) ρP) e.2.1 ≤
    available (applySeq (D capacity owner).toUpdateSig (initial capacity owner) ρS) e.2.1 := by
  have hsub : ρP.toFinset ⊆ ρS.toFinset := by
    intro x hx
    have hxP := (hpP.2 x).mp (List.mem_toFinset.mp hx)
    exact List.mem_toFinset.mpr ((hpS.2 x).mpr (hpast x hxP.2))
  have hdebit : ρP.toFinset.sum (debit e.2.1) =
      ρS.toFinset.sum (debit e.2.1) := by
    apply Finset.sum_subset hsub
    intro x hxS hxP
    by_contra hn
    have hxSset := (hpS.2 x).mp (List.mem_toFinset.mp hxS)
    have hxev := hEev x (hSsub hxSset)
    have heev := hEev e heE
    have hne : x ≠ e := fun h => heS (h ▸ hxSset)
    obtain ⟨r₁,s₁,hL₁,hs₁⟩ := hxev
    obtain ⟨r₂,s₂,hL₂,hs₂⟩ := heev
    rcases C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ hne (debit_support hn) with hxe | hex
    · exact hxP (List.mem_toFinset.mpr ((hpP.2 x).mpr ⟨⟨r₁,s₁,hL₁,hs₁⟩,hxe⟩))
    · exact hfut x hxSset hex
  have hcredit : ρP.toFinset.sum (credit e.2.1) ≤
      ρS.toFinset.sum (credit e.2.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => credit_nonnegative _ x)
  rw [available_fold, available_fold]
  rw [← List.sum_toFinset _ hpP.1, ← List.sum_toFinset _ hpS.1,
    ← List.sum_toFinset _ hpP.1, ← List.sum_toFinset _ hpS.1]
  omega

theorem safetyStep (capacity owner : Nat) [EventOrder (D capacity owner).toUpdateSig] :
    SafetyStepOn (D capacity owner) Nonnegative (fun e s => applicable owner s e) := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hσS hσP hInv happ
  obtain ⟨ρS,hpS,hrS,hfS⟩ := hσS
  obtain ⟨ρP,hpP,hrP,hfP⟩ := hσP
  have hfund : available σP e.2.1 ≤ available σS e.2.1 := by
    rw [← hfS, ← hfP]
    exact available_prefix_ge_past hEev hSsub heE heS hfut hpast hpS hpP
  intro r
  change 0 ≤ available (update σS e) r
  rw [step_refines]
  rcases e with ⟨ts,rep,op⟩
  dsimp only at hfund
  cases op <;> simp only [applicable, Op.op] at happ
  · exact hInv r
  · have hr := hInv r
    simp only [step, Op.op]
    split_ifs <;> (try simp_all only) <;> omega
  · have hr := hInv r
    simp only [step, Op.op]
    split_ifs <;> (try simp_all only) <;> omega
  · have hr := hInv r
    have hbudget := happ.2.2.2.2
    simp only [step, Op.op]
    split_ifs <;> (try simp_all only) <;> omega

def project (s : State) : Accounts := ⟨available s, s.allocations⟩

@[ext] theorem accounts_ext {a b : Accounts}
    (hbal : a.balance = b.balance) (hcons : a.consumed = b.consumed) : a = b := by
  cases a; cases b; simp_all

theorem project_initial (capacity owner : Nat) :
    project (initial capacity owner) = initialAccounts capacity owner := by
  apply accounts_ext
  · funext r; simp [project,available,initial,initialAccounts,initialBalance]
  · rfl

theorem project_update (s : State) (e : Event) :
    project (update s e) = accountStep (project s) e := by
  apply accounts_ext
  · exact step_refines s e
  · funext r
    rcases e with ⟨ts,rep,op⟩
    cases op <;> simp [project,accountStep,update,bump,Op.op]

theorem query_refines (s : State) (q : Query) : query s q = accountQuery (project s) q := by
  cases q <;> simp [query,accountQuery,project,available,reserved]

def run (capacity owner : Nat) (ops : List Event) : Accounts :=
  ops.foldl accountStep (initialAccounts capacity owner)

theorem run_refines (capacity owner : Nat) (ops : List Event) :
    run capacity owner ops = project (applySeq (D capacity owner).toUpdateSig (initial capacity owner) ops) := by
  have aux : ∀ s : State, ops.foldl accountStep (project s) =
      project (applySeq (D capacity owner).toUpdateSig s ops) := by
    induction ops with
    | nil => intro s; rfl
    | cons e rest ih =>
      intro s
      change rest.foldl accountStep (accountStep (project s) e) = _
      rw [← project_update, ih]
      rfl
  rw [run, ← project_initial]
  exact aux _

private theorem run_append (capacity owner : Nat) (pre : List Event) (e : Event) :
    run capacity owner (pre ++ [e]) = accountStep (run capacity owner pre) e := by
  simp [run,List.foldl_append]

theorem accepted_of_prefix_nonnegative (capacity owner : Nat) (ops : List Event)
    (safe : ∀ pre suf, ops = pre ++ suf → ∀ r, 0 ≤ (run capacity owner pre).balance r)
    (funded : ∀ pre e suf, ops = pre ++ e :: suf → affordable (run capacity owner pre).balance e)
    (q : Query) :
    (spec capacity owner).admits (ops.map SeqLabel.update ++
      [.query q (accountQuery (run capacity owner ops) q)]) := by
  have aux : ∀ (pre rest : List Event), ops = pre ++ rest →
      Runs (machine capacity owner).transition (run capacity owner pre)
        (rest.map SeqLabel.update) (run capacity owner ops) := by
    intro pre rest
    induction rest generalizing pre with
    | nil => intro split; subst ops; simpa using Runs.nil (step := (machine capacity owner).transition) (run capacity owner pre)
    | cons e rest ih =>
      intro split
      have split' : ops = (pre ++ [e]) ++ rest := by simpa [List.append_assoc] using split
      refine .cons (m := run capacity owner (pre ++ [e])) ?_ (ih _ split')
      exact ⟨run_append _ _ _ _, safe _ _ split', funded pre e rest split⟩
  refine ⟨run capacity owner ops, ?_⟩
  exact (aux [] ops rfl).append (.cons ⟨rfl,rfl⟩ (.nil _))

theorem applicable_affordable {owner : Nat} {s : State} {e : Event}
    (h : applicable owner s e) : affordable (available s) e := by
  rcases e with ⟨ts,rep,op⟩
  cases op with
  | participants ids => trivial
  | allocate n => exact h
  | transfer n target => exact h
  | rebalance n target => exact h.2.2.2.2

/-- An issued debit remains affordable at its place in any causal
serialization: the source has no additional outgoing requests, and may have
additional incoming credits. -/
theorem causal_prefix_affordable {capacity owner : Nat}
    [EventOrder (D capacity owner).toUpdateSig]
    {C : Configuration (D capacity owner)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D capacity owner) (fun e s => applicable owner s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis)
    (pre : List Event) (e : Event) (suf : List Event) (split : ops = pre ++ e :: suf) :
    affordable (run capacity owner pre).balance e := by
  have hEev := hG.version_events_supported v s E hv
  have hEcl := hG.version_events_causal v s E hv
  have hnd : (pre ++ e :: suf).Nodup := by rw [← split]; exact hp.1
  have hpw : (pre ++ e :: suf).Pairwise (fun a b => ¬ C.vis b a) := by
    rw [← split]; exact hc
  obtain ⟨_,hpwE,hcross⟩ := List.pairwise_append.mp hpw
  have hsuf_no_e := (List.pairwise_cons.mp hpwE).1
  have hmem : ∀ x, x ∈ pre ++ e :: suf ↔ x ∈ E := by
    intro x; rw [← split]; exact hp.2 x
  have heE : e ∈ E := (hmem e).mp (List.mem_append_right _ List.mem_cons_self)
  have hsub : {x : Event | x ∈ pre} ⊆ E := fun x hx =>
    (hmem x).mp (List.mem_append_left _ hx)
  have henot : e ∉ ({x : Event | x ∈ pre} : Set Event) := by
    intro hm
    exact (List.nodup_append.mp hnd).2.2 e hm e List.mem_cons_self rfl
  have hfut : ∀ x ∈ ({x : Event | x ∈ pre} : Set Event), ¬ C.vis e x :=
    fun x hx => hcross x hx e List.mem_cons_self
  have hpast : ∀ x, C.vis x e → x ∈ ({x : Event | x ∈ pre} : Set Event) := by
    intro x hxe
    have hxE := hEcl x e hxe heE
    rcases List.mem_append.mp ((hmem x).mpr hxE) with hx | hx
    · exact hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hxe (hG.vis_irrefl x)
      · exact absurd hxe (hsuf_no_e x hx)
  obtain ⟨pastState,⟨past,hpP,_,hfP⟩,guard⟩ := honest e (hEev e heE)
  have funds : available pastState e.2.1 ≤
      available (applySeq (D capacity owner).toUpdateSig (initial capacity owner) pre) e.2.1 := by
    rw [← hfP]
    exact available_prefix_ge_past hEev hsub heE henot hfut hpast
      ⟨(List.nodup_append.mp hnd).1,fun _ => Iff.rfl⟩ hpP
  have budget := applicable_affordable guard
  rw [run_refines]
  change affordable (available (applySeq (D capacity owner).toUpdateSig (initial capacity owner) pre)) e
  rcases e with ⟨ts,rep,op⟩
  dsimp only at funds
  cases op <;> simp only [affordable,Op.op] at budget ⊢
  all_goals exact le_trans budget funds

/-- Every causal explanation of a stored state has an independent legal
account history; preparation constraints are used only at the original past. -/
theorem causal_history_accepts {capacity owner : Nat}
    [EventOrder (D capacity owner).toUpdateSig]
    {C : Configuration (D capacity owner)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D capacity owner) (fun e s => applicable owner s e) C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis) (q : Query) :
    (spec capacity owner).admits (ops.map SeqLabel.update ++ [.query q (query s q)]) := by
  have safe := prefix_inv_of_causal_witness (initial_nonnegative capacity owner)
    (safetyStep capacity owner) hG honest hv hp hc
  have accepted := accepted_of_prefix_nonnegative capacity owner ops (by
    intro pre suf split r
    rw [run_refines]
    exact safe pre suf split r) (causal_prefix_affordable hG honest hv hp hc) q
  have hfold : applySeq (D capacity owner).toUpdateSig (initial capacity owner) ops = s := by
    obtain ⟨other,hpo,_,ho⟩ := hG.canonical v s E hv
    have perm : ops.Perm other := List.perm_ext_iff_of_nodup hp.1 hpo.1 |>.mpr (by
      intro x; exact (hp.2 x).trans (hpo.2 x).symm)
    exact (applySeq_perm_of_all_comm (all_comm capacity owner) perm _).trans ho
  simpa [run_refines, hfold, ← query_refines] using accepted

#print axioms safetyStep
#print axioms causal_history_accepts

abbrev policy := SimpleEventPorts.emptyPolicy Action

theorem certifiedV (capacity owner : Nat) :
    EventCertifiedSpecificationRAV (D capacity owner) policy (spec capacity owner)
      (generation capacity owner) := by
  letI : EventOrder (D capacity owner).toUpdateSig := policy.lift
  intro C reach
  have hjoin : @Join (D capacity owner) policy.lift := by
    simpa [policy, SimpleEventPorts.emptyPolicy, OperationPolicy.lift,
      EventOrder.default, EventOrder.unconstrained] using join capacity owner
  have hG := canonicalConfig_of_mintCertifiedV (fun _ _ => hjoin _) reach
  have hCC := causalCanonical_of_all_comm_replayOrder_either (all_comm capacity owner)
    (fun _ _ => by
      change (policy.lift (D := (D capacity owner).toUpdateSig)).order _ _ = OrderResult.Either
      simp [policy, SimpleEventPorts.emptyPolicy, OperationPolicy.lift]) hG
  have honest : HonestAppOn (D capacity owner) (fun e s => applicable owner s e) C := by
    intro e he
    obtain ⟨past,hp,hr,hguard⟩ := reach.mintHonest e he
    exact ⟨applySeq (D capacity owner).toUpdateSig (D capacity owner).init past,
      ⟨past,hp,hr,rfl⟩,hguard⟩
  intro v s E hv q
  obtain ⟨ops,hp,hvis,horder,hfold⟩ := hCC v s E hv
  refine ⟨ops,hp,?_,?_,causal_history_accepts hG honest hv hp hvis q⟩
  · apply List.pairwise_of_forall
    intro a b h
    rcases h with h | h
    · exact h.2 (all_comm capacity owner b a)
    · exact h.2.2.1
  · exact hvis.imp (fun {_ _} h hspec => h hspec.1)

theorem certified (capacity owner : Nat) :
    EventCertifiedSpecificationRA (D capacity owner) policy (spec capacity owner)
      (generation capacity owner) := (certifiedV capacity owner).ordinary

#print axioms certifiedV

end Sal.MRDTs.Paper1.TransferableBoundedCounterCorrectedEvent
