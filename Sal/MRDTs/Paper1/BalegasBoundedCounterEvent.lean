import Sal.MRDTs.Paper1.BalegasBoundedCounterProjection
import Sal.MRDTs.Paper1.BoundedCounterEvent

/-! Independent escrow sequential semantics. The scalar counter is the client
observation; balances represent the separately exposed local-rights query.
An increment mints rights, a decrement consumes rights, and a transfer moves
rights without changing the scalar counter. -/
namespace Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
open Foundation Instances.BalegasBoundedCounter
open Classical

abbrev Event := Op Action
structure Accounts where
  value : Int
  balance : Nat → Int

@[ext] theorem accounts_ext {a b : Accounts}
    (hv : a.value = b.value) (hb : a.balance = b.balance) : a = b := by
  cases a; cases b; simp_all

def initialAccounts (K : Int) : Accounts := ⟨K, fun _ => 0⟩

def scalarDelta (e : Event) : Int := match e.op with
  | .increment amount => amount
  | .decrement amount => -(amount : Int)
  | .transfer _ _ => 0

def credit (r : Nat) (e : Event) : Int := match e.op with
  | .increment amount => if r = e.2.1 then amount else 0
  | .transfer amount target => if r = target then amount else 0
  | .decrement _ => 0

def debit (r : Nat) (e : Event) : Int := match e.op with
  | .decrement amount | .transfer amount _ => if r = e.2.1 then amount else 0
  | .increment _ => 0

def accountStep (s : Accounts) (e : Event) : Accounts :=
  ⟨s.value + scalarDelta e, fun r => s.balance r + credit r e - debit r e⟩

def validIssuer (n : Nat) (e : Event) : Prop := e.2.1 < n ∧ match e.op with
  | .transfer _ target => target < n ∧ target ≠ e.2.1
  | _ => True

def affordable (s : Accounts) (e : Event) : Prop := match e.op with
  | .increment _ => True
  | .decrement amount | .transfer amount _ => (amount : Int) ≤ s.balance e.2.1

abbrev Observation := Query

def accountQuery (s : Accounts) : Observation → Int
  | .value => s.value
  | .localRights replica => s.balance replica

def machine (n : Nat) (K : Int) : HistoryMachine Event Observation Int where
  State := Accounts
  initial := initialAccounts K
  transition s label next := match label with
    | .update e => next = accountStep s e ∧ validIssuer n e ∧ affordable s e
    | .query q answer => next = s ∧ answer = accountQuery s q

def spec (n : Nat) (K : Int) := (machine n K).toSpec

def run (K : Int) (ops : List Event) : Accounts :=
  ops.foldl accountStep (initialAccounts K)

theorem credit_nonnegative (r : Nat) (e : Event) : 0 ≤ credit r e := by
  rcases e with ⟨ts,rep,op⟩; cases op <;> simp only [credit, Op.op]
  all_goals try split_ifs
  all_goals omega

theorem debit_support {r : Nat} {e : Event} (h : debit r e ≠ 0) : e.2.1 = r := by
  rcases e with ⟨ts,rep,op⟩; cases op <;> simp [debit, Op.op] at h
  all_goals exact h.1.symm

theorem accountStep_nonnegative {s : Accounts} (h : ∀ r, 0 ≤ s.balance r)
    {e : Event} (funded : affordable s e) : ∀ r, 0 ≤ (accountStep s e).balance r := by
  intro r
  have hr := h r
  rcases e with ⟨ts,rep,op⟩
  have hrep := h rep
  cases op with
  | increment amount =>
    simp only [accountStep,credit,debit,Op.op]
    split_ifs <;> omega
  | decrement amount =>
    simp only [affordable,Op.op] at funded
    simp only [accountStep,credit,debit,Op.op]
    split_ifs <;> subst_vars <;> omega
  | transfer amount target =>
    have ht := h target
    simp only [affordable,Op.op] at funded
    simp only [accountStep,credit,debit,Op.op]
    split_ifs <;> subst_vars <;> omega

theorem run_balance (K : Int) (ops : List Event) (r : Nat) :
    (run K ops).balance r = (ops.map (credit r)).sum - (ops.map (debit r)).sum := by
  have aux : ∀ s : Accounts, (ops.foldl accountStep s).balance r =
      s.balance r + (ops.map (credit r)).sum - (ops.map (debit r)).sum := by
    induction ops with
    | nil => intro s; simp
    | cons e rest ih =>
      intro s
      change (rest.foldl accountStep (accountStep s e)).balance r = _
      rw [ih]
      simp only [accountStep,List.map_cons,List.sum_cons]
      omega
  simpa [run,initialAccounts] using aux (initialAccounts K)

theorem run_value (K : Int) (ops : List Event) :
    (run K ops).value = K + (ops.map scalarDelta).sum := by
  have aux : ∀ s : Accounts, (ops.foldl accountStep s).value =
      s.value + (ops.map scalarDelta).sum := by
    induction ops with
    | nil => intro s; simp
    | cons e rest ih =>
      intro s
      change (rest.foldl accountStep (accountStep s e)).value = _
      rw [ih]
      simp [accountStep]; omega
  exact aux (initialAccounts K)
def project (n : Nat) (K : Int) (s : State) : Accounts :=
  ⟨value n K s, localRights n s⟩

theorem project_initial (n : Nat) (K : Int) : project n K initial = initialAccounts K := by
  apply accounts_ext
  · simp [project,value,initial,initialAccounts]
  · funext r; simp [project,localRights,initial,initialAccounts]

theorem balance_update {n : Nat} (s : State) {e : Event}
    (valid : validIssuer n e) (r : Nat) :
    localRights n (update s e) r = localRights n s r + credit r e - debit r e := by
  rcases e with ⟨ts,rep,op⟩
  cases op with
  | increment amount => simpa [credit,debit,Op.op] using localRights_increment n s ts rep amount r
  | decrement amount => simpa [credit,debit,Op.op] using localRights_decrement n s ts rep amount r
  | transfer amount target =>
    simpa [credit,debit,Op.op] using localRights_transfer n s ts rep amount target r valid.1 valid.2.1 valid.2.2

theorem scalar_update {n : Nat} {K : Int} (s : State) {e : Event}
    (valid : validIssuer n e) :
    value n K (update s e) = value n K s + scalarDelta e := by
  rcases e with ⟨ts,rep,op⟩
  have hr : rep ∈ Finset.range n := Finset.mem_range.mpr valid.1
  cases op with
  | increment amount =>
    simp [value,update,bumpMatrix,scalarDelta,Op.op,Nat.cast_add,
      Finset.sum_add_distrib,hr]
    omega
  | decrement amount =>
    simp [value,update,bump,scalarDelta,Op.op,Nat.cast_add,
      Finset.sum_add_distrib,hr]
    omega
  | transfer amount target =>
    have hne : target ≠ rep := valid.2.2
    have hz : ∀ r, ¬ (r = rep ∧ r = target) := by grind
    simp [value,update,bumpMatrix,scalarDelta,Op.op,Nat.cast_add,hz]

theorem project_update {n : Nat} {K : Int} (s : State) {e : Event}
    (valid : validIssuer n e) : project n K (update s e) = accountStep (project n K s) e := by
  apply accounts_ext
  · exact scalar_update s valid
  · funext r; exact balance_update s valid r

theorem query_refines (n : Nat) (K : Int) (s : State) (q : Query) :
    query n K s q = accountQuery (project n K s) q := by
  cases q <;> rfl

theorem applicable_valid {n : Nat} {s : State} {e : Event} (h : applicable n s e) : validIssuer n e := by
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [applicable,validIssuer,Op.op] at h ⊢
  · exact ⟨h.1,trivial⟩
  · exact ⟨h.1,trivial⟩
  · exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem applicable_affordable {n : Nat} {K : Int} {s : State} {e : Event}
    (h : applicable n s e) : affordable (project n K s) e := by
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [applicable,affordable,project,Op.op] at h ⊢
  · exact h.2
  · exact h.2.2.2

theorem run_refines {n : Nat} {K : Int} {ops : List Event}
    (valid : ∀ e ∈ ops, validIssuer n e) :
    run K ops = project n K (applySeq (D n K).toUpdateSig initial ops) := by
  have aux : ∀ s : State, ops.foldl accountStep (project n K s) =
      project n K (applySeq (D n K).toUpdateSig s ops) := by
    induction ops with
    | nil => intro s; rfl
    | cons e rest ih =>
      intro s
      change rest.foldl accountStep (accountStep (project n K s) e) = _
      rw [← project_update s (valid e (by simp))]
      exact ih (fun x hx => valid x (by simp [hx])) _
  rw [run, ← project_initial n K]
  exact aux _

theorem balance_prefix_ge_past {n : Nat} {K : Int}
    [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} {E S : Set Event} {e : Event}
    (hEev : ∀ a ∈ E, a ∈ C.events) (hSsub : S ⊆ E) (heE : e ∈ E)
    (heS : e ∉ S) (hfut : ∀ x ∈ S, ¬ C.vis e x)
    (hpast : ∀ x, C.vis x e → x ∈ S)
    {ρS ρP : List Event} (hpS : listPermOf ρS S)
    (hpP : listPermOf ρP {x ∈ C.events | C.vis x e}) :
    (run K ρP).balance e.2.1 ≤
    (run K ρS).balance e.2.1 := by
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
  rw [run_balance, run_balance]
  rw [← List.sum_toFinset _ hpP.1, ← List.sum_toFinset _ hpS.1,
    ← List.sum_toFinset _ hpP.1, ← List.sum_toFinset _ hpS.1]
  omega

theorem causal_prefix_affordable {n : Nat} {K : Int}
    [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : ∀ e ∈ C.events, ∃ past : List Event,
      listPermOf past {x ∈ C.events | C.vis x e} ∧ affordable (run K past) e)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E))
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis)
    (pre : List Event) (e : Event) (suf : List Event) (split : ops = pre ++ e :: suf) :
    affordable (run K pre) e := by
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
  obtain ⟨past,hpP,guard⟩ := honest e (hEev e heE)
  have funds : (run K past).balance e.2.1 ≤ (run K pre).balance e.2.1 :=
    balance_prefix_ge_past hEev hsub heE henot hfut hpast
      ⟨(List.nodup_append.mp hnd).1,fun _ => Iff.rfl⟩ hpP
  rcases e with ⟨ts,rep,op⟩
  dsimp only at funds
  cases op <;> simp only [affordable,Op.op] at guard ⊢
  all_goals exact le_trans guard funds

theorem causal_prefix_affordable_on {n : Nat} {K : Int}
    [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : ∀ e ∈ C.events, ∃ past : List Event,
      listPermOf past {x ∈ C.events | C.vis x e} ∧ affordable (run K past) e)
    {E : Set Event} (hEev : ∀ e ∈ E, e ∈ C.events)
    (hEcl : ∀ x y, C.vis x y → y ∈ E → x ∈ E)
    {ops : List Event} (hp : listPermOf ops E) (hc : respects ops C.vis)
    (pre : List Event) (e : Event) (suf : List Event) (split : ops = pre ++ e :: suf) :
    affordable (run K pre) e := by
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
  obtain ⟨past,hpP,guard⟩ := honest e (hEev e heE)
  have funds : (run K past).balance e.2.1 ≤ (run K pre).balance e.2.1 :=
    balance_prefix_ge_past hEev hsub heE henot hfut hpast
      ⟨(List.nodup_append.mp hnd).1,fun _ => Iff.rfl⟩ hpP
  rcases e with ⟨ts,rep,op⟩
  dsimp only at funds
  cases op <;> simp only [affordable,Op.op] at guard ⊢
  all_goals exact le_trans guard funds

theorem accountStep_outside {n r : Nat} {s : Accounts} {e : Event}
    (valid : validIssuer n e) (outside : n ≤ r) :
    (accountStep s e).balance r = s.balance r := by
  rcases e with ⟨ts,rep,op⟩
  have hr : r ≠ rep := (Nat.ne_of_lt (lt_of_lt_of_le valid.1 outside)).symm
  cases op with
  | increment amount => simp [accountStep,credit,debit,Op.op,hr]
  | decrement amount => simp [accountStep,credit,debit,Op.op,hr]
  | transfer amount target =>
    have ht : r ≠ target := (Nat.ne_of_lt (lt_of_lt_of_le valid.2.1 outside)).symm
    simp [accountStep,credit,debit,Op.op,hr,ht]

theorem run_outside {n r : Nat} {K : Int} {ops : List Event}
    (valid : ∀ e ∈ ops, validIssuer n e) (outside : n ≤ r) :
    (run K ops).balance r = 0 := by
  have aux : ∀ s : Accounts, (ops.foldl accountStep s).balance r = s.balance r := by
    induction ops with
    | nil => intro s; rfl
    | cons e rest ih =>
      intro s
      change (rest.foldl accountStep (accountStep s e)).balance r = _
      rw [ih (fun x hx => valid x (by simp [hx]))]
      exact accountStep_outside (valid e (by simp)) outside
  exact aux (initialAccounts K)

end Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
