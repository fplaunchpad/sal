import LeanProofs_no_spec_non_comm.Implementations.BoundedCounter.Definition
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import LeanProofs_no_spec_non_comm.Interface.CausalRoute
import LeanProofs_no_spec_non_comm.Metatheory.CausalAdequacy
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/BoundedCounter/VCs.lean` with the namespace changed. The
last section is what this folder adds: the chosen history respects
**specification visibility** as well, with no appeal to SPEC-NON-COMM.

# The bounded counter: `Laws(D_type)`, VC1 and VC2

Every effector adds its amount to one cell, so every pair of events
commutes and `rc` is empty. `Laws(D_type)` is then immediate, VC1 is the
commutativity of `max`, and VC2 is `max 0 x = x`.

VC3, VC4 and VC5 are **not** here. `Negative.lean` shows VC4 is false.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {n : Nat} {K : Int}

theorem do_eq (s : St) (e : (D n K).Event) : (D n K).do_ s e = step s e := rfl

theorem merge_eq (l a b : (D n K).Sigma) : (D n K).merge l a b = mergeState l a b := rfl

theorem sigma0_eq : (D n K).sigma0 = initial := rfl

/-! ## Every pair of events commutes -/

theorem bump_comm (f : Nat → Nat) (r₁ a₁ r₂ a₂ : Nat) :
    bump (bump f r₁ a₁) r₂ a₂ = bump (bump f r₂ a₂) r₁ a₁ := by
  funext k; simp only [bump]; omega

theorem bumpMatrix_comm (f : Nat → Nat → Nat) (r₁ c₁ a₁ r₂ c₂ a₂ : Nat) :
    bumpMatrix (bumpMatrix f r₁ c₁ a₁) r₂ c₂ a₂
      = bumpMatrix (bumpMatrix f r₂ c₂ a₂) r₁ c₁ a₁ := by
  funext i j; simp only [bumpMatrix]; omega

theorem all_commute (e₁ e₂ : (D n K).Event) : (D n K).Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  rcases h₁ : e₁.op with a₁ | a₁ | ⟨a₁, j₁⟩ <;> rcases h₂ : e₂.op with a₂ | a₂ | ⟨a₂, j₂⟩ <;>
    simp only [step, h₁, h₂] <;>
    refine St.ext (fun i j => ?_) (fun i => ?_) <;>
    simp only [bumpMatrix, bump] <;> omega

/-! ## `Laws(D_type)` -/

theorem no_rc_edge (e₁ e₂ : (D n K).Event) : ¬ (D n K).EventRcBefore e₁ e₂ := by
  simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOf]

theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ ((D n K).RcBefore o₁ o₂ ∧ (D n K).RcBefore o₂ o₃) := by
  rintro ⟨h, -⟩
  simp [Impl.RcBefore, D, rcOf] at h

theorem rc_non_comm (e₁ e₂ : (D n K).Event)
    (_ht : (D n K).time e₁ ≠ (D n K).time e₂)
    (_hr : (D n K).rep e₁ ≠ (D n K).rep e₂) :
    ((¬ (D n K).Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      (D n K).EventRcBefore e₁ e₂ ∨ (D n K).EventRcBefore e₂ e₁) := by
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h.1
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

theorem cond_comm (sigma : (D n K).Sigma) (e e' e'' : (D n K).Event)
    (pi : List (D n K).Event)
    (_ht : (D n K).time e ≠ (D n K).time e') (_hr : (D n K).rep e ≠ (D n K).rep e')
    (hrc : (D n K).EventRcBefore e e') (_hnc : ¬ (D n K).Commutes e' e'') :
    (D n K).do_ ((D n K).applyList ((D n K).do_ ((D n K).do_ sigma e') e) pi) e''
      = (D n K).do_ ((D n K).applyList ((D n K).do_ ((D n K).do_ sigma e) e') pi) e'' :=
  absurd hrc (no_rc_edge e e')

theorem laws : Laws (D n K) := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-! ## VC1 and VC2 -/

theorem vc1_merge_comm (l a b : (D n K).Sigma) :
    (D n K).merge l a b = (D n K).merge l b a := by
  simp only [merge_eq, mergeState]
  exact St.ext (fun i j => Nat.max_comm _ _) (fun i => Nat.max_comm _ _)

theorem vc2_merge_init (s : (D n K).Sigma) :
    (D n K).merge (D n K).sigma0 (D n K).sigma0 s = s := by
  simp only [merge_eq, mergeState, sigma0_eq]
  exact St.ext (fun i j => by simp [initial]) (fun i => by simp [initial])


/-! ## Part III: the five conditions at the full causal past

`Negative.lean` shows VC4 false at `downset`, and false again at any larger
dependency set while maximality stays vacuous. `Interface/CausalRoute.lean`
changes both halves at once, and this section discharges the row's five
conditions at that reading.

The whole argument is one observation about the state: **every cell is
written by one replica only**, so a cell carries the sum of the
contributions of that replica's events. Writing the canonical state's cells
as sums over the event set turns VC4 into two facts about sets, and causal
maximality supplies the second.
-/

/-- The amount `e` adds to cell `R i j`. -/
def contribR (i j : Nat) (e : Op AppOp) : Nat :=
  match e.op with
  | .increment a => if i = e.rep ∧ j = e.rep then a else 0
  | .decrement _ => 0
  | .transfer a t => if i = e.rep ∧ j = t then a else 0

/-- The amount `e` adds to cell `U i`. -/
def contribU (i : Nat) (e : Op AppOp) : Nat :=
  match e.op with
  | .increment _ => 0
  | .decrement a => if i = e.rep then a else 0
  | .transfer _ _ => 0

/-- **Only the issuer writes a cell of `R`.** This is the single-writer
discipline, as a statement about contributions. -/
theorem contribR_rep {i j : Nat} {e : Op AppOp} (h : contribR i j e ≠ 0) :
    i = e.rep := by
  by_contra hne
  exact h (by unfold contribR; split <;> simp [hne])

/-- **Only the issuer writes a cell of `U`.** -/
theorem contribU_rep {i : Nat} {e : Op AppOp} (h : contribU i e ≠ 0) :
    i = e.rep := by
  by_contra hne
  exact h (by unfold contribU; split <;> simp [hne])

/-! ### Cells as sums -/

theorem step_R (s : St) (e : Op AppOp) (i j : Nat) :
    (step s e).R i j = s.R i j + contribR i j e := by
  rcases hop : e.op with a | a | ⟨a, t⟩ <;>
    simp [step, contribR, hop, bumpMatrix]

theorem step_U (s : St) (e : Op AppOp) (i : Nat) :
    (step s e).U i = s.U i + contribU i e := by
  rcases hop : e.op with a | a | ⟨a, t⟩ <;>
    simp [step, contribU, hop, bump]

theorem fold_R (s : St) (π : List (Op AppOp)) (i j : Nat) :
    (π.foldl step s).R i j = s.R i j + (π.map (contribR i j)).sum := by
  induction π generalizing s with
  | nil => simp
  | cons e rest ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, step_R]
    omega

theorem fold_U (s : St) (π : List (Op AppOp)) (i : Nat) :
    (π.foldl step s).U i = s.U i + (π.map (contribU i)).sum := by
  induction π generalizing s with
  | nil => simp
  | cons e rest ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, step_U]
    omega

/-- **The canonical state's cells, as sums over the event set.** Any
enumeration of `E` will do, because a sum over a `Finset` does not see the
order. -/
theorem canon_sums {C : Ctx (D n K)} {E : Set (D n K).Event} {s : St}
    (hs : IsPaperCan (D n K) C E s) :
    ∃ t : Finset (D n K).Event, (∀ x, x ∈ t ↔ x ∈ E) ∧
      (∀ i j, s.R i j = ∑ x ∈ t, contribR i j x) ∧
      (∀ i, s.U i = ∑ x ∈ t, contribU i x) := by
  classical
  obtain ⟨π, hp, -, hf⟩ := hs
  refine ⟨π.toFinset, fun x => by simpa using hp.2 x, ?_, ?_⟩
  · intro i j
    rw [List.sum_toFinset _ hp.1, ← hf]
    simpa [sigma0_eq, initial] using fold_R initial π i j
  · intro i
    rw [List.sum_toFinset _ hp.1, ← hf]
    simpa [sigma0_eq, initial] using fold_U initial π i

/-! ### VC4

Two facts about the event sets. `B`'s set is contained in `A`'s, which
bounds every cell. And on the one cell `e` writes the two sets agree,
because a contributor to that cell is issued by `e`'s own replica, so it is
`vis`-comparable with `e`, and causal maximality rules out the direction
that would put it after `e`. -/

/-- **VC4** CAUSAL-DELTA, at the full causal past. -/
theorem vc4_causal_delta (C : Ctx (D n K)) (U : Set (D n K).Event)
    (A B : St) (e : (D n K).Event)
    (_hvs : VisStrict (D n K) C)
    (hsup : SupportedOn (D n K) C U) (hcl : CausallyClosed (D n K) C U)
    (heU : e ∈ U) (hcmax : CausalMaximalOn (D n K) C U e)
    (hA : IsPaperCan (D n K) C (U \ {e}) A)
    (hB : IsPaperCan (D n K) C (CausalPast (D n K) C e \ {e}) B) :
    (D n K).merge B A ((D n K).do_ B e) = (D n K).do_ A e := by
  classical
  obtain ⟨tA, hmA, hRA, hUA⟩ := canon_sums hA
  obtain ⟨tB, hmB, hRB, hUB⟩ := canon_sums hB
  -- `B`'s set sits inside `A`'s.
  have hpast : CausalPast (D n K) C e ⊆ U :=
    (causalScheme (D n K) C).past_subset U e hcl heU
  have hsub : tB ⊆ tA := by
    intro x hx
    have hx' := (hmB x).mp hx
    exact (hmA x).mpr ⟨hpast hx'.1, hx'.2⟩
  -- A contributor to a cell of `e`'s replica is in `B`'s set.
  have key : ∀ x ∈ tA, x.rep = e.rep → x ∈ tB := by
    intro x hx hrep
    obtain ⟨hxU, hxne⟩ := (hmA x).mp hx
    have hne : x ≠ e := hxne
    have := C.vis_total_same_replica (hsup x hxU).choose_spec.choose_spec.1
      (hsup x hxU).choose_spec.choose_spec.2
      (hsup e heU).choose_spec.choose_spec.1
      (hsup e heU).choose_spec.choose_spec.2 hne hrep
    have hv : C.vis x e := by
      rcases this with h | h
      · exact h
      · exact absurd h (hcmax x hxU hne)
    exact (hmB x).mpr ⟨Or.inr (Relation.TransGen.single hv), hne⟩
  -- Cellwise.
  refine St.ext (fun i j => ?_) (fun i => ?_)
  · show max (A.R i j) ((step B e).R i j) = (step A e).R i j
    rw [step_R, step_R, hRA i j, hRB i j]
    have hle : ∑ x ∈ tB, contribR i j x ≤ ∑ x ∈ tA, contribR i j x :=
      Finset.sum_le_sum_of_subset hsub
    by_cases hc : contribR i j e = 0
    · rw [hc]; omega
    · have heq : ∑ x ∈ tB, contribR i j x = ∑ x ∈ tA, contribR i j x := by
        refine Finset.sum_subset hsub (fun x hx hxn => ?_)
        by_contra hnz
        exact hxn (key x hx ((contribR_rep hnz).symm.trans (contribR_rep hc)))
      rw [heq]; omega
  · show max (A.U i) ((step B e).U i) = (step A e).U i
    rw [step_U, step_U, hUA i, hUB i]
    have hle : ∑ x ∈ tB, contribU i x ≤ ∑ x ∈ tA, contribU i x :=
      Finset.sum_le_sum_of_subset hsub
    by_cases hc : contribU i e = 0
    · rw [hc]; omega
    · have heq : ∑ x ∈ tB, contribU i x = ∑ x ∈ tA, contribU i x := by
        refine Finset.sum_subset hsub (fun x hx hxn => ?_)
        by_contra hnz
        exact hxn (key x hx ((contribU_rep hnz).symm.trans (contribU_rep hc)))
      rw [heq]; omega

/-! ### VC3 and VC5

Merge ignores its first argument, so it is the componentwise maximum, a join
semilattice. Both conditions are then instances of associativity,
commutativity and idempotence, and neither needs a hypothesis. -/

/-- **VC3** LOCAL-REDISTRIBUTE, with no side conditions at all. -/
theorem vc3_unconditional (l m x y d : (D n K).Sigma) :
    (D n K).merge l ((D n K).merge m x d) y
      = (D n K).merge m ((D n K).merge l x y) d := by
  simp only [merge_eq, mergeState]
  exact St.ext (fun i j => by dsimp only; omega) (fun i => by dsimp only; omega)

/-- **VC5** REDISTRIBUTE, likewise. -/
theorem vc5_unconditional (m x₀ x₁ x₂ d : (D n K).Sigma) :
    (D n K).merge ((D n K).merge m x₀ d) ((D n K).merge m x₁ d)
        ((D n K).merge m x₂ d)
      = (D n K).merge m ((D n K).merge x₀ x₁ x₂) d := by
  simp only [merge_eq, mergeState]
  exact St.ext (fun i j => by dsimp only; omega) (fun i => by dsimp only; omega)

/-! ## The bundle -/

/-- `rc` relates no pair of operations. -/
theorem no_rc_before (o₁ o₂ : type.OType) : ¬ (D n K).RcBefore o₁ o₂ := by
  simp [Impl.RcBefore, D, rcOf]

/-- **RC-NON-COMM without the guards.** Both sides are false. -/
theorem uniform_rc_non_comm : UniformRcNonComm (D n K) := by
  intro e₁ e₂
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

/-- **COND-COMM without the guards.** Vacuous: there is no `rc` edge. -/
theorem uniform_cond_comm : UniformCondComm (D n K) :=
  fun _ e e' _ _ hrc _ => absurd hrc (no_rc_edge e e')

/-- **VC1 to VC5 at the full causal past.** -/
theorem causalJoinLaws : CausalJoinLawsOn (D n K) (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun _ _ s _ _ _ => vc2_merge_init s
  vc3_local_redistribute := fun _ _ _ l m x y _ => by
    intros; exact vc3_unconditional l m x y _
  vc4_causal_delta := fun C U A B e _ hvs hsup hcl heU _ hcmax hA hB =>
    vc4_causal_delta C U A B e hvs hsup hcl heU hcmax hA hB
  vc5_redistribute := fun _ _ _ x₀ x₁ x₂ m _ => by
    intros; exact vc5_unconditional m x₀ x₁ x₂ _

/-- **The obligation bundle at the full causal past.** The enumeration
obligation is discharged by `causalEnumerable_of_no_rc`, since this row's
`rc` is empty, so `lo^C_E` is a subrelation of `vis` and a topological sort
of `vis` respects both. -/
theorem causalObligations : CausalObligations (D n K) where
  laws := laws
  equal_op_commutes :=
    EqualOpCommutes.of_concurrent laws.no_rc_chain uniform_rc_non_comm.toConcurrent
  same_rep_cond_comm := uniform_cond_comm.toSameReplica
  joinLaws := causalJoinLaws
  enumerable := causalEnumerable_of_no_rc no_rc_before
  executionOrder := ⟨ExecutionOrder.ofUniform uniform_rc_non_comm⟩

/-- **The join lemma for this row.** Merging the canonical states of two
admissible event sets gives the canonical state of their union, which is
what drives clause 1 of Definition 4. The statement is the one Part II's
rows reach as well, so from here the two routes are the same development.

Definition 4 itself needs one further premise, the sequential one, and this
row carries no `Spec` yet. `Negative.lean` says what the obstacles to
writing one are. -/
theorem joinLemma : PaperJoinOn (D n K) (fun _ => True) :=
  Metatheory.causalJoinLemma causalObligations

#print axioms causalObligations
#print axioms joinLemma

/-! ## The sequential premise

`AnyOrderSound` is false for this row, and not for a subtle reason: `value`
sums the diagonal over `range n` only, so an increment issued by a replica
outside that range is invisible to the query while a sequential history
counts it. Only issuance rules those out, so the premise this row supplies
is the execution-scoped one.
-/

/-- What issuance guarantees about an event, as the value query needs it:
the issuer is one of the `n` replicas, and a transfer does not name its own
issuer. The second is why a transfer leaves the value alone, since a
self-transfer would land on the diagonal. -/
def WellIssued (n : Nat) (e : Op AppOp) : Prop :=
  e.rep < n ∧ ∀ a t, e.op = AppOp.transfer a t → t ≠ e.rep

theorem wellIssued_of_canIssue {e : Op AppOp} {s : St}
    (h : (issuance n K).CanIssue e s) : WellIssued n e := by
  obtain ⟨hrep, hop⟩ := h
  refine ⟨hrep, fun a t ht => ?_⟩
  rw [ht] at hop
  exact hop.2.1

/-- **One event moves the value by exactly its specification delta.** The
three cases are the three reasons the cells are arranged as they are. -/
theorem contrib_sum {x : Op AppOp} (hw : WellIssued n x) :
    (∑ r ∈ Finset.range n, ((contribR r r x : Nat) : Int))
        - (∑ r ∈ Finset.range n, ((contribU r x : Nat) : Int))
      = specDelta x.op := by
  obtain ⟨hrep, htr⟩ := hw
  have hmem : x.rep ∈ Finset.range n := Finset.mem_range.mpr hrep
  rcases hop : x.op with a | a | ⟨a, t⟩ <;>
    simp only [contribR, contribU, specDelta, hop, and_self]
  · push_cast
    rw [Finset.sum_ite_eq' (Finset.range n) x.rep (fun _ => (a : Int))]
    simp [hmem]
  · push_cast
    rw [Finset.sum_ite_eq' (Finset.range n) x.rep (fun _ => (a : Int))]
    simp [hmem]
  · have hne : t ≠ x.rep := htr a t hop
    have hfalse : ∀ r : Nat, ¬ (r = x.rep ∧ r = t) := by
      rintro r ⟨rfl, rfl⟩
      exact hne rfl
    simp [hfalse]

theorem value_step (s : St) (e : Op AppOp) (hw : WellIssued n e) :
    value n K (step s e) = value n K s + specDelta e.op := by
  simp only [value, step_R, step_U]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [contrib_sum (n := n) hw]

/-- **The value of a replay is the specification's fold.** -/
theorem value_fold (s : St) (π : List (Op AppOp))
    (hw : ∀ x ∈ π, WellIssued n x) :
    value n K (π.foldl step s)
      = value n K s + (π.map (fun x => specDelta x.op)).sum := by
  induction π generalizing s with
  | nil => simp
  | cons e rest ih =>
    rw [List.foldl_cons, ih _ (fun x hx => hw x (List.mem_cons_of_mem _ hx)),
      value_step s e (hw e (List.mem_cons_self ..)), List.map_cons, List.sum_cons]
    ring

/-- The specification's own fold, as a run of the machine. -/
theorem spec_update_run (K : Int) (z : Int) (π : List (Op AppOp)) :
    Runs (specMachine K).transition z
      (projectedUpdates (D := (D n K).toMRDTSig) π)
      (z + (π.map (fun x => specDelta x.op)).sum) := by
  induction π generalizing z with
  | nil => simpa using Runs.nil (step := (specMachine K).transition) z
  | cons e rest ih =>
    refine Runs.cons (l := SeqLabel.update e.op) rfl ?_
    have := ih (z + specDelta e.op)
    simp only [List.map_cons, List.sum_cons]
    rw [show z + (specDelta e.op + (rest.map (fun x => specDelta x.op)).sum)
        = z + specDelta e.op + (rest.map (fun x => specDelta x.op)).sum from by ring]
    exact this

/-- **`Spec` admits the history this row produces**, for every query. The
value query is answered exactly; the rights query is admitted whatever the
implementation answers, which is what leaving it unconstrained means. -/
theorem spec_admits (π : List (Op AppOp)) (hw : ∀ x ∈ π, WellIssued n x)
    (q : type.QType) :
    (historySpec K).admits (projectedUpdates (D := (D n K).toMRDTSig) π ++
      [.query q ((D n K).query ((D n K).applyList (D n K).sigma0 π) q)]) := by
  have hval : value n K (π.foldl step initial)
      = K + (0 + (π.map (fun x => specDelta x.op)).sum) := by
    rw [value_fold (n := n) (K := K) initial π hw]
    simp [value, initial]
  set z : Int := 0 + (π.map (fun x => specDelta x.op)).sum with hz
  refine ⟨z, Runs.append (spec_update_run K 0 π)
    (Runs.cons (m := z) ?_ (Runs.nil z))⟩
  refine ⟨rfl, ?_⟩
  cases q with
  | value => exact hval
  | localRights r => trivial

/-- **The execution-scoped sequential premise.** The chosen history is the
events in timestamp order. That respects `vis`, because a configuration's
`causal_mono` makes every `vis` edge increase the timestamp, and it respects
`lo^C_E`, because this row's `rc` is empty so `lo^C_E` is a subrelation of
`vis`. -/
theorem chosenOrderSound :
    Soundness.ChosenOrderSound (D n K) (historySpec K) (issuance n K) := by
  rintro C hhon E hsup hcl ⟨π₀, hp₀⟩ q
  obtain ⟨π, hperm, hr⟩ := exists_respecting_perm
    (R := fun a b : Op AppOp => a.1 < b.1)
    (fun hab hbc => Nat.lt_trans hab hbc) (fun a => Nat.lt_irrefl a.1) π₀
  have hpE : listPermOf π E :=
    ⟨hperm.nodup hp₀.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp₀.2 a)⟩
  have hvis : respects π (fun a b : Op AppOp => C.replayContext.vis a b) :=
    hr.imp (fun {_ _} hno hv => hno (C.causal_mono hv))
  refine ⟨π, hpE, hvis.imp (fun {_ _} hno hedge =>
    hno (paperOrder_sub_vis no_rc_before hedge)), ?_⟩
  refine spec_admits π (fun x hx => ?_) q
  obtain ⟨ρ, -, -, hcan⟩ := hhon x (hsup x ((hpE.2 x).mp hx))
  exact wellIssued_of_canIssue hcan

/-! ## Part IV: the event alphabet, where `localRights` is specified

`Definition.lean` gives a second specification whose alphabet is the whole
event, timestamp and replica included. Everything below connects the
implementation's `localRights` to that specification's `balance`, which is
the step the projected reading cannot take: `projectedUpdates` keeps only
`e.op`, and a transfer records its target but not its issuer.

The escrow reading makes the connection cell by cell. `rights_delta` says
one event moves the issuer's and the target's rights by exactly the
specification's credit and debit, `accounts_agree` lifts that to a whole
replay, and `affordable_prefix` discharges the specification's funding side
condition at every prefix of the chosen history.
-/

theorem validIssuer_of_canIssue {e : Op AppOp} {s : St}
    (h : (issuance n K).CanIssue e s) : ValidIssuer n e := by
  obtain ⟨hrep, hop⟩ := h
  refine ⟨hrep, fun a t ht => ?_⟩
  rw [ht] at hop
  exact ⟨hop.1, hop.2.1⟩

theorem wellIssued_of_validIssuer {e : Op AppOp} (h : ValidIssuer n e) :
    WellIssued n e :=
  ⟨h.1, fun a t ht => (h.2 a t ht).2⟩

theorem rights_delta (e : Op AppOp) (r : Nat) (hv : ValidIssuer n e) :
    (contribR r r e : Int)
        + (∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int))
        - (∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int))
        - (contribU r e : Int)
      = credit r e - debit r e := by
  obtain ⟨hrep, htr⟩ := hv
  rcases hop : e.op with a | a | ⟨a, t⟩
  · -- increment: only the diagonal cell moves, and the sums skip it
    have h₁ : ∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        have hjr := (Finset.mem_erase.mp hj).1
        simp only [contribR, hop]
        by_cases hc : j = e.rep ∧ r = e.rep
        · exact absurd (hc.1.trans hc.2.symm) hjr
        · simp [hc])
    have h₂ : ∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        have hjr := (Finset.mem_erase.mp hj).1
        simp only [contribR, hop]
        by_cases hc : r = e.rep ∧ j = e.rep
        · exact absurd (hc.2.trans hc.1.symm) hjr
        · simp [hc])
    rw [h₁, h₂]
    simp only [contribR, contribU, credit, debit, hop, and_self]
    split_ifs <;> simp
  · -- decrement: only the consumption vector moves
    have h₁ : ∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by simp [contribR, hop])
    have h₂ : ∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by simp [contribR, hop])
    rw [h₁, h₂]
    simp only [contribR, contribU, credit, debit, hop]
    split_ifs <;> simp
  · -- transfer: the off-diagonal cell moves, and it is in range both ways
    obtain ⟨htn, htne⟩ := htr a t hop
    have hdiag : (contribR r r e : Int) = 0 := by
      simp only [contribR, hop]
      by_cases hc : r = e.rep ∧ r = t
      · exact absurd (hc.1.symm.trans hc.2) (Ne.symm htne)
      · simp [hc]
    have hU : (contribU r e : Int) = 0 := by simp [contribU, hop]
    by_cases hrt : r = t
    · have hrp : r ≠ e.rep := by rw [hrt]; exact htne
      have hmem : e.rep ∈ (Finset.range n).erase r :=
        Finset.mem_erase.mpr ⟨fun h => hrp h.symm, Finset.mem_range.mpr hrep⟩
      have h₁ : ∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int) = (a : Int) := by
        rw [Finset.sum_eq_single_of_mem e.rep hmem (fun b _ hb => by
          simp only [contribR, hop]
          by_cases hc : b = e.rep ∧ r = t
          · exact absurd hc.1 hb
          · simp [hc])]
        simp [contribR, hop, hrt]
      have h₂ : ∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int) = 0 :=
        Finset.sum_eq_zero (fun j _ => by
          simp only [contribR, hop]
          by_cases hc : r = e.rep ∧ j = t
          · exact absurd hc.1 hrp
          · simp [hc])
      rw [hdiag, hU, h₁, h₂]
      simp [credit, debit, hop, hrt, hrp, htne, htne.symm]
    · by_cases hrp : r = e.rep
      · have hmem : t ∈ (Finset.range n).erase r :=
          Finset.mem_erase.mpr ⟨fun h => hrt h.symm, Finset.mem_range.mpr htn⟩
        have h₁ : ∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int) = 0 :=
          Finset.sum_eq_zero (fun j _ => by
            simp only [contribR, hop]
            by_cases hc : j = e.rep ∧ r = t
            · exact absurd hc.2 hrt
            · simp [hc])
        have h₂ : ∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int) = (a : Int) := by
          rw [Finset.sum_eq_single_of_mem t hmem (fun b _ hb => by
            simp only [contribR, hop]
            by_cases hc : r = e.rep ∧ b = t
            · exact absurd hc.2 hb
            · simp [hc])]
          simp [contribR, hop, hrp]
        rw [hdiag, hU, h₁, h₂]
        simp [credit, debit, hop, hrt, hrp, htne, htne.symm]
      · have h₁ : ∑ j ∈ (Finset.range n).erase r, (contribR j r e : Int) = 0 :=
          Finset.sum_eq_zero (fun j _ => by
            simp only [contribR, hop]
            by_cases hc : j = e.rep ∧ r = t
            · exact absurd hc.2 hrt
            · simp [hc])
        have h₂ : ∑ j ∈ (Finset.range n).erase r, (contribR r j e : Int) = 0 :=
          Finset.sum_eq_zero (fun j _ => by
            simp only [contribR, hop]
            by_cases hc : r = e.rep ∧ j = t
            · exact absurd hc.1 hrp
            · simp [hc])
        rw [hdiag, hU, h₁, h₂]
        simp [credit, debit, hop, hrt, hrp, htne, htne.symm]

theorem localRights_initial (r : Nat) : localRights n initial r = 0 := by
  simp [localRights, initial]

theorem localRights_step (s : St) (e : Op AppOp) (r : Nat) (hv : ValidIssuer n e) :
    localRights n (step s e) r = localRights n s r + credit r e - debit r e := by
  have hR : ∀ i j, (((step s e).R i j : Nat) : Int)
      = ((s.R i j : Nat) : Int) + ((contribR i j e : Nat) : Int) := by
    intro i j; rw [step_R]; push_cast; ring
  have hU : ∀ i, (((step s e).U i : Nat) : Int)
      = ((s.U i : Nat) : Int) + ((contribU i e : Nat) : Int) := by
    intro i; rw [step_U]; push_cast; ring
  simp only [localRights, hR, hU, Finset.sum_add_distrib]
  linarith [rights_delta (n := n) e r hv]

/-- **The two states agree at every prefix of a replay.** The
specification's `value` is the implementation's `value` and its `balance` is
the implementation's `localRights`, cell for cell. -/
theorem accounts_agree (π : List (Op AppOp)) (hv : ∀ x ∈ π, ValidIssuer n x)
    (s : Accounts) (σ : St) (hval : s.value = value n K σ)
    (hbal : ∀ r, s.balance r = localRights n σ r) :
    (π.foldl accountStep s).value = value n K (π.foldl step σ) ∧
      ∀ r, (π.foldl accountStep s).balance r = localRights n (π.foldl step σ) r := by
  induction π generalizing s σ with
  | nil => exact ⟨hval, hbal⟩
  | cons e rest ih =>
    have hve : ValidIssuer n e := hv e (List.mem_cons_self ..)
    refine ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) _ _ ?_ ?_
    · show s.value + specDelta e.op = value n K (step σ e)
      rw [value_step (n := n) (K := K) σ e (wellIssued_of_validIssuer hve), hval]
    · intro r
      show s.balance r + credit r e - debit r e = localRights n (step σ e) r
      rw [localRights_step (n := n) σ e r hve, hbal r]

theorem credit_nonneg (r : Nat) (e : Op AppOp) : 0 ≤ credit r e := by
  unfold credit
  split
  all_goals try split_ifs
  all_goals positivity

theorem debit_eq_zero (r : Nat) (e : Op AppOp) (h : r ≠ e.rep) : debit r e = 0 := by
  unfold debit; split <;> simp [h]

theorem localRights_list (σ : St) (π : List (Op AppOp))
    (hv : ∀ x ∈ π, ValidIssuer n x) (r : Nat) :
    localRights n (π.foldl step σ) r
      = localRights n σ r + (π.map (fun x => credit r x - debit r x)).sum := by
  induction π generalizing σ with
  | nil => simp
  | cons e rest ih =>
    rw [List.foldl_cons, ih _ (fun x hx => hv x (List.mem_cons_of_mem _ hx)),
      localRights_step (n := n) σ e r (hv e (List.mem_cons_self ..)),
      List.map_cons, List.sum_cons]
    ring

/-- The rights of `r` as a sum over the event set. -/
theorem localRights_sum (π : List (Op AppOp)) (hnd : π.Nodup)
    (hv : ∀ x ∈ π, ValidIssuer n x) (r : Nat) :
    localRights n (π.foldl step initial) r
      = ∑ x ∈ π.toFinset, (credit r x - debit r x) := by
  classical
  rw [List.sum_toFinset _ hnd, localRights_list (n := n) initial π hv r,
    localRights_initial (n := n) r, zero_add]

/-- **Adding events issued by other replicas never lowers `r`'s rights.**
Only an issuer spends, so every foreign event contributes a credit or
nothing at all. -/
theorem rights_mono {F G : Finset (Op AppOp)} (r : Nat) (hsub : F ⊆ G)
    (hother : ∀ x ∈ G, x ∉ F → x.rep ≠ r) :
    ∑ x ∈ F, (credit r x - debit r x) ≤ ∑ x ∈ G, (credit r x - debit r x) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx hxn => ?_)
  rw [debit_eq_zero r x (Ne.symm (hother x hx hxn))]
  simpa using credit_nonneg r x

/-! ### The issuer can always pay at the chosen history

The chosen history is timestamp-ordered, so the prefix before `e` contains
`e`'s whole causal past, which is the state `CanIssue` spoke about, plus
events concurrent with `e`. No concurrent event in that prefix is issued by
`e`'s replica, because same-replica events are `vis`-comparable and the
timestamps rule out the other direction. By `rights_mono` those events can
only have raised `e`'s replica's balance. -/

theorem affordable_prefix
    {C : Configuration (D n K).toMRDTSig}
    (hhon : MintHonest (D n K).toMRDTSig (issuance n K).CanIssue C)
    {E : Set (Op AppOp)} (hsup : ∀ x ∈ E, x ∈ C.events)
    (hcl : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {π : List (Op AppOp)} (hpE : listPermOf π E)
    (hsorted : respects π (fun a b : Op AppOp => a.1 < b.1))
    {pre rest : List (Op AppOp)} {e : Op AppOp} (hsplit : pre ++ e :: rest = π) :
    Affordable (pre.foldl accountStep (initialAccounts K)) e := by
  classical
  subst hsplit
  obtain ⟨hpre, htail, hcross⟩ := List.pairwise_append.mp hsorted
  have hndπ := hpE.1
  obtain ⟨hndpre, hndtail, hdisj⟩ := List.nodup_append.mp hndπ
  have hmemπ : ∀ x, x ∈ pre ++ e :: rest ↔ x ∈ E := hpE.2
  have heE : e ∈ E := (hmemπ e).mp (by simp)
  -- every observed event is validly issued
  have hvalid : ∀ x, x ∈ E → ValidIssuer n x := by
    intro x hx
    obtain ⟨σ, -, -, hc⟩ := hhon x (hsup x hx)
    exact validIssuer_of_canIssue hc
  have hvpre : ∀ x ∈ pre, ValidIssuer n x :=
    fun x hx => hvalid x ((hmemπ x).mp (List.mem_append_left _ hx))
  -- the specification's balance is the implementation's local rights
  have hbal : ∀ r, (pre.foldl accountStep (initialAccounts K)).balance r
      = localRights n (pre.foldl step initial) r :=
    (accounts_agree (n := n) (K := K) pre hvpre (initialAccounts K) initial
      (by simp [initialAccounts, value, initial])
      (fun r => by simp [initialAccounts, localRights_initial (n := n) r])).2
  -- the causal past, as `CanIssue` saw it
  obtain ⟨ρ, hρ, -, hcan⟩ := hhon e (hsup e heE)
  have hvρ : ∀ x ∈ ρ, ValidIssuer n x :=
    fun x hx => hvalid x (hcl x e ((hρ.2 x).mp hx).2 heE)
  -- the causal past sits inside the prefix
  have hsub : ρ.toFinset ⊆ pre.toFinset := by
    intro x hx
    have hxρ : x ∈ ρ := List.mem_toFinset.mp hx
    have hvxe : C.vis x e := ((hρ.2 x).mp hxρ).2
    have htime : x.1 < e.1 := C.causal_mono hvxe
    have hxπ : x ∈ pre ++ e :: rest := (hmemπ x).mpr (hcl x e hvxe heE)
    refine List.mem_toFinset.mpr ?_
    rcases List.mem_append.mp hxπ with h | h
    · exact h
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd htime (Nat.lt_irrefl _)
      · exact absurd htime ((List.pairwise_cons.mp htail).1 x h)
  -- every event of the prefix outside it belongs to another replica
  have hother : ∀ x ∈ pre.toFinset, x ∉ ρ.toFinset → x.rep ≠ e.rep := by
    intro x hx hxn hrep
    have hxpre : x ∈ pre := List.mem_toFinset.mp hx
    have hxE : x ∈ E := (hmemπ x).mp (List.mem_append_left _ hxpre)
    have hxne : x ≠ e := hdisj x hxpre e (List.mem_cons_self ..)
    have hnvis : ¬ C.vis x e := by
      intro hv
      exact hxn (List.mem_toFinset.mpr ((hρ.2 x).mpr ⟨hsup x hxE, hv⟩))
    obtain ⟨rx, sx, hLx, hmx⟩ := hsup x hxE
    obtain ⟨re, se, hLe, hme⟩ := hsup e heE
    rcases C.vis_total_same_replica hLx hmx hLe hme hxne hrep with h | h
    · exact hnvis h
    · exact hcross x hxpre e (List.mem_cons_self ..) (C.causal_mono h)
  -- so the prefix affords whatever the causal past afforded
  have hmono : localRights n (ρ.foldl step initial) e.rep
      ≤ localRights n (pre.foldl step initial) e.rep := by
    rw [localRights_sum (n := n) ρ hρ.1 hvρ e.rep,
      localRights_sum (n := n) pre hndpre hvpre e.rep]
    exact rights_mono e.rep hsub hother
  intro a hop
  rw [hbal e.rep]
  refine le_trans ?_ hmono
  obtain ⟨-, hguard⟩ := hcan
  rcases hop with h | ⟨t, h⟩ <;> rw [h] at hguard
  · exact hguard
  · exact hguard.2.2

/-! ### The run -/

theorem event_run
    {C : Configuration (D n K).toMRDTSig}
    (hhon : MintHonest (D n K).toMRDTSig (issuance n K).CanIssue C)
    {E : Set (Op AppOp)} (hsup : ∀ x ∈ E, x ∈ C.events)
    (hcl : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {π : List (Op AppOp)} (hpE : listPermOf π E)
    (hsorted : respects π (fun a b : Op AppOp => a.1 < b.1)) :
    ∀ pre suf, pre ++ suf = π →
      Runs (eventMachine n K).transition
        (pre.foldl accountStep (initialAccounts K))
        (projectedLabels (D := (D n K).toMRDTSig) id suf)
        (π.foldl accountStep (initialAccounts K)) := by
  intro pre suf
  induction suf generalizing pre with
  | nil =>
    intro h
    rw [List.append_nil] at h
    subst h
    exact Runs.nil _
  | cons e rest ih =>
    intro h
    have heπ : e ∈ π := h ▸ List.mem_append_right pre (List.mem_cons_self ..)
    have hvalid : ValidIssuer n e := by
      obtain ⟨σ, -, -, hc⟩ := hhon e (hsup e ((hpE.2 e).mp heπ))
      exact validIssuer_of_canIssue hc
    refine Runs.cons (m := accountStep (pre.foldl accountStep (initialAccounts K)) e)
      ⟨rfl, hvalid, affordable_prefix hhon hsup hcl hpE hsorted h⟩ ?_
    have hnext := ih (pre ++ [e]) (by rw [List.append_assoc]; exact h)
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hnext

/-- **The execution-scoped sequential premise at the event alphabet.** The
chosen history is the same timestamp-ordered one, and both queries are now
answered exactly. -/
theorem eventChosenOrderSound :
    EventIssuedHistoryAdequacy (D n K).toMRDTSig (policy (D n K))
      (eventSpec n K) (issuance n K) := by
  rintro C hhon E hsup hcl ⟨π₀, hp₀⟩ q
  obtain ⟨π, hperm, hr⟩ := exists_respecting_perm
    (R := fun a b : Op AppOp => a.1 < b.1)
    (fun hab hbc => Nat.lt_trans hab hbc) (fun a => Nat.lt_irrefl a.1) π₀
  have hpE : listPermOf π E :=
    ⟨hperm.nodup hp₀.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp₀.2 a)⟩
  have hvis : respects π (fun a b : Op AppOp => C.replayContext.vis a b) :=
    hr.imp (fun {_ _} hno hv => hno (C.causal_mono hv))
  have hvalid : ∀ x ∈ π, ValidIssuer n x := by
    intro x hx
    obtain ⟨σ, -, -, hc⟩ := hhon x (hsup x ((hpE.2 x).mp hx))
    exact validIssuer_of_canIssue hc
  have hagree := accounts_agree (n := n) (K := K) π hvalid
    (initialAccounts K) initial (by simp [initialAccounts, value, initial])
    (fun r => by simp [initialAccounts, localRights_initial (n := n) r])
  refine ⟨π, hpE,
    hvis.imp (fun {_ _} hno hedge => hno (paperOrder_sub_vis no_rc_before hedge)),
    hvis.imp (fun {_ _} hno hedge => hno hedge.1), ?_⟩
  refine ⟨π.foldl accountStep (initialAccounts K),
    Runs.append (event_run hhon hsup hcl hpE hr [] π rfl)
      (Runs.cons (m := π.foldl accountStep (initialAccounts K))
        ⟨rfl, ?_⟩ (Runs.nil _))⟩
  cases q with
  | value => exact hagree.1.symm
  | localRights r => exact (hagree.2 r).symm

/-! # Specification visibility, without SPEC-NON-COMM

This row is the cheapest of the ported ones, because `chosenOrderSound`
already builds its witness as a `vis`-respecting permutation and says so:
`exists_respecting_perm` on the timestamp order, then `causal_mono`. Every
specification-visibility arrow runs along `vis`, so the new clause is the
same `hvis` read once more.

Whether SPEC-NON-COMM holds here is not settled either way in the tree. It
is not needed: the clause below does not go through it. -/

/-- **The scoped premise with specification visibility.** The same witness
as `chosenOrderSound`, the timestamp order, with the extra clause. -/
theorem specChosenOrderSound :
    NoSpecNonComm.Soundness.SpecChosenOrderSound (D n K) (historySpec K)
      (issuance n K) := by
  rintro C hhon _ E hsup hcl ⟨π₀, hp₀⟩ q
  obtain ⟨π, hperm, hr⟩ := exists_respecting_perm
    (R := fun a b : Op AppOp => a.1 < b.1)
    (fun hab hbc => Nat.lt_trans hab hbc) (fun a => Nat.lt_irrefl a.1) π₀
  have hpE : listPermOf π E :=
    ⟨hperm.nodup hp₀.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp₀.2 a)⟩
  have hvis : respects π (fun a b : Op AppOp => C.replayContext.vis a b) :=
    hr.imp (fun {_ _} hno hv => hno (C.causal_mono hv))
  refine ⟨π, hpE, hvis.imp (fun {_ _} hno hedge =>
      hno (paperOrder_sub_vis no_rc_before hedge)),
    hvis.imp (fun {_ _} hno hs => hno hs.1), ?_⟩
  refine spec_admits π (fun x hx => ?_) q
  obtain ⟨ρ, -, -, hcan⟩ := hhon x (hsup x ((hpE.2 x).mp hx))
  exact wellIssued_of_canIssue hcan

end LeanProofs.NoSpecNonComm.Implementations.BoundedCounter
