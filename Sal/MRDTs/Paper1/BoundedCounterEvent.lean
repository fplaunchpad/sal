import Sal.MRDTs.Paper1.SimpleEventPorts
import Sal.MRDTs.Instances.BoundedCounter

/-! The independent bounded-counter history language stores account balances,
not increment/decrement components. Every update must leave every account
nonnegative. Honest causal serialization supplies this guard; arbitrary
reordering is deliberately not assumed to preserve legality. -/
namespace Sal.MRDTs.Paper1.BoundedCounterEvent
open Foundation
open Instances.BoundedCounter
open SimpleEventPorts

abbrev Event := Op BCOp
abbrev Balance := Nat → Int

def step (balance : Balance) (e : Event) : Balance := fun r => match e.op with
  | .inc => balance r + if r = e.2.1 then 1 else 0
  | .dec => balance r - if r = e.2.1 then 1 else 0

def machine : HistoryMachine Event Nat Int where
  State := Balance
  initial := fun _ => 0
  transition balance label next := match label with
    | .update e => next = step balance e ∧ ∀ r, 0 ≤ next r
    | .query r answer => next = balance ∧ answer = balance r

def spec := machine.toSpec

def run (ops : List Event) : Balance := ops.foldl step (fun _ => 0)

theorem run_refines (ops : List Event) (r : Nat) :
    run ops r = (applySeq BC.toUpdateSig BC.init ops).1 r -
      (applySeq BC.toUpdateSig BC.init ops).2 r := by
  exact sequential_run ops r

private theorem run_append (pre : List Event) (e : Event) :
    run (pre ++ [e]) = step (run pre) e := by simp [run, List.foldl_append]

private theorem guarded_run_aux (ops : List Event)
    (safe : ∀ pre suf, ops = pre ++ suf → ∀ r, 0 ≤ run pre r)
    (pre rest : List Event) (split : ops = pre ++ rest) :
    Runs machine.transition (run pre)
      (rest.map (fun e => SeqLabel.update e)) (run ops) := by
  induction rest generalizing pre with
  | nil => subst ops; simpa using Runs.nil (step := machine.transition) (run pre)
  | cons e rest ih =>
      have split' : ops = (pre ++ [e]) ++ rest := by simpa [List.append_assoc] using split
      refine .cons (m := run (pre ++ [e])) ?_ (ih _ split')
      exact ⟨run_append pre e, safe _ _ split'⟩

/-- The abstract guard follows from each concrete prefix's issued safety;
the language itself refers only to mathematical account balances. -/
theorem accepted_of_prefix_safety (ops : List Event) (legal : SequentialHonest ops) (q : Nat) :
    spec.admits ((ops.map SeqLabel.update) ++ [.query q (run ops q)]) := by
  have hs : ∀ pre suf, ops = pre ++ suf → ∀ r, 0 ≤ run pre r := by
    intro pre suf split r
    rw [run_refines]
    have hp := legal pre suf split r
    omega
  exact ⟨run ops, (guarded_run_aux ops hs [] ops rfl).append
    (.cons ⟨rfl,rfl⟩ (.nil _))⟩

abbrev policy := emptyPolicy BCOp
abbrev laws : RestrictedLaws BC.toUpdateSig policy := emptyLaws BC_all_comm

theorem join : @Join BC policy.lift := by
  simpa [policy, emptyPolicy, OperationPolicy.lift, ReplayPolicy.default,
    ReplayPolicy.unconstrained] using
    JoinProof.ofArbitraryStateLaws BC_mergeLaws BC_deltaLaws
      (causalDeltaLaw_of_all_comm BC_mergeLaws BC_commutingPeelLaw BC_all_comm)

/-- Every allocated version has a legal full-input history preserving all
visibility edges. Mint provenance and issuer guards remain explicit. -/
theorem certifiedV : EventCertifiedSpecificationRAV BC policy spec generation := by
  letI : ReplayPolicy BC.toUpdateSig := policy.lift
  intro C reach
  have hG := canonicalConfig_of_mintCertifiedV (fun _ _ => join _) reach
  have hCC := causalCanonical_of_all_comm_rc_either BC_all_comm
    (fun _ _ => by
      change (policy.lift (D := BC.toUpdateSig)).order _ _ = RcRes.Either
      simp [policy, emptyPolicy, OperationPolicy.lift]) hG
  intro v s E hv q
  obtain ⟨ops,hperm,hvis,_,hfold⟩ := hCC v s E hv
  have honest : HonestAppOn BC bcApplicable C := by
    intro e he
    obtain ⟨past,hp,hr,hguard⟩ := reach.mintHonest e he
    exact ⟨applySeq BC.toUpdateSig BC.init past, ⟨past,hp,hr,rfl⟩, hguard⟩
  have legal : SequentialHonest ops :=
    prefix_inv_of_causal_witness bc_inv_init bc_safetyStep hG
      honest hv hperm hvis
  refine ⟨ops,hperm,?_,?_,?_⟩
  · apply List.pairwise_of_forall
    intro a b
    intro h
    rcases h with h | h
    · exact h.2 (BC_all_comm b a)
    · exact h.2.2.1
  · exact hvis.imp (fun {_ _} h hspec => h hspec.1)
  · have accepted := accepted_of_prefix_safety ops legal q
    have hanswer : run ops q = BC.query s q := by
      rw [run_refines, hfold]
      rfl
    simpa only [projectedLabels, List.map_id_fun, hanswer] using accepted

theorem certified : EventCertifiedSpecificationRA BC policy spec generation := certifiedV.ordinary

/-- PASS+FAIL: one account cannot consume another account's rights. -/
theorem account_control :
    spec.admits [.update (1,0,.inc), .query 0 1] ∧
    ¬ spec.admits [.update (1,0,.inc), .update (2,1,.dec), .query 1 (-1)] := by
  constructor
  · refine ⟨step (fun _ => 0) (1,0,.inc), .cons ⟨rfl,?_⟩ (.cons ⟨rfl,rfl⟩ (.nil _))⟩
    intro r; simp [step, Op.op, machine]; split <;> omega
  · rintro ⟨final,hr⟩
    cases hr with
    | cons inc rest =>
      cases rest with
      | cons dec rest =>
        have hn := dec.2 1
        rw [dec.1, inc.1] at hn
        change (0 : Int) ≤ -1 at hn
        omega

/-- A decrement without rights is rejected at the update itself. -/
theorem initial_decrement_rejected : ¬ spec.admits [.update (1,0,.dec)] := by
  rintro ⟨final,hr⟩
  cases hr with
  | cons h _ =>
    have hn := h.2 0
    rw [h.1] at hn
    change (0 : Int) ≤ -1 at hn
    omega

/-- Global commutation compatibility fails because legal inc/dec cannot be
swapped at zero. The issued chosen-history route is load-bearing. -/
theorem commutationCompatibility_fails : ¬ CommutationCompatibility BC id spec := by
  intro compatible
  have hc := compatible (1,0,.inc) (2,0,.dec) (BC_all_comm _ _)
  have forward : spec.admits [.update (1,0,.inc), .update (2,0,.dec)] := by
    refine ⟨step (step (fun _ => 0) (1,0,.inc)) (2,0,.dec),
      .cons ⟨rfl,?_⟩ (.cons ⟨rfl,?_⟩ (.nil _))⟩
    · intro r; simp [step, Op.op, machine]; split <;> omega
    · intro r; simp [step, Op.op, machine]
  have reverse := (hc [] []).mp forward
  obtain ⟨final,hr⟩ := reverse
  cases hr with
  | cons h _ =>
    have hn := h.2 0
    rw [h.1] at hn
    change (0 : Int) ≤ -1 at hn
    omega

#print axioms certifiedV
#print axioms commutationCompatibility_fails
end Sal.MRDTs.Paper1.BoundedCounterEvent
