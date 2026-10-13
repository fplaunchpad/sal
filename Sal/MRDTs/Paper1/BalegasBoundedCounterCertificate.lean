import Sal.MRDTs.Paper1.BalegasBoundedCounterBudget
import Sal.MRDTs.Paper1.BalegasBoundedCounterVC

namespace Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
open Foundation Instances.BalegasBoundedCounter
open Classical

theorem canonicalV {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K)) (generation n K) C) :
    CanonicalConfig C := BalegasBoundedCounterVC.canonicalConfig n K reach

theorem honestV {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K)) (generation n K) C) :
    HonestAppOn (D n K) (fun e s => applicable n s e) C := by
  intro e he
  obtain ⟨past,hp,hc,hg⟩ := reach.mintHonest e he
  exact ⟨applySeq (D n K).toUpdateSig (D n K).init past,⟨past,hp,hc,rfl⟩,hg⟩

abbrev policy := SimpleEventPorts.emptyPolicy Action

theorem certifiedV (n : Nat) (K : Int) :
    EventCertifiedSpecificationRAV (D n K) policy (spec n K) (generation n K) := by
  letI ord : EventOrder (D n K).toUpdateSig := policy.lift
  intro C reach
  have hG : CanonicalConfig C := by
    simpa [ord,policy,SimpleEventPorts.emptyPolicy,OperationPolicy.lift,EventOrder.default,
      EventOrder.unconstrained] using canonicalV reach
  have hCC := causalCanonical_of_all_comm_replayOrder_either (all_comm n K)
    (fun _ _ => by
      change (policy.lift (D := (D n K).toUpdateSig)).order _ _ = OrderResult.Either
      simp [policy,SimpleEventPorts.emptyPolicy,OperationPolicy.lift]) hG
  have honest : HonestAppOn (D n K) (fun e s => applicable n s e) C := by
    intro e he
    obtain ⟨past,hp,hr,hguard⟩ := reach.mintHonest e he
    exact ⟨applySeq (D n K).toUpdateSig (D n K).init past,⟨past,hp,hr,rfl⟩,hguard⟩
  intro v s E hv q
  obtain ⟨ops,hp,hvis,horder,hfold⟩ := hCC v s E hv
  refine ⟨ops,hp,?_,?_,causal_history_accepts hG honest hv hp hvis q⟩
  · apply List.pairwise_of_forall
    intro a b h
    rcases h with h | h
    · exact h.2 (all_comm n K b a)
    · exact h.2.2.1
  · exact hvis.imp (fun {_ _} h hspec => h hspec.1)

theorem certified (n : Nat) (K : Int) :
    EventCertifiedSpecificationRA (D n K) policy (spec n K) (generation n K) :=
  (certifiedV n K).ordinary

theorem versions_safeV {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K)) (generation n K) C) :
    VersionsSatisfy (fun s => (∀ r, 0 ≤ localRights n s r) ∧ K ≤ value n K s ∧
      Conserved n K (project n K s)) C := by
  have hG := canonicalV reach
  have hCC := causalCanonical_of_all_comm_replayOrder_either (all_comm n K) (fun _ _ => rfl) hG
  intro v s E hv
  obtain ⟨ops,hp,hc,_,hf⟩ := hCC v s E hv
  exact causal_history_bounds hG (honestV reach) hv hp hc hf

theorem versions_safe {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReach (D n K) (generation n K) C) :
    VersionsSatisfy (fun s => (∀ r, 0 ≤ localRights n s r) ∧ K ≤ value n K s ∧
      Conserved n K (project n K s)) C := versions_safeV reach.toV

#print axioms certifiedV
#print axioms versions_safeV

end Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
