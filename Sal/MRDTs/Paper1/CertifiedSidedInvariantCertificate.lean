import Sal.MRDTs.Paper1.CertifiedSidedInvariantHistory
import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.ExecutionTrace
import Sal.MRDTs.Paper1.CertifiedSidedInvariantReplay

namespace Sal.MRDTs.Paper1.CertifiedSidedInvariantCertificate
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.ProductionRGA

abbrev language (Γ : OrderedPrefixCode) := GuardedHistory.language (sidedClientSpec  Γ)
abbrev invariant (Γ : OrderedPrefixCode) (C : Configuration (S Γ)) :=
  CertifiedSidedInvariant.Valid Γ C.replayContext
abbrev policy := CertifiedSidedInvariantHistory.emptyPolicy

theorem closed (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C) :
    InvariantOrder.Closed (S Γ) C.replayContext (invariant Γ C) :=
  CertifiedSidedInvariant.closed Γ C.replayContext
    (sHonest_core (sHonest_of_mint execution.mintHonest))

theorem stored_valid (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v : Version} {s : SState} {H : Set (Op (SOp))}
    (stored : C.ver v = some (s,H)) : invariant Γ C s :=
  CertifiedSidedInvariant.represented_valid Γ C.replayContext H s
    (CertifiedRGAExecution.Sided.representedVersions Γ execution stored)

theorem versions (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C) :
    InvariantOrder.VersionsRA (S Γ) (invariant Γ C) policy (language Γ) C := by
  intro v s H stored q
  have good := CertifiedRGAExecution.Sided.canonicalConfig Γ execution
  have rep := CertifiedRGAExecution.Sided.representedVersions Γ execution stored
  obtain ⟨ops,perm,ordered,fold⟩ := rep.2.2.2.2
  obtain ⟨can,order,_,spec,admitted⟩ :=
    CertifiedSidedInvariantHistory.canonical_valid_history execution good stored perm ordered fold q
  exact ⟨SidedWitness.canonical ops,can,order,spec,admitted⟩

/-- The recursively synthesized merge base is valid, not merely stored states. -/
theorem virtual_base_valid (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v₁ v₂ : Version} {s₁ s₂ : SState} {H₁ H₂ : Set (Op (SOp))}
    (left : C.ver v₁ = some (s₁,H₁)) (right : C.ver v₂ = some (s₂,H₂)) :
    invariant Γ C (virtualMergeBaseState C v₁ v₂) := by
  have store : StoreInv C.ver C.parents := by
    cases execution with
    | ordinary reach => exact storeInv_reachable reach.toReachable
    | virtual reach => exact storeInv_reachableV reach.toReachable
  have good := CertifiedRGAExecution.Sided.canonicalConfig Γ execution
  have base := CertifiedClosedExecution.virtualMergeBaseState_canonical store good
    (CertifiedRGAExecution.Sided.closedJoinAt Γ C execution.mintHonest) left right
  have rep := CertifiedRGAExecution.Sided.represented_of_canonical Γ C.replayContext
    (sHonest_core (sHonest_of_mint execution.mintHonest))
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl (H₁ ∩ H₂)
    (virtualMergeBaseState C v₁ v₂)
    (fun e he => good.version_events_supported v₁ s₁ H₁ left e he.1)
    (fun a b vis hb => ⟨good.version_events_causal v₁ s₁ H₁ left a b vis hb.1,
      good.version_events_causal v₂ s₂ H₂ right a b vis hb.2⟩) base
  exact CertifiedSidedInvariant.represented_valid Γ C.replayContext _ _ rep

/-- Generic invariant replay convergence for implementation histories. This is
separate from the insert-first sequential history, which may move causal deletes. -/
theorem implementation_replay_equal (Γ : OrderedPrefixCode)
    {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v : Version} {s : SState} {H : Set (Op (SOp))}
    (stored : C.ver v = some (s,H))
    {xs ys : List (Op (SOp))} (px : listPermOf xs H) (py : listPermOf ys H)
    (cx : respects xs C.vis) (cy : respects ys C.vis) :
    applySeq (S Γ).toUpdateSig (S Γ).init xs =
      applySeq (S Γ).toUpdateSig (S Γ).init ys :=
  CertifiedSidedInvariantReplay.replay_equal Γ execution stored px py cx cy

structure Correct (Γ : OrderedPrefixCode) (C : Configuration (S Γ)) : Prop where
  closed : InvariantOrder.Closed (S Γ) C.replayContext (invariant Γ C)
  stored_valid : ∀ v s H, C.ver v = some (s,H) → invariant Γ C s
  replay : ∀ v s H, C.ver v = some (s,H) →
    InvariantReplay.RestrictedLaws (CertifiedSidedInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedSidedInvariantReplay.policy ∧
    InvariantReplay.Canonical (CertifiedSidedInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedSidedInvariantReplay.policy (S Γ).init s
  versions : InvariantOrder.VersionsRA (S Γ) (invariant Γ C) policy (language Γ) C

theorem correct (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C) : Correct Γ C :=
  ⟨closed Γ execution,fun _ _ _ hv => stored_valid Γ execution hv,
    fun _ _ _ hv => ⟨CertifiedSidedInvariantReplay.laws Γ execution hv,
      CertifiedSidedInvariantReplay.storedCanonical Γ execution hv⟩,versions Γ execution⟩

theorem correctV (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (reach : MintCertifiedReachV (S Γ) (canonicalVirtualMergeBase (S Γ))
      (generation Γ) C) : Correct Γ C := correct Γ (.virtual reach)

theorem executions (Γ : OrderedPrefixCode) (trace : List (Label (S Γ) × Configuration (S Γ)))
    (run : (certifiedTS (S Γ) (generation Γ)).Execution (initConfig (S Γ)) trace) :
    Correct Γ (initConfig (S Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach (S Γ) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : OrderedPrefixCode) (trace : List (Label (S Γ) × Configuration (S Γ)))
    (run : (certifiedTSV (S Γ) (generation Γ)).Execution (initConfig (S Γ)) trace) :
    Correct Γ (initConfig (S Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReachV (S Γ) (canonicalVirtualMergeBase (S Γ)) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

#print axioms implementation_replay_equal
#print axioms virtual_base_valid
#print axioms correct
#print axioms correctV
end Sal.MRDTs.Paper1.CertifiedSidedInvariantCertificate
