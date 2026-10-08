import Sal.MRDTs.Paper1.CertifiedRGAInvariantHistory
import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.ExecutionTrace
import Sal.MRDTs.Paper1.CertifiedRGAInvariantReplay
import Sal.MRDTs.Paper1.PaperPresentation

namespace Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate
open Foundation Sal.EmbedRGA
open Instances.EmbedRGA Instances.ProductionRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

abbrev language (Γ : OrderedPrefixCode) := GuardedHistory.language (embedClientSpec (α := α) Γ)
abbrev invariant (Γ : OrderedPrefixCode) (C : Configuration (E Γ α)) :=
  CertifiedRGAInvariant.Valid Γ C.replayContext
abbrev policy := CertifiedRGAInvariantHistory.emptyPolicy (α := α)

theorem closed (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C) :
    InvariantOrder.Closed (E Γ α) C.replayContext (invariant Γ C) :=
  CertifiedRGAInvariant.closed Γ C.replayContext
    (eHonest_core (eHonest_of_mint execution.mintHonest))

theorem stored_valid (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))}
    (stored : C.ver v = some (s,H)) : invariant Γ C s :=
  CertifiedRGAInvariant.represented_valid Γ C.replayContext H s
    (CertifiedRGAExecution.Embedded.representedVersions Γ execution stored)

theorem versions (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C) :
    InvariantOrder.VersionsRA (E Γ α) (invariant Γ C) policy (language Γ) C := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  apply PaperPresentation.invariant_versions_of_exact_histories
  · intro v s H stored e member edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,before,_⟩
    · exact good.vis_irrefl e vis
    · exact before
  intro v s H stored q
  have rep := CertifiedRGAExecution.Embedded.representedVersions Γ execution stored
  obtain ⟨ops,perm,ordered,fold⟩ := rep.2.2.2.2
  obtain ⟨can,order,state,spec,admitted⟩ :=
    CertifiedRGAInvariantHistory.canonical_valid_history execution good stored perm ordered fold q
  refine ⟨EmbedWitness.canonical ops,can,order,spec,state,?_⟩
  simpa only [show applySeq (E Γ α).toUpdateSig (E Γ α).init
    (EmbedWitness.canonical ops) = s from state] using admitted

/-- The recursively synthesized merge base is valid, not merely stored states. -/
theorem virtual_base_valid (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v₁ v₂ : Version} {s₁ s₂ : EState α} {H₁ H₂ : Set (Op (EOp α))}
    (left : C.ver v₁ = some (s₁,H₁)) (right : C.ver v₂ = some (s₂,H₂)) :
    invariant Γ C (virtualMergeBaseState C v₁ v₂) := by
  have store : StoreInv C.ver C.parents := by
    cases execution with
    | ordinary reach => exact storeInv_reachable reach.toReachable
    | virtual reach => exact storeInv_reachableV reach.toReachable
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  have base := CertifiedClosedExecution.virtualMergeBaseState_canonical store good
    (CertifiedRGAExecution.Embedded.closedJoinAt Γ C execution.mintHonest) left right
  have rep := CertifiedRGAExecution.Embedded.represented_of_canonical Γ C.replayContext
    (eHonest_core (eHonest_of_mint execution.mintHonest))
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl (H₁ ∩ H₂)
    (virtualMergeBaseState C v₁ v₂)
    (fun e he => good.version_events_supported v₁ s₁ H₁ left e he.1)
    (fun a b vis hb => ⟨good.version_events_causal v₁ s₁ H₁ left a b vis hb.1,
      good.version_events_causal v₂ s₂ H₂ right a b vis hb.2⟩) base
  exact CertifiedRGAInvariant.represented_valid Γ C.replayContext _ _ rep

/-- Generic invariant replay convergence for implementation histories. This is
separate from the insert-first sequential history, which may move causal deletes. -/
theorem implementation_replay_equal (Γ : OrderedPrefixCode)
    {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))}
    (stored : C.ver v = some (s,H))
    {xs ys : List (Op (EOp α))} (px : listPermOf xs H) (py : listPermOf ys H)
    (cx : respects xs C.vis) (cy : respects ys C.vis) :
    applySeq (E Γ α).toUpdateSig (E Γ α).init xs =
      applySeq (E Γ α).toUpdateSig (E Γ α).init ys :=
  CertifiedRGAInvariantReplay.replay_equal Γ execution stored px py cx cy

structure Correct (Γ : OrderedPrefixCode) (C : Configuration (E Γ α)) : Prop where
  closed : InvariantOrder.Closed (E Γ α) C.replayContext (invariant Γ C)
  stored_valid : ∀ v s H, C.ver v = some (s,H) → invariant Γ C s
  replay : ∀ v s H, C.ver v = some (s,H) →
    InvariantReplay.RestrictedLaws (CertifiedRGAInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedRGAInvariantReplay.policy ∧
    InvariantReplay.Canonical (CertifiedRGAInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedRGAInvariantReplay.policy (E Γ α).init s
  versions : InvariantOrder.VersionsRA (E Γ α) (invariant Γ C) policy (language Γ) C

theorem correct (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C) : Correct Γ C :=
  ⟨closed Γ execution,fun _ _ _ hv => stored_valid Γ execution hv,
    fun _ _ _ hv => ⟨CertifiedRGAInvariantReplay.laws Γ execution hv,
      CertifiedRGAInvariantReplay.storedCanonical Γ execution hv⟩,versions Γ execution⟩

theorem correctV (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (reach : MintCertifiedReachV (E Γ α) (canonicalVirtualMergeBase (E Γ α))
      (generation Γ) C) : Correct Γ C := correct Γ (.virtual reach)

theorem executions (Γ : OrderedPrefixCode) (trace : List (Label (E Γ α) × Configuration (E Γ α)))
    (run : (certifiedTS (E Γ α) (generation Γ)).Execution (initConfig (E Γ α)) trace) :
    Correct Γ (initConfig (E Γ α)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach (E Γ α) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : OrderedPrefixCode) (trace : List (Label (E Γ α) × Configuration (E Γ α)))
    (run : (certifiedTSV (E Γ α) (generation Γ)).Execution (initConfig (E Γ α)) trace) :
    Correct Γ (initConfig (E Γ α)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReachV (E Γ α) (canonicalVirtualMergeBase (E Γ α)) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

#print axioms implementation_replay_equal
#print axioms virtual_base_valid
#print axioms correct
#print axioms correctV
end Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate
