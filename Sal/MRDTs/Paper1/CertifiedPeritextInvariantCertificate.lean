import Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedPeritextVC
import Sal.MRDTs.Instances.Peritext
import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.AbstractSoundness
import Sal.MRDTs.Paper1.CertifiedRGAInvariantReplay

namespace Sal.MRDTs.Paper1.CertifiedPeritextInvariantCertificate
open Foundation Sal.EmbedRGA
open Instances.EmbedRGA Instances.ProductionRGA Instances.Peritext

abbrev language (Γ : OrderedPrefixCode) := GuardedHistory.language (embedClientSpec (α := Element) Γ)
abbrev invariant (Γ : OrderedPrefixCode) (C : Configuration (D Γ)) :=
  CertifiedRGAInvariant.Valid Γ C.replayContext
abbrev policy := CertifiedRGAInvariantHistory.emptyPolicy (α := Element)

theorem closed (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C) :
    InvariantOrder.Closed (D Γ) C.replayContext (invariant Γ C) :=
  CertifiedRGAInvariant.closed Γ C.replayContext
    (eHonest_core (eHonest_of_mint execution.mintHonest))

theorem stored_valid (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C)
    {v : Version} {s : EState Element} {H : Set (Op (EOp Element))}
    (stored : C.ver v = some (s,H)) : invariant Γ C s :=
  CertifiedRGAInvariant.represented_valid Γ C.replayContext H s
    (CertifiedRGAExecution.Embedded.representedVersions Γ execution stored)

theorem versions (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C) :
    InvariantOrder.VersionsRA (D Γ) (invariant Γ C) policy (language Γ) C := by
  intro v s H stored q
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ execution
  have rep := CertifiedRGAExecution.Embedded.representedVersions Γ execution stored
  obtain ⟨ops,perm,ordered,fold⟩ := rep.2.2.2.2
  obtain ⟨can,order,_,spec,admitted⟩ :=
    CertifiedRGAInvariantHistory.canonical_valid_history execution good stored perm ordered fold q
  exact ⟨EmbedWitness.canonical ops,can,order,spec,admitted⟩

/-- The recursively synthesized merge base is valid, not merely stored states. -/
theorem virtual_base_valid (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C)
    {v₁ v₂ : Version} {s₁ s₂ : EState Element} {H₁ H₂ : Set (Op (EOp Element))}
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
    {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C)
    {v : Version} {s : EState Element} {H : Set (Op (EOp Element))}
    (stored : C.ver v = some (s,H))
    {xs ys : List (Op (EOp Element))} (px : listPermOf xs H) (py : listPermOf ys H)
    (cx : respects xs C.vis) (cy : respects ys C.vis) :
    applySeq (D Γ).toUpdateSig (D Γ).init xs =
      applySeq (D Γ).toUpdateSig (D Γ).init ys :=
  CertifiedRGAInvariantReplay.replay_equal Γ execution stored px py cx cy

structure Correct (Γ : OrderedPrefixCode) (C : Configuration (D Γ)) : Prop where
  closed : InvariantOrder.Closed (D Γ) C.replayContext (invariant Γ C)
  stored_valid : ∀ v s H, C.ver v = some (s,H) → invariant Γ C s
  replay : ∀ v s H, C.ver v = some (s,H) →
    InvariantReplay.RestrictedLaws (CertifiedRGAInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedRGAInvariantReplay.policy ∧
    InvariantReplay.Canonical (CertifiedRGAInvariantReplay.scope Γ C H)
      (invariant Γ C) CertifiedRGAInvariantReplay.policy (D Γ).init s
  versions : InvariantOrder.VersionsRA (D Γ) (invariant Γ C) policy (language Γ) C

theorem correct (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (execution : CertifiedExecution (D Γ) (generation Γ) C) : Correct Γ C :=
  ⟨closed Γ execution,fun _ _ _ hv => stored_valid Γ execution hv,
    fun _ _ _ hv => ⟨CertifiedRGAInvariantReplay.laws Γ execution hv,
      CertifiedRGAInvariantReplay.storedCanonical Γ execution hv⟩,versions Γ execution⟩

theorem correctV (Γ : OrderedPrefixCode) {C : Configuration (D Γ)}
    (reach : MintCertifiedReachV (D Γ) (canonicalVirtualMergeBase (D Γ))
      (generation Γ) C) : Correct Γ C := correct Γ (.virtual reach)

theorem executions (Γ : OrderedPrefixCode) (trace : List (Label (D Γ) × Configuration (D Γ)))
    (run : (certifiedTS (D Γ) (generation Γ)).Execution (initConfig (D Γ)) trace) :
    Correct Γ (initConfig (D Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReach (D Γ) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : OrderedPrefixCode) (trace : List (Label (D Γ) × Configuration (D Γ)))
    (run : (certifiedTSV (D Γ) (generation Γ)).Execution (initConfig (D Γ)) trace) :
    Correct Γ (initConfig (D Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReachV (D Γ) (canonicalVirtualMergeBase (D Γ)) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

theorem mergeVCs (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.MergeVCs
    (CertifiedRGAVCReplay.Embedded.model (α := Element) Γ)
    CertifiedRGAVCReplay.Embedded.policy (CertifiedPeritextVC.representation Γ)
    (CertifiedRGAVCReplay.Embedded.scheme Γ) := CertifiedPeritextVC.mergeVCs Γ

theorem representationJoin (Γ : OrderedPrefixCode) :
    AbstractMRDT.RepresentationJoin (CertifiedPeritextVC.representation Γ) :=
  CertifiedPeritextVC.representationJoin Γ

#print axioms implementation_replay_equal
#print axioms virtual_base_valid
#print axioms correct
#print axioms correctV
end Sal.MRDTs.Paper1.CertifiedPeritextInvariantCertificate
