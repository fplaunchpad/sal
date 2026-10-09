import Sal.MRDTs.Paper1.Automation.LocalAssembly
import Sal.MRDTs.Paper1.Automation.CausalCoverage
import Sal.MRDTs.Paper1.Automation.InductivePolicy

/-! Reusable assembly for policy-governed replay carriers. All operation and
state inputs are finite equations. Policy log commutation and the causal/local
coverage arguments are derived by the existing generic equation inductions. -/
namespace Sal.MRDTs.Paper1.Automation.PolicyExpansion
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

structure Kit (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (order : Op D.AppOp → Op D.AppOp → RcRes) : Prop where
  comm : ∀l a b,D.merge l a b=D.merge l b a
  initial : ∀s,D.merge D.init D.init s=s
  shared : ∀t₀ t₁ t₂ B e,
    D.merge (D.merge B t₀ (D.update B e))
      (D.merge B t₁ (D.update B e)) (D.merge B t₂ (D.update B e)) =
    D.merge B (D.merge t₀ t₁ t₂) (D.update B e)
  localKernels : (LocalAssembly.ofMRDT D order).LocalKernels
  causalKernels : CausalCoverage.Kernels (CausalCoverage.signatureOf D order)
  eventCertificate : CausalCoverage.EventCertificate D order
  noncomm_exact : ∀a b:Op D.AppOp,@distinctOps D.toUpdateSig a b → a.rep≠b.rep →
    (¬D.toUpdateSig.commutes a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  noChain : ∀a b c:Op D.AppOp,¬(P.before a.op b.op ∧ P.before b.op c.op)
  policy_order : ∀a b,order a b=.Fst_then_snd ↔ P.before a.op b.op
  conditionalBase : (CausalCoverage.signatureOf D order).ConditionalBase
  kernelStable : (CausalCoverage.signatureOf D order).KernelStable

variable {D : MRDTSig} {P : OperationPolicy D.AppOp}
variable {order : Op D.AppOp → Op D.AppOp → RcRes}

/-- The sole log-valued policy field is built generically from two finite
state equations, rather than supplied as a datatype history theorem. -/
theorem laws (kit : Kit D P order) : GuardedReplay.Laws D.toUpdateSig P := by
  constructor
  · exact kit.noncomm_exact
  · intro a b c _ _; exact kit.noChain a b c
  · intro s a b c between _ _ _ before noncomm
    exact (Signature.conditional_log (CausalCoverage.signatureOf D order)
      kit.conditionalBase kit.kernelStable s a b c ((kit.policy_order a b).mpr before)
      noncomm between).symm

/-- Direct replay-witness conversion for policy-lifted update orders. The
noncommutation equivalence is a finite event obligation, not a history law. -/
theorem canonical_of_loWitness
    (noncomm : ∀a b:Op D.AppOp,¬D.toUpdateSig.commutes a b ↔
      P.before a.op b.op ∨ P.before b.op a.op)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State)
    (witness : ∃π,listPermOf π E ∧ respects π (@loOn D.toUpdateSig P.lift C E) ∧
      applySeq D.toUpdateSig D.init π=s) : Canonical P C E s := by
  obtain ⟨π,perm,ordered,replay⟩ := witness
  refine ⟨π,perm,?_,replay⟩
  apply ordered.imp
  intro a b hn edge
  have eq : paperOrder P C E b a ↔ @loOn D.toUpdateSig P.lift C E b a := by
    simp only [paperOrder,loOn,OperationPolicy.lift_rc_iff,←noncomm]
  exact hn (eq.mp edge)

/-- All unchanged Raw fields, with the two history-sensitive equations
assembled through generic coverage. No datatype local/causal statement or
proof is supplied at the per-carrier interface. -/
theorem assemble (kit : Kit D P order) (R : Representation D)
    (canonical : ∀C E s,R C E s→Canonical P C E s)
    (scheme : ∀C,MetadataDependencies C) : Raw.MergeVCs P R scheme := by
  constructor
  · intros; apply kit.comm
  · intros; apply kit.initial
  · exact CausalCoverage.raw_causal_delta D order kit.eventCertificate kit.causalKernels
      P (laws kit) kit.policy_order kit.noChain R canonical scheme
  · exact LocalAssembly.raw_local_redistribute D order kit.localKernels P (laws kit)
      kit.noChain R canonical scheme
  · intros; apply kit.shared

#print axioms assemble
#print axioms canonical_of_loWitness
end Sal.MRDTs.Paper1.Automation.PolicyExpansion
