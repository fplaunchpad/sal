import Sal.MRDTs.Paper1.ConcreteHistoryBridge
import Sal.MRDTs.Paper1.GuardedRawORSetJoin

/-! Exact OR-set execution correctness with raw equality. The merge induction
uses the raw VC bundle, and the stored-state evidence comes from that derived
join. The full-event history certificate has no outstanding canonicality or
Join premise. -/
namespace Sal.MRDTs.Paper1.ORSet.RawExecution
open Foundation
variable {α : Type} [DecidableEq α]
noncomputable local instance : ReplayPolicy (D α).toUpdateSig := (conflict α).lift

theorem vcJoinAt (C : ReplayContext (D α).toUpdateSig) :
    @JoinAt (D α) (conflict α).lift C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have tr : Transitive C.vis := fun _ _ _ h k => trans h k
  have kit := RawReplay.replaySupply C tr irrefl
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := (D α).toUpdateSig) hp₁ hp₂
  have sizes := ConcreteMRDT.Raw.join_at_sizes GuardedRawVC.mergeVCs RawReplay.unique
    (fun C _ _ _ => RawReplay.initial C) RawReplay.finite
    C tr irrefl kit.represented kit.peel
  have joined := sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun x y edge mem => closed₁ x y edge.1 edge.2 mem)
    (fun x y edge mem => closed₂ x y edge.1 edge.2 mem)
    ⟨hl,fun x hx => sup₁ x hx.1⟩
    ⟨⟨π₁,hp₁,by assumption,by assumption⟩,sup₁⟩
    ⟨⟨π₂,hp₂,by assumption,by assumption⟩,sup₂⟩
  exact joined.1

theorem vcCanonicalConfig {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV (fun C _ => vcJoinAt C.replayContext) reach

theorem representedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    ∀ v s E, C.ver v = some (s,E) → RawReplay.representation C.replayContext E s := by
  have good := vcCanonicalConfig reach
  intro v s E hv
  exact ⟨good.canonical v s E hv,good.version_events_supported v s E hv⟩

private theorem virtual_reach {C : Configuration (D α)}
    (exec : CertifiedExecution (D α) (issuance α) C) :
    MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C := by
  cases exec with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

theorem compatibility : CommutationCompatibility (D α) id (EventSpec.spec α) := EventSpec.commutationCompatibility

def certificate : ConcreteMRDT.ScopedCertificate
    (conflict α) (EventSpec.spec α) (issuance α) :=
  ConcreteMRDT.ScopedCertificate.ofTotal Guarded.laws
    (fun C E supported _ _ hs ht => ConcreteMRDT.canonical_unique Guarded.laws C E supported hs ht)
    (fun _ exec v s E hv => (representedVersions (virtual_reach exec) v s E hv).2)
    (fun C exec v s E hv =>
      RawReplay.representsCanonical C.replayContext E s
        (representedVersions (virtual_reach exec) v s E hv))
    compatibility EventSpec.foldHistorySound

/-- Every stored state is exactly a semantic-order replay, including its tags. -/
theorem storedCanonical {C : Configuration (D α)}
    (execution : CertifiedExecution (D α) (issuance α) C)
    {v : Version} {s : (D α).State} {E : Set (Op (Update α))}
    (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder (conflict α) C.replayContext E) ∧
      applySeq (D α).toUpdateSig (D α).init π = s :=
  certificate.canonicalVersions C execution v s E hv

theorem versionsV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    ConcreteMRDT.VersionsWitness
      (conflict α) (EventSpec.spec α) C := certificate.versionsV reach

theorem versions {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) (issuance α) C) :
    ConcreteMRDT.VersionsWitness
      (conflict α) (EventSpec.spec α) C := certificate.versions (.ordinary reach)

theorem convergence {C : Configuration (D α)}
    (execution : CertifiedExecution (D α) (issuance α) C)
    {v w : Version} {s t : (D α).State} {E : Set (Op (Update α))}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  certificate.convergence execution hv hw

theorem executions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    ConcreteMRDT.ExecutionCorrect
      (conflict α) (EventSpec.spec α) trace := certificate.executions trace execution

theorem executionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    ConcreteMRDT.ExecutionCorrect
      (conflict α) (EventSpec.spec α) trace := certificate.executionsV trace execution

#print axioms vcJoinAt
#print axioms certificate
#print axioms convergence
#print axioms executionsV
end Sal.MRDTs.Paper1.ORSet.RawExecution
