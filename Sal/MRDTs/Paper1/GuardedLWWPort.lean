import Sal.MRDTs.Paper1.GuardedSimplePorts
import Sal.MRDTs.Instances.LWWRegister

/-! LWW admits the empty operation policy while preserving its max update,
merge, query, true issuance and independent ordinary overwrite specification.
A chronological full-event replay explains the stored maximum. This is a
scoped history bridge; the two specification writes need not commute. -/
namespace Sal.MRDTs.Paper1.LWW.GuardedPort
open Foundation AbstractMRDT
open Instances.LWWRegister

abbrev model := Raw.model D
abbrev policy := commutingPolicy LWWOp
abbrev language := GuardedHistory.language spec

/-- The universal max equations are unchanged; only their replay-law field
is specialized to the empty policy required by the commuting VC adapter. -/
theorem emptyMergeLaws : @MergeLaws D (ReplayPolicy.default D.toUpdateSig) := by
  refine ⟨ReplayLaws.of_all_comm all_comm ?_,?_,?_⟩
  · apply rcAcyclic_of_noRcChain
    intro a b c
    simp [UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]
  · intro l a b
    simpa only [D] using (max_comm (α := State) a b)
  · intro s
    simpa only [D] using (max_eq_right (α := State) (bot_le : (⊥ : State) ≤ s))

private theorem virtual_reach {C : Configuration D}
    (execution : CertifiedExecution D issuance C) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C := by
  cases execution with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

theorem chronological_respects_vis (C : Configuration D) (ops : List (Op LWWOp)) :
    respects (canonical ops) C.vis := by
  exact (canonical_pairwise ops).imp fun {a b} hle hvis => by
    have hlt : packedWrite b < packedWrite a :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (C.causal_mono hvis))
    exact (not_lt_of_ge hle) hlt

/-- The provenance comes from commuting VCs, independently of the production
LWW Join theorem and its timestamp replay resolver. -/
theorem history : EventExecutionHistoryAdequacy D policy language issuance := by
  intro C execution v s E hv q
  have good := CommutingPort.vcCanonicalConfig model all_comm emptyMergeLaws deltaLaws
    commutingPeelLaw (virtual_reach execution)
  obtain ⟨ops,hp,_,_⟩ := good.canonical v s E hv
  have perm : listPermOf (canonical ops) E :=
    ⟨hp.1.perm (canonical_perm ops).symm,
      fun e => (canonical_perm ops).mem_iff.trans (hp.2 e)⟩
  refine ⟨canonical ops,perm,?_,?_,?_⟩
  · exact perm.1.imp (fun {_ _} _ =>
      paperOrder_false_of_all_commute all_comm C.replayContext E _ _)
  · exact (chronological_respects_vis C ops).imp (fun {_ _} h edge => h edge.1)
  · have accepted := GuardedHistory.admits_updates_query spec
      (fun _ _ _ => True.intro) (canonical ops) True.intro q
    have answer : D.query (applySeq D.toUpdateSig D.init (canonical ops)) q =
        spec.query (spec.run (canonical ops)) q :=
      fold_refines_sorted (canonical ops) (canonical_pairwise ops)
    rw [answer]
    exact accepted

def certificate : Guarded.ScopedCertificate model policy language issuance :=
  Guarded.Positive.rawCommutingScoped all_comm emptyMergeLaws deltaLaws commutingPeelLaw issuance history

theorem versions {C : Configuration D} (reach : MintCertifiedReach D issuance C) :
    Guarded.VersionsRALinearizable model policy language C :=
  certificate.versions (.ordinary reach)

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) :
    Guarded.VersionsRALinearizable model policy language C := certificate.versionsV reach

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D issuance).Execution (initConfig D) trace) :
    Guarded.ExecutionCorrect model policy language trace := certificate.executions trace execution

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D issuance).Execution (initConfig D) trace) :
    Guarded.ExecutionCorrect model policy language trace := certificate.executionsV trace execution

theorem convergence {C : Configuration D} (execution : CertifiedExecution D issuance C)
    {v w : Version} {s t : D.State} {E : Set (Op LWWOp)}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  certificate.convergence execution hv hw

/-- PASS+FAIL: reversed concrete delivery keeps the timestamp maximum;
the independent overwrite history needs the chronological choice. -/
theorem control :
    D.query (applySeq D.toUpdateSig D.init [w₃,w₁,w₂]) () = some 30 ∧
    D.query (applySeq D.toUpdateSig D.init [w₃,w₁,w₂]) () ≠ some 20 ∧
    spec.run [w₁,w₂] = some 20 ∧ spec.run [w₂,w₁] = some 10 ∧
    spec.run [w₂,w₁] ≠ spec.run [w₁,w₂] :=
  ⟨reversed_delivery_same_winner,lower_timestamp_does_not_win,reversed_assignments_wrong_winner⟩

#print axioms history
#print axioms certificate
#print axioms executionsV
#print axioms convergence
end Sal.MRDTs.Paper1.LWW.GuardedPort
