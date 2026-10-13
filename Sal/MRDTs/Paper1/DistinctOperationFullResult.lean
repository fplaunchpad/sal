import Sal.MRDTs.Paper1.DistinctOperationSoundness
import Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
import Sal.MRDTs.Paper1.DistinctOperationFullExecution
import Sal.MRDTs.Paper1.DistinctOperationFullHistory
import Sal.MRDTs.Paper1.DistinctOperationFullTrace

/-! The complete revised scoped contract. The independent total minimum
register and the implementation agree on the issuer's one-update branches,
but scoped adequacy can explain a different merge replay than the stored one. -/
namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT

def fullConditions : DistinctScopedVCConditions P minimumSpec.toSpec issuance where
  representation := R
  scheme := scheme
  laws := laws
  vcs := vcs
  unique := unique
  initial := initial
  finite := finite
  canonical := canonical
  supported := supported
  replaySupply := replaySupply
  representedVersions := representedVersions
  history := scoped_history_of_represented (by
    intro C execution v s E hv
    cases execution with
    | ordinary reach => exact representedVersions C reach.toV v s E hv
    | virtual reach => exact representedVersions C reach v s E hv)

/-- This rules out every candidate history, not just the stored replay. -/
theorem no_versions_witness {C : Configuration D} {v : Version}
    (stored : C.ver v = some (2, {a,b})) :
    ¬ VersionsWitness P minimumSpec.toSpec C := by
  intro witness
  obtain ⟨π,perm,_,_,accepted⟩ := witness v 2 {a,b} stored ()
  have bad := two_event_answer perm accepted
  norm_num [D] at bad

/-- The counterexample also violates the public head-only RA criterion. -/
theorem no_head_witness {C : Configuration D} {r : Replica} {v : Version}
    (head : C.head r = some v) (stored : C.ver v = some (2, {a,b})) :
    ¬ EventSpecificationRALinearizable D P minimumSpec.toSpec C := by
  intro witness
  obtain ⟨π,perm,_,_,accepted⟩ := witness r v 2 {a,b} head stored ()
  have bad := two_event_answer perm accepted
  norm_num [D] at bad

/-- The original replay guard rejects the same unchanged model. -/
theorem original_laws_fail : ¬ GuardedReplay.Laws D.toUpdateSig P := by
  intro original
  have noncommuting : ¬ D.toUpdateSig.commutes a b := by
    intro commutes
    have bad := commutes 0
    norm_num [D,a,b,Op.time] at bad
  have edge := (original.noncomm_exact a b
    (by change (1 : Nat) ≠ 2; decide)
    (by change (0 : Nat) ≠ 1; decide)).mp noncommuting
  simp [P] at edge

/-- Full falsifier: every revised scoped assumption, an actual certified
execution, and failure of the public head-only RA-linearizability criterion. -/
theorem full_counterexample :
    Nonempty (DistinctScopedVCConditions P minimumSpec.toSpec issuance) ∧
    MintCertifiedReach D issuance afterMerge ∧
    ¬ EventSpecificationRALinearizable D P minimumSpec.toSpec afterMerge :=
  ⟨⟨fullConditions⟩,reached_afterMerge,no_head_witness head_afterMerge stored_afterMerge⟩

#print axioms fullConditions
#print axioms no_head_witness
#print axioms original_laws_fail
#print axioms full_counterexample
#print axioms DistinctVCConditions.executionsV
end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
