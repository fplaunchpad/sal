import Sal.MRDTs.Paper1.ExecutionTrace
import Sal.MRDTs.Paper1.CertifiedMVRExecution
import Sal.MRDTs.Paper1.CertifiedMVRHistory
import Sal.MRDTs.Paper1.CertifiedMVRReplay
import Sal.MRDTs.Paper1.CertifiedPolicy

/-! The compact MVR end-to-end bridge, parameterized by its VC-derived history
merge theorem. The scoped policy laws are stated explicitly; this is not an
inhabitant of the old globally quantified guarded-law class. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Certificate
open Foundation ConcreteMRDT Instances.MVRLive
local instance : ReplayPolicy D.toUpdateSig := rc
abbrev language := CertifiedMVRHistory.language

def representation : Representation D := fun _ E s => Represents E s

theorem unique : CertifiedHistory.CertifiedUnique representation issuance := by
  intro C execution v s E hv a b ha hb
  apply Finset.ext
  intro p
  exact (ha p).trans (hb p).symm

/-- Exact stored canonicality includes causal readiness and the unchanged
paper semantic order, using only independent fold legality and representation. -/
theorem storedCanonical (historyMerge : Execution.HistoryMerge)
    {C : Configuration D} (execution : CertifiedExecution D issuance C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E)) :
    CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init s := by
  have good := (Execution.representedExecution historyMerge execution).2.1
  obtain ⟨ops,hp,_,_⟩ := good.canonical v s E hv
  obtain ⟨π,perm,causal,order,_,rep,_⟩ := CertifiedMVRHistory.replay_history C execution E
    (fun e he => good.version_events_supported v s E hv e he)
    (good.version_events_causal v s E hv) ops hp ()
  have same : applySeq D.toUpdateSig D.init π = s :=
    unique C execution v s E hv _ _ rep
      (Execution.representedVersions historyMerge execution v s E hv)
  exact ⟨π,perm,legal_of_causal_enumeration C E perm causal,causal,order,same⟩

theorem history (historyMerge : Execution.HistoryMerge) :
    CertifiedHistory.RepresentedHistory representation emptyPolicy language issuance := by
  intro C execution v s E hv q
  have good := (Execution.representedExecution historyMerge execution).2.1
  obtain ⟨ops,hp,_,_⟩ := good.canonical v s E hv
  obtain ⟨π,perm,_,order,visible,rep,accepted⟩ := CertifiedMVRHistory.replay_history C execution E
    (fun e he => good.version_events_supported v s E hv e he)
    (good.version_events_causal v s E hv) ops hp q
  exact ⟨π,perm,order,visible,rep,accepted⟩

/-- Scoped restricted laws and exact canonicality accompany the explicit
RA history witness; no global law over illegal states is asserted. -/
def Correct (C : Configuration D) : Prop :=
  (∀ v s E, C.ver v = some (s,E) →
    CertifiedReplay.RestrictedLaws (scopeC C E) emptyPolicy ∧
    CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init s) ∧
  VersionsWitness emptyPolicy language C

theorem correct (historyMerge : Execution.HistoryMerge)
    {C : Configuration D} (execution : CertifiedExecution D issuance C) : Correct C := by
  constructor
  · intro v s E hv
    have good := (Execution.representedExecution historyMerge execution).2.1
    exact ⟨CertifiedReplay.restrictedEmpty _ (scope_laws execution E
      (fun e he => good.version_events_supported v s E hv e he)),
      storedCanonical historyMerge execution hv⟩
  · exact CertifiedHistory.versions_of_representation unique (history historyMerge) execution
      (Execution.representedVersions historyMerge execution)

/-- Closed certificate: the merge premise is discharged by the five raw VCs
and the generic strict-size merge induction. -/
theorem versions {C : Configuration D} (execution : CertifiedExecution D issuance C) :
    Correct C := correct Execution.vcHistoryMerge execution

theorem versionsV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) : Correct C :=
  versions (.virtual reach)

theorem convergence {C : Configuration D} (execution : CertifiedExecution D issuance C)
    {v w : Version} {s t : State} {E : Set Event}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : s = t :=
  unique C execution v s E hv _ _
    (Execution.vcRepresentedVersions execution v s E hv)
    (Execution.vcRepresentedVersions execution w t E hw)

theorem executions (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D issuance).Execution (initConfig D) trace) :
    Correct (initConfig D) ∧ ∀ entry ∈ trace, Correct entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach D issuance)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨versions (.ordinary .init),
    fun entry member => versions (.ordinary (reached entry member))⟩

theorem executionsV (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D issuance).Execution (initConfig D) trace) :
    Correct (initConfig D) ∧ ∀ entry ∈ trace, Correct entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨versions (.virtual .init),
    fun entry member => versions (.virtual (reached entry member))⟩

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Certificate
