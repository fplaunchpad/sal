import Sal.MRDTs.Paper1.GuardedAbstraction
import Sal.MRDTs.Paper1.ScopedHistoryBridge

/-! Full-event history correctness from guarded observational laws. Stored
canonicality is an explicit premise: this bridge does not discharge merge VCs.
Both total fold soundness and issuance-scoped admitted replay histories are
supported. The public criterion retains specification visibility and all event
labels, including timestamp and replica identity. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT.Guarded
open Foundation
variable {D : MRDTSig}

/-- Guarded datatype laws together with the full-event history witness. -/
def VersionsRALinearizable (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  Laws A P ∧ AbstractMRDT.VersionsWitness A P S C

def RALinearizable (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  Laws A P ∧ AbstractMRDT.Witness A P S C

theorem VersionsRALinearizable.heads {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (h : VersionsRALinearizable A P S C) : RALinearizable A P S C :=
  ⟨h.1, fun _ v s E _ hv q => h.2 v s E hv q⟩

/-- Total merge-free fold soundness transports directly along the guarded
canonical witness; this route needs no supported-events premise. -/
theorem of_canonical {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (laws : Laws A P)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s)
    (compatible : SpecificationCompatibility A S) (sound : EventFoldHistorySound D S) :
    VersionsRALinearizable A P S C := by
  refine ⟨laws, ?_⟩
  intro v s E hv q
  obtain ⟨π, hp, ho, hf⟩ := canonical v s E hv
  refine ⟨π, hp, ho, ?_, ?_⟩
  · exact ho.imp (fun {_ _} h edge =>
      h (Or.inl ⟨edge.1, fun commute => edge.2 (compatible _ _ commute)⟩))
  · have answer := equivalent_query hf q
    simpa only [answer] using sound π q

/-- The scoped witness describes an admitted merge-free fold. Guarded replay
uniqueness relates it to the separately certified stored state. -/
theorem versions_of_scoped_history {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (laws : Laws A P) (history : ExecutionHistoryAdequacy A P S I)
    {C : Configuration D} (execution : CertifiedExecution D I C)
    (supported : ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E)
    (canonical : ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s) :
    VersionsRALinearizable A P S C := by
  refine ⟨laws, ?_⟩
  intro v s E hv q
  obtain ⟨π, hp, ho, hs, accepted⟩ := history C execution v s E hv q
  have folded : Canonical A P C.replayContext E
      (applySeq D.toUpdateSig D.init π) := ⟨π, hp, ho, equivalent_refl A _⟩
  have same := canonical_query_unique laws C.replayContext E
    (supported v s E hv) folded (canonical v s E hv) q
  exact ⟨π, hp, ho, hs, by simpa only [same] using accepted⟩

/-- The execution bridge deliberately exposes the outstanding stored-state
canonicality obligation instead of asserting a completed merge VC campaign. -/
structure ScopedCertificate (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) : Prop where
  laws : Laws A P
  supportedVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E
  canonicalVersions : ∀ C, CertifiedExecution D I C →
    ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s
  history : ExecutionHistoryAdequacy A P S I

/-- Total history assumptions are an alternative to the scoped history field. -/
def ScopedCertificate.ofTotal {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (laws : Laws A P)
    (supported : ∀ C, CertifiedExecution D I C →
      ∀ v s E, C.ver v = some (s,E) → Supported C.replayContext E)
    (canonical : ∀ C, CertifiedExecution D I C →
      ∀ v s E, C.ver v = some (s,E) → Canonical A P C.replayContext E s)
    (compatible : SpecificationCompatibility A S) (sound : EventFoldHistorySound D S) :
    ScopedCertificate A P S I where
  laws := laws
  supportedVersions := supported
  canonicalVersions := canonical
  history := by
    intro C execution v s E hv q
    obtain ⟨π, hp, ho, _⟩ := canonical C execution v s E hv
    refine ⟨π, hp, ho, ?_, sound π q⟩
    exact ho.imp (fun {_ _} h edge =>
      h (Or.inl ⟨edge.1, fun commute => edge.2 (compatible _ _ commute)⟩))

theorem ScopedCertificate.versions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate A P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C) : VersionsRALinearizable A P S C :=
  versions_of_scoped_history cert.laws cert.history execution
    (cert.supportedVersions C execution) (cert.canonicalVersions C execution)

theorem ScopedCertificate.versionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate A P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsRALinearizable A P S C := cert.versions (.virtual reach)

/-- Same-history stored versions agree observationally; raw metadata equality
is neither assumed nor concluded. -/
theorem ScopedCertificate.convergence {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate A P S I) {C : Configuration D}
    (execution : CertifiedExecution D I C)
    {v w : Version} {s t : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : Equivalent A s t :=
  canonical_equivalent cert.laws C.replayContext E
    (cert.supportedVersions C execution v s E hv)
    (cert.canonicalVersions C execution v s E hv)
    (cert.canonicalVersions C execution w t E hw)

def ExecutionCorrect (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value)
    (trace : List (Label D × Configuration D)) : Prop :=
  VersionsRALinearizable A P S (initConfig D) ∧
    ∀ entry ∈ trace, VersionsRALinearizable A P S entry.2

theorem ScopedCertificate.executionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.virtual .init),
    fun entry he => cert.versions (.virtual (versions entry he))⟩

theorem ScopedCertificate.executions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : ScopedCertificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions (.ordinary .init),
    fun entry he => cert.versions (.ordinary (versions entry he))⟩

end Sal.MRDTs.Paper1.AbstractMRDT.Guarded
