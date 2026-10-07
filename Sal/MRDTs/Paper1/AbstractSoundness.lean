import Sal.MRDTs.Paper1.AbstractMerge

/-! Abstraction-first certificates and observable execution correctness. Raw
operational steps, event identities, and mint/issuance evidence are unchanged.
Representation Join is a checked construction contract; the execution proof
separately establishes that all stored states satisfy that representation. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

structure Certificate (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) where
  queryComplete : A.QueryComplete
  laws : Laws A P
  representation : Representation D
  representsCanonical : RepresentsCanonical A P representation
  representationJoin : RepresentationJoin representation
  representedVersions : ∀ C,
    MintCertifiedReachV D (canonicalVirtualMergeBase D) I C →
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s
  compatibility : SpecificationCompatibility A S
  historySound : EventFoldHistorySound D S

theorem Certificate.versionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : Certificate A P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsRALinearizable A P S C :=
  of_representation cert.laws (cert.representedVersions C reach)
    cert.representsCanonical cert.compatibility cert.historySound

theorem Certificate.versions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : Certificate A P S I) {C : Configuration D}
    (reach : MintCertifiedReach D I C) : VersionsRALinearizable A P S C :=
  cert.versionsV reach.toV

/-- Two stored states for the same event history agree semantically, including
all future local updates and reads. They need not have identical metadata. -/
theorem Certificate.convergence {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : Certificate A P S I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C)
    {v w : Version} {s t : D.State} {E : Set (Op D.AppOp)}
    (supported : ∀ e ∈ E, e ∈ C.replayContext.events)
    (hv : C.ver v = some (s,E)) (hw : C.ver w = some (t,E)) : Equivalent A s t :=
  canonical_equivalent cert.laws C.replayContext E supported
    (cert.representsCanonical _ _ _ (cert.representedVersions C reach v s E hv))
    (cert.representsCanonical _ _ _ (cert.representedVersions C reach w t E hw))

def ExecutionCorrect (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value)
    (trace : List (Label D × Configuration D)) : Prop :=
  VersionsRALinearizable A P S (initConfig D) ∧
    ∀ entry ∈ trace, VersionsRALinearizable A P S entry.2

theorem visited {T : LabeledTS} {Good : T.State → Prop}
    (preserve : ∀ s l t, Good s → T.step s l t → Good t)
    {initial : T.State} {trace : List (T.Label × T.State)}
    (execution : T.Execution initial trace) (start : Good initial) :
    ∀ entry ∈ trace, Good entry.2 := by
  induction execution with
  | nil => simp
  | @cons s t l rest step _ ih =>
    have head := preserve s l t start step
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact head
    · exact ih head entry he

theorem Certificate.executionsV {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : Certificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versionsV .init,fun entry he => cert.versionsV (versions entry he)⟩

theorem Certificate.executions {A : Model D} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {I : Issuance D}
    (cert : Certificate A P S I) (trace : List (Label D × Configuration D))
    (execution : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect A P S trace := by
  have versions := visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨cert.versions .init,fun entry he => cert.versions (versions entry he)⟩

end Sal.MRDTs.Paper1.AbstractMRDT
