import Sal.MRDTs.Paper1.GuardedCoverage
import Sal.MRDTs.Paper1.CertifiedMVRCertificate
import Sal.MRDTs.Paper1.CertifiedQueueMVRQueue
import Sal.MRDTs.Paper1.CertifiedRGAIssuance
import Sal.MRDTs.Paper1.CertifiedPolicy
import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.CertifiedRGACoreExecution
import Sal.MRDTs.Paper1.CertifiedRGACoreCertificate
import Sal.MRDTs.Paper1.CertifiedRGARichCertificate
import Sal.MRDTs.Paper1.CertifiedRGARawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedSidedRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedPeritextRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedFugueRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedFugueVCExecution

/-! Interim typed certified-scope coverage. The original fourteen guarded
positive certificates remain valid. Compact MVR and both sided Peritext cores additionally have closed scoped
execution correctness. Queue has a checked obstruction in an actual original
certified execution. Embedded RGA, sided RGA, native Peritext, and Fugue have original-issuer
certified raw-order obstructions for every payload policy. -/
namespace Sal.MRDTs.Paper1.CertifiedCoverage
open Foundation ConcreteMRDT Sal.EmbedRGA

structure ScopedResult (D : MRDTSig) (I : Issuance D) where
  policy : OperationPolicy D.AppOp
  spec : HistorySpec (Op D.AppOp) D.Query D.Value
  scope : Configuration D → Set (Op D.AppOp) → CertifiedReplay.Scope D.toUpdateSig
  context_eq : ∀ C E, (scope C E).context = C.replayContext
  events_eq : ∀ C E, (scope C E).events = E
  correct : ∀ C, CertifiedExecution D I C →
    (∀ v s E, C.ver v = some (s,E) →
      CertifiedReplay.RestrictedLaws (scope C E) policy ∧
      CertifiedReplay.Canonical (scope C E) policy D.init s) ∧
    VersionsWitness policy spec C

theorem ScopedResult.versionsWitness {D : MRDTSig} {I : Issuance D}
    (result : ScopedResult D I) {C : Configuration D} (execution : CertifiedExecution D I C) :
    VersionsWitness result.policy result.spec C :=
  (result.correct C execution).2

theorem ScopedResult.storedCanonical {D : MRDTSig} {I : Issuance D}
    (result : ScopedResult D I) {C : Configuration D} (execution : CertifiedExecution D I C)
    {v s E} (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder result.policy C.replayContext E) ∧
      applySeq D.toUpdateSig D.init π = s := by
  obtain ⟨π,perm,_,_,ordered,fold⟩ := ((result.correct C execution).1 v s E hv).2
  exact ⟨π,by simpa only [result.events_eq] using perm,
    by simpa only [result.context_eq,result.events_eq] using ordered,fold⟩

theorem ScopedResult.versionsV {D : MRDTSig} {I : Issuance D}
    (result : ScopedResult D I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsWitness result.policy result.spec C :=
  result.versionsWitness (.virtual reach)

theorem ScopedResult.executions {D : MRDTSig} {I : Issuance D}
    (result : ScopedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTS D I).Execution (initConfig D) trace) :
    VersionsWitness result.policy result.spec (initConfig D) ∧
      ∀ entry ∈ trace, VersionsWitness result.policy result.spec entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach D I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨result.versionsWitness (.ordinary .init),
    fun entry he => result.versionsWitness (.ordinary (reached entry he))⟩

theorem ScopedResult.executionsV {D : MRDTSig} {I : Issuance D}
    (result : ScopedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTSV D I).Execution (initConfig D) trace) :
    VersionsWitness result.policy result.spec (initConfig D) ∧
      ∀ entry ∈ trace, VersionsWitness result.policy result.spec entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReachV D (canonicalVirtualMergeBase D) I)
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨result.versionsWitness (.virtual .init),
    fun entry he => result.versionsWitness (.virtual (reached entry he))⟩

/-- VC-derived exact stored replay, without a policy or specification claim. -/
structure CanonicalProgress (D : MRDTSig) (I : Issuance D) where
  stored : ∀ C, CertifiedExecution D I C → ∀ v s E, C.ver v = some (s,E) →
    ∃ π, listPermOf π E ∧ respects π C.vis ∧ applySeq D.toUpdateSig D.init π = s

/-- An actual execution of the original issuer fails the raw event-history
criterion for every payload policy, against the specified client language. -/
structure RawOrderObstruction (D : MRDTSig) (I : Issuance D)
    (spec : HistorySpec (Op D.AppOp) D.Query D.Value) where
  configuration : Configuration D
  certified : MintCertifiedReach D I configuration
  impossible : ∀ P : OperationPolicy D.AppOp,
    ¬ EventVersionsSpecificationRA D P spec configuration

abbrev QueuePolicyObstruction : Prop :=
  ¬ ∃ P : OperationPolicy Instances.Queue.QOp,
    (∀ x y : Op Instances.Queue.QOp,
      x ∈ (CertifiedQueueMVR.Queue.config 3).events → y ∈ (CertifiedQueueMVR.Queue.config 3).events →
      ¬ (CertifiedQueueMVR.Queue.config 3).vis x y → ¬ (CertifiedQueueMVR.Queue.config 3).vis y x →
      distinctOps (D := Instances.Queue.Q.toUpdateSig) x y → x.rep ≠ y.rep →
      (Instances.Queue.qUpdate (Instances.Queue.qUpdate [] x) y ≠
        Instances.Queue.qUpdate (Instances.Queue.qUpdate [] y) x ↔
        P.before x.op y.op ∨ P.before y.op x.op)) ∧
    (∀ x y z : Op Instances.Queue.QOp,
      x ∈ (CertifiedQueueMVR.Queue.config 3).events → y ∈ (CertifiedQueueMVR.Queue.config 3).events →
      z ∈ (CertifiedQueueMVR.Queue.config 3).events →
      distinctOps (D := Instances.Queue.Q.toUpdateSig) x y →
      distinctOps (D := Instances.Queue.Q.toUpdateSig) y z →
      ¬ (P.before x.op y.op ∧ P.before y.op z.op))

/-- Every represented-state scope containing the certified root is excluded by
its actual policy interface, not merely by a single-state surrogate. -/
abbrev QueueScopedPolicyObstruction : Prop :=
  ∀ S : CertifiedReplay.Scope Instances.Queue.Q.toUpdateSig,
    S.context = (CertifiedQueueMVR.Queue.config 3).replayContext →
    S.events = (CertifiedQueueMVR.Queue.config 3).events →
    S.represented ∅ [] →
    ¬ ∃ P : OperationPolicy Instances.Queue.QOp, CertifiedReplay.PolicyLaws S P

inductive Disposition (original : PackagedMRDT) where
  | guarded (result : GuardedCoverage.ProvedResult original.D original.certificate.issuance)
  | scoped (result : ScopedResult original.D original.certificate.issuance)
  | canonicalOnly (progress : CanonicalProgress original.D original.certificate.issuance)
  | rawOrderObstruction (spec : HistorySpec (Op original.D.AppOp) original.D.Query original.D.Value)
      (evidence : RawOrderObstruction original.D original.certificate.issuance spec)
  | queueObstruction (exactEntry : original = PackagedMRDT.of "queue" Instances.Queue.verified)
      (certified : MintCertifiedReach Instances.Queue.Q Instances.Queue.generation
        (CertifiedQueueMVR.Queue.config 3)) (impossible : QueuePolicyObstruction)
      (scopedImpossible : QueueScopedPolicyObstruction)

structure Entry where
  original : PackagedMRDT
  disposition : Disposition original

inductive Tag where
  | guarded | scoped | canonicalOnly | rawOrderObstruction | queueObstruction
  deriving DecidableEq

def Disposition.tag {original : PackagedMRDT} : Disposition original → Tag
  | .guarded _ => .guarded
  | .scoped _ => .scoped
  | .canonicalOnly _ => .canonicalOnly
  | .rawOrderObstruction _ _ => .rawOrderObstruction
  | .queueObstruction _ _ _ _ => .queueObstruction

noncomputable def guarded (name : String) {D : MRDTSig} (original : VerifiedMRDT D)
    (result : GuardedCoverage.ProvedResult D original.issuance) : Entry :=
  ⟨PackagedMRDT.of name original,.guarded result⟩

noncomputable def canonicalOnly (name : String) {D : MRDTSig} (original : VerifiedMRDT D)
    (progress : CanonicalProgress D original.issuance) : Entry :=
  ⟨PackagedMRDT.of name original,.canonicalOnly progress⟩

def mvrResult : ScopedResult Instances.MVRLive.D Instances.MVRLive.issuance where
  policy := CertifiedQueueMVR.MVR.emptyPolicy
  spec := CertifiedQueueMVR.MVR.Certificate.language
  scope := CertifiedQueueMVR.MVR.scopeC
  context_eq _ _ := rfl
  events_eq _ _ := rfl
  correct _ execution := CertifiedQueueMVR.MVR.Certificate.versions execution

def embedObstruction : RawOrderObstruction (Instances.EmbedRGA.E unaryCode Nat)
    (Instances.EmbedRGA.generation unaryCode)
    (GuardedHistory.language (Instances.ProductionRGA.embedClientSpec (α := Nat) unaryCode)) where
  configuration := CertifiedRGARawOrderObstruction.config 6
  certified := CertifiedRGARawOrderObstruction.mint_certified
  impossible P := (CertifiedRGARawOrderObstruction.certified_raw_criterion_failure P).2

def sidedObstruction : RawOrderObstruction (Instances.SidedEmbedRGA.S unaryCode)
    (Instances.SidedEmbedRGA.generation unaryCode)
    (GuardedHistory.language (Instances.ProductionRGA.sidedClientSpec unaryCode)) where
  configuration := CertifiedSidedRawOrderObstruction.config 6
  certified := CertifiedSidedRawOrderObstruction.mint_certified
  impossible P := (CertifiedSidedRawOrderObstruction.certified_raw_criterion_failure P).2

def peritextObstruction : RawOrderObstruction (Instances.Peritext.D unaryCode)
    (Instances.EmbedRGA.generation unaryCode)
    (GuardedHistory.language (Instances.ProductionRGA.embedClientSpec (α := Instances.Peritext.Element) unaryCode)) where
  configuration := CertifiedPeritextRawOrderObstruction.config 6
  certified := CertifiedPeritextRawOrderObstruction.mint_certified
  impossible P := (CertifiedPeritextRawOrderObstruction.certified_raw_criterion_failure P).2

noncomputable def coreResult : ScopedResult (Instances.SidedPeritext.Core unaryCode)
    (Instances.SidedPeritext.generation unaryCode) where
  policy := CertifiedRGACoreVC.policy unaryCode
  spec := CertifiedRGACoreCertificate.language unaryCode
  scope := CertifiedRGACoreCertificate.scope unaryCode
  context_eq _ _ := rfl
  events_eq _ _ := rfl
  correct _ execution := CertifiedRGACoreCertificate.correct unaryCode execution

noncomputable def richResult : ScopedResult (Instances.SidedPeritext.RichCore unaryCode)
    (Instances.SidedPeritext.richGeneration unaryCode) where
  policy := CertifiedRGARichVC.policy unaryCode
  spec := CertifiedRGARichCertificate.language unaryCode
  scope := CertifiedRGARichCertificate.scope unaryCode
  context_eq _ _ := rfl
  events_eq _ _ := rfl
  correct _ execution := CertifiedRGARichCertificate.correct unaryCode execution

def fugueObstruction : RawOrderObstruction (Instances.SidedEmbedRGA.FugueMax.datatype unaryCode)
    (Instances.SidedEmbedRGA.FugueMax.generation unaryCode)
    (GuardedHistory.language (Instances.SidedEmbedRGA.FugueMax.listSpec unaryCode)) where
  configuration := CertifiedFugueRawOrderObstruction.config 3
  certified := CertifiedFugueRawOrderObstruction.mint_certified
  impossible P := (CertifiedFugueRawOrderObstruction.certified_raw_criterion_failure P).2

noncomputable def inventory : List Entry :=
  [ guarded "grow-only-set" Instances.GSet.verified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.gsetCertificate)
  , guarded "add-store" (Instances.AddStore.verified (α := Nat))
      (GuardedCoverage.provedScoped Guarded.SimplePorts.addStoreCertificate)
  , guarded "finite-add-store" (Instances.FinsetStore.verified (α := Nat))
      (GuardedCoverage.provedScoped Guarded.SimplePorts.finiteAddCertificate)
  , guarded "counter" Instances.FlatCounters.counterVerified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.counterCertificate)
  , guarded "increment-only-counter" Instances.FlatCounters.iocVerified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.iocCertificate)
  , guarded "pn-counter" Instances.FlatCounters.pnVerified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.pnCertificate)
  , guarded "flat-grow-only-set" Instances.FlatGrowOnly.gosetVerified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.booleanSetCertificate)
  , guarded "flat-grow-only-map" Instances.FlatGrowOnly.gomapVerified
      (GuardedCoverage.provedScoped Guarded.SimplePorts.booleanMapCertificate)
  , guarded "bounded-counter" Instances.BoundedCounter.verified
      (GuardedCoverage.provedScoped Guarded.ScopedPorts.boundedCertificate)
  , guarded "lww-register" Instances.LWWRegister.verified
      (GuardedCoverage.provedScoped LWW.GuardedPort.certificate)
  , guarded "rga" Instances.RGA.verified (GuardedCoverage.provedScoped Guarded.ScopedPorts.rgaCertificate)
  , ⟨PackagedMRDT.of "embed-rga" (Instances.ProductionRGA.embed (α := Nat) unaryCode),
      .rawOrderObstruction _ embedObstruction⟩
  , ⟨PackagedMRDT.of "sided-embed-rga" (Instances.ProductionRGA.sided unaryCode),
      .rawOrderObstruction _ sidedObstruction⟩
  , ⟨PackagedMRDT.of "peritext-embed-rga" (Instances.Peritext.verified unaryCode),
      .rawOrderObstruction _ peritextObstruction⟩
  , ⟨PackagedMRDT.of "sided-peritext-core" (Instances.SidedPeritext.verified unaryCode),.scoped coreResult⟩
  , ⟨PackagedMRDT.of "sided-peritext-rich-core" (Instances.SidedPeritext.richVerified unaryCode),.scoped richResult⟩
  , guarded "tree-move" Instances.TreeMove.verified (GuardedCoverage.provedScoped Guarded.ScopedPorts.treeCertificate)
  , guarded "aegis-sheet" Instances.AegisSheet.verified (GuardedCoverage.provedScoped Guarded.ScopedPorts.sheetCertificate)
  , guarded "efficient-or-set" (Instances.EfficientORSet.verified (α := Nat))
      (GuardedCoverage.provedScoped (EfficientORSet.RawCertificate.certificate (α := Nat)))
  , ⟨PackagedMRDT.of "queue" Instances.Queue.verified,
      .queueObstruction rfl CertifiedQueueMVR.Queue.certified CertifiedQueueMVR.Queue.no_local_payload_policy
        CertifiedQueueMVR.Queue.no_scoped_policy⟩
  , ⟨PackagedMRDT.of "mvr" Instances.MVRLive.verified,.scoped mvrResult⟩
  , ⟨PackagedMRDT.of "fugue-max" (Instances.SidedEmbedRGA.FugueMax.verified unaryCode),
      .rawOrderObstruction _ fugueObstruction⟩
  ]

theorem packages_eq_production : inventory.map Entry.original = Production.registry := rfl

theorem every_production_entry (original : PackagedMRDT) (member : original ∈ Production.registry) :
    ∃ entry ∈ inventory, entry.original = original := by
  rw [← packages_eq_production] at member
  exact List.mem_map.mp member

noncomputable def tags : List Tag := inventory.map (fun e => e.disposition.tag)

theorem counts : inventory.length = 22 ∧
    (tags.filter (· == .guarded)).length = 14 ∧
    (tags.filter (· == .scoped)).length = 3 ∧
    (tags.filter (· == .canonicalOnly)).length = 0 ∧
    (tags.filter (· == .rawOrderObstruction)).length = 4 ∧
    (tags.filter (· == .queueObstruction)).length = 1 := by decide

/-- Exact-paper OR-set remains an extra checked raw positive result. -/
noncomputable def exactORSet := GuardedCoverage.exactORSet
noncomputable def names : List String := inventory.map (fun e => e.original.name)
theorem names_eq_production : names = Production.names := rfl
theorem exactORSet_not_registry : "exact-paper-or-set" ∉ names := by decide

end Sal.MRDTs.Paper1.CertifiedCoverage
