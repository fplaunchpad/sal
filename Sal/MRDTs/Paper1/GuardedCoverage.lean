import Sal.MRDTs.Metatheory.ProductionLedger
import Sal.MRDTs.Paper1.GuardedSimplePorts
import Sal.MRDTs.Paper1.GuardedRawEfficientCertificate
import Sal.MRDTs.Paper1.GuardedRawExactExecution
import Sal.MRDTs.Paper1.GuardedQueueMVR
import Sal.MRDTs.Paper1.GuardedRGAObstructions
import Sal.MRDTs.Paper1.GuardedLWWExclusion
import Sal.MRDTs.Paper1.GuardedLWWPort

/-! Typed coverage of the corrected guarded contract. Positive entries carry
checked ordinary and virtual execution routes for the original datatype and
issuer. Blocked entries carry universal sound-model impossibility proofs.
LWW has a positive empty-policy certificate; the separate checked exclusion
of its original timestamp policy remains a control, not a datatype verdict. No verdict denotes a
failed or unfinished proof. -/
namespace Sal.MRDTs.Paper1.GuardedCoverage
open Foundation AbstractMRDT AbstractMRDT.Guarded

inductive ProofRoute {D : MRDTSig} (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) where
  | total (conditions : Guarded.Positive.TotalCertificate A P S I)
  | issued (conditions : Guarded.ScopedCertificate A P S I)

structure ProvedResult (D : MRDTSig) (I : Issuance D) where
  model : Model D
  policy : OperationPolicy D.AppOp
  spec : HistorySpec (Op D.AppOp) D.Query D.Value
  route : ProofRoute model policy spec I
  raw : ∀ s t, Equivalent model s t ↔ s = t

def provedTotal {D : MRDTSig} {I : Issuance D} {A : Model D}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    (conditions : Guarded.Positive.TotalCertificate A P S I)
    (raw : ∀ s t, Equivalent A s t ↔ s = t) : ProvedResult D I :=
  ⟨A,P,S,.total conditions,raw⟩

def provedScoped {D : MRDTSig} {I : Issuance D} {A : Model D}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    (conditions : Guarded.ScopedCertificate A P S I)
    (raw : ∀ s t, Equivalent A s t ↔ s = t) : ProvedResult D I :=
  ⟨A,P,S,.issued conditions,raw⟩

theorem ProvedResult.rawCommutes_iff {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (a b : Op D.AppOp) :
    Commutes result.model a b ↔ D.toUpdateSig.commutes a b := by
  unfold Commutes UpdateSig.commutes
  exact forall_congr' (fun s => result.raw _ _)

theorem ProvedResult.rawOrder_iff {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    order result.model result.policy C E a b ↔ paperOrder result.policy C E a b := by
  simp only [order, paperOrder, result.rawCommutes_iff]

/-- Every positive route exposes an exact stored-state replay witness. -/
theorem ProvedResult.storedCanonical {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (execution : CertifiedExecution D I C) {v s E}
    (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder result.policy C.replayContext E) ∧
      applySeq D.toUpdateSig D.init π = s := by
  have canonical : Guarded.Canonical result.model result.policy C.replayContext E s := by
    cases result.route with
    | total conditions => exact conditions.canonicalVersions C execution v s E hv
    | issued conditions => exact conditions.canonicalVersions C execution v s E hv
  obtain ⟨π,hp,hr,hf⟩ := canonical
  refine ⟨π,hp,?_,(result.raw _ _).mp hf⟩
  simpa only [respects, result.rawOrder_iff] using hr

theorem ProvedResult.versions {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (execution : CertifiedExecution D I C) :
    Guarded.VersionsRALinearizable result.model result.policy result.spec C := by
  cases result.route with
  | total conditions => exact conditions.versions execution
  | issued conditions => exact conditions.versions execution

theorem ProvedResult.versionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    AbstractMRDT.Guarded.VersionsRALinearizable result.model result.policy result.spec C := by
  cases result.route with
  | total conditions => exact conditions.versionsV reach
  | issued conditions => exact conditions.versionsV reach

theorem ProvedResult.executionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTSV D I).Execution (initConfig D) trace) :
    Guarded.ExecutionCorrect result.model result.policy result.spec trace := by
  cases result.route with
  | total conditions => exact conditions.executionsV trace run
  | issued conditions => exact conditions.executionsV trace run

theorem ProvedResult.executions {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTS D I).Execution (initConfig D) trace) :
    Guarded.ExecutionCorrect result.model result.policy result.spec trace := by
  cases result.route with
  | total conditions => exact conditions.executions trace run
  | issued conditions => exact conditions.executions trace run

inductive Disposition (original : PackagedMRDT) where
  | proved (result : ProvedResult original.D original.certificate.issuance)
  | blocked (impossible : ∀ A : Model original.D,
      ¬ ∃ P : OperationPolicy original.D.AppOp, Guarded.Laws A P)

structure Entry where
  original : PackagedMRDT
  disposition : Disposition original

inductive Tag where
  | proved | blocked
  deriving DecidableEq

def Disposition.tag {original : PackagedMRDT} : Disposition original → Tag
  | .proved _ => .proved
  | .blocked _ => .blocked

noncomputable def proved (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D) (result : ProvedResult D original.issuance) : Entry :=
  ⟨PackagedMRDT.of name original,.proved result⟩

noncomputable def blocked (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D)
    (impossible : ∀ A : Model D, ¬ ∃ P : OperationPolicy D.AppOp, Guarded.Laws A P) : Entry :=
  ⟨PackagedMRDT.of name original,.blocked impossible⟩

open Sal.EmbedRGA

noncomputable def inventory : List Entry :=
  [ proved "grow-only-set" Instances.GSet.verified
      (provedTotal Guarded.SimplePorts.gsetCertificate (fun _ _ => Iff.rfl))
  , proved "add-store" (Instances.AddStore.verified (α := Nat))
      (provedTotal Guarded.SimplePorts.addStoreCertificate (fun _ _ => Iff.rfl))
  , proved "finite-add-store" (Instances.FinsetStore.verified (α := Nat))
      (provedTotal Guarded.SimplePorts.finiteAddCertificate (fun _ _ => Iff.rfl))
  , proved "counter" Instances.FlatCounters.counterVerified
      (provedTotal Guarded.SimplePorts.counterCertificate (fun _ _ => Iff.rfl))
  , proved "increment-only-counter" Instances.FlatCounters.iocVerified
      (provedTotal Guarded.SimplePorts.iocCertificate (fun _ _ => Iff.rfl))
  , proved "pn-counter" Instances.FlatCounters.pnVerified
      (provedTotal Guarded.SimplePorts.pnCertificate (fun _ _ => Iff.rfl))
  , proved "flat-grow-only-set" Instances.FlatGrowOnly.gosetVerified
      (provedTotal Guarded.SimplePorts.booleanSetCertificate (fun _ _ => Iff.rfl))
  , proved "flat-grow-only-map" Instances.FlatGrowOnly.gomapVerified
      (provedTotal Guarded.SimplePorts.booleanMapCertificate (fun _ _ => Iff.rfl))
  , proved "bounded-counter" Instances.BoundedCounter.verified
      (provedScoped Guarded.ScopedPorts.boundedCertificate (fun _ _ => Iff.rfl))
  , proved "lww-register" Instances.LWWRegister.verified
      (provedScoped LWW.GuardedPort.certificate (fun _ _ => Iff.rfl))
  , proved "rga" Instances.RGA.verified (provedScoped Guarded.ScopedPorts.rgaCertificate (fun _ _ => Iff.rfl))
  , blocked "embed-rga" (Instances.ProductionRGA.embed (α := Nat) unaryCode)
      (GuardedRGAObstructions.embedded_no_laws unaryCode)
  , blocked "sided-embed-rga" (Instances.ProductionRGA.sided unaryCode)
      (GuardedRGAObstructions.Sided.no_laws unaryCode)
  , blocked "peritext-embed-rga" (Instances.Peritext.verified unaryCode)
      (GuardedRGAObstructions.peritext_no_laws unaryCode)
  , blocked "sided-peritext-core" (Instances.SidedPeritext.verified unaryCode)
      (GuardedRGAObstructions.SidedPeritext.core_no_laws unaryCode)
  , blocked "sided-peritext-rich-core" (Instances.SidedPeritext.richVerified unaryCode)
      (GuardedRGAObstructions.SidedPeritext.rich_no_laws unaryCode)
  , proved "tree-move" Instances.TreeMove.verified (provedScoped Guarded.ScopedPorts.treeCertificate (fun _ _ => Iff.rfl))
  , proved "aegis-sheet" Instances.AegisSheet.verified (provedScoped Guarded.ScopedPorts.sheetCertificate (fun _ _ => Iff.rfl))
  , proved "efficient-or-set" (Instances.EfficientORSet.verified (α := Nat))
      (provedScoped (EfficientORSet.RawCertificate.certificate (α := Nat)) (fun _ _ => Iff.rfl))
  , blocked "queue" Instances.Queue.verified GuardedQueueMVR.Queue.no_laws
  , blocked "mvr" Instances.MVRLive.verified GuardedQueueMVR.MVR.no_laws
  , blocked "fugue-max" (Instances.SidedEmbedRGA.FugueMax.verified unaryCode)
      (GuardedRGAObstructions.RegisteredFugueMax.no_laws unaryCode)
  ]

/-- Equality of complete packages checks carriers, names, original production
certificates, and issuance predicates, not just a textual inventory. -/
theorem packages_eq_production : inventory.map Entry.original = Production.registry := rfl

theorem every_production_entry (original : PackagedMRDT)
    (member : original ∈ Production.registry) :
    ∃ entry ∈ inventory, entry.original = original := by
  rw [← packages_eq_production] at member
  exact List.mem_map.mp member

noncomputable def tags : List Tag := inventory.map (fun e => e.disposition.tag)

theorem inventory_length : inventory.length = 22 := rfl

theorem counts :
    (tags.filter (· == .proved)).length = 14 ∧
    (tags.filter (· == .blocked)).length = 8 := by decide

/-- Additional exact-paper OR-set; the production registry remains unchanged. -/
noncomputable def exactORSet : ProvedResult (ORSet.D Nat) (ORSet.issuance Nat) :=
  provedScoped (ORSet.RawExecution.certificate (α := Nat)) (fun _ _ => Iff.rfl)

noncomputable def names : List String := inventory.map (fun e => e.original.name)
theorem names_eq_production : names = Production.names := rfl
theorem exactORSet_not_registry : "exact-paper-or-set" ∉ names := by decide

end Sal.MRDTs.Paper1.GuardedCoverage
