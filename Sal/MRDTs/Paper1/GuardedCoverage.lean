import Sal.MRDTs.Metatheory.ProductionLedger
import Sal.MRDTs.Paper1.ConcreteSimplePorts
import Sal.MRDTs.Paper1.GuardedRawEfficientCertificate
import Sal.MRDTs.Paper1.GuardedRawExactExecution
import Sal.MRDTs.Paper1.GuardedQueueMVR
import Sal.MRDTs.Paper1.GuardedRGAObstructions
import Sal.MRDTs.Paper1.GuardedLWWExclusion
import Sal.MRDTs.Paper1.GuardedLWWPort

/-! Typed coverage of the corrected guarded contract. Positive entries carry
checked ordinary and virtual execution routes for the original datatype and
issuer. Blocked entries carry concrete guarded-law impossibility proofs.
LWW has a positive empty-policy certificate; the separate checked exclusion
of its original timestamp policy remains a control, not a datatype verdict. No verdict denotes a
failed or unfinished proof. -/
namespace Sal.MRDTs.Paper1.GuardedCoverage
open Foundation ConcreteMRDT

structure ProvedResult (D : MRDTSig) (I : Issuance D) where
  policy : OperationPolicy D.AppOp
  spec : HistorySpec (Op D.AppOp) D.Query D.Value
  certificate : ScopedCertificate policy spec I

def provedScoped {D : MRDTSig} {I : Issuance D}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    (certificate : ScopedCertificate P S I) : ProvedResult D I :=
  ⟨P,S,certificate⟩

/-- Every positive route exposes the exact concrete replay of the stored state. -/
theorem ProvedResult.storedCanonical {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (execution : CertifiedExecution D I C) {v s E}
    (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E ∧ respects π (paperOrder result.policy C.replayContext E) ∧
      applySeq D.toUpdateSig D.init π = s :=
  result.certificate.canonicalVersions C execution v s E hv

theorem ProvedResult.versions {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (execution : CertifiedExecution D I C) :
    VersionsWitness result.policy result.spec C := result.certificate.versions execution

theorem ProvedResult.versionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    VersionsWitness result.policy result.spec C := result.certificate.versionsV reach

theorem ProvedResult.executionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect result.policy result.spec trace := result.certificate.executionsV trace run

theorem ProvedResult.executions {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect result.policy result.spec trace := result.certificate.executions trace run

inductive Disposition (original : PackagedMRDT) where
  | proved (result : ProvedResult original.D original.certificate.issuance)
  | blocked (impossible : ¬ ∃ P : OperationPolicy original.D.AppOp, GuardedReplay.Laws original.D.toUpdateSig P)

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
    (impossible : ¬ ∃ P : OperationPolicy D.AppOp, GuardedReplay.Laws D.toUpdateSig P) : Entry :=
  ⟨PackagedMRDT.of name original,.blocked impossible⟩

open Sal.EmbedRGA

noncomputable def inventory : List Entry :=
  [ proved "grow-only-set" Instances.GSet.verified
      (provedScoped Guarded.SimplePorts.gsetCertificate)
  , proved "add-store" (Instances.AddStore.verified (α := Nat))
      (provedScoped Guarded.SimplePorts.addStoreCertificate)
  , proved "finite-add-store" (Instances.FinsetStore.verified (α := Nat))
      (provedScoped Guarded.SimplePorts.finiteAddCertificate)
  , proved "counter" Instances.FlatCounters.counterVerified
      (provedScoped Guarded.SimplePorts.counterCertificate)
  , proved "increment-only-counter" Instances.FlatCounters.iocVerified
      (provedScoped Guarded.SimplePorts.iocCertificate)
  , proved "pn-counter" Instances.FlatCounters.pnVerified
      (provedScoped Guarded.SimplePorts.pnCertificate)
  , proved "flat-grow-only-set" Instances.FlatGrowOnly.gosetVerified
      (provedScoped Guarded.SimplePorts.booleanSetCertificate)
  , proved "flat-grow-only-map" Instances.FlatGrowOnly.gomapVerified
      (provedScoped Guarded.SimplePorts.booleanMapCertificate)
  , proved "bounded-counter" Instances.BoundedCounter.verified
      (provedScoped Guarded.ScopedPorts.boundedCertificate)
  , proved "lww-register" Instances.LWWRegister.verified
      (provedScoped LWW.GuardedPort.certificate)
  , proved "rga" Instances.RGA.verified (provedScoped Guarded.ScopedPorts.rgaCertificate)
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
  , proved "tree-move" Instances.TreeMove.verified (provedScoped Guarded.ScopedPorts.treeCertificate)
  , proved "aegis-sheet" Instances.AegisSheet.verified (provedScoped Guarded.ScopedPorts.sheetCertificate)
  , proved "efficient-or-set" (Instances.EfficientORSet.verified (α := Nat))
      (provedScoped (EfficientORSet.RawCertificate.certificate (α := Nat)))
  , blocked "queue" Instances.Queue.verified GuardedQueueMVR.Queue.no_raw_laws
  , blocked "mvr" Instances.MVRLive.verified GuardedQueueMVR.MVR.no_raw_laws
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
  provedScoped (ORSet.RawExecution.certificate (α := Nat))

noncomputable def names : List String := inventory.map (fun e => e.original.name)
theorem names_eq_production : names = Production.names := rfl
theorem exactORSet_not_registry : "exact-paper-or-set" ∉ names := by decide

end Sal.MRDTs.Paper1.GuardedCoverage
