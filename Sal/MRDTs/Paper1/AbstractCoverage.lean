import Sal.MRDTs.Paper1.MigrationCoverage
import Sal.MRDTs.Paper1.SimpleAbstractPorts
import Sal.MRDTs.Paper1.GuardedAbstractPorts
import Sal.MRDTs.Paper1.RGAAbstractPort
import Sal.MRDTs.Paper1.EfficientVCExecution
import Sal.MRDTs.Paper1.ObservationalObstructions
import Sal.MRDTs.Paper1.ObservationalObstructionsRGA

/-! Historical uniform-law coverage; `GuardedCoverage` is the current guarded
registry classification. This inventory keeps the production signatures and issuers unchanged.
Positive results carry a checked sufficient-condition instance, including the
chosen history bridge. Negative results quantify over every semantic model,
not just the particular abstraction selected by a port. -/
namespace Sal.MRDTs.Paper1.AbstractCoverage
open Foundation AbstractMRDT

inductive ProofRoute {D : MRDTSig} (A : Model D) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (I : Issuance D) where
  | total (conditions : VCConditions A P S I)
  | issued (conditions : ScopedVCConditions A P S I)

structure ProvedResult (D : MRDTSig) (I : Issuance D) where
  model : Model D
  policy : OperationPolicy D.AppOp
  spec : HistorySpec (Op D.AppOp) D.Query D.Value
  route : ProofRoute model policy spec I

def provedTotal {D : MRDTSig} {I : Issuance D} {A : Model D}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    (conditions : VCConditions A P S I) : ProvedResult D I :=
  ⟨A,P,S,.total conditions⟩

def provedScoped {D : MRDTSig} {I : Issuance D} {A : Model D}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    (conditions : ScopedVCConditions A P S I) : ProvedResult D I :=
  ⟨A,P,S,.issued conditions⟩

theorem ProvedResult.versionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    AbstractMRDT.VersionsRALinearizable result.model result.policy result.spec C := by
  cases result.route with
  | total conditions => exact conditions.toCertificate.versionsV reach
  | issued conditions => exact conditions.versionsV reach

theorem ProvedResult.executionsV {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTSV D I).Execution (initConfig D) trace) :
    ExecutionCorrect result.model result.policy result.spec trace := by
  cases result.route with
  | total conditions => exact conditions.executionsV trace run
  | issued conditions => exact conditions.executionsV trace run

theorem ProvedResult.executions {D : MRDTSig} {I : Issuance D}
    (result : ProvedResult D I) (trace : List (Label D × Configuration D))
    (run : (certifiedTS D I).Execution (initConfig D) trace) :
    ExecutionCorrect result.model result.policy result.spec trace := by
  cases result.route with
  | total conditions => exact conditions.executions trace run
  | issued conditions => exact conditions.executions trace run

inductive Disposition (original : PackagedMRDT) where
  | proved (result : ProvedResult original.D original.certificate.issuance)
  | blocked (impossible : ∀ A : Model original.D,
      ¬ ∃ P : OperationPolicy original.D.AppOp, Laws A P)
  | excludedLWW (exactEntry : original =
      PackagedMRDT.of "lww-register" Instances.LWWRegister.verified)

structure Entry where
  original : PackagedMRDT
  disposition : Disposition original

inductive Tag where
  | proved | blocked | excludedLWW
  deriving DecidableEq

def Disposition.tag {original : PackagedMRDT} : Disposition original → Tag
  | .proved _ => .proved
  | .blocked _ => .blocked
  | .excludedLWW _ => .excludedLWW

noncomputable def proved (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D) (result : ProvedResult D original.issuance) : Entry :=
  ⟨PackagedMRDT.of name original,.proved result⟩

noncomputable def blocked (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D)
    (impossible : ∀ A : Model D, ¬ ∃ P : OperationPolicy D.AppOp, Laws A P) : Entry :=
  ⟨PackagedMRDT.of name original,.blocked impossible⟩

open Sal.EmbedRGA

noncomputable def inventory : List Entry :=
  [ proved "grow-only-set" Instances.GSet.verified
      (provedTotal SimplePorts.gsetConditions)
  , proved "add-store" (Instances.AddStore.verified (α := Nat))
      (provedTotal SimplePorts.addStoreConditions)
  , proved "finite-add-store" (Instances.FinsetStore.verified (α := Nat))
      (provedTotal SimplePorts.finiteAddConditions)
  , proved "counter" Instances.FlatCounters.counterVerified
      (provedTotal SimplePorts.counterConditions)
  , proved "increment-only-counter" Instances.FlatCounters.iocVerified
      (provedTotal SimplePorts.iocConditions)
  , proved "pn-counter" Instances.FlatCounters.pnVerified
      (provedTotal SimplePorts.pnConditions)
  , proved "flat-grow-only-set" Instances.FlatGrowOnly.gosetVerified
      (provedTotal SimplePorts.booleanSetConditions)
  , proved "flat-grow-only-map" Instances.FlatGrowOnly.gomapVerified
      (provedTotal SimplePorts.booleanMapConditions)
  , proved "bounded-counter" Instances.BoundedCounter.verified
      (provedScoped GuardedPorts.Bounded.conditions)
  , ⟨PackagedMRDT.of "lww-register" Instances.LWWRegister.verified,.excludedLWW rfl⟩
  , proved "rga" Instances.RGA.verified (provedScoped RGA.AbstractPort.conditions)
  , blocked "embed-rga" (Instances.ProductionRGA.embed (α := Nat) unaryCode)
      (ObservationalObstructions.Embedded.no_laws unaryCode)
  , blocked "sided-embed-rga" (Instances.ProductionRGA.sided unaryCode)
      (ObservationalObstructions.Sided.no_laws unaryCode)
  , blocked "peritext-embed-rga" (Instances.Peritext.verified unaryCode)
      (ObservationalObstructions.peritext_no_laws unaryCode)
  , blocked "sided-peritext-core" (Instances.SidedPeritext.verified unaryCode)
      (ObservationalObstructions.SidedPeritext.core_no_laws unaryCode)
  , blocked "sided-peritext-rich-core" (Instances.SidedPeritext.richVerified unaryCode)
      (ObservationalObstructions.SidedPeritext.rich_no_laws unaryCode)
  , proved "tree-move" Instances.TreeMove.verified (provedScoped GuardedPorts.Tree.conditions)
  , proved "aegis-sheet" Instances.AegisSheet.verified (provedScoped GuardedPorts.Sheet.conditions)
  , proved "efficient-or-set" (Instances.EfficientORSet.verified (α := Nat))
      (provedTotal EfficientORSet.AbstractSpec.vcConditions)
  , blocked "queue" Instances.Queue.verified ObservationalObstructions.Queue.no_laws
  , blocked "mvr" Instances.MVRLive.verified ObservationalObstructions.MVR.no_laws
  , blocked "fugue-max" (Instances.SidedEmbedRGA.FugueMax.verified unaryCode)
      (ObservationalObstructions.RegisteredFugueMax.no_laws unaryCode)
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

theorem counts :
    (tags.filter (· == .proved)).length = 13 ∧
    (tags.filter (· == .blocked)).length = 8 ∧
    (tags.filter (· == .excludedLWW)).length = 1 := by decide

end Sal.MRDTs.Paper1.AbstractCoverage
