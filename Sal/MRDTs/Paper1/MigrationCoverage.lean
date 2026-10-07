import Sal.MRDTs.Metatheory.ProductionLedger
import Sal.MRDTs.Paper1.SimpleEventPorts
import Sal.MRDTs.Paper1.BoundedCounterEvent
import Sal.MRDTs.Paper1.TreeSheetEventSpec
import Sal.MRDTs.Paper1.RGAEventMigration
import Sal.MRDTs.Paper1.RGAEmbeddingObstructions
import Sal.MRDTs.Paper1.PolicyObstructions
import Sal.MRDTs.Paper1.EfficientORSetEventSpec
import Sal.MRDTs.Paper1.ORSetEventSpec

/-! Exhaustive typed coverage of the unchanged production registry. A positive
entry carries the restricted laws and the independent full-input history
criterion for that exact signature and its original issuer. A negative entry
rules out every operation policy satisfying the restricted laws. LWW is the
single explicit exclusion. Auxiliary direct results do not alter these verdicts.
-/
namespace Sal.MRDTs.Paper1.MigrationCoverage
open Foundation
open Sal.EmbedRGA

structure CompatibleResult (D : MRDTSig) (I : Issuance D) where
  policy : OperationPolicy D.AppOp
  spec : HistorySpec (Op D.AppOp) D.Query D.Value
  laws : RestrictedLaws D.toUpdateSig policy
  correct : EventCertifiedSpecificationRAV D policy spec I

inductive Disposition (original : PackagedMRDT) where
  | compatible (result : CompatibleResult original.D original.certificate.issuance)
  | incompatible (impossible : ¬ ∃ P : OperationPolicy original.D.AppOp,
      RestrictedLaws original.D.toUpdateSig P)
  | excludedLWW (exactEntry : original =
      PackagedMRDT.of "lww-register" Instances.LWWRegister.verified)

structure Entry where
  original : PackagedMRDT
  disposition : Disposition original

inductive Tag where
  | compatible | incompatible | excludedLWW
  deriving DecidableEq

def Disposition.tag {original : PackagedMRDT} : Disposition original → Tag
  | .compatible _ => .compatible
  | .incompatible _ => .incompatible
  | .excludedLWW _ => .excludedLWW

noncomputable def compatible (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D) (result : CompatibleResult D original.issuance) : Entry :=
  ⟨PackagedMRDT.of name original, .compatible result⟩

noncomputable def incompatible (name : String) {D : MRDTSig}
    (original : VerifiedMRDT D)
    (impossible : ¬ ∃ P : OperationPolicy D.AppOp, RestrictedLaws D.toUpdateSig P) : Entry :=
  ⟨PackagedMRDT.of name original, .incompatible impossible⟩

/-- Order, names, carriers, certificates, and issuers follow the production
registry exactly. Definitional checking ties each result to its original issuer.
-/
noncomputable def inventory : List Entry :=
  [ compatible "grow-only-set" Instances.GSet.verified
      ⟨SimpleEventPorts.emptyPolicy Nat, SimpleEventPorts.setMachine.toSpec,
        SimpleEventPorts.Add.laws, SimpleEventPorts.gsetCertifiedV⟩
  , compatible "add-store" (Instances.AddStore.verified (α := Nat))
      ⟨SimpleEventPorts.emptyPolicy Nat, SimpleEventPorts.setMachine.toSpec,
        SimpleEventPorts.Add.laws, SimpleEventPorts.gsetCertifiedV⟩
  , compatible "finite-add-store" (Instances.FinsetStore.verified (α := Nat))
      ⟨SimpleEventPorts.emptyPolicy Nat, SimpleEventPorts.finiteMachine.toSpec,
        SimpleEventPorts.Finite.laws, SimpleEventPorts.finiteAddCertifiedV⟩
  , compatible "counter" Instances.FlatCounters.counterVerified
      ⟨SimpleEventPorts.emptyPolicy Unit, (SimpleEventPorts.deltaMachine (fun _ => 1)).toSpec,
        SimpleEventPorts.Delta.laws (fun _ => 1), SimpleEventPorts.counterCertifiedV⟩
  , compatible "increment-only-counter" Instances.FlatCounters.iocVerified
      ⟨SimpleEventPorts.emptyPolicy Instances.FlatCounters.IOCOp,
        (SimpleEventPorts.deltaMachine (fun _ => 1)).toSpec,
        SimpleEventPorts.Delta.laws (fun _ => 1), SimpleEventPorts.iocCertifiedV⟩
  , compatible "pn-counter" Instances.FlatCounters.pnVerified
      ⟨SimpleEventPorts.emptyPolicy Instances.FlatCounters.PNOp,
        (SimpleEventPorts.deltaMachine Instances.FlatCounters.pnDelta).toSpec,
        SimpleEventPorts.Delta.laws Instances.FlatCounters.pnDelta,
        SimpleEventPorts.pnCertifiedV⟩
  , compatible "flat-grow-only-set" Instances.FlatGrowOnly.gosetVerified
      ⟨SimpleEventPorts.emptyPolicy Nat, SimpleEventPorts.booleanMachine.toSpec,
        SimpleEventPorts.Boolean.laws, SimpleEventPorts.booleanSetCertifiedV⟩
  , compatible "flat-grow-only-map" Instances.FlatGrowOnly.gomapVerified
      ⟨SimpleEventPorts.emptyPolicy (Nat × Nat), SimpleEventPorts.booleanMachine.toSpec,
        SimpleEventPorts.Boolean.laws, SimpleEventPorts.booleanMapCertifiedV⟩
  , compatible "bounded-counter" Instances.BoundedCounter.verified
      ⟨BoundedCounterEvent.policy, BoundedCounterEvent.spec,
        BoundedCounterEvent.laws, BoundedCounterEvent.certifiedV⟩
  , ⟨PackagedMRDT.of "lww-register" Instances.LWWRegister.verified, .excludedLWW rfl⟩
  , compatible "rga" Instances.RGA.verified
      ⟨RGA.emptyPolicy, RGA.EventSpec.spec, RGA.restrictedLaws, RGA.EventMigration.certifiedV⟩
  , incompatible "embed-rga" (Instances.ProductionRGA.embed (α := Nat) unaryCode)
      (RGA.EmbeddingObstructions.Embedded.no_restricted_policy unaryCode)
  , incompatible "sided-embed-rga" (Instances.ProductionRGA.sided unaryCode)
      (RGA.EmbeddingObstructions.Sided.no_restricted_policy unaryCode)
  , incompatible "peritext-embed-rga" (Instances.Peritext.verified unaryCode)
      (RGA.EmbeddingObstructions.peritext_no_restricted_policy unaryCode)
  , incompatible "sided-peritext-core" (Instances.SidedPeritext.verified unaryCode)
      (RGA.EmbeddingObstructions.SidedPeritext.core_no_restricted_policy unaryCode)
  , incompatible "sided-peritext-rich-core" (Instances.SidedPeritext.richVerified unaryCode)
      (RGA.EmbeddingObstructions.SidedPeritext.rich_no_restricted_policy unaryCode)
  , compatible "tree-move" Instances.TreeMove.verified
      ⟨commutingPolicy Instances.TreeMove.D.AppOp, TreeMoveEvent.spec,
        TreeMoveEvent.restricted, TreeMoveEvent.certifiedV⟩
  , compatible "aegis-sheet" Instances.AegisSheet.verified
      ⟨commutingPolicy Instances.AegisSheet.D.AppOp, AegisSheetEvent.spec,
        AegisSheetEvent.restricted, AegisSheetEvent.certifiedV⟩
  , incompatible "efficient-or-set" (Instances.EfficientORSet.verified (α := Nat))
      (by rintro ⟨P,laws⟩; exact EfficientORSet.EventSpec.restrictedLaws_impossible 0 P laws)
  , incompatible "queue" Instances.Queue.verified PolicyObstructions.Queue.no_restricted_policy
  , incompatible "mvr" Instances.MVRLive.verified PolicyObstructions.MVR.no_restricted_policy
  , incompatible "fugue-max" (Instances.SidedEmbedRGA.FugueMax.verified unaryCode)
      (RGA.EmbeddingObstructions.RegisteredFugueMax.no_restricted_policy unaryCode)
  ]

/-- Equality of full packages prevents a name-only coverage claim from hiding
a changed carrier, changed issuer, or replacement production certificate. -/
theorem packages_eq_production : inventory.map Entry.original = Production.registry := by rfl

noncomputable def names : List String := inventory.map (fun e => e.original.name)

theorem names_eq_production : names = Production.names := by rfl

theorem every_production_entry (original : PackagedMRDT)
    (member : original ∈ Production.registry) :
    ∃ e ∈ inventory, e.original = original := by
  rw [← packages_eq_production] at member
  exact List.mem_map.mp member

noncomputable def count (tag : Tag) : Nat :=
  (inventory.filter (fun e => e.disposition.tag == tag)).length

theorem counts : inventory.length = 22 ∧ count .compatible = 12 ∧
    count .incompatible = 9 ∧ count .excludedLWW = 1 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The exact paper OR-set is an additional compatible datatype, not a
replacement for the registered EfficientORSet carrier. -/
def exactORSet : CompatibleResult (ORSet.D Nat) (ORSet.issuance Nat) :=
  ⟨ORSet.conflict Nat, ORSet.EventSpec.spec Nat, ORSet.restrictedLaws,
    ORSet.EventSpec.certifiedVersionsRAV⟩

theorem exactORSet_not_registry : "exact-paper-or-set" ∉ names := by decide +kernel

/-- EfficientORSet has a direct full-input history theorem even though it
cannot inhabit the restricted sufficient-condition interface. This result is
kept separate and supplies no `RestrictedLaws` field. -/
theorem efficient_direct :
    EventCertifiedSpecificationRAV (Instances.EfficientORSet.D Nat)
      (EfficientORSet.EventSpec.conflict Nat) (EfficientORSet.EventSpec.spec Nat)
      Instances.EfficientORSet.issuance := EfficientORSet.EventSpec.certifiedVersionsRAV

#print axioms packages_eq_production
#print axioms counts
#print axioms exactORSet
#print axioms efficient_direct
end Sal.MRDTs.Paper1.MigrationCoverage
