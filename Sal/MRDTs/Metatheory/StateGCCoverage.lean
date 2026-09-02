import Sal.MRDTs.Metatheory.ProductionLedger
import Sal.MRDTs.Instances.TreeMoveGC
import Sal.MRDTs.Instances.SidedPeritextProtocol

/-!
# Typed datatype-state GC coverage

Every production package receives an explicit state-GC classification.  The
classification separates an exact-state preservation baseline from a
collector that actually changes a physical representation.  In particular,
`exactState` is not evidence of reclamation.
-/

namespace Sal.MRDTs

/-- Evidence status for datatype-state collection of one verified signature.

* `exactState` records that the current design uses its semantic state as its
  physical state and supplies only the non-collecting baseline certificate.
* `collecting` packages a representation-changing `StateGCCertificate`.
* `operational` packages a representation-changing `StateGCProtocol` for
  ordinary and virtual-merge-base execution.
* `staged` records a known collection obligation with only the exact-state
  baseline currently proved.
-/
inductive StateGCCoverage (D : MRDTSig) (I : Issuance D) where
  | exactState (baseline : StateGCCertificate D I)
  | collecting (certificate : StateGCCertificate D I)
  | operational
      (protocol : ∀ V : VirtualMergeBaseResolver D, StateGCProtocol D V)
  | staged (baseline : StateGCCertificate D I)

inductive StateGCCoverage.Kind where
  | exactState
  | collecting
  | operational
  | staged
deriving DecidableEq, Repr

def StateGCCoverage.kind {D : MRDTSig} {I : Issuance D} :
    StateGCCoverage D I → StateGCCoverage.Kind
  | .exactState _ => .exactState
  | .collecting _ => .collecting
  | .operational _ => .operational
  | .staged _ => .staged

/-- A production package paired with its datatype-state GC evidence status. -/
structure PackagedStateGC where
  package : PackagedMRDT
  coverage : StateGCCoverage package.D package.certificate.issuance

namespace PackagedStateGC

noncomputable def ofExactState (name : String) {D : MRDTSig}
    (verified : VerifiedMRDT D) : PackagedStateGC where
  package := PackagedMRDT.of name verified
  coverage := .exactState (StateGCCertificate.exactState D verified.issuance)

noncomputable def ofCollector (name : String) {D : MRDTSig}
    (verified : VerifiedMRDT D)
    (certificate : StateGCCertificate D verified.issuance) :
    PackagedStateGC where
  package := PackagedMRDT.of name verified
  coverage := .collecting certificate

noncomputable def ofProtocol (name : String) {D : MRDTSig}
    (verified : VerifiedMRDT D)
    (protocol : ∀ V : VirtualMergeBaseResolver D, StateGCProtocol D V) :
    PackagedStateGC where
  package := PackagedMRDT.of name verified
  coverage := .operational protocol

noncomputable def ofStaged (name : String) {D : MRDTSig}
    (verified : VerifiedMRDT D) : PackagedStateGC where
  package := PackagedMRDT.of name verified
  coverage := .staged (StateGCCertificate.exactState D verified.issuance)

end PackagedStateGC

namespace Production.StateGC

open Sal.EmbedRGA

/-- Datatype-state GC coverage in exactly the order of `Production.registry`.
The two staged entries are tombstone RGA and OR-Set. -/
noncomputable def registry : List PackagedStateGC :=
  [ PackagedStateGC.ofExactState "grow-only-set" Instances.GSet.verified
  , PackagedStateGC.ofExactState "add-store"
      (Instances.AddStore.verified (α := Nat))
  , PackagedStateGC.ofExactState "finite-add-store"
      (Instances.FinsetStore.verified (α := Nat))
  , PackagedStateGC.ofExactState "counter"
      Instances.FlatCounters.counterVerified
  , PackagedStateGC.ofExactState "increment-only-counter"
      Instances.FlatCounters.iocVerified
  , PackagedStateGC.ofExactState "pn-counter"
      Instances.FlatCounters.pnVerified
  , PackagedStateGC.ofExactState "flat-grow-only-set"
      Instances.FlatGrowOnly.gosetVerified
  , PackagedStateGC.ofExactState "flat-grow-only-map"
      Instances.FlatGrowOnly.gomapVerified
  , PackagedStateGC.ofExactState "bounded-counter"
      Instances.BoundedCounter.verified
  , PackagedStateGC.ofStaged "rga" Instances.RGA.verified
  , PackagedStateGC.ofExactState "embed-rga"
      (Instances.ProductionRGA.embed (α := Nat) unaryCode)
  , PackagedStateGC.ofExactState "sided-embed-rga"
      (Instances.ProductionRGA.sided unaryCode)
  , PackagedStateGC.ofExactState "peritext-embed-rga"
      (Instances.Peritext.verified unaryCode)
  , PackagedStateGC.ofExactState "sided-peritext-core"
      (Instances.SidedPeritext.verified unaryCode)
  , PackagedStateGC.ofProtocol "sided-peritext-rich-core"
      (Instances.SidedPeritext.richVerified unaryCode)
      (Instances.SidedPeritext.StateGC.Protocol.protocol unaryCode)
  , PackagedStateGC.ofProtocol "tree-move" Instances.TreeMove.verified
      Instances.TreeMove.GC.protocol
  , PackagedStateGC.ofCollector "aegis-sheet"
      Instances.AegisSheet.verified Instances.AegisSheet.GC.certificate
  , PackagedStateGC.ofStaged "or-set"
      (Instances.ORSet.verified (α := Nat))
  ]

noncomputable def names : List String :=
  registry.map (fun entry => entry.package.name)

example : registry.length = 18 := by rfl
example : names = Production.names := by rfl

end Production.StateGC

end Sal.MRDTs
