import Sal.MRDTs.Instances.GSet
import Sal.MRDTs.Instances.AddStore
import Sal.MRDTs.Instances.FinsetStore
import Sal.MRDTs.Instances.FlatCounters
import Sal.MRDTs.Instances.FlatGrowOnly
import Sal.MRDTs.Instances.BoundedCounter
import Sal.MRDTs.Instances.LWWRegister
import Sal.MRDTs.Instances.RGASequential
import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Instances.Peritext
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.Instances.AegisSheetSequential
import Sal.MRDTs.Instances.ORSet

/-!
# Typed production MRDT registry

Every entry contains a raw signature and a `VerifiedMRDT` for that exact
signature. A raw `MRDTSig`, an issuance/convergence pair, or a
`ReplayAdequateMRDT` cannot enter this list.
-/

namespace Sal.MRDTs.Production

open Sal.EmbedRGA

noncomputable def registry : List PackagedMRDT :=
  [ PackagedMRDT.of "grow-only-set" Instances.GSet.verified
  , PackagedMRDT.of "add-store" (Instances.AddStore.verified (α := Nat))
  , PackagedMRDT.of "finite-add-store"
      (Instances.FinsetStore.verified (α := Nat))
  , PackagedMRDT.of "counter" Instances.FlatCounters.counterVerified
  , PackagedMRDT.of "increment-only-counter"
      Instances.FlatCounters.iocVerified
  , PackagedMRDT.of "pn-counter" Instances.FlatCounters.pnVerified
  , PackagedMRDT.of "flat-grow-only-set"
      Instances.FlatGrowOnly.gosetVerified
  , PackagedMRDT.of "flat-grow-only-map"
      Instances.FlatGrowOnly.gomapVerified
  , PackagedMRDT.of "bounded-counter" Instances.BoundedCounter.verified
  , PackagedMRDT.of "lww-register" Instances.LWWRegister.verified
  , PackagedMRDT.of "rga" Instances.RGA.verified
  , PackagedMRDT.of "embed-rga"
      (Instances.ProductionRGA.embed (α := Nat) unaryCode)
  , PackagedMRDT.of "sided-embed-rga"
      (Instances.ProductionRGA.sided unaryCode)
  , PackagedMRDT.of "peritext-embed-rga"
      (Instances.Peritext.verified unaryCode)
  , PackagedMRDT.of "sided-peritext-core"
      (Instances.SidedPeritext.verified unaryCode)
  , PackagedMRDT.of "sided-peritext-rich-core"
      (Instances.SidedPeritext.richVerified unaryCode)
  , PackagedMRDT.of "tree-move" Instances.TreeMove.verified
  , PackagedMRDT.of "aegis-sheet" Instances.AegisSheet.verified
  , PackagedMRDT.of "or-set"
      (Instances.ORSet.verified (α := Nat))
  ]

noncomputable def names : List String := registry.map PackagedMRDT.name

example : registry.length = 19 := by rfl

#check registry
#check Instances.LWWRegister.verified
#check Instances.ORSet.verified
#check Instances.AegisSheet.verified

end Sal.MRDTs.Production
