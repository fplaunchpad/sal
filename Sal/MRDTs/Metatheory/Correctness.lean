import Sal.MRDTs.Metatheory.CertifiedAdequacy
import Sal.MRDTs.Metatheory.Join.RA_Lin_Of_Join

/-! Observable correctness target for ternary MRDT configurations. -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- Every registered version is the datatype fold of a linearization of its
event set respecting the generic MRDT arbitration order. -/
def IsRALinearizable (D : MRDTSig) (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (Sal.MRDTs.Foundation.lo C.core) ∧
      applySeq D.toCRDTSig D.init π = s

theorem isRALinearizable_iff_join (D : MRDTSig) (C : Configuration D) :
    IsRALinearizable D C ↔ IsRALinearizableJoin C := Iff.rfl

/-- End-to-end convergence for executions certified by the public generation
contract.  Datatype-specific Join proofs may consume `G.History` internally;
`MintCertifiedReach` ensures the bridge is available throughout the trace. -/
structure ConvergenceCertificate (D : MRDTSig) (G : GenerationContract D) where
  sound : ∀ {C}, MintCertifiedReach D G C → IsRALinearizable D C
  soundV : ∀ {C},
    MintCertifiedReachV D (canonicalVirtualLCA D) G C → IsRALinearizable D C

/-- Complete implementer-supplied verification package.  The framework does
not identify generation history, convergence history, and sequential honesty;
the implementer supplies the necessary bridges explicitly. -/
structure VerifiedMRDT (D : MRDTSig) where
  generation : GenerationContract D
  convergence : ConvergenceCertificate D generation
  Spec : SequentialSpec (Op D.AppOp)
  sequential : SequentialRefinement D Spec
  sequential_of_mint : ∀ ops,
    LinearMintHistory D generation.Guard ops → sequential.Honest ops
  safety : SafetyCertificate D (canonicalVirtualLCA D) generation

namespace VerifiedMRDT

variable {D : MRDTSig} (V : VerifiedMRDT D)

theorem converges {C : Configuration D}
    (h : MintCertifiedReach D V.generation C) :
    IsRALinearizable D C :=
  V.convergence.sound h

theorem convergesV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualLCA D) V.generation C) :
    IsRALinearizable D C :=
  V.convergence.soundV h

theorem sequentially_correct (ops : List (Op D.AppOp))
    (h : LinearMintHistory D V.generation.Guard ops) :
    V.sequential.Rel (applySeq D.toCRDTSig D.init ops) (V.Spec.run ops) :=
  V.sequential.sound ops (V.sequential_of_mint ops h)

end VerifiedMRDT

end Sal.MRDTs
