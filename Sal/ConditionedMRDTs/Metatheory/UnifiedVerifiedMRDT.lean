import Sal.ConditionedMRDTs.Metatheory.VerifiedMRDT
import Sal.ConditionedMRDTs.Metatheory.GenerationContract

/-!
# Unified conditioned certificates

This layer preserves the established `VerifiedMRDT` package while making its
previously external generation and safety assumptions public fields.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- Join correctness, sequential refinement, issuer generation, and client
safety in one public certificate. -/
structure UnifiedVerifiedMRDT (D : ConditionedMRDTSig) where
  verified : VerifiedMRDT D
  generation : GenerationContract D
  history_entails_honest : ∀ C, generation.History C →
    verified.Honest (Configuration.core C)
  safety : SafetyCertificate D generation

namespace UnifiedVerifiedMRDT

variable {D : ConditionedMRDTSig} (V : UnifiedVerifiedMRDT D)

/-- Contract reachability can be weakened pointwise. -/
private theorem mapHonestReach {H K : Configuration D → Prop}
    {hInit : D.Inv D.init} {C : Configuration D}
    (hHK : ∀ C, H C → K C) (h : HonestReach D H hInit C) :
    HonestReach D K hInit C := by
  induction h with
  | init => exact .init
  | step _ hH hs ih => exact ih.step (hHK _ hH) hs

private theorem mapHonestReachV {H K : Configuration D → Prop}
    {hInit : D.Inv D.init} {C : Configuration D}
    (hHK : ∀ C, H C → K C) (h : HonestReachV D H hInit C) :
    HonestReachV D K hInit C := by
  induction h with
  | init => exact .init
  | step _ hH hs ih => exact ih.step (hHK _ hH) hs

/-- The unified RA theorem consumes the explicit mint-provenance execution,
then reuses the existing verified Join certificate unchanged. -/
theorem ra_linearizable {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    IsRALinearizable3 C := by
  apply V.verified.ra_linearizable
  exact mapHonestReach
    (fun C hH => V.history_entails_honest C hH)
    (honestReach_of_mintCertified h)

theorem ra_linearizableV {C : Configuration D}
    (h : MintCertifiedReach3V D V.generation V.verified.initInv C) :
    IsRALinearizable3 C := by
  apply V.verified.ra_linearizableV
  exact mapHonestReachV
    (fun C hH => V.history_entails_honest C hH)
    (honestReachV_of_mintCertified h)

/-- The same execution supplies the separately stated client invariant for
every registered version. -/
theorem safe {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    VersionsSafe V.safety C :=
  V.safety.preservation h

theorem safeV {C : Configuration D}
    (h : MintCertifiedReach3V D V.generation V.verified.initInv C) :
    VersionsSafe V.safety C :=
  V.safety.preservationV h

/-- Every registered version also satisfies the certificate's explicitly
client-facing consequence. -/
theorem observable {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    VersionsObservable V.safety C :=
  versionsObservable_of_safe V.safety (V.safe h)

/-- Composition preserves the old `VerifiedMRDT.prod`; the product generation
and safety laws are explicit arguments because they describe client policy,
not a consequence of the component merge algorithms.  This prevents an
unsound implicit all-enumerations policy for order-sensitive components. -/
def prod {D₁ D₂ : ConditionedMRDTSig}
    (V₁ : UnifiedVerifiedMRDT D₁) (V₂ : UnifiedVerifiedMRDT D₂)
    (G : GenerationContract (prodSig D₁ D₂))
    (hHistory : ∀ C, G.History C →
      V₁.verified.Honest (projCore₁ (Configuration.core C)) ∧
      V₂.verified.Honest (projCore₂ (Configuration.core C)))
    (S : SafetyCertificate (prodSig D₁ D₂) G) :
    UnifiedVerifiedMRDT (prodSig D₁ D₂) where
  verified := VerifiedMRDT.prod V₁.verified V₂.verified
  generation := G
  history_entails_honest := hHistory
  safety := S

end UnifiedVerifiedMRDT

/-! ## Full-closure verified packages

`JoinLemma3F` is not coerced to the stronger plain/weak-closure doctrine.
This sibling package consumes it through the dedicated full-closure adequacy
theorem, preserving the Gate-G1 distinction. -/

structure VerifiedMRDTF (D : ConditionedMRDTSig) where
  initInv : D.Inv D.init
  joinF : JoinLemma3F D
  Spec : SequentialSpec (Op D.AppOp)
  seq : HistorySequentialRefinement D Spec

structure UnifiedVerifiedMRDTF (D : ConditionedMRDTSig) where
  verified : VerifiedMRDTF D
  generation : GenerationContract D
  safety : SafetyCertificate D generation

namespace UnifiedVerifiedMRDTF

variable {D : ConditionedMRDTSig} (V : UnifiedVerifiedMRDTF D)

theorem ra_linearizable {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_joinF V.verified.joinF C
    (rawReach_of_guardedReach (guardedReach_of_mintCertified h))

theorem ra_linearizableV {C : Configuration D}
    (h : MintCertifiedReach3V D V.generation V.verified.initInv C) :
    IsRALinearizable3 C :=
  ra_linearizable3V_of_joinF V.verified.joinF C
    (rawReachV_of_guardedReachV (guardedReachV_of_mintCertified h))

theorem safe {C : Configuration D}
    (h : MintCertifiedReach3 D V.generation V.verified.initInv C) :
    VersionsSafe V.safety C := V.safety.preservation h

theorem sequential (ops : List (Op D.AppOp))
    (h : V.verified.seq.Honest ops) :
    V.verified.seq.Rel (applySeq D.toCRDTSig D.init ops)
      (V.verified.Spec.run ops) :=
  V.verified.seq.sound ops h

end UnifiedVerifiedMRDTF

/-- A neutral safety component for instances whose client-safety invariant is
trivial.  Nontrivial instances such as the bounded counter must not use it. -/
def SafetyCertificate.trivial {D : ConditionedMRDTSig}
    (G : GenerationContract D) : SafetyCertificate D G where
  Safe := fun _ => True
  Observable := fun _ => True
  preservation := by
    intro hInit C h v s E hv
    exact True.intro
  preservationV := by
    intro hInit C h v s E hv
    exact True.intro
  consequence := fun _ _ => True.intro

#print axioms UnifiedVerifiedMRDT.ra_linearizable
#print axioms UnifiedVerifiedMRDT.safe
#print axioms UnifiedVerifiedMRDT.observable

end Sal.ConditionedMRDTs
