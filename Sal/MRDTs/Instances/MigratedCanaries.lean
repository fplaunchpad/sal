import Sal.MRDTs.Metatheory.LegacyBridge
import Sal.ConditionedMRDTs.MRDT_Instances.ConsolidatedConditioningCanaries

/-!
# Production canaries on the plain-signature API

These definitions are temporary proof-preserving migrations.  Their public
types mention only `Sal.MRDTs`; the bodies use `LegacyBridge` until the Join
and safety proofs have moved into this tree.
-/

namespace Sal.MRDTs.Instances.Migrated

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

noncomputable def BoundedCounter : MRDTSig :=
  LegacyBridge.signature Sal.ConditionedMRDTs.BC
noncomputable def Queue : MRDTSig :=
  LegacyBridge.signature Sal.ConditionedMRDTs.Q

noncomputable def boundedCounter : VerifiedMRDT BoundedCounter :=
  LegacyBridge.verified Sal.ConditionedMRDTs.BC (fun _ => trivial)
    Sal.ConditionedMRDTs.boundedCounterGenerationVerified.toUnified
    Sal.ConditionedMRDTs.boundedCounterGenerationVerified.sequential_of_mint

noncomputable def queue : VerifiedMRDT Queue :=
  LegacyBridge.verified Sal.ConditionedMRDTs.Q (fun _ => trivial)
    Sal.ConditionedMRDTs.queueGenerationVerified.toUnified
    Sal.ConditionedMRDTs.queueGenerationVerified.sequential_of_mint

noncomputable def EmbedRGA {α : Type} [DecidableEq α] [Inhabited α]
    (Γ : OrderedPrefixCode) : MRDTSig :=
  LegacyBridge.signature (Sal.ConditionedMRDTs.E Γ α)

noncomputable def embedRGA {α : Type} [DecidableEq α] [Inhabited α]
    (Γ : OrderedPrefixCode) : VerifiedMRDT (EmbedRGA (α := α) Γ) :=
  LegacyBridge.verified (Sal.ConditionedMRDTs.E Γ α) (fun _ => trivial)
    (Sal.ConditionedMRDTs.embedGenerationVerified (α := α) Γ).toUnified
    (Sal.ConditionedMRDTs.embedGenerationVerified
      (α := α) Γ).sequential_of_mint

noncomputable def SidedEmbedRGA (Γ : OrderedPrefixCode) : MRDTSig :=
  LegacyBridge.signature (Sal.ConditionedMRDTs.S Γ)

noncomputable def sidedEmbedRGA (Γ : OrderedPrefixCode) :
    VerifiedMRDT (SidedEmbedRGA Γ) :=
  LegacyBridge.verified (Sal.ConditionedMRDTs.S Γ) (fun _ => trivial)
    (Sal.ConditionedMRDTs.sidedGenerationVerified Γ).toUnified
    (Sal.ConditionedMRDTs.sidedGenerationVerified Γ).sequential_of_mint

noncomputable def PeritextEmbedRGA (Γ : OrderedPrefixCode) : MRDTSig :=
  LegacyBridge.signature
    (Sal.ConditionedMRDTs.E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)

noncomputable def peritextEmbedRGA (Γ : OrderedPrefixCode) :
    VerifiedMRDT (PeritextEmbedRGA Γ) :=
  LegacyBridge.verified
    (Sal.ConditionedMRDTs.E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt)
    (fun _ => trivial)
    (Sal.ConditionedMRDTs.peritextEmbedGenerationVerified Γ).toUnified
    (Sal.ConditionedMRDTs.peritextEmbedGenerationVerified Γ).sequential_of_mint

#print axioms boundedCounter
#print axioms queue
#print axioms embedRGA
#print axioms sidedEmbedRGA
#print axioms peritextEmbedRGA

end Sal.MRDTs.Instances.Migrated
