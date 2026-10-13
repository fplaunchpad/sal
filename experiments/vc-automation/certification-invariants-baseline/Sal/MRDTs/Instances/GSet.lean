import Sal.MRDTs.Instances.AddStore

/-!
# Grow-only set

The Nat grow-only set is the concrete specialization of the generic
`AddStore` proof. Keeping this module as aliases avoids a second, weaker
implementation of the same datatype.
-/

namespace Sal.MRDTs.Instances.GSet

open Sal.MRDTs.Foundation

noncomputable abbrev D : MRDTSig := AddStore.D Nat

abbrev generation : Issuance D := AddStore.generation
abbrev replayAdequacy : ReplayAdequacyCertificate D generation :=
  AddStore.replayAdequacy
abbrev spec : SequentialSpec D := AddStore.spec
abbrev sequential : SequentialRefinement D spec.toSequentialMachine :=
  AddStore.sequential

def safety : SafetyCertificate D (canonicalVirtualMergeBase D) generation where
  Safe := fun _ => True
  Observable := fun _ => True
  preservationV := fun _ _ _ _ _ => trivial
  consequence := fun _ _ => trivial

noncomputable def verified : VerifiedMRDT D := AddStore.verified

#print axioms sequential
#print axioms verified

end Sal.MRDTs.Instances.GSet
