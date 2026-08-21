import Sal.MRDTs.Framework.StateGC

/-! A dependency-free positive control for the new package boundary. -/

namespace Sal.MRDTs.Instances.GSet

open Sal.MRDTs.Foundation
open Classical

noncomputable def D : MRDTSig where
  State := Set Nat
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := ∅
  AppOp := Nat
  dec_op := inferInstance
  Query := Unit
  Value := Set Nat
  update := fun s e => insert e.2.2 s
  merge := (· ∪ ·)
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun _ a b => a ∪ b
  merge_init_slice := fun _ _ => rfl

def generation : GenerationContract D where
  Guard := fun _ _ => True
  History := fun _ => True
  history_of_mint := fun _ _ => trivial

def safety : SafetyCertificate D (canonicalVirtualLCA D) generation where
  Safe := fun _ => True
  Observable := fun _ => True
  preservation := fun _ _ _ _ _ => trivial
  preservationV := fun _ _ _ _ _ => trivial
  consequence := fun _ _ => trivial

def spec : SequentialSpec (Op Nat) where
  State := Set Nat
  init := ∅
  step := fun s e => insert e.2.2 s

def sequential : SequentialRefinement D spec where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := fun _ _ => rfl

#print axioms sequential

end Sal.MRDTs.Instances.GSet
