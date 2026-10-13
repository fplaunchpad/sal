import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.DistinctOperationReplay

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT

abbrev D : MRDTSig where
  State := Nat
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  update := fun _ e => e.time
  merge := fun _ x y => max x y
  Query := Unit
  Value := Nat
  query := fun s _ => s

def a : Op Unit := (1,0,())
def b : Op Unit := (2,1,())
def issuance : Issuance D := ⟨fun e s => (e = a ∨ e = b) ∧ s = 0⟩

def P : OperationPolicy Unit := ⟨fun _ _ => False⟩

def Good (C : ReplayContext D.toUpdateSig) : Prop :=
  (∀ x y, ¬ C.vis x y) ∧ (∀ e ∈ C.events, e = a ∨ e = b)

def R (C : ReplayContext D.toUpdateSig) (E : Set (Op Unit)) (s : Nat) : Prop :=
  Good C ∧ Supported C E ∧
  ((E = ∅ ∧ s = 0) ∨ (E = {a} ∧ s = 1) ∨
   (E = {b} ∧ s = 2) ∨ (E = {a,b} ∧ s = 2))

theorem laws : DistinctOperationReplay.Laws D.toUpdateSig P where
  noncomm_exact x y ne := False.elim (ne (Subsingleton.elim _ _))
  no_chain := by intros; simp [P]
  conditional_commutation := by intros; simp [P] at *

end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
