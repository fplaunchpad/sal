import Sal.MRDTs.Metatheory.Correctness

/-! Focused controls for the single public `rc` policy. -/

namespace Sal.MRDTs.Instances.RcSPOT

open Sal.MRDTs.Foundation

namespace LWW

def D : MRDTSig where
  State := Nat
  dec_state := inferInstance
  init := 0
  AppOp := Nat
  dec_op := inferInstance
  Query := Unit
  Value := Nat
  update _ e := e.2.2
  query s _ := s
  merge _ a b := max a b

def rc : ReplayPolicy D.toUpdateSig where
  order e₁ e₂ :=
    if e₁.time < e₂.time then .Fst_then_snd
    else if e₂.time < e₁.time then .Snd_then_fst
    else .Either

def w₁ : Op Nat := (1, 0, 10)
def w₂ : Op Nat := (2, 1, 20)
def w₃ : Op Nat := (3, 2, 30)

example : rc.order w₁ w₂ = .Fst_then_snd ∧
    rc.order w₂ w₃ = .Fst_then_snd := by
  simp [rc, w₁, w₂, w₃, Op.time]

/-- Acyclic timestamp order admits chains, so it refutes the retired
length-two no-chain condition. -/
theorem old_no_chain_refuted :
    ¬ (∀ a b c : Op D.AppOp,
      distinctOps (D := D.toUpdateSig) a b →
      distinctOps (D := D.toUpdateSig) b c →
      ¬ (rc.order a b = .Fst_then_snd ∧
         rc.order b c = .Fst_then_snd)) := by
  intro h
  apply h w₁ w₂ w₃
  · simp [distinctOps, w₁, w₂, Op.time]
  · simp [distinctOps, w₂, w₃, Op.time]
  · simp [rc, w₁, w₂, w₃, Op.time]

end LWW

namespace ObservedRemove

inductive AOp where
  | add
  | remove (observed : Finset Nat)
  deriving DecidableEq

def D : MRDTSig where
  State := Finset Nat × Finset Nat
  dec_state := inferInstance
  init := (∅, ∅)
  AppOp := AOp
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update s e := match e.2.2 with
    | .add => (insert e.time s.1, s.2)
    | .remove observed => (s.1, s.2 ∪ observed)
  query s _ := decide (∃ tag ∈ s.1, tag ∉ s.2)
  merge _ a b := (a.1 ∪ b.1, a.2 ∪ b.2)

def rc : ReplayPolicy D.toUpdateSig := ReplayPolicy.unconstrained _
def add : Op AOp := (2, 0, .add)
def remove : Op AOp := (1, 1, .remove ∅)

example : D.toUpdateSig.commutes add remove := by intro _; rfl
example : rc.order add remove = .Either := rfl

end ObservedRemove

#print axioms LWW.old_no_chain_refuted

end Sal.MRDTs.Instances.RcSPOT
