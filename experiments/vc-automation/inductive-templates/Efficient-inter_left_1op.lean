import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Instances.EfficientORSet

/-! Finite frozen-event equations from Neem's executable F* interface.
Proofs below use only definition unfolding and finite-set membership logic.
No represented-history invariant or previously proved merge VC is used. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace NeemExpansion
open Sal.MRDTs.Foundation

structure Signature where
  State : Type
  AppOp : Type
  init : State
  step : State → Op AppOp → State
  merge : State → State → State → State
  order : Op AppOp → Op AppOp → RcRes

namespace Signature
variable (D : Signature)
def distinct (p q : Op D.AppOp) : Prop := p.1 ≠ q.1
def admissible (p q : Op D.AppOp) : Prop :=
  D.order q p = .Fst_then_snd ∨ D.order q p = .Either
def Q1 (l a b : D.State) (p : Op D.AppOp) : Prop :=
  D.merge l (D.step a p) b = D.step (D.merge l a b) p
def Q2 (l a b : D.State) (p q : Op D.AppOp) : Prop :=
  D.merge l (D.step a p) (D.step b q) = D.step (D.merge l a (D.step b q)) p

def comm : Prop := ∀ l a b, D.merge l a b = D.merge l b a
def idem : Prop := ∀ s, D.merge s s s = s

def base1 : Prop := ∀ p, D.Q1 D.init D.init D.init p
def base2 : Prop := ∀ p q, D.admissible p q → p.2.1 ≠ q.2.1 → D.distinct p q →
  D.Q2 D.init D.init D.init p q

def common1 : Prop := ∀ l p h, D.distinct p h →
  (p.2.1 ≠ h.2.1 ∨ h.1 < p.1) → D.Q1 l l l p →
  D.Q1 (D.step l h) (D.step l h) (D.step l h) p

def common2 : Prop := ∀ l p q h, D.admissible p q → p.2.1 ≠ q.2.1 →
  D.distinct p q → D.distinct p h → D.distinct q h →
  D.Q1 (D.step l h) (D.step l h) (D.step l h) p → D.Q2 l l l p q →
  D.Q2 (D.step l h) (D.step l h) (D.step l h) p q

def zero : Prop := ∀ l a b h,
  D.merge (D.step l h) (D.step a h) (D.step b h) = D.step (D.merge l a b) h

-- Remaining frozen-event schemata: exact F* requires/ensures, no strengthening.
def inter_right_base_2op : Prop := ∀ (l a b : D.State) (o1 o2 ob ol : Op D.AppOp),
  ( (D.order o2 o1 = .Fst_then_snd) ∨ (D.order o2 o1 = .Either) ) ∧ o1.2.1 ≠ o2.2.1 ∧ (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ D.distinct o1 o2 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o2 ob ∧ D.distinct o2 ol ∧ D.distinct ob ol ∧ (((D.merge l ((D.step a o1)) ((D.step b o2)))) = ((D.step ((D.merge l a ((D.step b o2)))) o1))) ∧ (((D.merge l ((D.step a o1)) ((D.step ((D.step b ob)) o2)))) = ((D.step ((D.merge l a ((D.step ((D.step b ob)) o2)))) o1))) ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b ol)) o2)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step ((D.step b ob)) ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step ((D.step b ob)) ol)) o2)))) o1)))

def inter_left_base_2op : Prop := ∀ (l a b : D.State) (o1 o2 ob ol : Op D.AppOp),
  (D.order o2 o1 = .Fst_then_snd) ∧ (D.order ob ol = .Fst_then_snd) ∧ o2.2.1 ≠ o1.2.1 ∧ ob.2.1 ≠ ol.2.1 ∧ D.distinct o1 o2 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o2 ob ∧ D.distinct o2 ol ∧ D.distinct ob ol ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b ol)) o2)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a ob)) ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step a ob)) ol)) ((D.step ((D.step b ol)) o2)))) o1)))

def inter_right_2op : Prop := ∀ (l a b : D.State) (o1 o2 ob ol o : Op D.AppOp),
  ( (D.order o2 o1 = .Fst_then_snd) ∨ (D.order o2 o1 = .Either) ) ∧ o1.2.1 ≠ o2.2.1 ∧ (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ ( ¬ ( (D.order o ob = .Either) ) ∨ (D.order o ol = .Fst_then_snd) ) ∧ D.distinct o1 o2 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o1 o ∧ D.distinct o2 ob ∧ D.distinct o2 ol ∧ D.distinct o2 o ∧ D.distinct ob ol ∧ D.distinct ob o ∧ D.distinct ol o ∧ o.2.1 ≠ ol.2.1 ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step ((D.step b ob)) ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step ((D.step b ob)) ol)) o2)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step ((D.step ((D.step b o)) ob)) ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step ((D.step ((D.step b o)) ob)) ol)) o2)))) o1)))

def inter_left_2op : Prop := ∀ (l a b : D.State) (o1 o2 ob ol o : Op D.AppOp),
  (D.order o2 o1 = .Fst_then_snd) ∧ (D.order ob ol = .Fst_then_snd) ∧ o2.2.1 ≠ o1.2.1 ∧ ob.2.1 ≠ ol.2.1 ∧ ( ¬ ( (D.order o ob = .Either) ) ∨ (D.order o ol = .Fst_then_snd) ) ∧ D.distinct o1 o2 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o1 o ∧ D.distinct o2 ob ∧ D.distinct o2 ol ∧ D.distinct o2 o ∧ D.distinct ob ol ∧ D.distinct ob o ∧ D.distinct ol o ∧ o.2.1 ≠ ol.2.1 ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a ob)) ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step a ob)) ol)) ((D.step ((D.step b ol)) o2)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step ((D.step a o)) ob)) ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a o)) ob)) ol)) ((D.step ((D.step b ol)) o2)))) o1)))

def inter_lca_2op : Prop := ∀ (l a b : D.State) (o1 o2 ol : Op D.AppOp),
  ( (D.order o2 o1 = .Fst_then_snd) ∨ (D.order o2 o1 = .Either) ) ∧ o1.2.1 ≠ o2.2.1 ∧ D.distinct o1 o2 ∧ D.distinct o1 ol ∧ D.distinct o2 ol ∧ ( ∃ o, (D.order o ol = .Fst_then_snd) ) ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b ol)))) o1))) ∧ (((D.merge l ((D.step a o1)) ((D.step b o2)))) = ((D.step ((D.merge l a ((D.step b o2)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step b ol)) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b ol)) o2)))) o1)))

def ind_right_2op : Prop := ∀ (l a b : D.State) (o1 o2 o2' : Op D.AppOp),
  (D.order o2 o1 = .Fst_then_snd) ∧ o1.2.1 ≠ o2.2.1 ∧ D.distinct o1 o2 ∧ D.distinct o1 o2' ∧ D.distinct o2 o2' ∧ (((D.merge l ((D.step a o1)) ((D.step b o2)))) = ((D.step ((D.merge l a ((D.step b o2)))) o1))) →
  (((D.merge l ((D.step a o1)) ((D.step ((D.step b o2')) o2)))) = ((D.step ((D.merge l a ((D.step ((D.step b o2')) o2)))) o1)))

def ind_left_2op : Prop := ∀ (l a b : D.State) (o1 o2 o1' : Op D.AppOp),
  ( (D.order o2 o1 = .Fst_then_snd) ∨ (D.order o2 o1 = .Either) ) ∧ o1.2.1 ≠ o2.2.1 ∧ D.distinct o1 o2 ∧ D.distinct o1 o1' ∧ D.distinct o2 o1' ∧ (((D.merge l ((D.step a o1)) ((D.step b o2)))) = ((D.step ((D.merge l a ((D.step b o2)))) o1))) →
  (((D.merge l ((D.step ((D.step a o1')) o1)) ((D.step b o2)))) = ((D.step ((D.merge l ((D.step a o1')) ((D.step b o2)))) o1)))

def inter_right_base_1op : Prop := ∀ (l a b : D.State) (o1 ob ol : Op D.AppOp),
  (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct ob ol ∧ ( (D.order ob o1 = .Fst_then_snd) → (((D.merge l ((D.step a o1)) ((D.step b ob)))) = ((D.step ((D.merge l a ((D.step b ob)))) o1))) ) ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b ol)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step b ob)) ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b ob)) ol)))) o1)))

def inter_left_base_1op : Prop := ∀ (l a b : D.State) (o1 ob ol : Op D.AppOp),
  (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct ob ol ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b ol)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a ob)) ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step a ob)) ol)) ((D.step b ol)))) o1)))

def inter_right_1op : Prop := ∀ (l a b : D.State) (o1 ob ol o : Op D.AppOp),
  (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ ( ¬ ( (D.order o ob = .Either) ) ∨ (D.order o ol = .Fst_then_snd) ) ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o1 o ∧ D.distinct ob ol ∧ D.distinct ob o ∧ D.distinct ol o ∧ o.2.1 ≠ ol.2.1 ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step b ob)) ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b ob)) ol)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step ((D.step ((D.step b o)) ob)) ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step ((D.step b o)) ob)) ol)))) o1)))

def inter_left_1op : Prop := ∀ (l a b : D.State) (o1 ob ol o : Op D.AppOp),
  (D.order ob ol = .Fst_then_snd) ∧ ob.2.1 ≠ ol.2.1 ∧ ( ¬ ( (D.order o ob = .Either) ) ∨ (D.order o ol = .Fst_then_snd) ) ∧ D.distinct o1 ob ∧ D.distinct o1 ol ∧ D.distinct o1 o ∧ D.distinct ob ol ∧ D.distinct ob o ∧ D.distinct ol o ∧ o.2.1 ≠ ol.2.1 ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a ob)) ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step a ob)) ol)) ((D.step b ol)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step ((D.step a o)) ob)) ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step ((D.step ((D.step a o)) ob)) ol)) ((D.step b ol)))) o1)))

def inter_lca_1op : Prop := ∀ (l a b : D.State) (o1 ol oi : Op D.AppOp),
  D.distinct o1 ol ∧ D.distinct o1 oi ∧ D.distinct ol oi ∧ ( ∃ o, (D.order o ol = .Fst_then_snd) ) ∧ ( ∃ o, (D.order o oi = .Fst_then_snd) ) ∧ (((D.merge ((D.step l oi)) ((D.step ((D.step a oi)) o1)) ((D.step b oi)))) = ((D.step ((D.merge ((D.step l oi)) ((D.step a oi)) ((D.step b oi)))) o1))) ∧ (((D.merge ((D.step l ol)) ((D.step ((D.step a ol)) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b ol)))) o1))) →
  (((D.merge ((D.step ((D.step l oi)) ol)) ((D.step ((D.step ((D.step a oi)) ol)) o1)) ((D.step ((D.step b oi)) ol)))) = ((D.step ((D.merge ((D.step ((D.step l oi)) ol)) ((D.step ((D.step a oi)) ol)) ((D.step ((D.step b oi)) ol)))) o1)))

def ind_left_1op : Prop := ∀ (l a b : D.State) (o1 o1' ol : Op D.AppOp),
  D.distinct o1 o1' ∧ D.distinct o1 ol ∧ D.distinct o1' ol ∧ (((D.merge ((D.step l ol)) ((D.step a o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) a ((D.step b ol)))) o1))) →
  (((D.merge ((D.step l ol)) ((D.step ((D.step a o1')) o1)) ((D.step b ol)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a o1')) ((D.step b ol)))) o1)))

def ind_right_1op : Prop := ∀ (l a b : D.State) (o2 o2' ol : Op D.AppOp),
  D.distinct o2 o2' ∧ D.distinct o2 ol ∧ D.distinct o2' ol ∧ (((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) b)) o2))) →
  (((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step ((D.step b o2')) o2)))) = ((D.step ((D.merge ((D.step l ol)) ((D.step a ol)) ((D.step b o2')))) o2)))

end Signature
namespace Efficient
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
def signature : Signature := ⟨State α, SetOp α, ∅, update, merge, rc.order⟩
theorem trial : (signature (α := α)).inter_left_1op := by
  unfold Signature.inter_left_1op
  intro l a b o1 ob ol o hp
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  dsimp [signature] at *
  rcases o1 with ⟨o1t, o1r, o1op⟩
  rcases ob with ⟨obt, obr, obop⟩
  rcases ol with ⟨olt, olr, olop⟩
  rcases o with ⟨ot, or, oop⟩
  cases o1op <;> cases obop <;> cases olop <;> cases oop <;>
    ext x <;>
    have ih10 := Finset.ext_iff.mp h10 x <;>
    clear h10 <;>
    simp [Signature.distinct, rc, merge, update] at *
  all_goals
    -- SOLVER
end Efficient
end NeemExpansion
