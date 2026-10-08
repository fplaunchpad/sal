import InductiveLeaves

/-! Inductive kernels for the ACTUAL nested local redistribution equation.
The equation-shaped IH quantifies the reconstructed local remainder t, so
coverage concerns only common l, causal past B, and opposite branch b. -/
namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

def LocalEquation (D : Signature) (l B b : D.State) (e : Op D.AppOp) : Prop :=
  ∀ t, D.merge l (D.merge B t (D.step B e)) b =
    D.merge B (D.merge l t b) (D.step B e)

def Commute (D : Signature) (e h : Op D.AppOp) : Prop :=
  ∀ s, D.step (D.step s e) h = D.step (D.step s h) e

def local_base (D : Signature) : Prop := ∀ e,
  D.LocalEquation D.init D.init D.init e

def local_common_all (D : Signature) : Prop := ∀ l B b e h,
  D.LocalEquation l B b e →
  D.LocalEquation (D.step l h) (D.step B h) (D.step b h) e

def local_common_opposite (D : Signature) : Prop := ∀ l B b e h,
  D.LocalEquation l B b e →
  D.LocalEquation (D.step l h) B (D.step b h) e

def local_past_commuting (D : Signature) : Prop := ∀ l B b e h,
  D.Commute e h → D.LocalEquation l B b e →
  D.LocalEquation l (D.step B h) b e

def local_opposite_commuting (D : Signature) : Prop := ∀ l B b e h,
  D.Commute e h → D.LocalEquation l B b e →
  D.LocalEquation l B (D.step b h) e
/-- Equation-shaped freshness companion, proved by event-history expansion.
For Add it says the born tag is absent; Remove requires no birth evidence. -/
def FreshEquation (D : Signature) (s : D.State) (e : Op D.AppOp) : Prop :=
  D.merge s D.init (D.step s e) = D.step D.init e

def fresh_base (D : Signature) : Prop := ∀ e, D.FreshEquation D.init e

def fresh_step (D : Signature) : Prop := ∀ s e h,
  D.distinct e h → D.FreshEquation s e → D.FreshEquation (D.step s h) e

def local_past_fresh (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.FreshEquation b h → D.LocalEquation l B b e →
  D.LocalEquation l (D.step B h) b e

def local_opposite_fresh (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.FreshEquation B h → D.LocalEquation l B b e →
  D.LocalEquation l B (D.step b h) e

def local_empty_past (D : Signature) : Prop := ∀ l b e,
  D.FreshEquation l e → D.LocalEquation l D.init b e

def local_past_singleton (D : Signature) : Prop := ∀ l B b e h,
  D.FreshEquation l e → D.LocalEquation l B b e →
  D.LocalEquation l (D.step D.init h) b e →
  D.LocalEquation l (D.step B h) b e

end NeemExpansion.Signature

namespace NeemExpansion.Efficient
open Sal.MRDTs.Foundation Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem trial : (signature (α := α)).local_empty_past := by
  intro l b e fresh t
  rcases e with ⟨et,er,eo⟩
  cases eo <;> dsimp [Signature.FreshEquation,signature] at * <;> ext p <;>
    have fe := Finset.ext_iff.mp fresh p <;>
    simp [signature,merge,update] at *
  -- SOLVER
end NeemExpansion.Efficient
