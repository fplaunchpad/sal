import InductiveLeaves

/-! An equation-shaped expansion for the stronger, actual-noncommutation
conditional law used by Sal. No state/history invariant is supplied. -/
set_option linter.unusedSimpArgs false
namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

def commutes (D : Signature) (a b : Op D.AppOp) : Prop :=
  ∀ s, D.step (D.step s a) b = D.step (D.step s b) a

def KernelStable (D : Signature) : Prop := ∀ s t o c,
  D.step s c = D.step t c →
  D.step (D.step s o) c = D.step (D.step t o) c

def ConditionalBase (D : Signature) : Prop := ∀ s a b c,
  D.order a b = .Fst_then_snd → ¬ D.commutes b c →
  D.step (D.step (D.step s a) b) c = D.step (D.step (D.step s b) a) c

/-- The final absorber stays frozen while the intervening log grows. The
equation before that extension is the entire induction hypothesis. -/
theorem conditional_log (D : Signature) (base : D.ConditionalBase)
    (stable : D.KernelStable) (s : D.State) (a b c : Op D.AppOp)
    (order : D.order a b = .Fst_then_snd) (noncomm : ¬ D.commutes b c)
    (between : List (Op D.AppOp)) :
    D.step (between.foldl D.step (D.step (D.step s a) b)) c =
      D.step (between.foldl D.step (D.step (D.step s b) a)) c := by
  induction between using List.reverseRecOn with
  | nil => exact base s a b c order noncomm
  | append_singleton xs o ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact stable _ _ o c ih

end NeemExpansion.Signature

namespace NeemExpansion.Exact
open Sal.MRDTs.Paper1.ORSet
variable {α : Type} [DecidableEq α]

theorem kernelStable : (signature (α := α)).KernelStable := by
  intro s t o c ih
  dsimp [signature] at *
  rcases o with ⟨ot, or, oo⟩; rcases c with ⟨ct, cr, co⟩
  cases oo <;> cases co <;> ext p <;>
    have hp := Finset.ext_iff.mp ih p <;>
    simp [signature, step] at hp ⊢ <;> grind only

theorem conditionalBase : (signature (α := α)).ConditionalBase := by
  intro s a b c before noncomm
  dsimp [Signature.commutes, signature] at *
  rcases a with ⟨ats, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  rcases c with ⟨ct, cr, co⟩
  cases ao <;> cases bo <;> simp only [order] at before
  all_goals try split_ifs at before
  all_goals try cases before
  subst_vars
  rename_i x
  cases co with
  | add z =>
    exfalso
    apply noncomm
    intro t
    ext p
    simp [signature, step]
    tauto
  | remove z =>
    have same : x = z := by
      by_contra ne
      apply noncomm
      intro t
      ext p
      simp [signature, step]
      grind only
    subst z
    ext p
    simp [signature, step]
    grind only

end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem kernelStable : (signature (α := α)).KernelStable := by
  intro s t o c ih
  dsimp [signature] at *
  rcases o with ⟨ot, or, oo⟩; rcases c with ⟨ct, cr, co⟩
  cases oo <;> cases co <;> ext p <;>
    have hp := Finset.ext_iff.mp ih p <;>
    simp [signature, update] at hp ⊢ <;> grind only

theorem conditionalBase : (signature (α := α)).ConditionalBase := by
  intro s a b c before noncomm
  dsimp [Signature.commutes, signature] at *
  rcases a with ⟨ats, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  rcases c with ⟨ct, cr, co⟩
  cases ao <;> cases bo <;> simp only [rc] at before
  all_goals try split_ifs at before
  all_goals try cases before
  subst_vars
  rename_i x
  cases co with
  | add z =>
    have same : br = cr ∧ x = z := by
      by_contra ne
      apply noncomm
      intro t
      ext p
      simp [signature, update]
      grind only
    rcases same with ⟨rfl, rfl⟩
    ext p
    simp [signature, update]
    grind only
  | remove z =>
    have same : x = z := by
      by_contra ne
      apply noncomm
      intro t
      ext p
      simp [signature, update]
      grind only
    subst z
    ext p
    simp [signature, update]
    grind only

end NeemExpansion.Efficient
