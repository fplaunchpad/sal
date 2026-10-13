import Sal.MRDTs.Paper1.Automation.InductiveLeaves

/-! An equation-shaped expansion for the stronger, actual-noncommutation
conditional law used by Sal. No state/history invariant is supplied. -/
set_option linter.unusedSimpArgs false
namespace Sal.MRDTs.Paper1.Automation.Signature
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

end Sal.MRDTs.Paper1.Automation.Signature
