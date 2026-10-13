import Sal.MRDTs.Paper1.Automation.GenericGuardedFold
import Sal.MRDTs.Paper1.Automation.CertifiedOriginBridge

/-! Hand-derived controls: a nonempty trace needs a real transition;
prefix guard transport preserves the original independently specified guard. -/
namespace Sal.MRDTs.Paper1.Automation.SequentialBridgeFamilyControls
open Foundation

def lengthReplay (ops : List Nat) : Nat := ops.foldl (fun n _ => n + 1) 0

theorem length_fusion (ops : List Nat) : lengthReplay ops = ops.length := by
  exact snoc_fold_fusion lengthReplay List.length id (fun n _ => n + 1)
    rfl (fun _ _ => by simp [lengthReplay, List.foldl_append]) (fun _ _ => by simp) ops

theorem guarded_length_fusion (ops : List Nat) : lengthReplay ops = ops.length := by
  exact guarded_fold_projection lengthReplay List.length id (fun n _ => n + 1)
    (fun _ => True) rfl (fun _ _ => by simp) (fun _ _ _ => True.intro)
    (fun _ _ _ => by simp [lengthReplay, List.foldl_append]) True.intro

example : lengthReplay [4, 7] = 2 := guarded_length_fusion [4, 7]
example : lengthReplay [4, 7] ≠ 0 := by decide

example : ¬ (∀ pre : List Nat, ∀ e : Nat,
    (0 : Nat) = (fun n _ => n + 1) (0 : Nat) e) := by
  intro h
  have bad := h [] 4
  simp at bad

example (h : ∀ before e after, [1, 2, 3] = before ++ e :: after → e > 0) :
    ∀ before e after, [1, 2] = before ++ e :: after → e > 0 := by
  exact split_guard_prefix (pre := [1, 2]) (suf := [3]) h

example : ¬ (∀ before e after, [1, 0] = before ++ e :: after → e > 0) := by
  intro h
  have bad := h [1] 0 [] (by decide)
  omega

#print axioms length_fusion
end Sal.MRDTs.Paper1.Automation.SequentialBridgeFamilyControls
