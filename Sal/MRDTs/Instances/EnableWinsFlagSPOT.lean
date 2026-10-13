import Sal.MRDTs.Instances.EnableWinsFlag

/-! Hand-derived PASS+FAIL controls for the corrected Neem enable-wins flag.
Branches use distinct issuers, and each ternary merge uses the actual common
history as its ancestor. Query expectations are Boolean flag semantics. -/
namespace Sal.MRDTs.Instances.EnableWinsFlagSPOT
open Foundation NeemFlag
open Classical

private def win (ts r : Nat) : Op Action := (ts,r,.winning)
private def reset (ts r : Nat) : Op Action := (ts,r,.reset)
private def empty : State := initial false

example : active empty = false ∧ active empty ≠ true := by
  simp [empty,active_initial]

/-- A concurrent enable wins over a reset, in either merge direction. -/
example :
    active (merge empty (update empty (win 1 0)) (update empty (reset 2 1))) = true ∧
    active (merge empty (update empty (reset 2 1)) (update empty (win 1 0))) ≠ false := by
  have left : (merge empty (update empty (win 1 0)) (update empty (reset 2 1)) 0).2 = true := by
    norm_num [merge,mergeCell,mergeFlag,empty,initial,update,win,reset,Op.op]
  have right : (merge empty (update empty (reset 2 1)) (update empty (win 1 0)) 0).2 = true := by
    norm_num [merge,mergeCell,mergeFlag,empty,initial,update,win,reset,Op.op]
  have a := (active_true_iff _).mpr ⟨0,left⟩
  have b := (active_true_iff _).mpr ⟨0,right⟩
  exact ⟨a,by simp [b]⟩

/-- A reset after observing the enable must actually clear it. -/
example : active (update (update empty (win 1 0)) (reset 2 1)) = false ∧
    active (update (update empty (win 1 0)) (reset 2 1)) ≠ true := by
  simp [reset,active_reset]

/-- After both branches disable their observed enables, merging cannot
resurrect either flag. This excludes the old scalar-counter design's verdict. -/
private def leftWin := update empty (win 1 0)
private def leftReset := update leftWin (reset 2 0)
private def rightWin := update empty (win 3 1)
private def intermediate := merge empty leftReset rightWin
private def rightReset := update rightWin (reset 4 1)
private def finalState := merge rightWin intermediate rightReset

theorem no_resurrection : active finalState = false ∧ active finalState ≠ true := by
  have allfalse : ∀ r, (finalState r).2 = false := by
    intro r
    by_cases h0 : r = 0 <;> by_cases h1 : r = 1
    all_goals simp [finalState,intermediate,leftReset,leftWin,rightReset,rightWin,
      merge,mergeCell,mergeFlag,update,empty,initial,win,reset,Op.op,h0,h1]
  have result : active finalState = false := by simp [active,allfalse]
  exact ⟨result,by simp [result]⟩

end Sal.MRDTs.Instances.EnableWinsFlagSPOT
