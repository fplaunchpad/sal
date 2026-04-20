import Lean
import Aesop
import Blaster

open Lean Elab Tactic

/--
The `sal` tactic tries multiple proof strategies in sequence:
1. dsimp + grind
2. blaster
3. dsimp + aesop + all_goals try grind

Each strategy is attempted in order, stopping at the first one that succeeds.
Each tactic has a default timeout of 100000 heartbeats.
-/
syntax "sal" : tactic

def salImpl (maxHeartbeats : Nat := 100000) : TacticM Unit := do
  -- Helper function to run tactic with timeout
  let runWithTimeout (tac : TSyntax `tactic) : TacticM Unit := do
    withOptions (fun opts => opts.setNat `maxHeartbeats maxHeartbeats) do
      evalTactic tac

  -- Try strategy 1: dsimp + grind
  try
    runWithTimeout (← `(tactic| dsimp <;> grind))
    return ()
  catch _ =>
    -- Try strategy 2: blaster
    try
      runWithTimeout (← `(tactic| blaster))
      return ()
    catch _ =>
      -- Try strategy 3: dsimp + aesop + all_goals try grind
      runWithTimeout (← `(tactic| dsimp <;> aesop <;> all_goals (try grind)))

elab_rules : tactic
  | `(tactic| sal) => salImpl
