import Lean
import Aesop
import Blaster

open Lean Elab Tactic

/--
The `sal` tactic tries multiple proof strategies in sequence:
1. dsimp + grind
2. blaster (with an SMT wall-clock timeout)
3. dsimp + aesop + all_goals try grind

Each strategy is attempted in order, stopping at the first one that succeeds.
The kernel/elaborator is given a budget of `maxHeartbeats` heartbeats
(a step count, not wall-clock), and `simp` normalization inside aesop is
given a budget of `maxSimpSteps`. The blaster stage separately passes a
wall-clock `smtTimeoutSec` down to Z3; without this, Blaster's default is
unlimited and a stuck goal can hang indefinitely.
-/
syntax "sal" : tactic

def salImpl
    (maxHeartbeats : Nat := 400000)
    (maxSimpSteps : Nat := 1000000)
    (smtTimeoutSec : Nat := 30) : TacticM Unit := do
  let runBudgeted (tac : TSyntax `tactic) : TacticM Unit := do
    withOptions (fun opts =>
        (opts.setNat `maxHeartbeats maxHeartbeats).setNat `maxSimpSteps maxSimpSteps) do
      evalTactic tac

  -- Strategy 1: dsimp + grind
  try
    runBudgeted (← `(tactic| dsimp <;> grind))
    return ()
  catch _ =>
    -- Strategy 2: blaster with SMT timeout
    try
      let n := Syntax.mkNumLit (toString smtTimeoutSec)
      runBudgeted (← `(tactic| blaster (timeout: $n)))
      return ()
    catch _ =>
      -- Strategy 3: dsimp + aesop + all_goals try grind
      runBudgeted (← `(tactic| dsimp <;> aesop <;> all_goals (try grind)))

elab_rules : tactic
  | `(tactic| sal) => salImpl
