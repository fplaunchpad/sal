import Lean
import Aesop
import Blaster

open Lean Elab Tactic

/--
The `sal` tactic tries multiple proof strategies in sequence:
1. dsimp + grind
2. blaster (with an SMT wall-clock timeout)
3. dsimp + aesop + all_goals try grind

Each strategy is attempted in order, stopping at the first one that
genuinely succeeds. The kernel/elaborator is given a budget of
`maxHeartbeats` heartbeats (a step count, not wall-clock), and `simp`
normalization inside aesop is given a budget of `maxSimpSteps`. The
blaster stage separately passes a wall-clock `smtTimeoutSec` down to
Z3; without this, Blaster's default is unlimited and a stuck goal can
hang indefinitely.

**Silent-sorry guard.** After each stage, we check that the proof
terms assigned to the original goals do not contain `sorryAx`. Aesop
in its default configuration can "succeed" by emitting a warning and
leaving a goal closed with a `sorry` placeholder; without this guard,
such a stage would be treated as a successful proof even though it
actually depends on `sorryAx`. The guard rejects any sorry-containing
assignment, forcing the tactic to try the next stage (and, at the end,
to fail outright rather than produce an unsound "proof").
-/
syntax "sal" : tactic

/-- Throw an error if any of `mvarIds`'s assigned proof terms contains
`sorryAx` (directly, or via a nested metavariable). Used to guard
against aesop's non-terminal "succeed with warning + sorry" behaviour. -/
def failIfSorry (mvarIds : List MVarId) (stage : String) : TacticM Unit := do
  for mvarId in mvarIds do
    let e ← Lean.instantiateMVars (Expr.mvar mvarId)
    if e.hasSorry then
      throwError "sal stage {stage}: proof term contains sorry"

def salImpl
    (maxHeartbeats : Nat := 400000)
    (maxSimpSteps : Nat := 1000000)
    (smtTimeoutSec : Nat := 30) : TacticM Unit := do
  -- Snapshot the goals at entry; we'll check each one's final proof
  -- term for sorry after each stage.
  let initialGoals ← Lean.Elab.Tactic.getGoals

  let runBudgeted (tac : TSyntax `tactic) : TacticM Unit := do
    withOptions (fun opts =>
        (opts.setNat `maxHeartbeats maxHeartbeats).setNat `maxSimpSteps maxSimpSteps) do
      evalTactic tac

  -- Strategy 1: dsimp + grind
  try
    runBudgeted (← `(tactic| dsimp <;> grind))
    failIfSorry initialGoals "1 (dsimp + grind)"
    return ()
  catch _ =>
    -- Strategy 2: blaster with SMT timeout
    try
      let n := Syntax.mkNumLit (toString smtTimeoutSec)
      runBudgeted (← `(tactic| blaster (timeout: $n)))
      failIfSorry initialGoals "2 (blaster)"
      return ()
    catch _ =>
      -- Strategy 3: dsimp + aesop + all_goals try grind.
      -- The post-stage failIfSorry is essential here: aesop's default
      -- mode can silently fill goals with sorry when exhaustive search
      -- doesn't close them.
      runBudgeted (← `(tactic| dsimp <;> aesop <;> all_goals (try grind)))
      failIfSorry initialGoals "3 (dsimp + aesop)"

elab_rules : tactic
  | `(tactic| sal) => salImpl
