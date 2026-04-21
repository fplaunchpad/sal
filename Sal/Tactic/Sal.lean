import Lean
import Aesop
import Blaster

open Lean Elab Tactic

/--
The `sal` tactic tries three proof strategies in sequence:
1. dsimp + grind
2. blaster (SMT-backed, via Z3)
3. dsimp + aesop + all_goals try grind

Each strategy is attempted in order, stopping at the first one that
succeeds. The kernel/elaborator is given a budget of `maxHeartbeats`
heartbeats (a step count, not wall-clock), and `simp` normalization is
given a budget of `maxSimpSteps`. The blaster stage separately passes
a wall-clock `smtTimeoutSec` down to Z3; without this, Blaster's
default is unlimited and a stuck goal can hang indefinitely.

**Silent-sorry guard (stages 1 and 3 only).** After stages 1 and 3 we
check that the proof terms assigned to the original goals do not
contain `sorryAx`. Aesop in its default configuration can "succeed"
by emitting a warning and leaving a goal closed with a `sorry`
placeholder; the guard rejects any such assignment and forces the
tactic to try the next stage. Stage 2 (blaster) is NOT guarded,
because Blaster intentionally closes goals via `MVarId.admit`
(sorryAx) when Z3 reports "valid" — this is the mechanism that
enlarges the TCB to include Z3 (as described in the paper). Users
who want a strict no-sorry policy should invoke stage 1 or stage 3
directly instead of `sal`.
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
  let initialGoals ← Lean.Elab.Tactic.getGoals

  let runBudgeted (tac : TSyntax `tactic) : TacticM Unit := do
    withOptions (fun opts =>
        (opts.set `maxHeartbeats maxHeartbeats).set `maxSimpSteps maxSimpSteps) do
      evalTactic tac

  -- Strategy 1: dsimp + grind (no sorry allowed).
  try
    runBudgeted (← `(tactic| dsimp <;> grind))
    failIfSorry initialGoals "1 (dsimp + grind)"
    return ()
  catch _ =>
    -- Strategy 2: blaster with SMT timeout.
    -- No failIfSorry here: Blaster uses sorryAx by design to accept
    -- Z3's "valid" verdict. That enlarges the TCB to include Z3, which
    -- is the paper's intended semantics for the LB stage.
    try
      let n := Syntax.mkNumLit (toString smtTimeoutSec)
      runBudgeted (← `(tactic| blaster (timeout: $n)))
      return ()
    catch _ =>
      -- Strategy 3: dsimp + aesop + all_goals try grind.
      -- failIfSorry IS applied here: aesop's "succeed with warning +
      -- sorry" behaviour would otherwise produce unsound proofs.
      runBudgeted (← `(tactic| dsimp <;> aesop <;> all_goals (try grind)))
      failIfSorry initialGoals "3 (dsimp + aesop)"

elab_rules : tactic
  | `(tactic| sal) => salImpl
