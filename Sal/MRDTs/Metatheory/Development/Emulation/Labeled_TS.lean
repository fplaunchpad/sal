import Mathlib.Logic.Relation

/-!
# Labeled Transition Systems

Generic infrastructure shared by the Sal paper's semantics (lin.tex §3.1,
Fig. sem) and Liittschwager et al.'s op-based / state-based semantics
(arXiv:2504.05398v2 §3). We define an LTS as a four-tuple
`(State, Label, step, silent)` where `silent : Label → Prop` marks
unobservable transitions (e.g. network `send` / `deliver` events in the
Liittschwager setting).

Weak simulation and weak trace equivalence live in a later file; here we
only set up the generic step relation, executions, and reachability.
-/

namespace Sal.Emulation

/-- A labeled transition system: a state space, a label set, a step relation,
and a predicate marking labels as silent (unobservable). Silent labels are
elided when taking weak traces.

For the Sal TS, no label is silent (every transition is an observable event).
For Liittschwager's TS, `send` and `deliver` labels are silent. -/
structure LabeledTS where
  /-- The state space (configurations). -/
  State : Type
  /-- The label set (transition kinds + any metadata carried on the arrow). -/
  Label : Type
  /-- The step relation `s --ℓ--> s'`. -/
  step : State → Label → State → Prop
  /-- Labels that are silent and therefore elided in weak traces. -/
  silent : Label → Prop

namespace LabeledTS

/-- A single transition exists from `s` to `s'` under some label. -/
def Steps (T : LabeledTS) (s s' : T.State) : Prop :=
  ∃ ℓ, T.step s ℓ s'

/-- An execution: a finite sequence of transitions starting at `s`,
recording each state and label along the way. Matches lin.tex's notion of
$C_0 \xrightarrow{t_1} C_1 \cdots \xrightarrow{t_n} C_n$. -/
inductive Execution (T : LabeledTS) : T.State → List (T.Label × T.State) → Prop where
  | nil (s : T.State) : Execution T s []
  | cons {s s' : T.State} {ℓ : T.Label} {rest : List (T.Label × T.State)} :
      T.step s ℓ s' → Execution T s' rest → Execution T s ((ℓ, s') :: rest)

/-- A state `s'` is reachable from `s` if there is some execution from `s`
ending at `s'`. Equivalent to the reflexive-transitive closure of `Steps`. -/
def Reachable (T : LabeledTS) (s s' : T.State) : Prop :=
  Relation.ReflTransGen T.Steps s s'

/-- Given an `LTS` with a distinguished initial state, the set of reachable
states is the image of `init` under `Reachable`. Most configurations in the
Sal paper's developments are implicitly required to be reachable from the
initial configuration — see `def:well-formed` in §3.2 of the Liittschwager
paper and the Sal paper's notion of configurations "reachable in some
execution". -/
def ReachableFrom (T : LabeledTS) (init : T.State) (s : T.State) : Prop :=
  T.Reachable init s

end LabeledTS

end Sal.Emulation
