import Sal.ConditionedMRDTs.Framework.Base.Labeled_TS

/-!
# CRDT signature

The six-tuple $\langle\Sigma, \sigma_0, \mathsf{do}, \mathsf{merge},
\mathsf{query}, \mathsf{rc}\rangle$ for a state-based CRDT. Matches the
Sal paper's signature specialised to 2-way merge (no LCA argument).

Names in the Lean structure are English (`State`, `init`, `update`, …)
because `Σ` is taken by sigma types in Lean. Docstrings map back to
paper notation.
-/

namespace Sal.Emulation

/-- `rc` verdict, matching the existing Sal CRDT files. `Fst_then_snd`
means the first op must be linearized before the second; `Either` means
the order is semantically irrelevant. `Snd_then_fst` is conventional
symmetry. -/
inductive RcRes : Type where
  | Fst_then_snd
  | Snd_then_fst
  | Either
  deriving DecidableEq, Repr

/-- Replica identifier. Sal uses `Nat` by convention. -/
abbrev Replica : Type := Nat

/-- Timestamp. Sal uses `Nat` by convention; global uniqueness is
enforced at the transition-system level (the `apply` rule demands a
fresh timestamp). -/
abbrev Timestamp : Type := Nat

/-- Sal's `op_t`: `(timestamp, replica, abstract op)`. An event in an
execution is exactly one of these, uniquely identified by its timestamp. -/
abbrev Op (AppOp : Type) : Type := Timestamp × Replica × AppOp

namespace Op
variable {AppOp : Type}

/-- Timestamp projection. Paper notation: $\mathsf{time}(e)$. -/
def time (o : Op AppOp) : Timestamp := o.1
/-- Replica projection. Paper notation: $\mathsf{rep}(e)$. -/
def rep (o : Op AppOp) : Replica := o.2.1
/-- Application-op projection. Paper notation: $\mathsf{op}(e)$. -/
def op (o : Op AppOp) : AppOp := o.2.2

end Op

/-- State-based CRDT signature.

Glossary:
* `State`  — Σ, the state space.
* `init`   — σ₀, the initial state.
* `AppOp`  — set of abstract update operations (Sal's `app_op_t`).
* `Query`  — Q, set of query operations.
* `Value`  — V, set of query return values.
* `update` — `do : Σ × (T × R × O) → Σ`; Sal's `do_`.
* `merge`  — `merge : Σ × Σ → Σ`; the lattice join on `Σ`.
* `query`  — `query : Σ × Q → V`.
* `rc`     — Sal's linearization-order specification.

`update` takes the full `Op AppOp` (timestamp + replica + app op)
because some CRDTs (e.g. LWW registers) dispatch on the timestamp; most
ignore it and only use the app-op component. -/
structure CRDTSig where
  State : Type
  dec_state : DecidableEq State
  init : State
  AppOp : Type
  dec_op : DecidableEq AppOp
  Query : Type
  Value : Type
  update : State → Op AppOp → State
  merge : State → State → State
  query : State → Query → Value
  rc : Op AppOp → Op AppOp → RcRes

namespace CRDTSig

attribute [instance] dec_state dec_op

variable (D : CRDTSig)

/-- Two events commute in `D` if applying them in either order from any
state yields the same state. Paper notation: $e_1 \rightleftarrows e_2$
(lin.tex §3.2). -/
def commutes (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁

/-- Two app-ops commute if every pair of events using them commutes. -/
def appOpsCommute (o₁ o₂ : D.AppOp) : Prop :=
  ∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ → D.commutes e₁ e₂

end CRDTSig

end Sal.Emulation
