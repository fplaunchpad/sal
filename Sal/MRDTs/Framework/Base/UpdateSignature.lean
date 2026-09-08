/-!
# Update signatures and resolve-conflict policies

`UpdateSig` is the merge-free algebra used to fold event histories and state
the generic replay invariants. It is derived from an `MRDTSig`; implementers do
not provide a second datatype interface.

The optional `HistoricalBinaryMerge` class exists only so the retained binary
VC and countermodel modules continue to state their old two-way merge laws. It
is not part of `UpdateSig`, `MRDTSig`, operational execution, or `VerifiedMRDT`.

`ReplayPolicy` is the carrier of the Sal/Neem resolve-conflict relation. A
`VerifiedMRDT` stores its sole public `rc` explicitly; proof-local convergence
arguments may instantiate the same carrier independently.
-/

namespace Sal.MRDTs.Foundation

/-- Resolve-conflict verdict used by the absorber-based replay construction
and by the public `rc` stored in `VerifiedMRDT`. -/
inductive RcRes : Type where
  | Fst_then_snd
  | Snd_then_fst
  | Either
  deriving DecidableEq, Repr

/-- Replica identifier. Sal uses `Nat` by convention. -/
abbrev Replica : Type := Nat

/-- Lamport timestamp. Global uniqueness is enforced by the MRDT `apply`
transition's freshness premise. -/
abbrev Timestamp : Type := Nat

/-- An issued event: `(timestamp, replica, application operation)`. -/
abbrev Op (AppOp : Type) : Type := Timestamp × Replica × AppOp

namespace Op
variable {AppOp : Type}

/-- Timestamp projection. Paper notation: $\mathsf{time}(e)$. -/
def time (o : Op AppOp) : Timestamp := o.1
/-- Replica projection. Paper notation: $\mathsf{rep}(e)$. -/
def rep (o : Op AppOp) : Replica := o.2.1
/-- Application-operation projection. Paper notation: $\mathsf{op}(e)$. -/
def op (o : Op AppOp) : AppOp := o.2.2

end Op

/-- Merge-free proof algebra for finite update folds and replay invariants.

The MRDT framework derives this structure with `MRDTSig.toUpdateSig`; users do
not supply it independently. -/
structure UpdateSig where
  State : Type
  dec_state : DecidableEq State
  init : State
  AppOp : Type
  dec_op : DecidableEq AppOp
  update : State → Op AppOp → State

/-- Optional two-way merge used only by the retained historical binary theory.
It is deliberately separate from `UpdateSig`. -/
class HistoricalBinaryMerge (D : UpdateSig) where
  binaryMerge : D.State → D.State → D.State

/-- Carrier of the intended resolve-conflict relation for concurrent events.
`VerifiedMRDT` stores the selected public policy explicitly. Its direction
does not assert concrete noncommutativity: an implementation may realize the
policy with commuting updates, as timestamp-max updates do for LWW.
Algebraic replay laws are optional sufficient proof obligations, not fields
of this carrier. -/
class ReplayPolicy (D : UpdateSig) where
  order : Op D.AppOp → Op D.AppOp → RcRes

namespace ReplayPolicy

/-- The directed resolve-conflict relation induced by a three-valued policy.
Paper notation: `a →rc b`. -/
@[simp] def Before {D : UpdateSig} (P : ReplayPolicy D)
    (a b : Op D.AppOp) : Prop :=
  P.order a b = RcRes.Fst_then_snd

def unconstrained (D : UpdateSig) : ReplayPolicy D where
  order := fun _ _ => .Either

/-- Generic replay proofs need no resolver for commuting datatypes. This
low-priority default keeps the proof detail out of each MRDT declaration; a
convergence proof for a noncommuting datatype installs its own policy. -/
instance (priority := low) default (D : UpdateSig) : ReplayPolicy D :=
  unconstrained D

end ReplayPolicy

namespace UpdateSig

attribute [instance] dec_state dec_op

variable (D : UpdateSig)

/-- The optional historical binary operation. Its name keeps it visibly apart
from the ternary `MRDTSig.merge`. -/
def historicalMerge [HistoricalBinaryMerge D] : D.State → D.State → D.State :=
  HistoricalBinaryMerge.binaryMerge

def replayOrder [P : ReplayPolicy D] : Op D.AppOp → Op D.AppOp → RcRes :=
  P.order

/-- Directed resolve-conflict relation for the active replay policy. -/
abbrev rc [P : ReplayPolicy D] (a b : Op D.AppOp) : Prop :=
  P.Before a b

/-- Concrete-update commutation: applying events in either order from any
implementation state yields the same state. This proof property neither
defines semantic conflict nor excludes a resolve-conflict edge. -/
def commutes (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁

/-- Two application operations commute if every pair of events carrying them
commutes. -/
def appOpsCommute (o₁ o₂ : D.AppOp) : Prop :=
  ∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ → D.commutes e₁ e₂

end UpdateSig

end Sal.MRDTs.Foundation
