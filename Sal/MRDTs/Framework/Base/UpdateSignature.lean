/-!
# Update signatures and internal replay policies

`UpdateSig` is the merge-free algebra used to fold event histories and state
the generic replay invariants. It is derived from an `MRDTSig`; implementers do
not provide a second datatype interface.

The optional `HistoricalBinaryMerge` class exists only so the retained binary
VC and countermodel modules continue to state their old two-way merge laws. It
is not part of `UpdateSig`, `MRDTSig`, operational execution, or `VerifiedMRDT`.

A separate `ReplayPolicy` carries the historical Sal/Neem resolver used by one
internal convergence proof. Client-facing arbitration does not come from this
policy.
-/

namespace Sal.MRDTs.Foundation

/-- Internal replay-order verdict retained by the absorber-based convergence
construction. It is not part of an MRDT or its public semantic interaction
policy. -/
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

/-- A proof-local replay policy for the historical absorber construction.
`MRDTSig` does not contain this object. A convergence certificate may choose
this construction or prove its replay theorem by another route. -/
class ReplayPolicy (D : UpdateSig) where
  order : Op D.AppOp → Op D.AppOp → RcRes

namespace ReplayPolicy

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

/-- Two events commute if applying them in either order from any state yields
the same state. -/
def commutes (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁

/-- Two application operations commute if every pair of events carrying them
commutes. -/
def appOpsCommute (o₁ o₂ : D.AppOp) : Prop :=
  ∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ → D.commutes e₁ e₂

end UpdateSig

end Sal.MRDTs.Foundation
