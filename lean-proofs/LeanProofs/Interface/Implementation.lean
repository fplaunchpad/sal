import Artifact.MRDTs.Framework.Signature
import Artifact.MRDTs.Framework.Base.Replay

/-!
# The implementation tuple

Section 3 parameterises the store by an implementation

```
  D_type = < Sigma, sigma0, do, merge, query, rc >
```

of type `type = < O_type, Q_type, Val_type >`. `MRDTType` and `Impl` below are exactly
those two tuples, field for field. No proof appears in this file.

Lean needs decidable equality on `Sigma` and `O_type` that the paper leaves
implicit; those two fields are marked as bookkeeping and are not part of the
paper's tuple.

`Impl.toMRDTSig` and `Impl.toRc` send the tuple to the shared framework's
representation. Nothing else in this development mentions `MRDTSig`.
-/

namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation

/-- The type `type = < O_type, Q_type, Val_type >`. -/
structure MRDTType where
  /-- `O_type`, the update operations. -/
  OType : Type
  /-- Bookkeeping, not part of the paper's tuple. -/
  decOType : DecidableEq OType
  /-- `Q_type`, the queries. -/
  QType : Type
  /-- `Val_type`, the query results. -/
  ValType : Type

attribute [instance] MRDTType.decOType

namespace MRDTType

/-- `E = T x R x O_type`, the events. Each event is an instance of an update
operation, uniquely identified by its timestamp. -/
abbrev Event (type : MRDTType) : Type := Op type.OType

end MRDTType

/-- An implementation `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
structure Impl (type : MRDTType) where
  /-- `Sigma`, the set of implementation states. -/
  Sigma : Type
  /-- Bookkeeping, not part of the paper's tuple. -/
  decSigma : DecidableEq Sigma
  /-- `sigma0`, the initial state. -/
  sigma0 : Sigma
  /-- `do(sigma, t, r, o)`, written `e(sigma)` in the paper. -/
  do_ : Sigma → type.Event → Sigma
  /-- `merge(l, a, b)`, the LCA state first. -/
  merge : Sigma → Sigma → Sigma → Sigma
  /-- `query(sigma, q)`. -/
  query : Sigma → type.QType → type.ValType
  /-- `rc`, the conflict-resolution relation. `rc_res` is `OrderResult`. -/
  rc : type.Event → type.Event → OrderResult

attribute [instance] Impl.decSigma

namespace Impl

/-- `E`, repeated so that `D.Event` reads as in the paper. Events depend only
on `type`, so this ignores `D`. -/
abbrev Event {type : MRDTType} (_D : Impl type) : Type := type.Event

variable {type : MRDTType} (D : Impl type)

/-- `pi(sigma)`, applying the events of a list one after the other. -/
def applyList (sigma : D.Sigma) (pi : List D.Event) : D.Sigma :=
  pi.foldl D.do_ sigma

/-- `time(e)`. -/
abbrev time (e : D.Event) : Timestamp := e.time

/-- `rep(e)`. -/
abbrev rep (e : D.Event) : Replica := e.rep

/-- Events are uniquely identified by their timestamps. -/
def Distinct (e₁ e₂ : D.Event) : Prop := D.time e₁ ≠ D.time e₂

/-- `e1 <-> e2`: the two events commute. -/
def Commutes (e₁ e₂ : D.Event) : Prop :=
  ∀ sigma, D.do_ (D.do_ sigma e₁) e₂ = D.do_ (D.do_ sigma e₂) e₁

/-- `e1 --rc--> e2`. -/
abbrev RcBefore (e₁ e₂ : D.Event) : Prop :=
  D.rc e₁ e₂ = OrderResult.Fst_then_snd

/-- `rc` leaves the pair unordered. -/
abbrev RcEither (e₁ e₂ : D.Event) : Prop :=
  D.rc e₁ e₂ = OrderResult.Either

/-! ### Bridge to the shared framework -/

/-- The tuple as the framework's signature. -/
def toMRDTSig : MRDTSig where
  State := D.Sigma
  dec_state := D.decSigma
  init := D.sigma0
  AppOp := type.OType
  dec_op := type.decOType
  Query := type.QType
  Value := type.ValType
  update := D.do_
  merge := D.merge
  query := D.query

/-- `rc` as the framework's event order. -/
def toRc : EventOrder D.toMRDTSig.toUpdateSig where
  order := D.rc

@[simp] theorem applyList_eq (sigma : D.Sigma) (pi : List D.Event) :
    D.applyList sigma pi = applySeq D.toMRDTSig.toUpdateSig sigma pi := rfl

theorem commutes_iff (e₁ e₂ : D.Event) :
    D.Commutes e₁ e₂ ↔ D.toMRDTSig.toUpdateSig.commutes e₁ e₂ := Iff.rfl

end Impl
end LeanProofs.Interface
