import LeanProofs.Soundness.Common

/-!
# Clause 2: `ops(pi) . (q => b)` is in `Spec`

The conformance side of Definition 4. It compares `do` alone against an
independent sequential language and never mentions `merge`, `vis` or
`lo^C_E`.

Two forms of the premise appear here.

* `SpecSound` is the paper's premise verbatim, quantified over **every**
  list of events. A row that satisfies it hands any enumeration to clause 1.
* `HistorySound` is the execution-scoped form, in which the row **chooses**
  the explaining order itself. The LWW register is the first row that needs
  it, because its answer is the greatest write key and only a key-sorted
  history explains that. This is the `E = Y` column of Table 1.

Section 6's method for discharging either one is an abstraction function
with three conditions, which `Abstraction` states and `Abstraction.specSound`
discharges.
-/

namespace LeanProofs.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-- The sequential premise. For every `pi` and `q`, the projected history
`ops(pi) . (q => b)` is in `Spec`, with `b` the implementation's answer. -/
abbrev SpecSound (D : Impl type) (S : Spec type) : Prop :=
  FoldHistorySound D.toMRDTSig S

/-- The scoped sequential premise: a witness may be selected per event set,
given a mint-honest configuration and a supported, causally closed, finite
event set. -/
abbrev HistorySound (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  IssuedHistoryAdequacy D.toMRDTSig (policy D) S I

/-! ## The abstraction function of Section 6

Section 6 discharges the sequential premise with an abstraction function
`alpha : Sigma -> Phi` and three conditions on it. `Abstraction` below is
that function together with those conditions, stated separately as the
paper states them, and `Abstraction.specSound` is the paper's induction on
the length of an event sequence. -/

/-- An abstraction function and the three conditions of Section 6. -/
structure Abstraction (D : Impl type)
    (M : DeterministicSpec type.OType type.QType type.ValType) where
  /-- `alpha : Sigma -> Phi`, relating implementation states to
  specification states. -/
  alpha : D.Sigma → M.State
  /-- **(i)** `alpha(sigma0) = phi0`. -/
  init : alpha D.sigma0 = M.initial
  /-- **(ii)** `alpha(sigma) -o-> alpha(do(sigma, t, r, o))`. -/
  step : ∀ (s : D.Sigma) (e : D.Event),
    alpha (D.do_ s e) = M.update (alpha s) e.op
  /-- **(iii)** `alpha(sigma) -q => query(sigma,q)-> alpha(sigma)`. -/
  observes : ∀ (s : D.Sigma) (q : type.QType),
    M.query (alpha s) q = D.query s q

namespace Abstraction

variable {M : DeterministicSpec type.OType type.QType type.ValType}

/-- Conditions (i) and (ii), lifted to a whole sequence by induction on its
length: `alpha(pi(sigma0)) = ops(pi)(phi0)`. -/
theorem fold (A : Abstraction D M) (s : D.Sigma) (pi : List D.Event) :
    A.alpha (D.applyList s pi) = (pi.map Op.op).foldl M.update (A.alpha s) := by
  induction pi generalizing s with
  | nil => rfl
  | cons e rest ih =>
      simpa [Impl.applyList, A.step s e] using ih (D.do_ s e)

/-- **The sequential premise, from the three conditions.** Condition (iii)
then gives agreement of query results. -/
theorem specSound (A : Abstraction D M) : SpecSound D M.toSpec := by
  intro pi q
  have hlabels : projectedUpdates (D := D.toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, M.updates_query_iff, ← A.init, ← A.fold, A.observes]
  rfl

end Abstraction

end LeanProofs.Soundness
