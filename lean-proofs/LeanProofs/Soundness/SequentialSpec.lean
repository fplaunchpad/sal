import LeanProofs1.Soundness.Common

/-!
# Clause 2: `ops(pi) . (q => b)` is in `Spec`

The conformance side of Definition 4. It compares `do` alone against an
independent sequential language and never mentions `merge`, `vis` or
`lo^C_E`.

`SpecSound` is the paper's premise verbatim, quantified over **every** list
of events. A row that satisfies it hands any enumeration to clause 1, which
is what both rows here do.

Section 6's method for discharging either one is an abstraction function
with three conditions, which `Abstraction` states and `Abstraction.specSound`
discharges.
-/

namespace LeanProofs1.Soundness

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable {type : MRDTType} {D : Impl type}

/-- The sequential premise. For every `pi` and `q`, the projected history
`ops(pi) . (q => b)` is in `Spec`, with `b` the implementation's answer. -/
abbrev SpecSound (D : Impl type) (S : Spec type) : Prop :=
  FoldHistorySound D.toMRDTSig S

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
/-! ## The execution-scoped premise

`SpecSound` asks the row to explain **every** list of events. One row of the
paper cannot: the LWW register's answer is the value written at the greatest
key, and only a key-sorted history explains that. `HistorySound` is the form
in which the row chooses the explaining order itself, which is the `E = Y`
column of Table 1. -/

/-- **The sequential premise, execution-scoped.** The row supplies the
explaining history, rather than being asked about an arbitrary one. -/
abbrev HistorySound (D : Impl type) (S : Spec type)
    (I : Issuance D.toMRDTSig) : Prop :=
  IssuedHistoryAdequacy D.toMRDTSig (policy D) S I

end LeanProofs1.Soundness
