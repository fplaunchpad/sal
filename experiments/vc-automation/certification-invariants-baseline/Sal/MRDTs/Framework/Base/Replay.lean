import Sal.MRDTs.Framework.Base.UpdateSignature
import Mathlib.Data.Set.Basic

/-!
# Replay primitives

Generic list and fold definitions used to state MRDT replay properties. These
definitions are independent of configurations and execution semantics.
-/

namespace Sal.MRDTs.Foundation

/-- Apply a sequence of events to a state from left to right. -/
def applySeq (D : UpdateSig) (s : D.State)
    (π : List (Op D.AppOp)) : D.State :=
  π.foldl D.update s

/-- Appending one event applies it to the state produced by the prefix. -/
theorem applySeq_append_single {D : UpdateSig} (s : D.State)
    (π : List (Op D.AppOp)) (e : Op D.AppOp) :
    applySeq D s (π ++ [e]) = D.update (applySeq D s π) e := by
  simp [applySeq, List.foldl_append]

/-- `π` enumerates exactly the finite set `E`, without duplicates. -/
def listPermOf {α : Type} (π : List α) (E : Set α) : Prop :=
  π.Nodup ∧ ∀ a, a ∈ π ↔ a ∈ E

/-- `π` extends `R`; `R` need not itself be transitive. -/
def respects {α : Type} (π : List α) (R : α → α → Prop) : Prop :=
  π.Pairwise (fun a b => ¬ R b a)

end Sal.MRDTs.Foundation
