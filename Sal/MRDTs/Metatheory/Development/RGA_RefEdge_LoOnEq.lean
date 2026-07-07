import Sal.MRDTs.Metatheory.Conditioned.RGA_Instance
import Sal.MRDTs.Metatheory.Conditioned.BornApplicable_Guard
import Sal.MRDTs.Metatheory.Development.RGA_RefEdge_FromAccurate

/-!
# `RefEdge E (loOnEq)` from reference-causality + non-commutation

*Additive; modifies no existing file; 0 `sorry`.*

The engine's `RefEdge E (loOnEq)` — references become `loOnEq`-order edges — follows from the first
`loOnEq` disjunct `vis a b ∧ ¬ eqCommutesOn a b`, i.e. from two facts about referenced pairs:
* `reference ⟹ vis` (`hrefVis`) — established for reachable configs via `insertedIn_ev_of_ref`
  (`RGA_RefEdge_FromAccurate`) + the `apply` step's `ev → new op`;
* creator/user **non-commutation** (`hncomm`) — an op and an op referencing its id do not `≈`-commute.

This closes the `RefEdge` obligation of `hReady`/`hFoldCanon` down to exactly those two facts.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGARefEdgeLoOnEq

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient (loOnEq eqCommutesOn)
open Sal.Metatheory.RGAInstance (rgaEqEquiv' WfOpA)
open RGANoopFeasible (RefEdge refsOf)

/-- **`RefEdge E (loOnEq)`** from reference-causality (`hrefVis`) and creator/user non-commutation
(`hncomm`). Each referenced pair `(a, b)` (`a.1 ∈ refsOf b`, `a.1 ≠ b.1`) gets `loOnEq a b` via the
first disjunct `vis a b ∧ ¬ eqCommutesOn a b`. -/
theorem refEdge_loOnEq_of_refVis (E : Set op_t) (vis : op_t → op_t → Prop)
    (hrefVis : ∀ a ∈ E, ∀ b ∈ E, a.1 ∈ refsOf b → a.1 ≠ b.1 → vis a b)
    (hncomm : ∀ a ∈ E, ∀ b ∈ E, a.1 ∈ refsOf b → a.1 ≠ b.1 →
        ¬ eqCommutesOn rgaEqEquiv' WfOpA a b) :
    RefEdge E (loOnEq rgaEqEquiv' WfOpA vis E) := by
  intro a ha b hb href hne
  exact Or.inl ⟨hrefVis a ha b hb href hne, hncomm a ha b hb href hne⟩

#print axioms refEdge_loOnEq_of_refVis

end Sal.Metatheory.RGARefEdgeLoOnEq
