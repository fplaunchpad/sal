import Sal.MRDTs.GC.Refinement
import Sal.MRDTs.Framework.StateGC

/-!
# Composition of distributed commit GC and datatype-state GC

Commit-history collection changes only the replica-local commit store.  A
datatype-state protocol changes the physical materialization while retaining
the same semantic configuration.  This module composes the two independently
supplied mechanisms and proves the combined runtime refines the no-GC
semantics.  There is no global/STW intermediate semantics.
-/

namespace Sal.MRDTs.GC

open Sal.MRDTs Sal.MRDTs.Foundation

variable {D : MRDTSig} {V : VirtualLCAResolver D}

/-- Physical state of the combined runtime.  Epochs and datatype evidence are
owned by `state`; the generic commit protocol owns only `stores`. -/
structure Combined (S : StateGCProtocol D V) where
  state : S.Physical
  stores : World

def Combined.runtime (S : StateGCProtocol D V) (P : Combined S) : Runtime D :=
  ⟨S.semantic P.state, P.stores⟩

def Combined.Valid (S : StateGCProtocol D V) (P : Combined S) : Prop :=
  S.Valid P.state ∧ (P.runtime S).WellFormed

/-- A combined transition is either a datatype-state/runtime transition, with
the matching commit-store evolution for visible labels, or a silent fetch or
commit-history collection. -/
inductive CombinedStep (S : StateGCProtocol D V) :
    Combined S → Option (Label D) → Combined S → Prop where
  | state {P P' : Combined S} {l : Option (Label D)}
      (valid : P.Valid S)
      (physical : S.PhysicalStep P.state l P'.state)
      (stores : match l with
        | none => P'.stores = P.stores
        | some label => StoreEvolution (P.runtime S) (P'.runtime S) label)
      (valid' : P'.Valid S) : CombinedStep S P l P'
  | history {P : Combined S} {stores' : World}
      (step : RuntimeStep D (P.runtime S) none
        ⟨S.semantic P.state, stores'⟩) :
      CombinedStep S P none ⟨P.state, stores'⟩

inductive CombinedSteps (S : StateGCProtocol D V) :
    Combined S → List (Option (Label D)) → Combined S → Prop where
  | nil (P) : CombinedSteps S P [] P
  | cons {P P' P'' l ls} : CombinedStep S P l P' →
      CombinedSteps S P' ls P'' → CombinedSteps S P (l :: ls) P''

/-- The combined protocol is itself a datatype-state protocol.  This is the
virtual-LCA composition theorem: state collection, fetch, and commit GC all
stutter; every visible step is supplied by the datatype protocol. -/
def combinedProtocol (S : StateGCProtocol D V) : StateGCProtocol D V where
  Physical := Combined S
  semantic P := S.semantic P.state
  Valid := Combined.Valid S
  PhysicalStep := CombinedStep S
  valid_preserved := by
    intro P P' l h one
    cases one with
    | state _ _ _ h' => exact h'
    | history step =>
        refine ⟨h.1, ?_⟩
        cases step with
        | fetch _ _ _ wf' => exact wf'
        | gc _ _ _ wf' => exact wf'
  silent_stutters := by
    intro P P' h one
    cases one with
    | state _ physical _ _ => exact S.silent_stutters h.1 physical
    | history _ => rfl
  visible_refines := by
    intro P P' l h one
    cases one with
    | state _ physical _ _ => exact S.visible_refines h.1 physical

namespace CombinedSteps

def toProtocol {S : StateGCProtocol D V} {P P' : Combined S} {ls}
    (run : CombinedSteps S P ls P') :
    StateGCProtocol.Steps (combinedProtocol S) P ls P' := by
  induction run with
  | nil => exact .nil _
  | cons one _ ih => exact .cons one ih

/-- Finite combined traces refine widened no-GC semantics directly. -/
theorem refinesV {S : StateGCProtocol D V} {P P' : Combined S} {ls}
    (valid : P.Valid S) (run : CombinedSteps S P ls P') :
    StateGCProtocol.SemanticSteps V (S.semantic P.state)
      (StateGCProtocol.eraseLabels ls) (S.semantic P'.state) :=
  StateGCProtocol.refines (combinedProtocol S) valid run.toProtocol

/-- Ordinary refinement is available when the datatype protocol proves its
visible steps are raw steps, rather than genuine virtual-LCA steps. -/
theorem refinesRaw {S : StateGCProtocol D V} {P P' : Combined S} {ls}
    (valid : P.Valid S) (run : CombinedSteps S P ls P')
    (raw : ∀ {A A' l}, S.Valid A → S.PhysicalStep A (some l) A' →
      Sal.MRDTs.Step D (S.semantic A) l (S.semantic A')) :
    CoreSteps D (S.semantic P.state)
      (StateGCProtocol.eraseLabels ls) (S.semantic P'.state) := by
  induction run with
  | nil => exact .nil _
  | @cons P P₁ P₂ l tail one rest ih =>
      have valid₁ : P₁.Valid S := by
        cases one with
        | state _ _ _ h' => exact h'
        | history step =>
            refine ⟨valid.1, ?_⟩
            cases step with
            | fetch _ _ _ wf' => exact wf'
            | gc _ _ _ wf' => exact wf'
      have tailProof := ih valid₁
      cases l with
      | none =>
          have hsem : S.semantic P₁.state = S.semantic P.state := by
            cases one with
            | state _ physical _ _ => exact S.silent_stutters valid.1 physical
            | history _ => rfl
          rw [← hsem]
          simpa [StateGCProtocol.eraseLabels] using tailProof
      | some label =>
          cases one with
          | state _ physical _ _ =>
              exact CoreSteps.cons (raw valid.1 physical)
                (by simpa [StateGCProtocol.eraseLabels] using tailProof)

end CombinedSteps

end Sal.MRDTs.GC
