import Sal.MRDTs.Paper1.MetadataInduction

/-! Metadata dependencies are causal event relations, distinct from semantic
state equality. They cover observable causal conflicts and may additionally
retain commuting predecessors whose tags affect reconstruction. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

structure MetadataDependencies (A : Model D) (C : ReplayContext D.toUpdateSig) where
  before : Op D.AppOp → Op D.AppOp → Prop
  causal : ∀ a b, before a b → C.vis a b
  covers : ∀ a b, C.vis a b → ¬ Commutes A a b → before a b

namespace MetadataDependencies

def ofConcrete (A : Model D) (C : ReplayContext D.toUpdateSig) : MetadataDependencies A C where
  before a b := C.vis a b ∧ ¬ D.toUpdateSig.commutes a b
  causal _ _ h := h.1
  covers _ _ vis nc := ⟨vis,fun h => nc (of_state_commutes h)⟩

def Closed {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (E : Set (Op D.AppOp)) : Prop :=
  ∀ a b, M.before a b → b ∈ E → a ∈ E

def Past {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (e : Op D.AppOp) : Set (Op D.AppOp) :=
  {x | x = e ∨ Relation.TransGen M.before x e}

theorem past_subset {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (E : Set (Op D.AppOp)) (e : Op D.AppOp)
    (closed : M.Closed E) (mem : e ∈ E) : M.Past e ⊆ E := by
  rintro x (rfl | h)
  · exact mem
  · induction h using Relation.TransGen.head_induction_on with
    | single edge => exact closed _ _ edge mem
    | head edge _ ih => exact closed _ _ edge ih

theorem observable_past_subset {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (e : Op D.AppOp) : causalPast A C e ⊆ M.Past e := by
  rintro x (rfl | h)
  · exact Or.inl rfl
  · apply Or.inr
    induction h with
    | single edge =>
      exact .single (M.covers _ _ edge.1
        (fun hc => edge.2 ((commutes_iff A _ _).mpr hc)))
    | tail _ edge ih =>
      exact .tail ih (M.covers _ _ edge.1
        (fun hc => edge.2 ((commutes_iff A _ _).mpr hc)))

theorem closed_implies_conflictClosed {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (E : Set (Op D.AppOp)) (closed : M.Closed E) :
    ConflictClosed A C E := fun a b vis nc mem => closed a b (M.covers a b vis nc) mem

/-- Removing an event maximal for metadata dependencies preserves the closure
needed by the smaller induction problem. Abstract maximality alone does not. -/
theorem closed_diff_of_max {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (U E : Set (Op D.AppOp)) (e : Op D.AppOp)
    (subset : E ⊆ U) (closed : M.Closed E)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ M.before e x) : M.Closed (E \ {e}) := by
  intro a b edge hb
  refine ⟨closed a b edge hb.1,?_⟩
  intro equal
  change a = e at equal
  subst a
  exact maximal b (subset hb.1) hb.2 edge

end MetadataDependencies

/-- The induction chooses a maximum safe for both semantic order and metadata
dependencies, with represented update reconstructions in the richer past. -/
structure DependencyPeelChoice (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (C : ReplayContext D.toUpdateSig)
    (M : MetadataDependencies A C) (U : Set (Op D.AppOp)) where
  event : Op D.AppOp
  member : event ∈ U
  semantic_maximal : ∀ x ∈ U, x ≠ event → ¬ order A P C U event x
  metadata_maximal : ∀ x ∈ U, x ≠ event → ¬ M.before event x
  remainder : D.State
  past : D.State
  remainder_admissible : Admissible A P R C (U \ {event}) remainder
  past_admissible : Admissible A P R C (M.Past event \ {event}) past
  reconstructed_past : R C (M.Past event) (D.update past event)
  reconstructed_union : R C U (D.update remainder event)

/-- VC reconstruction pasts are explicitly selected by the metadata scheme;
semantic commutation and the RA order remain abstraction-based. -/
abbrev DependencyMergeVCs (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies A C) : Prop :=
  MergeVCs A P R (fun C e => (scheme C).Past e)

end Sal.MRDTs.Paper1.AbstractMRDT
