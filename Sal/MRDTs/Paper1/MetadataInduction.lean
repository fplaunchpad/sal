import Sal.MRDTs.Paper1.MetadataSubstitution

/-! Metadata companions required by the observational merge induction.
They are directed preservation laws for the VC rewrites, not unrestricted
saturation of representation under observational equivalence. In particular,
the induction must choose an abstract-maximal event whose reconstruction also
preserves metadata; arbitrary abstract maxima need not do so. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def Supported (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) : Prop :=
  ∀ e ∈ E, e ∈ C.events

def ConflictClosed (A : Model D) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) : Prop :=
  ∀ e f, C.vis e f → ¬ Commutes A e f → f ∈ E → e ∈ E

structure PeelChoice (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (C : ReplayContext D.toUpdateSig)
    (U : Set (Op D.AppOp)) where
  event : Op D.AppOp
  member : event ∈ U
  maximal : ∀ x ∈ U, x ≠ event → ¬ order A P C U event x
  remainder : D.State
  past : D.State
  remainder_admissible : Admissible A P R C (U \ {event}) remainder
  past_admissible : Admissible A P R C (causalPast A C event \ {event}) past
  reconstructed_past : R C (causalPast A C event) (D.update past event)
  reconstructed_union : R C U (D.update remainder event)

/-- The initial rewrite's metadata companion. Analogous directed companions
are needed for causal delta and the two redistribution equations. -/
def InitMetadata (R : Representation D) : Prop :=
  ∀ C E s, Supported C E → R C E s → R C E (D.merge D.init D.init s)

def InitialMetadata (R : Representation D) : Prop :=
  ∀ C E s, R C E s → R C ∅ D.init

/-- The empty-side induction case follows from the observable init VC and
metadata obligations alone; representation Join is not a premise. -/
theorem join_empty_left {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D}
    {past : ReplayContext D.toUpdateSig → Op D.AppOp → Set (Op D.AppOp)}
    (vcs : MergeVCs A P R past)
    (canonical : RepresentsCanonical A P R) (substitute : MetadataSubstitution A R)
    (initial : InitialMetadata R) (initMetadata : InitMetadata R)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (l a b : D.State)
    (supported : Supported C E) (hl : R C ∅ l) (ha : R C ∅ a) (hb : R C E b) :
    Admissible A P R C E (D.merge l a b) := by
  have target := canonical C E b hb
  have eq := vcs.delta.init C E b supported ⟨target,hb⟩
  have can := canonical_congr target (equivalent_symm eq)
  have metadata := initMetadata C E b supported hb
  have frame := substitute C ∅ E l a b D.init D.init b
    (by simp) supported (by simpa using hl) ha hb
    (by simpa using initial C E b hb) (initial C E b hb) hb
  exact ⟨canonical_congr can (equivalent_symm frame.1),
    by simpa using frame.2 (by simpa using metadata)⟩

end Sal.MRDTs.Paper1.AbstractMRDT
