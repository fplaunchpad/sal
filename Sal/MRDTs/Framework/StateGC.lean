import Sal.MRDTs.Metatheory.Correctness

/-!
# Optional datatype-state garbage collection

Distributed commit-history collection belongs to the generic runtime.  This
interface is instead supplied by a datatype implementation whose materialized
representation can discard internal metadata.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- General operational certificate for datatype-state GC.  It is deliberately
separate from commit-history GC. `Physical` may contain knowledge, epoch maps,
frontiers, and per-version materializations. Silent steps are local state-GC;
visible steps refine the datatype's widened semantic execution. -/
structure StateGCProtocol (D : MRDTSig) (V : VirtualLCAResolver D) where
  Physical : Type
  semantic : Physical → Configuration D
  Valid : Physical → Prop
  PhysicalStep : Physical → Option (Label D) → Physical → Prop
  valid_preserved : ∀ {P P' l}, Valid P → PhysicalStep P l P' → Valid P'
  silent_stutters : ∀ {P P'}, Valid P → PhysicalStep P none P' →
    semantic P' = semantic P
  visible_refines : ∀ {P P' l}, Valid P → PhysicalStep P (some l) P' →
    StepV D V (semantic P) l (semantic P')

namespace StateGCProtocol

inductive Steps {D : MRDTSig} {V : VirtualLCAResolver D}
    (S : StateGCProtocol D V) :
    S.Physical → List (Option (Label D)) → S.Physical → Prop where
  | nil (P) : Steps S P [] P
  | cons {P P' P'' l ls} : S.PhysicalStep P l P' →
      Steps S P' ls P'' → Steps S P (l :: ls) P''

inductive SemanticSteps {D : MRDTSig} (V : VirtualLCAResolver D) :
    Configuration D → List (Label D) → Configuration D → Prop where
  | nil (C) : SemanticSteps V C [] C
  | cons {C C' C'' l ls} : StepV D V C l C' →
      SemanticSteps V C' ls C'' → SemanticSteps V C (l :: ls) C''

def eraseLabels {D : MRDTSig} :
    List (Option (Label D)) → List (Label D) := List.filterMap id

/-- Any valid physical trace erases to widened semantic execution. State-GC
steps stutter, while subsequent update/merge/query steps remain covered. -/
theorem refines {D : MRDTSig} {V : VirtualLCAResolver D}
    (S : StateGCProtocol D V) {P P' : S.Physical} {ls}
    (valid : S.Valid P) (run : Steps S P ls P') :
    SemanticSteps V (S.semantic P) (eraseLabels ls) (S.semantic P') := by
  induction run with
  | nil => exact .nil _
  | @cons P P₁ P₂ l ls one rest ih =>
      have valid₁ := S.valid_preserved valid one
      have tail := ih valid₁
      cases l with
      | none =>
          rw [← S.silent_stutters valid one]
          simpa [eraseLabels] using tail
      | some l =>
          exact SemanticSteps.cons (S.visible_refines valid one)
            (by simpa [eraseLabels] using tail)

end StateGCProtocol

/-- A compact interpreter related to the full semantic state.  Epoch maps,
frontiers, retained spines, and reclaimed-ID evidence may be stored in
`CompactState` or `Evidence`; the generic framework does not prescribe their
encoding. -/
structure StateGCCertificate (D : MRDTSig)
    (I : Issuance D) where
  CompactState : Type
  Evidence : Type
  Represents : CompactState → D.State → Prop
  EvidenceValid : Evidence → CompactState → D.State → Prop
  /-- Cross-branch condition inherited from the semantic execution. Timestamp-
  keyed representations typically require equal timestamps to identify the
  same event; other datatypes may use `True`. -/
  Compatible : D.State → D.State → Prop

  init : CompactState
  collect : Evidence → CompactState → CompactState
  update : CompactState → Op D.AppOp → CompactState
  merge : CompactState → CompactState → CompactState → CompactState
  query : CompactState → D.Query → D.Value

  init_represents : Represents init D.init
  collect_represents : ∀ {e compact full},
    Represents compact full → EvidenceValid e compact full →
      Represents (collect e compact) full
  update_represents : ∀ {compact full op},
    Represents compact full → I.CanIssue op full →
      Represents (update compact op) (D.update full op)
  merge_represents : ∀ {cl ca cb l a b},
    Represents cl l → Represents ca a → Represents cb b →
      Compatible a b →
      Represents (merge cl ca cb) (D.mergeL l a b)
  query_correct : ∀ {compact full}, Represents compact full →
    ∀ q, query compact q = D.query full q

/-- Some implementations can compute a merge result from the two branch
heads while the semantic virtual LCA remains ghost state. -/
structure HeadOnlyMergeCapability {D : MRDTSig} {I : Issuance D}
    (S : StateGCCertificate D I) where
  MergeEvidence : S.CompactState → S.CompactState →
    D.State → D.State → D.State → Type
  mergeHeads : ∀ {ca cb a b l}, MergeEvidence ca cb l a b → S.CompactState
  correct : ∀ {ca cb a b l} (e : MergeEvidence ca cb l a b),
    S.Represents ca a → S.Represents cb b → S.Compatible a b →
      S.Represents (mergeHeads e) (D.mergeL l a b)

end Sal.MRDTs
