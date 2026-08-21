import Sal.MRDTs.Metatheory.Correctness

/-!
# Optional datatype-state garbage collection

Distributed commit-history collection belongs to the generic runtime.  This
interface is instead supplied by a datatype implementation whose materialized
representation can discard internal metadata.
-/

namespace Sal.MRDTs

open Sal.Emulation

/-- A compact interpreter related to the full semantic state.  Epoch maps,
frontiers, retained spines, and reclaimed-ID evidence may be stored in
`CompactState` or `Evidence`; the generic framework does not prescribe their
encoding. -/
structure StateGCCertificate (D : MRDTSig)
    (G : GenerationContract D) where
  CompactState : Type
  Evidence : Type
  Represents : CompactState → D.State → Prop
  EvidenceValid : Evidence → CompactState → D.State → Prop

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
    Represents compact full → G.Guard op full →
      Represents (update compact op) (D.update full op)
  merge_represents : ∀ {cl ca cb l a b},
    Represents cl l → Represents ca a → Represents cb b →
      Represents (merge cl ca cb) (D.mergeL l a b)
  query_correct : ∀ {compact full}, Represents compact full →
    ∀ q, query compact q = D.query full q

/-- Some implementations can compute a merge result from the two branch
heads while the semantic virtual LCA remains ghost state. -/
structure HeadOnlyMergeCapability {D : MRDTSig} {G : GenerationContract D}
    (S : StateGCCertificate D G) where
  MergeEvidence : S.CompactState → S.CompactState →
    D.State → D.State → D.State → Type
  mergeHeads : ∀ {ca cb a b l}, MergeEvidence ca cb l a b → S.CompactState
  correct : ∀ {ca cb a b l} (e : MergeEvidence ca cb l a b),
    S.Represents ca a → S.Represents cb b →
      S.Represents (mergeHeads e) (D.mergeL l a b)

end Sal.MRDTs
