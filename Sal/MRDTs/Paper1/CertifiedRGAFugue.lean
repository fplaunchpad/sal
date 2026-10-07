import Sal.MRDTs.Paper1.CertifiedPrefixScope
import Sal.MRDTs.Instances.FugueMaxReplayProof

/-! Certified-prefix equality for the unchanged registered FugueMax carrier,
including its insertion birth set and original executable issuer. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAFugue
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

private theorem respects_lo (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (H : Set (Op Payload)) (xs : List (Op Payload)) (perm : listPermOf xs H)
    (support : H ⊆ C.events) (ordered : respects xs C.vis) :
    respects xs (loOn C.replayContext H) := by
  apply ordered.imp_of_mem
  intro a b ha hb hn edge
  have ea := support ((perm.2 a).mp ha)
  have eb := support ((perm.2 b).mp hb)
  exact hn (rc_visible C mint trans eb ea ((lo_iff_rc C mint trans H eb ea).mp edge))

theorem unique (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis) :
    ∀ H s t, CertifiedPrefixScope.represented (datatype Γ) C.replayContext H s →
      CertifiedPrefixScope.represented (datatype Γ) C.replayContext H t → s = t := by
  intro H s t hs ht
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2
  have subX : ∀ e ∈ xs, e ∈ C.events := fun e he => hs.1 ((px.2 e).mp he)
  have subY : ∀ e ∈ ys, e ∈ C.events := fun e he => ht.1 ((py.2 e).mp he)
  have lx := respects_lo Γ C mint trans H xs px hs.1 rx
  have ly := respects_lo Γ C mint trans H ys py ht.1 ry
  have wfX := projected_wf C mint trans px (fun _ h => hs.1 h) lx
  have wfY := projected_wf C mint trans py (fun _ h => ht.1 h) ly
  have live : mFold Γ (xs.map recordOf) = mFold Γ (ys.map recordOf) := by
    rw [liveFold_project C mint trans xs subX, liveFold_project C mint trans ys subY]
    apply f_fold_canon Γ wfX wfY
    intro o
    simp only [List.mem_map]
    constructor
    · rintro ⟨e,he,eq⟩
      exact ⟨e,(py.2 e).mpr ((px.2 e).mp he),eq⟩
    · rintro ⟨e,he,eq⟩
      exact ⟨e,(px.2 e).mpr ((py.2 e).mp he),eq⟩
  apply fx.symm.trans
  apply Eq.trans _ fy
  rw [rawFold_records,rawFold_records]
  change State.mk _ _ = State.mk _ _
  apply congrArg₂ State.mk
  · exact live
  · apply Finset.ext
    intro g
    simp only [stateOf,List.mem_toFinset,mMinted,List.mem_filter,List.mem_map]
    constructor
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(py.2 e).mpr ((px.2 e).mp he),eq⟩,hi⟩
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(px.2 e).mpr ((py.2 e).mp he),eq⟩,hi⟩

/-- Mint honesty is the original issuer's fact at actual origin histories.
Replay laws use that fixed evidence, not reissuance at reordered prefixes. -/
theorem laws (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (P : OperationPolicy Payload) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (datatype Γ) C.replayContext) P :=
  CertifiedPrefixScope.laws (datatype Γ) C.replayContext (unique Γ C mint trans)
    (fun _ _ vis => C.vis_src vis) P

#print axioms unique
#print axioms laws
end Sal.MRDTs.Paper1.CertifiedRGAFugue
