import Sal.MRDTs.Paper1.CertifiedFugueVC
import Sal.MRDTs.Paper1.CertifiedClosedExecution

namespace Sal.MRDTs.Paper1.CertifiedFugueVCExecution
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

theorem folds_equal (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (H : Set (Op Payload)) (xs ys : List (Op Payload))
    (px : listPermOf xs H) (py : listPermOf ys H) (support : H ⊆ C.events)
    (rx : respects xs (loOn C.replayContext H))
    (ry : respects ys (loOn C.replayContext H)) :
    applySeq (datatype Γ).toUpdateSig (datatype Γ).init xs =
      applySeq (datatype Γ).toUpdateSig (datatype Γ).init ys := by
  have subX : ∀ e ∈ xs, e ∈ C.events := fun e he => support ((px.2 e).mp he)
  have subY : ∀ e ∈ ys, e ∈ C.events := fun e he => support ((py.2 e).mp he)
  have wfX := projected_wf C mint trans px (fun _ h => support h) rx
  have wfY := projected_wf C mint trans py (fun _ h => support h) ry
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
  rw [rawFold_records,rawFold_records]
  change State.mk _ _ = State.mk _ _
  apply congrArg₂ State.mk
  · exact live
  · apply Finset.ext
    intro g
    simp only [List.mem_toFinset,mMinted,List.mem_filter,List.mem_map]
    constructor
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(py.2 e).mpr ((px.2 e).mp he),eq⟩,hi⟩
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(px.2 e).mpr ((py.2 e).mp he),eq⟩,hi⟩

theorem represented_of_canonical (Γ : OrderedPrefixCode)
    (C : Configuration (datatype Γ)) (mint : MintHonest (datatype Γ) (applicable Γ) C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (H : Set (Op Payload)) (s : State) (support : H ⊆ C.events)
    (canonical : IsCanonicalState C.replayContext H s) :
    representation Γ C.replayContext H s := by
  obtain ⟨xs,perm,order,fold⟩ := canonical
  obtain ⟨t,rep⟩ := supply Γ C.replayContext ⟨C,mint,rfl⟩ trans irrefl H xs perm support
  obtain ⟨ys,py,ry,fy⟩ := rep.2.2.2.2
  have ly := respects_lo Γ C mint trans H ys py support ry
  have same : t = s := fy.symm.trans ((folds_equal Γ C mint trans H ys xs py perm support ly order).trans fold)
  simpa only [same] using rep

theorem canonical_of_represented (Γ : OrderedPrefixCode)
    (C : ReplayContext (datatype Γ).toUpdateSig) (H : Set (Op Payload)) (s : State)
    (rep : representation Γ C H s) : IsCanonicalState C H s := by
  obtain ⟨K,mint,rfl⟩ := rep.1
  obtain ⟨xs,perm,order,fold⟩ := rep.2.2.2.2
  exact ⟨xs,perm,respects_lo Γ K mint rep.2.1 H xs perm rep.2.2.2.1 order,fold⟩

theorem closedJoinAt (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (FugueMax.generation Γ).CanIssue C) :
    CertifiedClosedExecution.ClosedJoinAt (datatype Γ) C.replayContext := by
  intro A B l a b trans irrefl supA supB closedA closedB hl ha hb
  apply canonical_of_represented
  exact CertifiedFugueVC.representationJoin Γ C.replayContext A B l a b
    (fun _ _ _ h k => trans h k) irrefl supA supB closedA closedB
    (represented_of_canonical Γ C mint (fun _ _ _ h k => trans h k) irrefl _ _
      (fun x hx => supA x hx.1) hl)
    (represented_of_canonical Γ C mint (fun _ _ _ h k => trans h k) irrefl _ _ supA ha)
    (represented_of_canonical Γ C mint (fun _ _ _ h k => trans h k) irrefl _ _ supB hb)

theorem canonicalConfig (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C) : CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_execution (closedJoinAt Γ) execution

theorem representedVersions (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v : Version} {s : State} {H : Set (Op Payload)} (hv : C.ver v = some (s,H)) :
    representation Γ C.replayContext H s := by
  have good := canonicalConfig Γ execution
  exact represented_of_canonical Γ C execution.mintHonest
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl H s
    (fun e he => good.version_events_supported v s H hv e he) (good.canonical v s H hv)

#print axioms closedJoinAt
#print axioms representedVersions
end Sal.MRDTs.Paper1.CertifiedFugueVCExecution
