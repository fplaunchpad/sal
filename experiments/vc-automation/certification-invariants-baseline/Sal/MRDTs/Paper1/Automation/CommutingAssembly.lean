import Sal.MRDTs.Paper1.Automation.CommonVerification
namespace Sal.MRDTs.Paper1.ConcreteMRDT.CommutingPort
open Foundation
variable {D : MRDTSig}
theorem automatedJoinAt (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (vcs : Raw.MergeVCs (commutingPolicy D.AppOp) (representation D) (scheme commute))
    (C : ReplayContext D.toUpdateSig) : JoinAt D C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have rep : ∀ E s, Supported C E → @IsCanonicalState D.toUpdateSig (ReplayPolicy.default _) C E s → representation D C E s := by
    rintro E s sup ⟨π,hp,_,hf⟩
    exact ⟨sup,π,hp,hf⟩
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have kit := replaySupply commute C
  have sizes := Raw.join_at_sizes vcs
    (unique commute) initial finite C (fun _ _ _ h k => trans h k) irrefl
    kit.represented kit.peel
  have joined := sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun _ _ h _ => h.elim) (fun _ _ h _ => h.elim)
    (rep _ _ (fun e h => sup₁ e h.1) hl)
    (rep _ _ sup₁ ⟨π₁,hp₁,by assumption,by assumption⟩)
    (rep _ _ sup₂ ⟨π₂,hp₂,by assumption,by assumption⟩)
  obtain ⟨_,π,hp,hf⟩ := joined
  exact ⟨π,hp,hp.1.imp (fun {_ _} _ => by simp [loOn,UpdateSig.rc,UpdateSig.replayOrder,ReplayPolicy.default,ReplayPolicy.unconstrained]),hf⟩

theorem automatedCanonicalConfig (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (vcs : Raw.MergeVCs (commutingPolicy D.AppOp) (representation D) (scheme commute))
    {I : Issuance D} {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) : CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV (fun C _ => automatedJoinAt commute vcs C.replayContext) reach

def automatedReplayConditions (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (vcs : Raw.MergeVCs (commutingPolicy D.AppOp) (representation D) (scheme commute))
    (I : Issuance D) : VCReplayConditions (commutingPolicy D.AppOp) I where
  representation := representation D
  scheme := scheme commute
  laws := GuardedReplay.ofUniform (restricted_of_all_commute commute)
  vcs := vcs
  unique := unique commute
  initial := initial
  finite := finite
  canonical := canonical commute
  supported := fun _ _ _ h => h.1
  replaySupply := fun C _ _ _ _ _ _ _ _ _ _ => replaySupply commute C
  representedVersions := by
    intro C reach v s E hv
    have good := automatedCanonicalConfig commute vcs reach
    obtain ⟨π,hp,_,hf⟩ := good.canonical v s E hv
    exact ⟨good.version_events_supported v s E hv,π,hp,hf⟩

def automatedScopedConditions (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (vcs : Raw.MergeVCs (commutingPolicy D.AppOp) (representation D) (scheme commute))
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} (I : Issuance D)
    (history : EventExecutionHistoryAdequacy D (commutingPolicy D.AppOp) S I) :
    ScopedVCConditions (commutingPolicy D.AppOp) S I where
  toVCReplayConditions := automatedReplayConditions commute vcs I
  history := history

end Sal.MRDTs.Paper1.ConcreteMRDT.CommutingPort
