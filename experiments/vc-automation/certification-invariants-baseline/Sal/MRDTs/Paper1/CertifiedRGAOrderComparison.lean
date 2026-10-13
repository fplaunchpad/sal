import Sal.MRDTs.Paper1.CertifiedRGARawOrderObstruction

/-! Compare the unchanged main-branch client correctness contract and the
paper's raw-commutation order on exactly the same certified execution. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAOrderComparison
open Foundation Sal.EmbedRGA Instances.EmbedRGA Instances.ProductionRGA
open CertifiedRGARawOrderObstruction

/-- The production correctness theorem inherited unchanged from main accepts
all stored versions of exactly the configuration rejected by paperOrder. -/
theorem main_accepts_same_execution :
    IsSpecLinearizable RGAM (embedRc unaryCode)
      (embedClientSpec (α := Nat) unaryCode) embedRel (config 6) :=
  (embed (α := Nat) unaryCode).correct mint_certified

/-- There is no inconsistency: the two correctness contracts disagree on the
same original-issuer certified execution, with the same client specification. -/
theorem contracts_differ (P : OperationPolicy RGAM.AppOp) :
    MintCertifiedReach RGAM issuance (config 6) ∧
    IsSpecLinearizable RGAM (embedRc unaryCode)
      (embedClientSpec (α := Nat) unaryCode) embedRel (config 6) ∧
    ¬ EventVersionsSpecificationRA RGAM P
      (GuardedHistory.language (embedClientSpec (α := Nat) unaryCode)) (config 6) :=
  ⟨mint_certified,main_accepts_same_execution,(certified_raw_criterion_failure P).2⟩

/-- Main deliberately classifies this insert/delete pair as independent: the
deleted identifier is 1 and the inserted identifier is 3. -/
theorem main_pair_independent :
    embedSemanticCommutes (event 1) (event 2) ∧
    eRcOrder (event 1) (event 2) = RcRes.Either ∧
    eRcOrder (event 2) (event 1) = RcRes.Either := by
  simp [embedSemanticCommutes,eRcOrder,event]

theorem main_has_no_extra_edge :
    ¬ @loOn RGAM.toUpdateSig (embedRc unaryCode) (config 6).replayContext
      (↑((indices 6).image event) : Set Event) (event 1) (event 2) := by
  simp [loOn, UpdateSig.rc, ReplayPolicy.Before, embedRc, EReplayPolicy,
    eRcOrder, event]

/-- The hand-described explaining history also respects main's actual order. -/
theorem goodHistory_respects_main :
    respects goodHistory (@loOn RGAM.toUpdateSig (embedRc unaryCode)
      (config 6).replayContext (↑((indices 6).image event) : Set Event)) := by
  simp [respects,goodHistory,loOn,UpdateSig.rc,ReplayPolicy.Before,embedRc,
    EReplayPolicy,eRcOrder,event]
  change ¬ vis 6 (event 1) (event 0)
  decide

/-- The new causal edge exists independently of the supplied payload policy. -/
theorem paper_has_extra_edge (P : OperationPolicy RGAM.AppOp) :
    paperOrder P (config 6).replayContext
      (↑((indices 6).image event) : Set Event) (event 1) (event 2) := by
  refine Or.inl ⟨?_,?_⟩
  · change vis 6 (event 1) (event 2)
    decide
  · intro commute
    have unequal :
        RGAM.update (RGAM.update CertifiedRGAHistory.Controls.scratch (event 1)) (event 2) ≠
        RGAM.update (RGAM.update CertifiedRGAHistory.Controls.scratch (event 2)) (event 1) := by
      decide +kernel
    exact unequal (commute CertifiedRGAHistory.Controls.scratch)


/-- At main 50e48e2 the internal resolver was constantly Either, so its raw
replay order was exactly the empty-policy paperOrder. This witness reconstructs
the implementation, but its independent sequential read is different. -/
theorem earlier_internal_replay_control :
    respects allOps (paperOrder (commutingPolicy RGAM.AppOp) (config 6).replayContext
      (↑((indices 6).image event) : Set Event)) ∧
    applySeq RGAM.toUpdateSig RGAM.init allOps = (records 6).1 ∧
    (embedClientSpec (α := Nat) unaryCode).query
      ((embedClientSpec (α := Nat) unaryCode).run allOps) () = [30] ∧
    RGAM.query (records 6).1 () ≠ [30] := by
  refine ⟨?_,?_,?_,?_⟩
  · have causal : respects allOps (config 6).vis := by
      change respects allOps (vis 6)
      unfold respects
      decide +kernel
    apply causal.imp
    intro a b no edge
    rcases edge with ⟨visible,_⟩ | ⟨_,_,impossible,_⟩
    · exact no visible
    · exact impossible
  · decide +kernel
  · change (eSpecFold allOps).map Prod.snd = [30]
    decide +kernel
  · change [30,40] ≠ [30]
    decide

/-- The earlier public InteractionSpec.ofIndependence has no directed
concurrent preference; its causal clause uses the syntactic independence
predicate. The explaining history respects this separate public order. -/
theorem earlier_public_history_control :
    respects goodHistory (fun a b => (config 6).vis a b ∧ ¬embedSemanticCommutes a b) ∧
    (GuardedHistory.language (embedClientSpec (α := Nat) unaryCode)).admits
      (projectedLabels id goodHistory ++ [.query () [30,40]]) ∧
    ¬respects goodHistory (paperOrder (commutingPolicy RGAM.AppOp)
      (config 6).replayContext (↑((indices 6).image event) : Set Event)) := by
  refine ⟨?_,admitted_history_control⟩
  simp [respects,goodHistory,event,embedSemanticCommutes]
  change ¬vis 6 (event 1) (event 0)
  decide


#print axioms contracts_differ
end Sal.MRDTs.Paper1.CertifiedRGAOrderComparison
