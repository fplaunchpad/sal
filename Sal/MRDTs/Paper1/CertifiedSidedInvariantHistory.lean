import Sal.MRDTs.Paper1.CertifiedRGAHistoryCommutation
import Sal.MRDTs.Paper1.InvariantOrder
import Sal.MRDTs.Paper1.CertifiedSidedInvariant

namespace Sal.MRDTs.Paper1.CertifiedSidedInvariantHistory
open Foundation Instances.ProductionRGA CertifiedRGAHistory
open Sal.EmbedRGA (OrderedPrefixCode)

def emptyPolicy : OperationPolicy Instances.SidedEmbedRGA.SOp where
  before _ _ := False

theorem canonical_history_data {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State} {E : Set (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).Query) :
    listPermOf (SidedWitness.canonical ops) E ∧
      Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ (SidedWitness.canonical ops) = s ∧
      respects (SidedWitness.canonical ops) (projectedSpecVisibility id
        (GuardedHistory.language (sidedClientSpec Γ)) C.replayContext) ∧
      (GuardedHistory.language (sidedClientSpec Γ)).admits
        (projectedLabels id (SidedWitness.canonical ops) ++ [.query q ((Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s q)]) := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    have hseq := sidedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := sidedLegal_of_seqOK hseq
    have hcan := SidedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : SHonestCore Γ C.replayContext :=
      sHonest_core (sHonest_of_mint exec.mintHonest)
    have hwfReplay : SWf Γ ops :=
      CertifiedRGAScope.Sided.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : SWf Γ (SidedWitness.canonical ops) :=
      sWf_of_seqOK hseq
    have hcanonFold :
        sFold Γ (SidedWitness.canonical ops) = sFold Γ ops :=
      s_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : sFold Γ (SidedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := sided_seq_read hseq
    have hrel : sidedRel s ((sidedClientSpec Γ).run
        (SidedWitness.canonical ops)) := by
      unfold sidedRel
      change s.map sProj = (sSpecFold (SidedWitness.canonical ops)).filter
        (fun p => decide (p.1 ≠ 0))
      rw [← hstate]
      exact hsound
    have observes : ∀ query, (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s query =
        (sidedClientSpec Γ).query ((sidedClientSpec Γ).run (SidedWitness.canonical ops)) query := by
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        (((sidedClientSpec Γ).run (SidedWitness.canonical ops)).filter
          (fun p => decide (p.1 ≠ 0))).map Prod.snd
      simpa [sProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel
    refine ⟨hcan,hstate,?_,?_⟩
    · exact sided_canonical_specVisibility Γ C hgood exec.mintHonest E hsub ops hperm
    · rw [observes q]
      exact GuardedHistory.admits_updates_query (sidedClientSpec Γ)
        (sided_legal_prefix Γ) (SidedWitness.canonical ops) hlegal q

theorem canonical_respects_invariant {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (good : CanonicalConfig C)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ C.replayContext)
    (Inv : (Instances.SidedEmbedRGA.S Γ).State → Prop)
    (swaps : ∀ a ∈ C.events, ∀ b ∈ C.events,
      sidedSemanticCommutes a b →
        InvariantOrder.Commutes (Instances.SidedEmbedRGA.S Γ).toUpdateSig Inv a b)
    {v : Version} {s : (Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op (Instances.SidedEmbedRGA.SOp))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.SidedEmbedRGA.SOp))} (perm : listPermOf ops E) :
    respects (SidedWitness.canonical ops)
      (InvariantOrder.order Inv emptyPolicy C.replayContext E) := by
  have old := sidedCanonical_respects_of good honest stored perm
  have can := SidedWitness.canonical_listPermOf perm
  have supported := good.version_events_supported v s E stored
  apply old.imp_of_mem
  intro a b ha hb ordered edge
  have haC := supported a ((can.2 a).mp ha)
  have hbC := supported b ((can.2 b).mp hb)
  rcases edge with ⟨vis,nc⟩ | ⟨_,_,before,_⟩
  · apply ordered
    apply Or.inl
    refine ⟨vis, (sidedRc_noncomm Γ b a).mpr ?_⟩
    exact fun independent => nc (swaps b hbC a haC independent)
  · exact before

/-- One explicit original public history carries invariant order, exact raw
state equality, specification visibility and independent language admission. -/
theorem canonical_full_history {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.S Γ)
      (Instances.SidedEmbedRGA.generation Γ) C)
    (good : CanonicalConfig C)
    (Inv : (Instances.SidedEmbedRGA.S Γ).State → Prop)
    (swaps : ∀ a ∈ C.events, ∀ b ∈ C.events,
      sidedSemanticCommutes a b →
        InvariantOrder.Commutes (Instances.SidedEmbedRGA.S Γ).toUpdateSig Inv a b)
    {v : Version} {s : (Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op (Instances.SidedEmbedRGA.SOp))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.SidedEmbedRGA.SOp))}
    (perm : listPermOf ops E) (ordered : respects ops C.vis)
    (fold : Instances.SidedEmbedRGA.sFold Γ ops = s)
    (q : (Instances.SidedEmbedRGA.S Γ).Query) :
    listPermOf (SidedWitness.canonical ops) E ∧
    respects (SidedWitness.canonical ops)
      (InvariantOrder.order Inv emptyPolicy C.replayContext E) ∧
    Instances.SidedEmbedRGA.sFold Γ (SidedWitness.canonical ops) = s ∧
    respects (SidedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (sidedClientSpec Γ)) C.replayContext) ∧
    (GuardedHistory.language (sidedClientSpec Γ)).admits
      (projectedLabels id (SidedWitness.canonical ops) ++
        [.query q ((Instances.SidedEmbedRGA.S Γ).query s q)]) := by
  obtain ⟨can,state,spec,admitted⟩ :=
    canonical_history_data execution good stored perm ordered fold q
  have honest := Instances.SidedEmbedRGA.sHonest_core
    (Instances.SidedEmbedRGA.sHonest_of_mint execution.mintHonest)
  exact ⟨can,canonical_respects_invariant good honest Inv swaps stored perm,
    state,spec,admitted⟩

/-- Instantiate the swap premise using sorted states with immutable supported
birth provenance. The same original issued events act on every valid state. -/
theorem invariant_swaps (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.SidedEmbedRGA.S Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ C)
    (a b : Op (Instances.SidedEmbedRGA.SOp)) (ha : a ∈ C.events) (hb : b ∈ C.events)
    (semantic : sidedSemanticCommutes a b) :
    InvariantOrder.Commutes (Instances.SidedEmbedRGA.S Γ).toUpdateSig
      (CertifiedSidedInvariant.Valid Γ C) a b :=
  CertifiedSidedInvariant.semantic_commutes Γ C honest a b ha hb semantic

theorem canonical_valid_history {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.SidedEmbedRGA.S Γ)}
    (execution : CertifiedExecution (Instances.SidedEmbedRGA.S Γ)
      (Instances.SidedEmbedRGA.generation Γ) C)
    (good : CanonicalConfig C)
    {v : Version} {s : (Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op (Instances.SidedEmbedRGA.SOp))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.SidedEmbedRGA.SOp))}
    (perm : listPermOf ops E) (ordered : respects ops C.vis)
    (fold : Instances.SidedEmbedRGA.sFold Γ ops = s)
    (q : (Instances.SidedEmbedRGA.S Γ).Query) :
    listPermOf (SidedWitness.canonical ops) E ∧
    respects (SidedWitness.canonical ops)
      (InvariantOrder.order (CertifiedSidedInvariant.Valid Γ C.replayContext)
        emptyPolicy C.replayContext E) ∧
    Instances.SidedEmbedRGA.sFold Γ (SidedWitness.canonical ops) = s ∧
    respects (SidedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (sidedClientSpec Γ)) C.replayContext) ∧
    (GuardedHistory.language (sidedClientSpec Γ)).admits
      (projectedLabels id (SidedWitness.canonical ops) ++
        [.query q ((Instances.SidedEmbedRGA.S Γ).query s q)]) := by
  have honest := Instances.SidedEmbedRGA.sHonest_core
    (Instances.SidedEmbedRGA.sHonest_of_mint execution.mintHonest)
  exact canonical_full_history execution good _
    (fun a ha b hb sem => invariant_swaps Γ C.replayContext honest a b ha hb sem)
    stored perm ordered fold q

end Sal.MRDTs.Paper1.CertifiedSidedInvariantHistory
