import Sal.MRDTs.Paper1.Automation.EmbeddedSequentialBridge
import Sal.MRDTs.Paper1.CertifiedRGAHistoryCommutation
import Sal.MRDTs.Paper1.InvariantOrder
import Sal.MRDTs.Paper1.CertifiedRGAInvariant

/-! The original independent full-event specification is witnessed by the same
insertion-first enumeration whose raw fold equals the stored state. Invariant
order obligations are added below; no datatype Join theorem is used here. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAInvariantHistory
open Foundation
open Instances.ProductionRGA
open CertifiedRGAHistory
open Sal.EmbedRGA (OrderedPrefixCode)
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem canonical_history_data {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α) (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State} {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.EmbedRGA.eFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).Query) :
    listPermOf (EmbedWitness.canonical ops) E ∧
      Sal.MRDTs.Instances.EmbedRGA.eFold Γ (EmbedWitness.canonical ops) = s ∧
      respects (EmbedWitness.canonical ops) (projectedSpecVisibility id
        (GuardedHistory.language (embedClientSpec Γ)) C.replayContext) ∧
      (GuardedHistory.language (embedClientSpec Γ)).admits
        (projectedLabels id (EmbedWitness.canonical ops) ++ [.query q ((Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s q)]) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hseq := embedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := embedLegal_of_seqOK hseq
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : EHonestCore Γ C.replayContext :=
      eHonest_core (eHonest_of_mint exec.mintHonest)
    have hwfReplay : EWf Γ ops :=
      CertifiedRGAScope.Embedded.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : EWf Γ (EmbedWitness.canonical ops) :=
      eWf_of_seqOK hseq
    have hcanonFold :
        eFold Γ (EmbedWitness.canonical ops) = eFold Γ ops :=
      e_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : eFold Γ (EmbedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := Automation.EmbeddedSequentialBridge.sound hseq
    have hrel : embedRel s ((embedClientSpec Γ).run
        (EmbedWitness.canonical ops)) := by
      unfold embedRel
      change s.map eProj = eSpecFold (EmbedWitness.canonical ops)
      rw [← hstate]
      exact hsound
    have observes : ∀ query, (Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s query =
        (embedClientSpec Γ).query ((embedClientSpec Γ).run (EmbedWitness.canonical ops)) query := by
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        ((embedClientSpec Γ).run (EmbedWitness.canonical ops)).map Prod.snd
      simpa [eProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel
    refine ⟨hcan,hstate,?_,?_⟩
    · exact embed_canonical_specVisibility Γ C hgood exec.mintHonest E hsub ops hperm
    · rw [observes q]
      exact GuardedHistory.admits_updates_query (embedClientSpec Γ)
        (embed_legal_prefix Γ) (EmbedWitness.canonical ops) hlegal q

def emptyPolicy : OperationPolicy (Instances.EmbedRGA.EOp α) where
  before _ _ := False

/-- Actual invariant-state swaps imply that the new order is no stronger than
syntactic birth/deletion conflicts, on the supported events of this history. -/
theorem canonical_respects_invariant {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.EmbedRGA.E Γ α)}
    (good : CanonicalConfig C)
    (honest : Instances.EmbedRGA.EHonestCore Γ C.replayContext)
    (Inv : (Instances.EmbedRGA.E Γ α).State → Prop)
    (swaps : ∀ a ∈ C.events, ∀ b ∈ C.events,
      embedSemanticCommutes a b →
        InvariantOrder.Commutes (Instances.EmbedRGA.E Γ α).toUpdateSig Inv a b)
    {v : Version} {s : (Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Instances.EmbedRGA.EOp α))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.EmbedRGA.EOp α))} (perm : listPermOf ops E) :
    respects (EmbedWitness.canonical ops)
      (InvariantOrder.order Inv emptyPolicy C.replayContext E) := by
  have old := embedCanonical_respects_of good honest stored perm
  have can := EmbedWitness.canonical_listPermOf perm
  have supported := good.version_events_supported v s E stored
  apply old.imp_of_mem
  intro a b ha hb ordered edge
  have haC := supported a ((can.2 a).mp ha)
  have hbC := supported b ((can.2 b).mp hb)
  rcases edge with ⟨vis,nc⟩ | ⟨_,_,before,_⟩
  · apply ordered
    apply Or.inl
    refine ⟨vis, (embedRc_noncomm Γ b a).mpr ?_⟩
    exact fun independent => nc (swaps b hbC a haC independent)
  · exact before

/-- One explicit original public history carries invariant order, exact raw
state equality, specification visibility and independent language admission. -/
theorem canonical_full_history {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.EmbedRGA.E Γ α)}
    (execution : CertifiedExecution (Instances.EmbedRGA.E Γ α)
      (Instances.EmbedRGA.generation Γ) C)
    (good : CanonicalConfig C)
    (Inv : (Instances.EmbedRGA.E Γ α).State → Prop)
    (swaps : ∀ a ∈ C.events, ∀ b ∈ C.events,
      embedSemanticCommutes a b →
        InvariantOrder.Commutes (Instances.EmbedRGA.E Γ α).toUpdateSig Inv a b)
    {v : Version} {s : (Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Instances.EmbedRGA.EOp α))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.EmbedRGA.EOp α))}
    (perm : listPermOf ops E) (ordered : respects ops C.vis)
    (fold : Instances.EmbedRGA.eFold Γ ops = s)
    (q : (Instances.EmbedRGA.E Γ α).Query) :
    listPermOf (EmbedWitness.canonical ops) E ∧
    respects (EmbedWitness.canonical ops)
      (InvariantOrder.order Inv emptyPolicy C.replayContext E) ∧
    Instances.EmbedRGA.eFold Γ (EmbedWitness.canonical ops) = s ∧
    respects (EmbedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (embedClientSpec Γ)) C.replayContext) ∧
    (GuardedHistory.language (embedClientSpec Γ)).admits
      (projectedLabels id (EmbedWitness.canonical ops) ++
        [.query q ((Instances.EmbedRGA.E Γ α).query s q)]) := by
  obtain ⟨can,state,spec,admitted⟩ :=
    canonical_history_data execution good stored perm ordered fold q
  have honest := Instances.EmbedRGA.eHonest_core
    (Instances.EmbedRGA.eHonest_of_mint execution.mintHonest)
  exact ⟨can,canonical_respects_invariant good honest Inv swaps stored perm,
    state,spec,admitted⟩

/-- Instantiate the swap premise using sorted states with immutable supported
birth provenance. The same original issued events act on every valid state. -/
theorem invariant_swaps (Γ : OrderedPrefixCode)
    (C : ReplayContext (Instances.EmbedRGA.E Γ α).toUpdateSig)
    (honest : Instances.EmbedRGA.EHonestCore Γ C)
    (a b : Op (Instances.EmbedRGA.EOp α)) (ha : a ∈ C.events) (hb : b ∈ C.events)
    (semantic : embedSemanticCommutes a b) :
    InvariantOrder.Commutes (Instances.EmbedRGA.E Γ α).toUpdateSig
      (CertifiedRGAInvariant.Valid Γ C) a b :=
  CertifiedRGAInvariant.semantic_commutes Γ C honest a b ha hb semantic

theorem canonical_valid_history {Γ : OrderedPrefixCode}
    {C : Configuration (Instances.EmbedRGA.E Γ α)}
    (execution : CertifiedExecution (Instances.EmbedRGA.E Γ α)
      (Instances.EmbedRGA.generation Γ) C)
    (good : CanonicalConfig C)
    {v : Version} {s : (Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Instances.EmbedRGA.EOp α))}
    (stored : C.ver v = some (s,E))
    {ops : List (Op (Instances.EmbedRGA.EOp α))}
    (perm : listPermOf ops E) (ordered : respects ops C.vis)
    (fold : Instances.EmbedRGA.eFold Γ ops = s)
    (q : (Instances.EmbedRGA.E Γ α).Query) :
    listPermOf (EmbedWitness.canonical ops) E ∧
    respects (EmbedWitness.canonical ops)
      (InvariantOrder.order (CertifiedRGAInvariant.Valid Γ C.replayContext)
        emptyPolicy C.replayContext E) ∧
    Instances.EmbedRGA.eFold Γ (EmbedWitness.canonical ops) = s ∧
    respects (EmbedWitness.canonical ops)
      (projectedSpecVisibility id (GuardedHistory.language (embedClientSpec Γ)) C.replayContext) ∧
    (GuardedHistory.language (embedClientSpec Γ)).admits
      (projectedLabels id (EmbedWitness.canonical ops) ++
        [.query q ((Instances.EmbedRGA.E Γ α).query s q)]) := by
  have honest := Instances.EmbedRGA.eHonest_core
    (Instances.EmbedRGA.eHonest_of_mint execution.mintHonest)
  exact canonical_full_history execution good _
    (fun a ha b hb sem => invariant_swaps Γ C.replayContext honest a b ha hb sem)
    stored perm ordered fold q

end Sal.MRDTs.Paper1.CertifiedRGAInvariantHistory
