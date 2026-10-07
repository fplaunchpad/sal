import Sal.MRDTs.Paper1.CertifiedRGACoreCertificate

namespace Sal.MRDTs.Paper1.CertifiedRGARichCertificate
open Foundation Classical Sal.EmbedRGA
open Instances.SidedPeritext Instances.SidedEmbedRGA
open CertifiedRGACoreVC CertifiedRGACoreCertificate
attribute [local instance] richRc

abbrev language (Γ : OrderedPrefixCode) := GuardedHistory.language (richClientSpec Γ)

theorem legal_prefix (Γ : OrderedPrefixCode) (pre suf : List (Op (RichCore Γ).AppOp))
    (legal : (richClientSpec Γ).Legal (pre++suf)) : (richClientSpec Γ).Legal pre := by
  change Instances.ProductionRGA.sidedLegal Γ (projList₁ (pre++suf)) at legal
  change Instances.ProductionRGA.sidedLegal Γ (projList₁ pre)
  rw [projList₁_append] at legal
  intro before e after split
  apply legal before e (after++(show List (Op SOp) from projList₁ suf))
  simp only [split,List.append_assoc,List.cons_append]

theorem admitted (Γ : OrderedPrefixCode) (ops : List (Op (RichCore Γ).AppOp))
    (seq : sSeqOK Γ (projList₁ ops)) (q : (RichCore Γ).Query) :
    (language Γ).admits (projectedLabels id ops ++
      [.query q ((RichCore Γ).query (applySeq (RichCore Γ).toUpdateSig (RichCore Γ).init ops) q)]) := by
  have rel : coreRel (applySeq (RichCore Γ).toUpdateSig (RichCore Γ).init ops) (richSpec.run ops) :=
    (richSequential Γ).sound ops seq
  have legal : (richClientSpec Γ).Legal ops := Instances.ProductionRGA.sidedLegal_of_seqOK seq
  have query : (RichCore Γ).query (applySeq (RichCore Γ).toUpdateSig (RichCore Γ).init ops) q =
      (richClientSpec Γ).query ((richClientSpec Γ).run ops) q := by
    have doc := documentOf_eq_richDocumentOf rel
    change renderState _ q = Instances.PeritextRender.renderMarksDoc
      (richDocumentOf ((richClientSpec Γ).run ops)) ((richClientSpec Γ).run ops).2.2.toList q
    rw [renderState,doc,rel.2]
    simp [richClientSpec,SequentialSpec.run]
  rw [query]
  exact GuardedHistory.admits_updates_query (richClientSpec Γ) (legal_prefix Γ) ops legal q

theorem history (Γ : OrderedPrefixCode) : CertifiedHistory.RepresentedHistory
    (CertifiedRGARichVC.representation Γ) (CertifiedRGARichVC.policy Γ) (language Γ) (richGeneration Γ) := by
  intro C execution v s H hv q
  have good := CertifiedRGACoreExecution.Rich.canonicalConfig Γ execution
  have rep := CertifiedRGACoreExecution.Rich.representedVersions Γ execution hv
  obtain ⟨ops,perm,_,_⟩ := rep.2.2.2.2.2
  let π := chronological ops
  have pπ : listPermOf π H := ⟨(chronological_perm ops).nodup perm.1,
    fun e => (chronological_perm ops).mem_iff.symm.trans (perm.2 e)⟩
  have causal := chronological_vis Γ (asCoreConfig C) ops
  have txt := text_canonical Γ (asCoreConfig C) rep.2.1 H ops perm rep.2.2.2.2.1
  have hvText : (projConf₁ (asCoreConfig C)).ver v=some (s.1,evRes₁ H) := by simp [projConf₁,asCoreConfig,hv]
  have seq := Instances.ProductionRGA.sidedCanonical_seqOK_of
    (coreCanonicalConfig_proj₁ (canonicalConfig_to_core good)) (mintHonest_text (mintHonest_to_core execution.mintHonest)) hvText
    (listPermOf_projList₁ pπ)
  rw [←txt] at seq
  refine ⟨π,pπ,?_,?_,?_,admitted Γ π seq q⟩
  · apply causal.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩|⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad
  · apply causal.imp
    intro a b hn edge
    exact hn edge.1
  · exact ⟨rep.1,rep.2.1,rep.2.2.1,rep.2.2.2.1,rep.2.2.2.2.1,π,pπ,causal,rfl⟩

noncomputable def scope (Γ : OrderedPrefixCode) (C : Configuration (RichCore Γ)) (H : Set (Op (RichCore Γ).AppOp)) :=
  CertifiedReplay.restrict (CertifiedPrefixScope.scope (RichCore Γ) C.replayContext) H

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (execution : CertifiedExecution (RichCore Γ) (richGeneration Γ) C)
    {v : Version} {s : (RichCore Γ).State} {H : Set (Op (RichCore Γ).AppOp)} (hv : C.ver v=some (s,H)) :
    CertifiedReplay.RestrictedLaws (scope Γ C H) (CertifiedRGARichVC.policy Γ) := by
  have good := CertifiedRGACoreExecution.Rich.canonicalConfig Γ execution
  apply CertifiedReplay.restrictedEmpty
  exact CertifiedReplay.restrict_laws (CertifiedRGAIssuance.SidedPeritext.rich_laws Γ C execution.mintHonest (CertifiedRGARichVC.policy Γ)) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (execution : CertifiedExecution (RichCore Γ) (richGeneration Γ) C)
    {v : Version} {s : (RichCore Γ).State} {H : Set (Op (RichCore Γ).AppOp)} (hv : C.ver v=some (s,H)) :
    CertifiedReplay.Canonical (scope Γ C H) (CertifiedRGARichVC.policy Γ) (RichCore Γ).init s := by
  have rep := CertifiedRGACoreExecution.Rich.representedVersions Γ execution hv
  obtain ⟨xs,perm,causal,fold⟩ := rep.2.2.2.2.2
  refine ⟨xs,perm,CertifiedReplay.legal_of_causal_enumeration rep.2.2.2.1 perm causal,causal,?_,fold⟩
  apply causal.imp
  intro a b hn edge
  rcases edge with ⟨vis,_⟩|⟨_,_,bad,_⟩
  · exact hn vis
  · exact bad

def Correct (Γ : OrderedPrefixCode) (C : Configuration (RichCore Γ)) : Prop :=
  (∀v s H, C.ver v=some (s,H) →
    CertifiedReplay.RestrictedLaws (scope Γ C H) (CertifiedRGARichVC.policy Γ) ∧
    CertifiedReplay.Canonical (scope Γ C H) (CertifiedRGARichVC.policy Γ) (RichCore Γ).init s) ∧
  EventVersionsSpecificationRA (RichCore Γ) (CertifiedRGARichVC.policy Γ) (language Γ) C

theorem correct (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (execution : CertifiedExecution (RichCore Γ) (richGeneration Γ) C) : Correct Γ C := by
  constructor
  · intro v s H hv
    exact ⟨laws Γ execution hv,storedCanonical Γ execution hv⟩
  · exact CertifiedHistory.versions_of_representation (D := RichCore Γ) (R := CertifiedRGARichVC.representation Γ)
      (fun C execution v s H hv a b ha hb => unique Γ C.replayContext H a b ha hb)
      (history Γ) execution (fun v s H hv => CertifiedRGACoreExecution.Rich.representedVersions Γ execution hv)

theorem correctV (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (reach : MintCertifiedReachV (RichCore Γ) (canonicalVirtualMergeBase (RichCore Γ))
      (richGeneration Γ) C) : Correct Γ C := correct Γ (.virtual reach)

theorem executions (Γ : OrderedPrefixCode) (trace : List (Label (RichCore Γ) × Configuration (RichCore Γ)))
    (run : (certifiedTS (RichCore Γ) (richGeneration Γ)).Execution (initConfig (RichCore Γ)) trace) :
    Correct Γ (initConfig (RichCore Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReach (RichCore Γ) (richGeneration Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : OrderedPrefixCode) (trace : List (Label (RichCore Γ) × Configuration (RichCore Γ)))
    (run : (certifiedTSV (RichCore Γ) (richGeneration Γ)).Execution (initConfig (RichCore Γ)) trace) :
    Correct Γ (initConfig (RichCore Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReachV (RichCore Γ) (canonicalVirtualMergeBase (RichCore Γ)) (richGeneration Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

#print axioms correct
#print axioms correctV
#print axioms history
end Sal.MRDTs.Paper1.CertifiedRGARichCertificate
