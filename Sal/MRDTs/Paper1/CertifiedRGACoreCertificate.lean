import Sal.MRDTs.Paper1.CertifiedRGACoreExecution
import Sal.MRDTs.Paper1.CertifiedRGACertificate
import Sal.MRDTs.Paper1.CertifiedHistoryBridge
import Sal.MRDTs.Paper1.AbstractSoundness
import Sal.MRDTs.Paper1.GuardedHistory

namespace Sal.MRDTs.Paper1.CertifiedRGACoreCertificate
open Foundation Classical Sal.EmbedRGA
open Instances.SidedPeritext Instances.SidedEmbedRGA
open CertifiedRGACoreVC
attribute [local instance] coreRc

abbrev language (Γ : OrderedPrefixCode) := GuardedHistory.language (clientSpec Γ)
def chronological (ops : List (Op (Core Γ).AppOp)) :=
  ops.mergeSort (fun a b => decide (a.1 ≤ b.1))

theorem chronological_perm (ops : List (Op (Core Γ).AppOp)) : ops.Perm (chronological ops) :=
  (List.mergeSort_perm ops _).symm

theorem chronological_ordered (ops : List (Op (Core Γ).AppOp)) :
    (chronological ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  have h : (ops.mergeSort (fun a b => decide (a.1≤b.1))).Pairwise
      (fun a b => decide (a.1≤b.1)=true) := by
    apply List.pairwise_mergeSort
    · intro a b c ab bc
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
    · intro a b
      simp only [Bool.or_eq_true,decide_eq_true_eq]
      exact Nat.le_total a.1 b.1
  simpa only [chronological,decide_eq_true_eq] using h

theorem chronological_vis (Γ : OrderedPrefixCode) (C : Configuration (Core Γ))
    (ops : List (Op (Core Γ).AppOp)) : respects (chronological ops) C.vis :=
  (chronological_ordered ops).imp (fun {_ _} le vis => (not_lt_of_ge le) (C.causal_mono vis))

theorem text_canonical (Γ : OrderedPrefixCode) (C : Configuration (Core Γ))
    (native : NativeInsertOnly Γ C.replayContext) (H : Set (Op (Core Γ).AppOp))
    (ops : List (Op (Core Γ).AppOp)) (perm : listPermOf ops H) (support : H ⊆ C.events) :
    projList₁ (chronological ops) = Instances.ProductionRGA.SidedWitness.canonical (projList₁ (chronological ops)) := by
  let xs := projList₁ (chronological ops)
  have px : listPermOf xs (evRes₁ H) := listPermOf_projList₁
    ⟨(chronological_perm ops).nodup perm.1,fun e =>
      (chronological_perm ops).mem_iff.symm.trans (perm.2 e)⟩
  have py := Instances.ProductionRGA.SidedWitness.canonical_listPermOf px
  have inserts : ∀e∈xs, sIsIns e=true := by
    intro e he
    have eligible := support ((px.2 e).mp he)
    rcases e with ⟨t,r,op⟩
    cases op with
    | ins el pref anchor side => rfl
    | del target => exact False.elim (native _ eligible target rfl)
  have chrono : xs.Pairwise (fun a b => a.1≤b.1) := by
    unfold xs projList₁
    rw [List.pairwise_filterMap]
    apply (chronological_ordered ops).imp
    intro a b times x hx y hy
    rw [oplOp_eq_some] at hx hy
    subst a; subst b
    exact times
  have ordered : xs.Pairwise Instances.ProductionRGA.SidedWitness.LE := by
    apply chrono.imp_of_mem
    intro a b ha hb times
    have ia := inserts a ha
    have ib := inserts b hb
    rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
    cases oa <;> cases ob <;> simp [sIsIns] at ia ib
    simpa [Instances.ProductionRGA.SidedWitness.LE,Instances.ProductionRGA.SidedWitness.leBool] using times
  apply List.Perm.eq_of_pairwise _ ordered (Instances.ProductionRGA.SidedWitness.canonical_ordered xs)
    (Instances.ProductionRGA.SidedWitness.canonical_perm xs)
  intro a b ha hb ab ba
  have hbx := (Instances.ProductionRGA.SidedWitness.canonical_perm xs).mem_iff.mpr hb
  have ia := inserts a ha
  have ib := inserts b hbx
  have stamps : a.1=b.1 := by
    rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
    cases oa <;> cases ob <;> simp [sIsIns] at ia ib
    exact Nat.le_antisymm (by simpa [Instances.ProductionRGA.SidedWitness.LE,Instances.ProductionRGA.SidedWitness.leBool] using ab)
      (by simpa [Instances.ProductionRGA.SidedWitness.LE,Instances.ProductionRGA.SidedWitness.leBool] using ba)
  exact (projReplayContext₁ C.replayContext).ts_unique
    (mem_projReplayContext₁_events.mpr (support ((px.2 a).mp ha)))
    (mem_projReplayContext₁_events.mpr (support ((py.2 b).mp hb))) stamps

theorem legal_prefix (Γ : OrderedPrefixCode) (pre suf : List (Op (Core Γ).AppOp))
    (legal : (clientSpec Γ).Legal (pre++suf)) : (clientSpec Γ).Legal pre := by
  change Instances.ProductionRGA.sidedLegal Γ (projList₁ (pre++suf)) at legal
  change Instances.ProductionRGA.sidedLegal Γ (projList₁ pre)
  rw [projList₁_append] at legal
  intro before e after split
  apply legal before e (after++(show List (Op SOp) from projList₁ suf))
  simp only [split,List.append_assoc,List.cons_append]

theorem admitted (Γ : OrderedPrefixCode) (ops : List (Op (Core Γ).AppOp))
    (seq : sSeqOK Γ (projList₁ ops)) (q : (Core Γ).Query) :
    (language Γ).admits (projectedLabels id ops ++
      [.query q ((Core Γ).query (applySeq (Core Γ).toUpdateSig (Core Γ).init ops) q)]) := by
  have rel := (sequential Γ).sound ops seq
  have legal : (clientSpec Γ).Legal ops := Instances.ProductionRGA.sidedLegal_of_seqOK seq
  have query : (Core Γ).query (applySeq (Core Γ).toUpdateSig (Core Γ).init ops) q =
      (clientSpec Γ).query ((clientSpec Γ).run ops) q := by
    cases q with
    | inl text =>
      apply congrArg Sum.inl
      simpa [Core,clientSpec,SequentialSpec.run,sProj,List.map_map,Function.comp_def] using
        congrArg (List.map Prod.snd) rel.1
    | inr store =>
      apply congrArg Sum.inr
      exact congrArg (fun st => Stores.query st store) rel.2
  rw [query]
  exact GuardedHistory.admits_updates_query (clientSpec Γ) (legal_prefix Γ) ops legal q

theorem history (Γ : OrderedPrefixCode) : CertifiedHistory.RepresentedHistory
    (representation Γ) (policy Γ) (language Γ) (Instances.SidedPeritext.generation Γ) := by
  intro C execution v s H hv q
  have good := CertifiedRGACoreExecution.canonicalConfig Γ execution
  have rep := CertifiedRGACoreExecution.representedVersions Γ execution hv
  obtain ⟨ops,perm,_,_⟩ := rep.2.2.2.2.2
  let π := chronological ops
  have pπ : listPermOf π H := ⟨(chronological_perm ops).nodup perm.1,
    fun e => (chronological_perm ops).mem_iff.symm.trans (perm.2 e)⟩
  have causal := chronological_vis Γ C ops
  have txt := text_canonical Γ C rep.2.1 H ops perm rep.2.2.2.2.1
  have hvText : (projConf₁ C).ver v=some (s.1,evRes₁ H) := by simp [projConf₁,hv]
  have seq := Instances.ProductionRGA.sidedCanonical_seqOK_of
    (coreCanonicalConfig_proj₁ good) (mintHonest_text execution.mintHonest) hvText
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

noncomputable def scope (Γ : OrderedPrefixCode) (C : Configuration (Core Γ)) (H : Set (Op (Core Γ).AppOp)) :=
  CertifiedReplay.restrict (CertifiedPrefixScope.scope (Core Γ) C.replayContext) H

theorem laws (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (execution : CertifiedExecution (Core Γ) (Instances.SidedPeritext.generation Γ) C)
    {v : Version} {s : (Core Γ).State} {H : Set (Op (Core Γ).AppOp)} (hv : C.ver v=some (s,H)) :
    CertifiedReplay.RestrictedLaws (scope Γ C H) (policy Γ) := by
  have good := CertifiedRGACoreExecution.canonicalConfig Γ execution
  apply CertifiedReplay.restrictedEmpty
  exact CertifiedReplay.restrict_laws (CertifiedRGAIssuance.SidedPeritext.laws Γ C execution.mintHonest (policy Γ)) H
    (fun e he => good.version_events_supported v s H hv e he)
    (fun a _ b hb vis => good.version_events_causal v s H hv a b vis hb)

theorem storedCanonical (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (execution : CertifiedExecution (Core Γ) (Instances.SidedPeritext.generation Γ) C)
    {v : Version} {s : (Core Γ).State} {H : Set (Op (Core Γ).AppOp)} (hv : C.ver v=some (s,H)) :
    CertifiedReplay.Canonical (scope Γ C H) (policy Γ) (Core Γ).init s := by
  have rep := CertifiedRGACoreExecution.representedVersions Γ execution hv
  obtain ⟨xs,perm,causal,fold⟩ := rep.2.2.2.2.2
  refine ⟨xs,perm,CertifiedReplay.legal_of_causal_enumeration rep.2.2.2.1 perm causal,causal,?_,fold⟩
  apply causal.imp
  intro a b hn edge
  rcases edge with ⟨vis,_⟩|⟨_,_,bad,_⟩
  · exact hn vis
  · exact bad

def Correct (Γ : OrderedPrefixCode) (C : Configuration (Core Γ)) : Prop :=
  (∀v s H, C.ver v=some (s,H) →
    CertifiedReplay.RestrictedLaws (scope Γ C H) (policy Γ) ∧
    CertifiedReplay.Canonical (scope Γ C H) (policy Γ) (Core Γ).init s) ∧
  EventVersionsSpecificationRA (Core Γ) (policy Γ) (language Γ) C

theorem correct (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (execution : CertifiedExecution (Core Γ) (Instances.SidedPeritext.generation Γ) C) : Correct Γ C := by
  constructor
  · intro v s H hv
    exact ⟨laws Γ execution hv,storedCanonical Γ execution hv⟩
  · exact CertifiedHistory.versions_of_representation
      (fun C execution v s H hv a b ha hb => unique Γ C.replayContext H a b ha hb)
      (history Γ) execution (fun v s H hv => CertifiedRGACoreExecution.representedVersions Γ execution hv)

theorem correctV (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (reach : MintCertifiedReachV (Core Γ) (canonicalVirtualMergeBase (Core Γ))
      (Instances.SidedPeritext.generation Γ) C) : Correct Γ C := correct Γ (.virtual reach)

theorem executions (Γ : OrderedPrefixCode) (trace : List (Label (Core Γ) × Configuration (Core Γ)))
    (run : (certifiedTS (Core Γ) (Instances.SidedPeritext.generation Γ)).Execution (initConfig (Core Γ)) trace) :
    Correct Γ (initConfig (Core Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReach (Core Γ) (Instances.SidedPeritext.generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : OrderedPrefixCode) (trace : List (Label (Core Γ) × Configuration (Core Γ)))
    (run : (certifiedTSV (Core Γ) (Instances.SidedPeritext.generation Γ)).Execution (initConfig (Core Γ)) trace) :
    Correct Γ (initConfig (Core Γ)) ∧ ∀entry∈trace, Correct Γ entry.2 := by
  have reached := AbstractMRDT.visited (Good := MintCertifiedReachV (Core Γ) (canonicalVirtualMergeBase (Core Γ)) (Instances.SidedPeritext.generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) run .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

#print axioms correct
#print axioms correctV
#print axioms history
#print axioms text_canonical
end Sal.MRDTs.Paper1.CertifiedRGACoreCertificate
