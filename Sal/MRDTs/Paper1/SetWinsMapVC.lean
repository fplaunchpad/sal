import Sal.MRDTs.Instances.SetWinsMap
import Sal.MRDTs.Paper1.Automation.PolicyKitAutomation
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion
import Sal.MRDTs.Paper1.ConcreteReplay
import Sal.MRDTs.Paper1.CertifiedClosedExecution
import Sal.MRDTs.Paper1.SplitPolicy

namespace Sal.MRDTs.Paper1.SetWinsMap
open Foundation ConcreteMRDT Instances.SetWinsMap
open Classical
set_option maxHeartbeats 1000000
attribute [local policy_expansion_simps] D Automation.LocalAssembly.ofMRDT update merge Instances.SetWinsMap.order policy Op.op Op.rep Op.time

def kit : Automation.PolicyExpansion.Kit D policy Instances.SetWinsMap.order := by derive_policy_kit

theorem noncomm_exact (a b : Op Action) :
    ¬ D.toUpdateSig.commutes a b ↔ policy.before a.op b.op ∨ policy.before b.op a.op := by
  policy_auto

def laws : GuardedReplay.Laws D.toUpdateSig policy := Automation.PolicyExpansion.laws kit

def restrictedLaws : RestrictedLaws D.toUpdateSig policy where
  noncomm_exact := noncomm_exact
  no_chain := by
    rintro a b c ⟨⟨k,v,rfl,h⟩,⟨j,w,h',hc⟩⟩
    cases h.symm.trans h'
  conditional_commutation := by
    intro s a b c between edge noncomm
    exact (Automation.Signature.conditional_log
      (Automation.CausalCoverage.signatureOf D Instances.SetWinsMap.order) kit.conditionalBase kit.kernelStable
      s a b c ((kit.policy_order a b).mpr edge) noncomm between).symm

def splitLaws : SplitPolicy.Laws D.toUpdateSig policy := SplitPolicy.Laws.ofGuarded laws

noncomputable local instance : EventOrder D.toUpdateSig := policy.lift

def scheme (C : ReplayContext D.toUpdateSig) := MetadataDependencies.ofConcrete C

def representation (C : ReplayContext D.toUpdateSig) (E : Set (Op Action)) (s : State) : Prop :=
  IsCanonicalState C E s ∧ Supported C E

theorem canonical (C : ReplayContext D.toUpdateSig) (E : Set (Op Action)) (s : State)
    (h : representation C E s) : Canonical policy C E s := by
  exact Automation.PolicyExpansion.canonical_of_loWitness noncomm_exact C E s h.1

theorem unique : Raw.Unique representation := by
  intro C E s t hs ht
  exact canonical_unique laws C E hs.2 (canonical C E s hs) (canonical C E t ht)

theorem initial (C : ReplayContext D.toUpdateSig) : representation C ∅ D.init := by
  refine ⟨⟨[],⟨List.nodup_nil,by simp⟩,?_,rfl⟩,?_⟩
  · simp [respects]
  · simp [Supported]

theorem finite (C : ReplayContext D.toUpdateSig) (E : Set (Op Action)) (s : State)
    (h : representation C E s) : ∃ π, listPermOf π E := by
  obtain ⟨π,hp,_,_⟩ := h.1
  exact ⟨π,hp⟩

private theorem raw_maximal (C : ReplayContext D.toUpdateSig) (U : Set (Op Action))
    (e : Op Action) (h : ∀ x ∈ U, x ≠ e → ¬ paperOrder policy C U e x) :
    ∀ x ∈ U, x ≠ e → ¬ loOn C U e x := by
  intro x hx ne edge
  exact h x hx ne ((paperOrder_iff_loOn restrictedLaws C U e x).mpr edge)

theorem replaySupply (C : ReplayContext D.toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    Raw.ReplaySupply policy representation scheme C := by
  refine ⟨?_,?_⟩
  · intro E π perm supported
    obtain ⟨s,hs⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
      (fun {_ _ _} h k => trans h k) irrefl perm supported
    exact ⟨s,hs,supported⟩
  · intro U s rep supported nonempty closed
    let M := scheme C
    obtain ⟨π,hp,hr,hf⟩ := canonical C U s rep
    have metadata : respects π M.before := hr.imp (fun {_ _} h edge => h (Or.inl edge))
    obtain ⟨e,he,semantic,maximal⟩ := joint_maximal_of_enumeration π hp nonempty hr metadata
    have pastSub : M.Past e ⊆ U := M.past_subset U e closed he
    obtain ⟨pre,hpre⟩ := enumeration_subset hp (show U \ {e} ⊆ U from fun _ h => h.1)
    obtain ⟨past,hpast⟩ := enumeration_subset hp (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
    obtain ⟨a,ha⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
      (fun {_ _ _} h k => trans h k) irrefl hpre (fun x h => supported x h.1)
    obtain ⟨b,hb⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
      (fun {_ _ _} h k => trans h k) irrefl hpast (fun x h => supported x (pastSub h.1))
    refine ⟨⟨e,he,semantic,maximal,a,b,⟨ha,fun x h => supported x h.1⟩,
      ⟨hb,fun x h => supported x (pastSub h.1)⟩,?_,?_⟩⟩
    · exact ⟨isCanonicalState_snoc (Or.inl rfl)
        (raw_maximal C _ e (M.past_semantic_maximal policy trans irrefl e)) hb,
        fun x h => supported x (pastSub h)⟩
    · exact ⟨isCanonicalState_snoc he (raw_maximal C U e semantic) ha,supported⟩

/-- Five raw equality VCs are derived from finite source equations and generic
policy replay. No Join premise or implementation correctness result is used. -/
theorem fiveVC : Raw.MergeVCs policy representation scheme :=
  Automation.PolicyExpansion.assemble kit representation canonical scheme

theorem representationJoin : RepresentationJoin representation := by
  apply Raw.representationJoin_of_vcs fiveVC unique (fun C _ _ _ => initial C) finite
  intro C _ _ _ _ trans irrefl _ _ _ _
  exact replaySupply C trans irrefl

theorem joinAt (C : ReplayContext D.toUpdateSig) : @JoinAt D policy.lift C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have tr : Transitive C.vis := fun _ _ _ h k => trans h k
  have supply := replaySupply C tr irrefl
  obtain ⟨π₁,hp₁,hr₁,hf₁⟩ := ha
  obtain ⟨π₂,hp₂,hr₂,hf₂⟩ := hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have sizes := Raw.join_at_sizes fiveVC unique (fun C _ _ _ => initial C) finite
    C tr irrefl supply.represented supply.peel
  have joined := sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun x y edge mem => closed₁ x y edge.1 edge.2 mem)
    (fun x y edge mem => closed₂ x y edge.1 edge.2 mem)
    ⟨hl,fun x hx => sup₁ x hx.1⟩ ⟨⟨π₁,hp₁,hr₁,hf₁⟩,sup₁⟩ ⟨⟨π₂,hp₂,hr₂,hf₂⟩,sup₂⟩
  exact joined.1

theorem canonicalConfig {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) : CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV (fun C _ => joinAt C.replayContext) reach

theorem representedVersions {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C)
    (v : Version) (s : State) (E : Set (Op Action)) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s := by
  have good := canonicalConfig reach
  exact ⟨good.canonical v s E hv,good.version_events_supported v s E hv⟩

#print axioms fiveVC
#print axioms representationJoin
#print axioms joinAt
end Sal.MRDTs.Paper1.SetWinsMap
