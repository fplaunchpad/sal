import Sal.MRDTs.Paper1.VCExecutionContract
import Sal.MRDTs.Paper1.ORSetCausalMetadata

namespace Sal.MRDTs.Paper1.ORSet.AbstractSpec
open Foundation
variable {α : Type} [DecidableEq α]

private theorem concrete_closed (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (closed : AbstractMRDT.ConflictClosed (model (α := α)) C E) :
    (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed E := by
  intro a b edge mem
  apply closed a b edge.1 _ mem
  intro commute
  exact edge.2 ((QuerySpec.commutes_iff_concrete a b).mp
    ((AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).mp commute))

/-- All five observational merge VCs are discharged independently of Join. -/
theorem mergeVCs : AbstractMRDT.DependencyMergeVCs (model (α := α)) (conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  refine ⟨?_,⟨?_,?_,?_⟩,?_⟩
  · intro l a b
    have equation : (D α).merge l a b = (D α).merge l b a := by
      change merge l a b = merge l b a
      apply Finset.ext
      intro p
      simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    rw [equation]
    exact AbstractMRDT.equivalent_refl _ _
  · intro C E s _ _
    exact initVC C E s
  · intro C E₁ E₂ l B t s e _ _ sup₁ sup₂ closed₁ _ member absent _ base past _ other
    have equation := local_replay_eq C E₁ E₂ l B t s e member absent sup₁ sup₂
      (concrete_closed C E₁ closed₁) base.2 past.2 other.2
    change AbstractMRDT.Equivalent (model (α := α)) (merge l (merge B t (step B e)) s)
      (merge B (merge l t s) (step B e))
    rw [equation]
    exact AbstractMRDT.equivalent_refl _ _
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [shared_replay_eq]
    exact AbstractMRDT.equivalent_refl _ _
  · intro C U A B e _ _ supported closed member maximal pre past
    have equation := causal_replay_eq C U A B e member supported (concrete_closed C U closed)
      maximal pre.2 past.2
    change AbstractMRDT.Equivalent (model (α := α)) (merge B A (step B e)) (step A e)
    rw [equation]
    exact AbstractMRDT.equivalent_refl _ _

/-- The new induction, rather than the existing direct history Join proof,
establishes this representation Join. -/
theorem vcRepresentationJoin : AbstractMRDT.RepresentationJoin (representation (α := α)) := by
  apply AbstractMRDT.representationJoin_of_vcs laws mergeVCs representsCanonical metadataSubstitution
    initialMetadata initMetadata mergeCommMetadata causalMetadata localMetadata sharedMetadata
  intro C E₁ E₂ a b trans irrefl _ _ _ _
  exact replaySupply C trans irrefl

/-- Execution's conflict-closed merge contract is obtained from the same
metadata induction, since exact set's metadata edges are concrete conflicts. -/
theorem vcJoinAt (C : ReplayContext (D α).toUpdateSig) :
    @JoinAt (D α) (conflict α).lift C := by
  intro E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  have transitive : Transitive C.vis := fun _ _ _ h k => trans h k
  have kit := replaySupply C transitive irrefl
  obtain ⟨π₁,hp₁,_,_⟩ := ha
  obtain ⟨π₂,hp₂,_,_⟩ := hb
  have perm := listPermOf_union (D := (D α).toUpdateSig) hp₁ hp₂
  have sizes := AbstractMRDT.join_at_sizes laws mergeVCs representsCanonical metadataSubstitution
    initialMetadata initMetadata mergeCommMetadata causalMetadata localMetadata sharedMetadata
    C transitive irrefl kit.represented kit.peel
  exact (sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun x y edge mem => closed₁ x y edge.1 edge.2 mem)
    (fun x y edge mem => closed₂ x y edge.1 edge.2 mem) hl
    ⟨π₁,hp₁,by assumption,by assumption⟩ ⟨π₂,hp₂,by assumption,by assumption⟩).2

theorem vcRepresentedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have hjoin : ∀ C, MintHonest (D α) (issuance α).CanIssue C →
      @JoinAt (D α) (conflict α).lift C.replayContext := fun C _ => vcJoinAt C.replayContext
  exact (canonicalConfig_of_mintCertifiedV hjoin reach).canonical

def vcConditions : AbstractMRDT.VCConditions (model (α := α)) (conflict α)
    (EventSpec.spec α) (issuance α) where
  representation := representation
  scheme C := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  queryComplete := AbstractMRDT.ofQuery_complete QuerySpec.abstraction
  laws := laws
  vcs := mergeVCs
  canonical := representsCanonical
  substitute := metadataSubstitution
  initial := initialMetadata
  initMetadata := initMetadata
  symmetry := mergeCommMetadata
  causal := causalMetadata
  localMetadata := localMetadata
  sharedMetadata := sharedMetadata
  replaySupply := fun C _ _ _ _ trans irrefl _ _ _ _ => replaySupply C trans irrefl
  representedVersions _ := vcRepresentedVersions
  compatibility := compatibility
  historySound := EventSpec.foldHistorySound

def vcCertificate : AbstractMRDT.Certificate (model (α := α)) (conflict α)
    (EventSpec.spec α) (issuance α) := vcConditions.toCertificate

theorem vcCertifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (issuance α) C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α)) (conflict α) (EventSpec.spec α) C :=
  vcCertificate.versionsV reach

theorem vcCertifiedExecutionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    AbstractMRDT.ExecutionCorrect (model (α := α)) (conflict α) (EventSpec.spec α) trace :=
  vcCertificate.executionsV trace execution

theorem vcCertifiedExecutions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) (issuance α)).Execution (initConfig (D α)) trace) :
    AbstractMRDT.ExecutionCorrect (model (α := α)) (conflict α) (EventSpec.spec α) trace :=
  vcCertificate.executions trace execution

end Sal.MRDTs.Paper1.ORSet.AbstractSpec
