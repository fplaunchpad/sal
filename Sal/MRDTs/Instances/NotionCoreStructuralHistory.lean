import Sal.MRDTs.Instances.NotionCoreStructuralExecution

/-! Transport the existing independent history language with the very same
witness. The sole additional hypothesis is registered-version query agreement;
its concrete structural-renderer discharge belongs to the final integration. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralHistory
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreStructuralExecution
open NotionCoreStructuralTransport (project)

def VersionQueryAgreement (query : Query) (C : Configuration NotionCoreMRDT.D) : Prop :=
  ∀ v archive events, C.ver v = some (archive,events) →
    query (project archive) () = NotionCoreMRDT.observe archive

/-- No new sequential witness is selected: metadata and specification are
unchanged, and every answer is transported at its actual registered state. -/
theorem versions_witness (query : Query) (C : Configuration NotionCoreMRDT.D)
    (agreement : VersionQueryAgreement query C)
    (reference : VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec C) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec (mapConfig query C) := by
  intro v state events registered q
  obtain ⟨archive, source, projected⟩ := (mapVer_some_iff C.ver v state events).mp registered
  subst state
  obtain ⟨witness, enumeration, order, visibility, admitted⟩ := reference v archive events source q
  refine ⟨witness, enumeration, ?_, ?_, ?_⟩
  · apply order.imp
    intro a b _ before
    exact paperOrder_false_of_all_commute (NotionCoreStructuralVC.all_comm query)
      (mapConfig query C).replayContext events b a before
  · exact visibility
  · cases q
    change NotionCoreMRDT.spec.admits (projectedLabels id witness ++
      [.query () (query (project archive) ())])
    rw [agreement v archive events source]
    exact admitted

/-- Honest protocol endpoint, with query agreement still explicit. -/
theorem protocol_versions (query : Query)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (agreement : VersionQueryAgreement query C) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec (mapConfig query C) :=
  versions_witness query C agreement (NotionCoreProtocol.versions_witness injective honest)

theorem VersionQueryAgreement.heads {query : Query} {C : Configuration NotionCoreMRDT.D}
    (agreement : VersionQueryAgreement query C) : QueryAgreement query C := by
  intro replica archive head
  unfold Configuration.headState headStateFrom at head
  cases hv : C.head replica with
  | none => simp [hv] at head
  | some version =>
    cases stored : C.ver version with
    | none => simp [hv, stored] at head
    | some pair =>
      have same : pair.1 = archive := by simpa [hv, stored] using head
      exact same ▸ agreement version pair.1 pair.2 stored

/-- Component renderer contract on honest closed versions. This contract is
not an issuance guard and will be discharged by structural reconstruction. -/
def ClosedQueryAgreement (query : Query) : Prop :=
  ∀ network, NotionCoreMachineNetwork.Reach network → ∀ version,
    NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version →
    query (NotionCoreStructuralFacts.ofTransactions
      (NotionCoreReconstruction.transactionsFor network version)) () =
      (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
        NotionCoreMachine.render)

theorem honest_version_agreement (query : Query)
    (renderer : ClosedQueryAgreement query)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    VersionQueryAgreement query C := by
  have paired := honest.paired injective
  have payloadReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable paired.honest)
  have certified := NotionCoreCarrierExecution.certify honest.raw
  have execution := CertifiedExecution.virtual certified
  have metadata := execution.canonicalConfig
    (fun C _ => CommutingPort.automatedJoinAt (D := NotionCoreMRDT.D)
      NotionCoreMRDT.all_comm NotionCoreMRDT.fiveVCs C.replayContext)
  intro v archive events registered
  have image := NotionCoreArchiveCertificate.represented_state_image network payloadReach
    C.replayContext events lift paired.events archive
    (NotionCoreMRDT.represented_versions certified v archive events registered)
  have closed := NotionCoreArchiveEvents.version_closed network payloadReach C.events events C.vis lift
    paired.events (metadata.version_events_causal v archive events registered)
  rw [image, NotionCoreMRDTArchive.observe_carrierFor network payloadReach]
  change query (project (NotionCoreReconstruction.transactionsFor network
    (NotionCoreArchiveEvents.version network events lift)).toFinset) () = _
  rw [NotionCoreStructuralTransport.project_list]
  exact renderer network paired.honest _ closed

/-- All reference guards and factory restrictions are inherited unchanged;
only the renderer component remains parameterized. -/
theorem protocol_versions_of_closed (query : Query)
    (renderer : ClosedQueryAgreement query)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec (mapConfig query C) :=
  protocol_versions query injective honest (honest_version_agreement query renderer injective honest)

theorem protocol_execution_of_closed (query : Query)
    (renderer : ClosedQueryAgreement query)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    (labeledTSV (Target query) (canonicalVirtualMergeBase (Target query))).ReachableFrom
      (initConfig (Target query)) (mapConfig query C) :=
  protocol_reachable query sessions initialLift
    (fun prior => (honest_version_agreement query renderer injective prior).heads) honest

theorem protocol_ra_of_closed (query : Query)
    (renderer : ClosedQueryAgreement query)
    {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    EventSpecificationRALinearizable (Target query) (commutingPolicy Transaction)
      NotionCoreMRDT.spec (mapConfig query C) :=
  (protocol_versions_of_closed query renderer injective honest).heads

#print axioms protocol_ra_of_closed
#print axioms protocol_execution_of_closed
#print axioms honest_version_agreement
#print axioms protocol_versions_of_closed
#print axioms versions_witness
#print axioms protocol_versions
end Sal.MRDTs.Instances.NotionCoreStructuralHistory
