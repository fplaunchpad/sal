import Sal.MRDTs.Instances.NotionCoreMachineGenesis
import Sal.MRDTs.Instances.NotionCoreIssuanceGuard
import Sal.MRDTs.Instances.NotionCoreArchiveCertificate
import Sal.MRDTs.Instances.NotionCoreCarrierExecution

/-! Explicit source factory initialization and honest ordinary protocol
extensions. The global factory phase is not encoded as a local empty-state
issuance guard. All rendering/history consequences use the same archive witness. -/
namespace Sal.MRDTs.Instances.NotionCoreProtocol
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction reservation)
open NotionCorePayloadNetwork (State)
open NotionCoreMRDT (D)
open NotionCoreArchiveEvents (Event version)
open NotionCoreMachineExecution (Pair)
open NotionRunAllocation (Session)

/-- Actual carrier representation and head/receipt matching identify the
current local finite store with the source peer's received version. -/
theorem head_state_image (network : State) (config : Configuration D)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift)
    {I : Issuance D} (execution : CertifiedExecution D I config)
    (sender : Replica) (v : Version) (state : Finset Transaction) (events : Set Event)
    (head : config.head sender = some v) (registered : config.ver v = some (state,events)) :
    state = NotionCoreMRDTArchive.carrierFor network (network.allocation.peers (sessions sender)).received := by
  have virtual : MintCertifiedReachV D (canonicalVirtualMergeBase D) I config := by
    cases execution with
    | ordinary reachable => exact reachable.toV
    | virtual reachable => exact reachable
  have archiveReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable paired.honest)
  have represented := NotionCoreMRDT.represented_versions virtual v state events registered
  rw [NotionCoreArchiveCertificate.represented_state_image network archiveReach config.replayContext
    events lift paired.events state represented]
  have headEvents := config.headEvents_eq_of_head_ver head registered
  apply Finset.ext
  intro tx
  change tx ∈ (NotionCoreReconstruction.transactionsFor network (version network events lift)).toFinset ↔ _
  rw [List.mem_toFinset,NotionCoreArchiveEvents.selected_transactions network archiveReach events lift tx,
    NotionCoreMRDTArchive.carrierFor_membership]
  constructor
  · rintro ⟨archived,selected⟩
    obtain ⟨entry,member,equal⟩ := List.mem_map.mp archived
    exact ⟨⟨entry,member,equal⟩,equal ▸
      (paired.heads.receipts sender events headEvents entry member).mpr (equal ▸ selected)⟩
  · rintro ⟨⟨entry,member,equal⟩,received⟩
    exact ⟨List.mem_map.mpr ⟨entry,member,equal⟩,
      equal ▸ (paired.heads.receipts sender events headEvents entry member).mp (equal ▸ received)⟩

/-- The ordinary local guard is sufficient for actual Sal apply/source mint
pair preservation. Source receipt correspondence and clock alignment are
conclusions of the existing structural pairing and carrier VC representation. -/
theorem ordinary_apply_preserves (network : State) (config next : Configuration D)
    (sessions : Replica → Session) (lift : Transaction → Event)
    (paired : Pair config network sessions lift)
    {I : Issuance D} (execution : CertifiedExecution D I config)
    (time : Timestamp) (sender : Replica) (tx : Transaction)
    (v : Version) (state : Finset Transaction) (events : Set Event)
    (head : config.head sender = some v) (registered : config.ver v = some (state,events))
    (guard : NotionCoreIssuanceGuard.CanIssue sessions (time,sender,tx) state)
    (raw : Step D config (.apply time sender tx) next) :
    let ticks := tx.id.counter - ((network.allocation.peers (sessions sender)).clock + 1)
    Pair next (NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap network (sessions sender) ticks)
      (sessions sender) tx.payload tx) sessions
      (NotionCoreMachineExecution.extendLift lift tx (time,sender,tx)) := by
  have stateImage := head_state_image network config sessions lift paired execution sender v state events head registered
  obtain ⟨document,request,draft,reconstructed,nonempty,selected,prepared,later⟩ :=
    NotionCoreIssuanceGuard.guard_prepares network paired.honest sessions (time,sender,tx) state stateImage
      (paired.tight (sessions sender)) guard
  have preparedLater := NotionCoreMachineMint.prepare_later network (sessions sender) tx.payload draft prepared
    tx.id.counter later
  have allocated : reservation tx = NotionRunAllocation.reserve
      ((NotionCorePayloadNetwork.gap network (sessions sender)
        (tx.id.counter - ((network.allocation.peers (sessions sender)).clock + 1))).allocation.peers (sessions sender))
      (sessions sender) tx.payload.width := by
    have finalPrepared : NotionCorePayload.prepare
        (NotionCorePayloadNetwork.forget (NotionCorePayloadNetwork.gap network (sessions sender)
          (tx.id.counter - ((network.allocation.peers (sessions sender)).clock + 1))))
        (sessions sender) tx.payload = some tx := by
      have sameSession : tx.id.session = sessions sender := guard.1
      simpa only [← sameSession] using preparedLater
    exact congrArg NotionCoreIssuance.Record.run (NotionCorePayload.prepare_record finalPrepared)
  obtain ⟨_,_,honestNext⟩ := NotionCoreIssuanceGuard.guard_issues network paired.honest sessions
    (time,sender,tx) state stateImage (paired.tight (sessions sender)) guard
  exact NotionCoreMachineExecution.emit_preserves network sessions lift paired time sender tx raw _ allocated honestNext

/-- A source protocol trace refining actual Sal steps. The factory constructor
requires the source archive to be initial; ordinary applies use only the local
guard. Recursive virtual merge bases remain the actual framework operation. -/
inductive Reach (sessions : Replica → Session) (initialLift : Transaction → Event) :
    Configuration D → State → (Transaction → Event) → Prop where
  | init : Reach sessions initialLift (initConfig D) NotionCorePayloadNetwork.initial initialLift
  | fork {config next network lift} (before : Reach sessions initialLift config network lift)
      (target source : Replica) (raw : Step D config (.fork target source) next) :
      Reach sessions initialLift next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) lift
  | merge {config next network lift} (before : Reach sessions initialLift config network lift)
      (target source : Replica) (raw : StepV D (canonicalVirtualMergeBase D) config (.merge target source) next) :
      Reach sessions initialLift next (NotionCorePayloadNetwork.exchange network (sessions target) (sessions source)) lift
  | factory {config next lift} (before : Reach sessions initialLift config NotionCorePayloadNetwork.initial lift)
      (time : Timestamp) (sender : Replica) (atoms : List Nat) (factorySession : sessions sender = [65])
      (raw : Step D config (.apply time sender (NotionCorePayload.bootstrap atoms)) next) :
      Reach sessions initialLift next (NotionCorePayloadNetwork.seeded atoms)
        (NotionCoreMachineExecution.extendLift lift (NotionCorePayload.bootstrap atoms) (time,sender,NotionCorePayload.bootstrap atoms))
  | apply {config next network lift} (before : Reach sessions initialLift config network lift)
      (time : Timestamp) (sender : Replica) (tx : Transaction)
      (v : Version) (state : Finset Transaction) (events : Set Event)
      (head : config.head sender = some v) (registered : config.ver v = some (state,events))
      (guard : NotionCoreIssuanceGuard.CanIssue sessions (time,sender,tx) state)
      (raw : Step D config (.apply time sender tx) next) :
      Reach sessions initialLift next
        (NotionCorePayloadNetwork.emit (NotionCorePayloadNetwork.gap network (sessions sender)
          (tx.id.counter - ((network.allocation.peers (sessions sender)).clock + 1))) (sessions sender) tx.payload tx)
        (NotionCoreMachineExecution.extendLift lift tx (time,sender,tx))
  | query {config network lift} (before : Reach sessions initialLift config network lift)
      (sender : Replica) (query : Unit) (answer : Option NotionCoreHistory.View)
      (raw : Step D config (.query sender query answer) config) :
      Reach sessions initialLift config network lift

theorem Reach.raw {sessions initialLift config network lift}
    (reachable : Reach sessions initialLift config network lift) :
    (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) config := by
  induction reachable with
  | init => exact .refl
  | fork before target source step ih => exact ih.tail ⟨_, .base step⟩
  | merge before target source step ih => exact ih.tail ⟨_, step⟩
  | factory before time sender atoms session step ih => exact ih.tail ⟨_, .base step⟩
  | apply before time sender tx v state events head registered guard step ih => exact ih.tail ⟨_, .base step⟩
  | query before sender query answer step ih => exact ih

theorem Reach.paired {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift) : Pair config network sessions lift := by
  induction reachable with
  | init => exact NotionCoreMachineGenesis.initial_pair sessions injective initialLift
  | fork before target source step ih => exact NotionCoreMachineExecution.fork_preserves _ _ _ ih target source step
  | merge before target source step ih => exact NotionCoreMachineExecution.mergeV_preserves _ _ _ _ ih target source step
  | factory before time sender atoms session step ih => exact NotionCoreMachineGenesis.factory_pair _ _ ih time sender atoms session step
  | apply before time sender tx v state events head registered guard step ih =>
    exact ordinary_apply_preserves _ _ _ _ _ ih
      (.virtual (NotionCoreCarrierExecution.certify before.raw)) time sender tx v state events head registered guard step
  | query before sender query answer step ih => exact ih

/-- Every registered version of the explicit honest protocol has one shared
witness for actual rendering, causal visibility and the independent history
specification. No archive coupling or state-image equation is supplied. -/
theorem versions_witness {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec config := by
  have paired := reachable.paired injective
  exact NotionCoreArchiveCertificate.certified_versions_witness network paired.honest
    (.virtual (NotionCoreCarrierExecution.certify reachable.raw)) lift paired.events

/-- The full-input RA criterion for current heads follows from the stronger
certificate for every allocated version. -/
theorem specification_ra {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift) :
    EventSpecificationRALinearizable D (commutingPolicy Transaction) NotionCoreMRDT.spec config :=
  (versions_witness injective reachable).heads

#print axioms specification_ra
#print axioms Reach.paired
#print axioms versions_witness
#print axioms head_state_image
#print axioms ordinary_apply_preserves
end Sal.MRDTs.Instances.NotionCoreProtocol
