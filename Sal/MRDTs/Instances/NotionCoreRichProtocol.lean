import Sal.MRDTs.Instances.NotionCoreRichProtocolPair
import Sal.MRDTs.Instances.NotionCoreRichProtocolExecution

/-! The repaired rich caller and the actual version-DAG semantics move together.
Source requests execute preparation and reference checks and reserve complete
transactions. The protocol does not accept completed replay, coordinate,
state-image or sequential-correctness assertions as constructor premises.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocol
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction Payload)
open NotionCoreRichProtocolNetwork (State Request initial)
open NotionCoreRichProtocolEvents (Event archive reservation version witness)
open NotionCoreRichProtocolPair (Pair extendLift)
open NotionCoreRichProtocolCarrier (D)
open NotionRunAllocation (Session)

def draft (network : State) (session : Session) (payload : Payload) : Transaction :=
  ⟨(NotionRunAllocation.reserve (network.allocation.peers session) session payload.width).first,payload⟩

def factoryTx (atoms : List Nat) : Transaction := ⟨⟨1,[65]⟩,.edit (.bootstrap atoms)⟩

private theorem initial_events : (initConfig D).events = ∅ := by
  ext event
  constructor
  · rintro ⟨replica,events,head,member⟩
    by_cases zero : replica = 0
    · subst replica
      simp [Configuration.headEvents,headEventsFrom,initConfig] at head
      subst events
      exact member
    · simp [Configuration.headEvents,headEventsFrom,initConfig,zero] at head
  · exact fun impossible => impossible.elim

theorem initial_pair (sessions : Replica → Session) (injective : Function.Injective sessions)
    (lift : Transaction → Event) : Pair (initConfig D) initial sessions lift := by
  refine ⟨.init,injective,?_,?_,?_⟩
  · constructor
    · intro tx member; simp [archive,initial] at member
    · intro event; simp [initial_events,archive,initial]
    · intro left right member; simp [archive,initial] at member
  · constructor
    · intro replica events head entry member; simp [initial] at member
    · intro replica absent; rfl
  · intro peer; exact NotionCoreAllocationClock.empty_tight

inductive Reach (sessions : Replica → Session) (initialLift : Transaction → Event) :
    Configuration D → State → (Transaction → Event) → Prop where
  | init : Reach sessions initialLift (initConfig D) initial initialLift
  | fork {config next network lift} (before : Reach sessions initialLift config network lift)
      (target source : Replica) (raw : Step D config (.fork target source) next) :
      Reach sessions initialLift next
        (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) lift
  | merge {config next network lift} (before : Reach sessions initialLift config network lift)
      (target source : Replica)
      (raw : StepV D (canonicalVirtualMergeBase D) config (.merge target source) next) :
      Reach sessions initialLift next
        (NotionCoreRichProtocolNetwork.exchange network (sessions target) (sessions source)) lift
  | factory {config next lift} (before : Reach sessions initialLift config initial lift)
      (time : Timestamp) (sender : Replica) (atoms : List Nat) (factorySession : sessions sender = [65])
      (raw : Step D config (.apply time sender (factoryTx atoms)) next) :
      Reach sessions initialLift next (NotionCoreRichProtocolNetwork.seeded atoms)
        (extendLift lift (factoryTx atoms) (time,sender,factoryTx atoms))
  | request {config next network lift} (before : Reach sessions initialLift config network lift)
      (time : Timestamp) (sender : Replica) (request : Request) (payload : Payload)
      (prepared : NotionCoreRichProtocolNetwork.prepareAt network (sessions sender) request = some payload)
      (references : (NotionCoreRichProtocolNetwork.references payload).all
        (NotionCoreRichProtocolNetwork.known network (sessions sender)) = true)
      (raw : Step D config (.apply time sender (draft network (sessions sender) payload)) next) :
      Reach sessions initialLift next (NotionCoreRichProtocolNetwork.emit network (sessions sender) payload)
        (extendLift lift (draft network (sessions sender) payload)
          (time,sender,draft network (sessions sender) payload))
  | query {config network lift} (before : Reach sessions initialLift config network lift)
      (sender : Replica) (answer : Option NotionCoreRichProtocolCarrier.View)
      (raw : Step D config (.query sender () answer) config) :
      Reach sessions initialLift config network lift

theorem Reach.raw {sessions initialLift config network lift}
    (reachable : Reach sessions initialLift config network lift) :
    (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) config := by
  induction reachable with
  | init => exact .refl
  | fork before target source step ih => exact ih.tail ⟨_,.base step⟩
  | merge before target source step ih => exact ih.tail ⟨_,step⟩
  | factory before time sender atoms session step ih => exact ih.tail ⟨_,.base step⟩
  | request before time sender request payload prepared references step ih => exact ih.tail ⟨_,.base step⟩
  | query before sender answer step ih => exact ih

theorem Reach.paired {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift) : Pair config network sessions lift := by
  induction reachable with
  | init => exact initial_pair sessions injective initialLift
  | fork before target source step ih =>
      exact NotionCoreRichProtocolPair.fork_preserves _ _ _ ih target source step
  | merge before target source step ih =>
      exact NotionCoreRichProtocolPair.mergeV_preserves _ _ _ _ ih target source step
  | factory before time sender atoms session step ih =>
      have allocated : reservation (factoryTx atoms) = NotionRunAllocation.reserve
          (initial.allocation.peers (sessions sender)) (sessions sender) (factoryTx atoms).payload.width := by
        rw [session]; rfl
      have source : NotionCoreRichProtocolNetwork.Reach
          (NotionCoreRichProtocolNetwork.publish initial (sessions sender) (factoryTx atoms)) := by
        rw [session]
        exact .bootstrap atoms
      simpa only [session] using
        NotionCoreRichProtocolPair.emit_preserves _ _ _ ih time sender (factoryTx atoms) step allocated source
  | @request config next network lift before time sender request payload prepared references step ih =>
      have issued : NotionCoreRichProtocolNetwork.issue network (sessions sender) request =
          some (NotionCoreRichProtocolNetwork.emit network (sessions sender) payload) := by
        simp [NotionCoreRichProtocolNetwork.issue,prepared,references]
      have source := NotionCoreRichProtocolNetwork.Reach.request (sessions sender) request ih.honest issued
      exact NotionCoreRichProtocolPair.emit_preserves _ _ _ ih time sender _ step rfl source
  | query before sender answer step ih => exact ih

theorem Reach.certified {sessions initialLift config network lift}
    (reachable : Reach sessions initialLift config network lift) :
    MintCertifiedReachV D (canonicalVirtualMergeBase D) NotionCoreRichProtocolCarrier.issuance config :=
  NotionCoreRichProtocolExecution.certify reachable.raw

/-- Every allocated version is exactly the finite image of one selected source
archive, as derived from the five VCs and structural event coupling. -/
theorem represented_state_image (network : State)
    (honest : NotionCoreRichProtocolNetwork.Reach network)
    (config : Configuration D) (lift : Transaction → Event)
    (coupled : NotionCoreRichProtocolEvents.Coupling network config.events config.vis lift)
    (events : Set Event) (state : Finset Transaction)
    (represented : NotionCoreRichProtocolCarrier.representation config.replayContext events state) :
    state = (NotionCoreRichProtocolEvents.transactionsFor network (version network events lift)).toFinset := by
  obtain ⟨supported,enumeration,enumerates,folded⟩ := represented
  rw [← folded,NotionCoreRichProtocolCarrier.fold_payloads]
  change ((∅ : Finset Transaction) ∪ (enumeration.map Op.op).toFinset) = _
  rw [Finset.empty_union]
  apply Finset.ext
  intro tx
  simp only [List.mem_toFinset,List.mem_map]
  rw [NotionCoreRichProtocolEvents.selected_transactions network honest events lift tx]
  constructor
  · rintro ⟨event,member,equal⟩
    have present := (enumerates.2 event).mp member
    have found := NotionCoreRichProtocolEvents.event_payload network config.events config.vis lift coupled
      event (supported event present)
    exact equal ▸ ⟨found.1,by simpa [found.2] using present⟩
  · rintro ⟨archived,present⟩
    exact ⟨lift tx,(enumerates.2 _).mpr present,coupled.payload tx archived⟩

theorem registered_state_image {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift)
    (v : Version) (state : Finset Transaction) (events : Set Event)
    (registered : config.ver v = some (state,events)) :
    state = (NotionCoreRichProtocolEvents.transactionsFor network (version network events lift)).toFinset := by
  have paired := reachable.paired injective
  exact represented_state_image network paired.honest config lift paired.events events state
    (NotionCoreRichProtocolCarrier.represented_versions reachable.certified v state events registered)

/-- The issuer's actual local finite carrier is derived to contain exactly
its received source transactions. This equation is not a Reach premise. -/
theorem head_state_image {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift)
    (sender : Replica) (v : Version) (state : Finset Transaction) (events : Set Event)
    (head : config.head sender = some v) (registered : config.ver v = some (state,events)) :
    state = NotionCoreRichProtocolCarrier.carrierFor network (sessions sender) := by
  have paired := reachable.paired injective
  have headEvents := config.headEvents_eq_of_head_ver head registered
  rw [registered_state_image injective reachable v state events registered]
  ext tx
  change tx ∈ (NotionCoreRichProtocolEvents.transactionsFor network (version network events lift)).toFinset ↔
    tx ∈ (NotionCoreRichProtocolNetwork.receivedTransactions network (sessions sender)).toFinset
  simp only [List.mem_toFinset]
  rw [NotionCoreRichProtocolEvents.selected_transactions network paired.honest events lift tx]
  simp only [NotionCoreRichProtocolNetwork.receivedTransactions,List.mem_map,List.mem_filter,
    List.contains_iff_mem]
  constructor
  · rintro ⟨archived,present⟩
    obtain ⟨entry,member,equal⟩ := archived
    refine ⟨entry,⟨member,?_⟩,equal⟩
    rw [paired.heads.receipts sender events headEvents entry member,equal]
    exact present
  · rintro ⟨entry,⟨member,received⟩,equal⟩
    refine ⟨⟨entry,member,equal⟩,?_⟩
    rw [paired.heads.receipts sender events headEvents entry member] at received
    simpa [equal] using received

/-- Actual rich observation at every allocated version, using that same
source selection and order. No read equality is a supplied protocol invariant. -/
theorem registered_query {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift)
    (v : Version) (state : Finset Transaction) (events : Set Event)
    (registered : config.ver v = some (state,events)) :
    D.query state () =
      ((NotionCoreAtomicFormattingMachine.replay {}
        (NotionCoreRichProtocolEvents.transactionsFor network (version network events lift)) >>=
          NotionCoreAtomicFormattingMachine.render).map NotionCoreRichProtocolCarrier.neutral) := by
  change NotionCoreRichProtocolCarrier.observe state = _
  rw [NotionCoreRichProtocolCarrier.observe,registered_state_image injective reachable v state events registered,
    NotionCoreRichProtocolCarrier.transactions_of_sorted _
      (NotionCoreRichProtocolEvents.transactionsFor_ordered network (reachable.paired injective).honest _)]

/-- One derived whole-event order supplies coverage, all visibility edges,
the exact source transaction list, causal closure and the actual query. -/
theorem registered_metadata {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : Reach sessions initialLift config network lift)
    (v : Version) (state : Finset Transaction) (events : Set Event)
    (registered : config.ver v = some (state,events)) :
    let runs := version network events lift
    ∃ ordered : List Event, listPermOf ordered events ∧ respects ordered config.vis ∧
      ordered.map Op.op = NotionCoreRichProtocolEvents.transactionsFor network runs ∧
      NotionCoreRichProtocolEvents.Closed network runs ∧
      D.query state () = ((NotionCoreAtomicFormattingMachine.replay {}
        (NotionCoreRichProtocolEvents.transactionsFor network runs) >>=
          NotionCoreAtomicFormattingMachine.render).map NotionCoreRichProtocolCarrier.neutral) := by
  have paired := reachable.paired injective
  have canonical := CommutingPort.automatedCanonicalConfig (D := D) NotionCoreRichProtocolCarrier.all_comm
    NotionCoreRichProtocolCarrier.fiveVCs reachable.certified
  have supported := canonical.version_events_supported v state events registered
  refine ⟨witness network events lift,
    NotionCoreRichProtocolEvents.witness_enumerates network paired.honest config.events events config.vis lift paired.events supported,
    NotionCoreRichProtocolEvents.witness_respects network paired.honest config.events events config.vis lift paired.events supported,
    NotionCoreRichProtocolEvents.witness_payloads network paired.honest config.events events config.vis lift paired.events,
    ?_,registered_query injective reachable v state events registered⟩
  exact NotionCoreRichProtocolEvents.version_closed network paired.honest config.events events config.vis lift paired.events
    (fun a b visible present => canonical.version_events_causal v state events registered a b visible present)

#print axioms Reach.paired
#print axioms registered_state_image
#print axioms registered_query
#print axioms registered_metadata
end Sal.MRDTs.Instances.NotionCoreRichProtocol
