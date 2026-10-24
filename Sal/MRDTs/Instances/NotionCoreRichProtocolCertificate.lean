import Sal.MRDTs.Instances.NotionCoreRichCanonicalHistory
import Sal.MRDTs.Instances.NotionCoreRichPlainConservation
import Sal.MRDTs.Instances.NotionCoreRichProtocolPeerClosure
import Sal.MRDTs.Instances.NotionCoreRichSequentialSelection
import Sal.MRDTs.Instances.NotionCoreRichSequentialIssuedCarrier

/-!
Positive certificate for the repaired Notion rich-text protocol.

All segments of one format transaction share a priority and issued Boolean.
The independent specification stores current character and insertion-gap
marks, with no annotation log or replay sorting. Actual source preparation,
allocation, receipt and framework transitions derive the history hypotheses.
The protocol includes ordinary and canonical recursive-base merge steps.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolCertificate
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction Part)
open NotionCoreRichProtocolCarrier (D)
open NotionCoreRichSequential.Refinement (Related)
open NotionCoreRichSequential.IssuedCarrier (issuedFormat formatted)

/-- One actual whole-event order supplies coverage, required order,
specification visibility and the full identified rich query. No invariant,
replay success, source/core image or sequential agreement is a premise. -/
theorem versions_witness {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreRichSequentialInputs.spec config :=
  NotionCoreRichProtocolTransport.versions_witness_of_history
    NotionCoreRichCanonicalHistory.honest_history injective reachable

theorem specification_ra {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift) :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreRichSequentialInputs.spec config := (versions_witness injective reachable).heads

/-- Source callers also obtain their independent state from their actual
received history. The state relation is a conclusion, never an issue guard. -/
theorem source_reconstruction (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session) :
    ∃ actual abstract, NotionCoreRichProtocolNetwork.reconstruct network session = some actual ∧
      Related actual abstract ∧ NotionCoreRichSequentialInputs.executeTransactions {}
        (NotionCoreRichProtocolEvents.transactionsFor network (network.allocation.peers session).received) =
          some abstract := by
  obtain ⟨actual,abstract,replayed,related,independent⟩ :=
    NotionCoreRichCanonicalHistory.canonical_history_version network reachable _
      (NotionCoreRichProtocolPeerClosure.peers_closed reachable session)
  exact ⟨actual,abstract,by rw [NotionCoreRichProtocolPeerClosure.reconstruct_peer]; exact replayed,
    related,independent⟩

/-- Every successful toggle uses a nonempty clipped selection and one issued
value. Its batch covers exactly those identities across all displayed blocks.
The physical-coordinate relation is derived from actual reachable callers. -/
theorem selection_exact (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List Part) (value : Bool) (priority : NotionRunAllocation.Id)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value)) :
    ∃ abstract rich, Related actual abstract ∧
      NotionCoreRichSequential.Selection.selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧
      rich ≠ [] ∧ value = !(rich.all (·.bold)) ∧
      NotionCoreRichSequential.Selection.selectedAddresses abstract (NotionCoreMachine.blockName block) start stop =
        some (rich.map (·.address)) ∧
      NotionCoreRichSequential.Selection.selectedVerdict abstract (NotionCoreMachine.blockName block) start stop = some value ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormatting.covers (NotionCoreAtomicFormattingMachine.instanceForest actual)
          (NotionCoreAtomicFormatting.Batch.ofFormat priority parts value) slot.address.1
          (NotionCoreRichSequential.Selection.coordinate actual slot.address) =
            (rich.map (·.address)).contains slot.address := by
  obtain ⟨current,abstract,currentReplay,related,independent⟩ := source_reconstruction network reachable session
  rw [reconstructed] at currentReplay
  cases Option.some.inj currentReplay
  obtain ⟨rich,selected,nonempty,verdict,addresses,chosen,coverage⟩ :=
    NotionCoreRichSequential.Selection.formatPayload_exact network reachable session actual abstract
      reconstructed related block start stop parts value priority prepared
  exact ⟨abstract,rich,related,selected,nonempty,verdict,addresses,chosen,coverage⟩

/-- The actual rich query at every allocated version succeeds; the public
history specification cannot justify a failed renderer as an empty document. -/
theorem query_total {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift)
    (version : Version) (state : Finset Transaction) (events : Set (Op Transaction))
    (registered : config.ver version = some (state,events)) :
    ∃ answer, D.query state () = some answer := by
  obtain ⟨ordered,covered,visible,payloads,closed,observed⟩ :=
    NotionCoreRichProtocol.registered_metadata injective reachable version state events registered
  obtain ⟨actual,abstract,replayed,related,independent⟩ :=
    NotionCoreRichCanonicalHistory.canonical_history_version network (reachable.paired injective).honest _ closed
  obtain ⟨answer,rendered,abstractRead⟩ := NotionCoreRichSequential.Refinement.render_total_related related
  refine ⟨NotionCoreRichProtocolCarrier.neutral answer,?_⟩
  rw [observed]
  simp only [replayed,Bind.bind,Option.bind,rendered,Option.map_some]

/-- The actual finite-carrier update performs the prepared assignment on
exactly the selected visible identities. Reachability derives every state,
freshness, coordinate and verdict premise of the local simulation. -/
theorem issued_format_effect (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List Part) (value : Bool)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value))
    (time : Timestamp) (replica : Replica) :
    ∃ abstract raw rich, Related actual abstract ∧
      D.query (D.update (NotionCoreRichProtocolCarrier.carrierFor network session)
        (time,replica,issuedFormat network session parts value)) () =
          some (NotionCoreRichProtocolCarrier.neutral raw) ∧
      NotionCoreAtomicFormattingMachine.render (formatted actual network session parts value) = some raw ∧
      NotionCoreRichSequential.Selection.selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧
      rich ≠ [] ∧ value = !(rich.all (·.bold)) ∧
      (∀ row ∈ NotionCoreRichProtocolCarrier.neutral raw, ∀ char ∈ row.2,
        char.bold = NotionCoreAtomicFormattingMachine.boldAt (formatted actual network session parts value) char.address) ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormattingMachine.boldAt (formatted actual network session parts value) slot.address =
          if (rich.map (·.address)).contains slot.address then value
          else NotionCoreAtomicFormattingMachine.boldAt actual slot.address := by
  obtain ⟨current,abstract,currentReplay,related,independent⟩ := source_reconstruction network reachable session
  rw [reconstructed] at currentReplay
  cases Option.some.inj currentReplay
  obtain ⟨raw,rich,checked⟩ := NotionCoreRichSequential.IssuedCarrier.format_update_effect network
    reachable session actual abstract reconstructed related block start stop parts value prepared time replica
  exact ⟨abstract,raw,rich,related,checked⟩

#print axioms versions_witness
#print axioms specification_ra
#print axioms source_reconstruction
#print axioms selection_exact
#print axioms query_total
#print axioms issued_format_effect
end Sal.MRDTs.Instances.NotionCoreRichProtocolCertificate
