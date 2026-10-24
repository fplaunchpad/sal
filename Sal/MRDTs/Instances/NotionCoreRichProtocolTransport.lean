import Sal.MRDTs.Instances.NotionCoreRichProtocol
import Sal.MRDTs.Instances.NotionCoreRichSequentialInputs
import Sal.MRDTs.Paper1.SplitSoundness

/-! Generic event/version transport for the independent rich sequential bridge.
This module isolates the ordinary source-history lemma consumed by the final
certificate. It is not itself the final positive certificate: that certificate
must instantiate `HonestHistoryFor` using proved canonical simulations.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolTransport
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction)
open NotionCoreRichProtocolNetwork (State)
open NotionCoreRichProtocolEvents (Event)
open NotionCoreRichProtocolCarrier (D)

/-- The ordinary sequential-history interface, discharged by the proved
canonical simulation in RichCanonicalHistory.honest_history. It retains the
complete source enumeration and its actual query; framework labels carry no
extra semantic choices. -/
def HonestHistoryFor : Prop :=
  ∀ (network : State), NotionCoreRichProtocolNetwork.Reach network →
    ∀ (runs : List NotionRunAllocation.Run), NotionCoreRichProtocolEvents.Closed network runs →
      ∀ (events : List Event), events.map Op.op = NotionCoreRichProtocolEvents.transactionsFor network runs →
        NotionCoreRichSequentialInputs.spec.admits
          (NotionCoreRichSequentialInputs.labels events ++ [.query ()
            ((NotionCoreAtomicFormattingMachine.replay {}
              (NotionCoreRichProtocolEvents.transactionsFor network runs) >>=
                NotionCoreAtomicFormattingMachine.render).map NotionCoreRichProtocolCarrier.neutral)])

/-- Once the ordinary canonical simulation is proved, the same whole-event
witness supplies coverage, paper order, independent conflict visibility and
actual rich-query agreement for every allocated version. -/
theorem versions_witness_of_history (history : HonestHistoryFor)
    {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreRichSequentialInputs.spec config := by
  intro v state events registered query
  cases query
  obtain ⟨ordered,covered,visible,payloads,closed,observed⟩ :=
    NotionCoreRichProtocol.registered_metadata injective reachable v state events registered
  refine ⟨ordered,covered,?_,?_,?_⟩
  · exact visible.imp (fun {_ _} _ =>
      paperOrder_false_of_all_commute (D := D.toUpdateSig) NotionCoreRichProtocolCarrier.all_comm _ _ _ _)
  · exact visible.imp (fun {_ _} hno edge => hno edge.1)
  · have accepted := history network (reachable.paired injective).honest _ closed ordered payloads
    rw [observed]
    exact accepted

theorem specification_ra_of_history (history : HonestHistoryFor)
    {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift) :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreRichSequentialInputs.spec config :=
  (versions_witness_of_history history injective reachable).heads

#print axioms versions_witness_of_history
end Sal.MRDTs.Instances.NotionCoreRichProtocolTransport
