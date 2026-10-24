import Sal.MRDTs.Instances.NotionCoreRichPlainReach
import Sal.MRDTs.Instances.NotionCoreRichProtocol

/-! Forgetting formatting preserves the existing plain editing observation
on the exact projected edit history. The statements include failures and all
registered versions, not only the current receipt peer or an empty example. -/
namespace Sal.MRDTs.Instances.NotionCoreRichPlainConservation
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionRunAllocation (Run)
open NotionCoreRichPayload (Transaction)
open NotionCoreRichPlainNetwork (erase keep)

theorem source_version (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (runs : List Run) :
    (((NotionCoreAtomicFormattingMachine.replay {}
      (NotionCoreRichProtocolEvents.transactionsFor network runs) >>=
        NotionCoreAtomicFormattingMachine.render).map NotionCoreRichProtocolCarrier.neutral).map
          NotionCoreFormattingSpec.forget) =
      (NotionCoreMachine.replay {}
        (NotionCoreReconstruction.transactionsFor (erase network) (runs.filter (keep network))) >>=
          NotionCoreMachine.render) := by
  simp only [Option.map_map,Function.comp_def,NotionCoreRichProtocolCarrier.neutral_forget]
  rw [NotionCoreAtomicFormattingMachine.replay_render_forget,
    NotionCoreRichPlainReach.eraseFormats_eq,
    ← NotionCoreRichPlainReach.transactionsFor_eq network reachable runs]

/-- The actual finite-carrier query at every registered version preserves
the old plain result. Source reachability and state selection are derived
from protocol transitions and the existing five VCs. -/
theorem registered_version {sessions initialLift config network lift}
    (injective : Function.Injective sessions)
    (reachable : NotionCoreRichProtocol.Reach sessions initialLift config network lift)
    (version : Version) (state : Finset Transaction) (events : Set (Op Transaction))
    (registered : config.ver version = some (state,events)) :
    ((NotionCoreRichProtocolCarrier.D).query state ()).map NotionCoreFormattingSpec.forget =
      (NotionCoreMachine.replay {}
        (NotionCoreReconstruction.transactionsFor (erase network)
          ((NotionCoreRichProtocolEvents.version network events lift).filter (keep network))) >>=
            NotionCoreMachine.render) := by
  rw [NotionCoreRichProtocol.registered_query injective reachable version state events registered]
  exact source_version network (reachable.paired injective).honest _

#print axioms source_version
#print axioms registered_version
end Sal.MRDTs.Instances.NotionCoreRichPlainConservation
