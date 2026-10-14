import Sal.MRDTs.Instances.NotionCoreStructuralRender
import Sal.MRDTs.Instances.NotionCoreStructuralHistory

/-! Direct structural MRDT for the honest Notion core. The maintained state
contains immutable facts, and query computes from rows/cuts/creation links;
neither query nor merge executes the transaction interpreter. The original
factory/client protocol is retained as trace provenance. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralMRDT
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreStructuralFacts (State)
open NotionCoreStructuralExecution (mapConfig)

noncomputable def query (facts : State) (_ : Unit) : Option NotionCoreHistory.View :=
  NotionCoreStructuralRender.observe facts
noncomputable abbrev D := NotionCoreStructuralVC.D query

/-- The complete renderer contract, discharged without a caller observation
premise. Honest issuance and closed-version selection are the existing scope. -/
theorem renderer : NotionCoreStructuralHistory.ClosedQueryAgreement query :=
  NotionCoreStructuralRender.honest_observe

theorem fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction)
    (NotionCoreStructuralVC.representation query) (NotionCoreStructuralVC.scheme query) :=
  NotionCoreStructuralVC.fiveVCs query

/-- Every registered version preserves the exact independent-history witness.
No archive-image, replay-success or desired-query premise is supplied. -/
theorem versions_witness {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec (mapConfig query C) :=
  NotionCoreStructuralHistory.protocol_versions_of_closed query renderer injective honest

theorem specification_ra {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreMRDT.spec (mapConfig query C) :=
  (versions_witness injective honest).heads

/-- Projected states are reached by actual target operations, including the
framework's canonical recursive virtual merge bases. -/
theorem operational_reach {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom
      (initConfig D) (mapConfig query C) :=
  NotionCoreStructuralHistory.protocol_execution_of_closed query renderer injective honest

theorem registered_query {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (v : Version) (archive : Finset Transaction) (events : Set (Op Transaction))
    (registered : C.ver v = some (archive,events)) :
    D.query (NotionCoreStructuralTransport.project archive) () = NotionCoreMRDT.D.query archive () :=
  NotionCoreStructuralHistory.honest_version_agreement query renderer injective honest v archive events registered

#print axioms renderer
#print axioms fiveVCs
#print axioms versions_witness
#print axioms specification_ra
#print axioms operational_reach
#print axioms registered_query
end Sal.MRDTs.Instances.NotionCoreStructuralMRDT
