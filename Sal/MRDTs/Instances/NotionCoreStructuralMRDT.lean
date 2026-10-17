import Sal.MRDTs.Instances.NotionCoreStructuralRender
import Sal.MRDTs.Instances.NotionCoreStructuralHistory

/-! Direct structural MRDT for the honest Notion core. The maintained state
contains immutable facts, and query computes from rows/cuts/creation links;
neither query nor merge executes the transaction interpreter. The original
factory/client protocol is retained as trace provenance. The carrier covers the
merge-free fragment: a block merge's effect depends on which blocks are alive
when it replays, which an order-free fact set cannot evaluate. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralMRDT
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreStructuralFacts (State)
open NotionCoreStructuralExecution (mapConfig)

noncomputable def query (facts : State) (_ : Unit) : Option NotionCoreHistory.View :=
  NotionCoreStructuralRender.observe facts
noncomputable abbrev D := NotionCoreStructuralVC.D query

/-- The complete renderer contract, discharged without a caller observation
premise. Honest issuance, closed-version selection and merge-free networks are
the scope; merge-free because the fact query has no replay order. -/
theorem renderer : NotionCoreStructuralHistory.ClosedQueryAgreement query :=
  NotionCoreStructuralRender.honest_observe

theorem fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction)
    (NotionCoreStructuralVC.representation query) (NotionCoreStructuralVC.scheme query) :=
  NotionCoreStructuralVC.fiveVCs query

/-- Every registered version preserves the exact independent-history witness.
No archive-image, replay-success or desired-query premise is supplied. The
network is merge-free, since the fact query cannot evaluate a block merge. -/
theorem versions_witness {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (free : NotionCoreMergeFree.MergeFree network) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec (mapConfig query C) :=
  NotionCoreStructuralHistory.protocol_versions_of_closed query renderer injective honest free

/-- RA-linearizability of the structural carrier on merge-free networks, the
fragment its order-free query can evaluate. -/
theorem specification_ra {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (free : NotionCoreMergeFree.MergeFree network) :
    EventSpecificationRALinearizable D (commutingPolicy Transaction)
      NotionCoreMRDT.spec (mapConfig query C) :=
  (versions_witness injective honest free).heads

/-- Projected states are reached by actual target operations, including the
framework's canonical recursive virtual merge bases. The network is merge-free,
since each step needs the renderer contract at the preceding configuration. -/
theorem operational_reach {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (free : NotionCoreMergeFree.MergeFree network) :
    (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom
      (initConfig D) (mapConfig query C) :=
  NotionCoreStructuralHistory.protocol_execution_of_closed query renderer injective honest free

/-- Registered-version query agreement with the reference carrier on
merge-free networks, the fragment the structural query covers. -/
theorem registered_query {sessions initialLift C network lift}
    (injective : Function.Injective sessions)
    (honest : NotionCoreProtocol.Reach sessions initialLift C network lift)
    (free : NotionCoreMergeFree.MergeFree network)
    (v : Version) (archive : Finset Transaction) (events : Set (Op Transaction))
    (registered : C.ver v = some (archive,events)) :
    D.query (NotionCoreStructuralTransport.project archive) () = NotionCoreMRDT.D.query archive () :=
  NotionCoreStructuralHistory.honest_version_agreement query renderer injective honest free
    v archive events registered

#print axioms renderer
#print axioms fiveVCs
#print axioms versions_witness
#print axioms specification_ra
#print axioms operational_reach
#print axioms registered_query
end Sal.MRDTs.Instances.NotionCoreStructuralMRDT
