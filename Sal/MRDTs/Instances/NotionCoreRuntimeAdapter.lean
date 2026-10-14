import Sal.MRDTs.Instances.NotionCoreRuntimeQuery
import Sal.MRDTs.Instances.NotionCoreRuntimeState

/-! Concrete native keyed-state adapter. The query's callbacks read maintained
hash maps and counts directly; row enumeration is supplied only to its proof. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeAdapter
open NotionCoreRuntimeState (State)
open NotionCorePartition (Entry)
open NotionCoreMachine (blockName)

def cutEntries (state : State) : List Entry :=
  state.created.toList.map (fun pair => ⟨blockName pair.1,(blockName pair.1,.start)⟩) ++
    state.cuts.toList.map (fun pair => ⟨blockName pair.2,
      NotionCorePhysicalReplay.address (blockName pair.1.1) pair.1.2⟩)

def toView (state : State) : NotionCoreRuntimeQuery.View where
  rows := NotionCoreRuntimeState.rowsAt state
  lookup := NotionCoreRuntimeState.lookupAt state
  bucket := NotionCoreRuntimeState.childrenAt state
  fuel := NotionCoreRuntimeState.countAt state
  links := NotionCoreRuntimeState.creatorLinks state
  records := cutEntries state

def observeState (state : State) : Option NotionCoreHistory.View :=
  NotionCoreRuntimeQuery.observe (toView state)


end Sal.MRDTs.Instances.NotionCoreRuntimeAdapter
