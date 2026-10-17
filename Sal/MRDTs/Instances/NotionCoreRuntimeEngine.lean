import Sal.MRDTs.Instances.NotionCoreRuntimeState
import Sal.MRDTs.Instances.NotionCoreRuntimeMetadata

/-! Pure executable boundary: immutable transaction identity checks and retained
receipt metadata surround the indexed core. Neither merge path replays payloads.
Failed batches return an error without exposing a partially updated state.
Transactions carrying a block-merge payload are refused on receipt. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEngine
open NotionCorePayload (Transaction)

structure State where
  core : NotionCoreRuntimeState.State := NotionCoreRuntimeState.empty
  metadata : NotionCoreRuntimeMetadata.State := NotionCoreRuntimeMetadata.empty

def empty : State := {}

def prior (state : NotionCoreRuntimeMetadata.State) (tx : Transaction) : Option Transaction :=
  state.archive.find? (fun old => decide (old.id = tx.id))

def receiveMetadata (state : NotionCoreRuntimeMetadata.State) (tx : Transaction) :
    Except String NotionCoreRuntimeMetadata.State :=
  match prior state tx with
  | some old => if old = tx then .ok state else .error "conflicting transaction identity"
  | none => .ok (NotionCoreRuntimeMetadata.receive state tx)

/-- Merge transactions are outside the executable's scope: its indexed fact
query has no replay order in which to evaluate a block merge. -/
def admissible (tx : Transaction) : Bool := match tx.payload with
  | .merge _ _ => false
  | _ => true

theorem admissible_notMerge {tx : Transaction} (admitted : admissible tx = true) :
    NotionCoreMergeFree.NotMerge tx := by
  intro source target payload
  simp [admissible,payload] at admitted

theorem admissible_of_notMerge {tx : Transaction} (notMerge : NotionCoreMergeFree.NotMerge tx) :
    admissible tx = true := by
  unfold admissible
  split
  · next source target payload => exact absurd payload (notMerge source target)
  · rfl

/-- Receipt of an admissible transaction: identity check, then fact integration. -/
def receiveAdmitted (state : State) (tx : Transaction) : Except String State := do
  match prior state.metadata tx with
  | some old =>
    if old = tx then return state else throw "conflicting transaction identity"
  | none =>
    let core ← NotionCoreRuntimeState.receive state.core tx
    return ⟨core, NotionCoreRuntimeMetadata.receive state.metadata tx⟩

/-- Merge transactions are outside the executable's scope and are refused on
receipt, so no stored archive contains one. -/
def receive (state : State) (tx : Transaction) : Except String State :=
  if admissible tx then receiveAdmitted state tx
  else .error "merge transactions are outside the executable scope"

def receiveMany (state : State) (txs : List Transaction) : Except String State :=
  txs.foldlM receive state

def merge (left right : State) : Except String State := do
  let metadata ← right.metadata.archive.foldlM receiveMetadata left.metadata
  let core ← NotionCoreRuntimeState.merge left.core right.core
  return ⟨core, metadata⟩

def gap (state : State) (ticks : Nat) : State :=
  {state with metadata := NotionCoreRuntimeMetadata.gap state.metadata ticks}

end Sal.MRDTs.Instances.NotionCoreRuntimeEngine
