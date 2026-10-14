import Sal.MRDTs.Instances.NotionCorePayload

/-! Retained receipt/archive metadata for the executable boundary. Local clock
gaps are explicit; a remote peer's unpublished gap is not copied by merge.
This layer does not replace or relax the existing positional issuance guard. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeMetadata
open NotionCorePayload (Transaction reservation)
open NotionRunAllocation (Peer)

structure State where
  archive : List Transaction
  peer : Peer

def empty : State := ⟨[], NotionRunAllocation.emptyPeer⟩

def Valid (state : State) : Prop :=
  state.peer.received = state.archive.map reservation ∧ NotionRunAllocation.Bounded state.peer

def receive (state : State) (tx : Transaction) : State :=
  ⟨tx :: state.archive, NotionRunAllocation.receive state.peer (reservation tx)⟩

def gap (state : State) (ticks : Nat) : State :=
  {state with peer := NotionRunAllocation.advance state.peer ticks}

/-- Only received transaction reservations cross the merge boundary. -/
def merge (left right : State) : State := right.archive.foldl receive left

def nextCounter (state : State) : Nat := state.peer.clock + 1

theorem empty_valid : Valid empty := by
  constructor
  · rfl
  · intro run member; simp [empty,NotionRunAllocation.emptyPeer] at member

theorem receive_valid (state : State) (valid : Valid state) (tx : Transaction) :
    Valid (receive state tx) := by
  constructor
  · simp [receive,NotionRunAllocation.receive,valid.1]
  · exact NotionRunAllocation.receive_bounded valid.2 (reservation tx)

theorem gap_valid (state : State) (valid : Valid state) (ticks : Nat) :
    Valid (gap state ticks) := by
  refine ⟨valid.1,?_⟩
  intro run member
  have bounded := valid.2 run member
  change run.last ≤ state.peer.clock + ticks
  omega

theorem fold_valid (txs : List Transaction) (state : State) (valid : Valid state) :
    Valid (txs.foldl receive state) := by
  induction txs generalizing state with
  | nil => exact valid
  | cons tx txs ih => exact ih _ (receive_valid state valid tx)

theorem merge_valid (left right : State) (valid : Valid left) :
    Valid (merge left right) := fold_valid right.archive left valid

theorem receive_clock (state : State) (tx : Transaction) :
    (receive state tx).peer.clock = max state.peer.clock (NotionCorePayload.clockMax tx) := by
  simp [receive,NotionRunAllocation.receive,NotionCorePayload.clockMax_reservation]

theorem gap_archive (state : State) (ticks : Nat) :
    (gap state ticks).archive = state.archive := rfl

namespace SPOT
private def seed := NotionCorePayload.bootstrap [97,98]
private def retained := receive empty seed
/-- A remote unpublished gap is not a received reservation. A local gap changes
allocation despite an unchanged archive, rejecting a facts-derived clock. -/
theorem clock_boundary :
    nextCounter retained = 3 ∧ nextCounter (gap retained 6) = 9 ∧
    nextCounter (gap retained 6) ≠ nextCounter retained ∧
    nextCounter (merge empty (gap retained 6)) = 3 ∧
    nextCounter (merge empty (gap retained 6)) ≠ 9 := by
  decide +kernel
end SPOT

#print axioms receive_valid
#print axioms merge_valid
#print axioms SPOT.clock_boundary
end Sal.MRDTs.Instances.NotionCoreRuntimeMetadata
