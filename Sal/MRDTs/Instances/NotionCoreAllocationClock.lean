import Sal.MRDTs.Instances.NotionCoreIssuance

/-! Allocator clocks at stable issuance boundaries are witnessed by received
transaction runs. Temporary clock gaps precede minting; the resulting run
records the advanced clock. This lets a carrier-based guard bound that clock. -/
namespace Sal.MRDTs.Instances.NotionCoreAllocationClock
open NotionRunAllocation

def Tight (peer : Peer) : Prop :=
  Bounded peer ∧ (peer.clock = 0 ∨ ∃ run ∈ peer.received, run.last = peer.clock)

theorem empty_tight : Tight emptyPeer := by
  simp [Tight, Bounded, emptyPeer]

theorem receive_tight {peer : Peer} (tight : Tight peer) (incoming : Run) :
    Tight (receive peer incoming) := by
  refine ⟨receive_bounded tight.1 incoming, ?_⟩
  by_cases incomingMax : peer.clock ≤ incoming.last
  · right
    exact ⟨incoming, by simp [receive], by simp [receive, max_eq_right incomingMax]⟩
  · have oldMax : incoming.last ≤ peer.clock := by omega
    rcases tight.2 with zero | ⟨run, member, attained⟩
    · left
      simpa [receive, max_eq_left oldMax] using zero
    · right
      exact ⟨run, by simp [receive, member], by simpa [receive, max_eq_left oldMax] using attained⟩

theorem counter_above_clock {peer : Peer} (tight : Tight peer) (counter : Nat)
    (positive : 0 < counter)
    (fresh : ∀ run ∈ peer.received, run.last < counter) : peer.clock < counter := by
  rcases tight.2 with zero | ⟨run, member, attained⟩
  · omega
  · rw [← attained]
    exact fresh run member

theorem advance_bounded {peer : Peer} (bounded : Bounded peer) (ticks : Nat) :
    Bounded (advance peer ticks) := by
  intro run member
  have bound := bounded run member
  change run.last ≤ peer.clock + ticks
  omega

/-- A successful full-run reservation makes its last ID witness the clock,
even when a gap was taken immediately before minting. -/
theorem mint_tight {peer : Peer} (bounded : Bounded peer)
    (session : Session) (width : Nat) (positive : 0 < width) :
    Tight (receive peer (reserve peer session width)) := by
  refine ⟨receive_bounded bounded _, Or.inr ?_⟩
  have newer : peer.clock ≤ (reserve peer session width).last := by
    simp only [reserve, Run.last]
    omega
  exact ⟨reserve peer session width, by simp [receive], by simp [receive, max_eq_right newer]⟩

theorem gap_mint_tight {peer : Peer} (bounded : Bounded peer)
    (ticks : Nat) (session : Session) (width : Nat) (positive : 0 < width) :
    Tight (receive (advance peer ticks) (reserve (advance peer ticks) session width)) :=
  mint_tight (advance_bounded bounded ticks) session width positive

theorem deliver_tight (network : Network) (tight : ∀ peer, Tight (network.peers peer))
    (target : Session) (run : Run) :
    ∀ peer, Tight ((deliver network target run).peers peer) := by
  intro peer
  by_cases same : peer = target
  · subst peer
    simpa [deliver] using receive_tight (tight target) run
  · simpa [deliver, same] using tight peer

theorem import_tight (network : Network) (tight : ∀ peer, Tight (network.peers peer))
    (target : Session) (runs : List Run) :
    ∀ peer, Tight ((NotionCoreIssuance.importRuns network target runs).peers peer) := by
  induction runs generalizing network with
  | nil => exact tight
  | cons run rest ih =>
    exact ih (deliver network target run) (deliver_tight network tight target run)

#print axioms counter_above_clock
#print axioms gap_mint_tight
#print axioms import_tight
end Sal.MRDTs.Instances.NotionCoreAllocationClock
