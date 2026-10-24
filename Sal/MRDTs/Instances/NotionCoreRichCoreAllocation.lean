import Sal.MRDTs.Instances.NotionCorePayloadNetwork

/-!
Filtering formatting reservations from the plain editing subsystem.

The rich allocator reserves distinct IDs for complete formatting batches.
The plain subsystem retains only edit reservations, while its clock still
observes every source counter. Whole-version exchange therefore projects to
plain exchange followed by an explicit clock advance. These are allocation
identities, not assumptions about document rendering or sequential histories.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichCoreAllocation
open NotionRunAllocation (Id Run Session Peer Network)

private theorem network_ext {left right : Network}
    (peers : left.peers = right.peers) (published : left.published = right.published) : left = right := by
  cases left
  cases right
  cases peers
  cases published
  rfl

def erasePeer (keep : Run → Bool) (peer : Peer) : Peer :=
  ⟨peer.clock,peer.received.filter keep⟩

def erase (keep : Run → Bool) (network : Network) : Network :=
  ⟨fun session => erasePeer keep (network.peers session),network.published.filter keep⟩

def importedClock (initial : Nat) : List Run → Nat
  | [] => initial
  | run :: rest => importedClock (max initial run.last) rest

theorem importedClock_ge (initial : Nat) (runs : List Run) :
    initial ≤ importedClock initial runs := by
  induction runs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons run rest ih => exact (Nat.le_max_left _ _).trans (ih _)

theorem importedClock_mono {left right : Nat} (before : left ≤ right) (runs : List Run) :
    importedClock left runs ≤ importedClock right runs := by
  induction runs generalizing left right with
  | nil => exact before
  | cons run rest ih => exact ih (by omega)

theorem importedClock_filter_le (keep : Run → Bool) (initial : Nat) (runs : List Run) :
    importedClock initial (runs.filter keep) ≤ importedClock initial runs := by
  induction runs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons run rest ih =>
    by_cases kept : keep run = true
    · simpa [importedClock,List.filter_cons,kept] using ih (max initial run.last)
    · have bound := importedClock_mono (Nat.le_max_left initial run.last) rest
      have filtered := (ih initial).trans bound
      simpa [List.filter_cons,kept,importedClock] using filtered

theorem import_peer (network : Network) (target : Session) (runs : List Run) (peer : Session) :
    (NotionCoreIssuance.importRuns network target runs).peers peer =
      if peer = target then
        ⟨importedClock (network.peers peer).clock runs,
          runs.reverse ++ (network.peers peer).received⟩
      else network.peers peer := by
  induction runs generalizing network with
  | nil => simp [NotionCoreIssuance.importRuns,importedClock]
  | cons run rest ih =>
    rw [NotionCoreIssuance.importRuns,ih]
    by_cases same : peer = target
    · subst peer
      simp [NotionRunAllocation.deliver,NotionRunAllocation.receive,importedClock,List.append_assoc]
    · simp [same,NotionRunAllocation.deliver]

/-- Clock-only advancement does not change which edit reservations were
received. This is how an atomic format's allocation is erased. -/
theorem erase_skip (keep : Run → Bool) (network : Network) (session : Session) (ticks : Nat) :
    erase keep (NotionRunAllocation.skip network session ticks) =
      NotionRunAllocation.skip (erase keep network) session ticks := by
  apply network_ext
  · funext peer
    by_cases same : peer = session
    · subst peer; simp [erase,erasePeer,NotionRunAllocation.skip,NotionRunAllocation.advance]
    · simp [erase,erasePeer,NotionRunAllocation.skip,same]
  · rfl

/-- Whole rich receipt projects to whole edit receipt plus the exact missing
clock information from omitted formatting reservations. -/
theorem erase_import (keep : Run → Bool) (network : Network) (target : Session) (runs : List Run) :
    erase keep (NotionCoreIssuance.importRuns network target runs) =
      NotionRunAllocation.skip
        (NotionCoreIssuance.importRuns (erase keep network) target (runs.filter keep)) target
        (importedClock (network.peers target).clock runs -
          importedClock (network.peers target).clock (runs.filter keep)) := by
  apply network_ext
  · funext peer
    by_cases same : peer = target
    · subst peer
      have bound := importedClock_filter_le keep (network.peers target).clock runs
      simp only [erase,erasePeer,NotionRunAllocation.skip,Function.update_self,import_peer,
        ↓reduceIte,NotionRunAllocation.advance,List.filter_append,List.filter_reverse]
      congr 1
      omega
    · simp [erase,erasePeer,NotionRunAllocation.skip,import_peer,same]
  · simp [erase,NotionRunAllocation.skip]

theorem erase_initial (keep : Run → Bool) : erase keep NotionRunAllocation.initial =
    NotionRunAllocation.initial := rfl

theorem erase_issue_kept (keep : Run → Bool) (network : Network) (session : Session) (width : Nat)
    (kept : keep (NotionRunAllocation.reserve (network.peers session) session width) = true) :
    erase keep (NotionRunAllocation.issue network session width) =
      NotionRunAllocation.issue (erase keep network) session width := by
  have name : keep ⟨⟨(network.peers session).clock + 1,session⟩,width⟩ = true := kept
  apply network_ext
  · funext peer
    by_cases same : peer = session
    · subst peer
      simp [erase,erasePeer,NotionRunAllocation.issue,NotionRunAllocation.reserve,
        NotionRunAllocation.receive,name]
    · simp [erase,erasePeer,NotionRunAllocation.issue,same]
  · simp [erase,erasePeer,NotionRunAllocation.issue,NotionRunAllocation.reserve,name]

/-- Omitting one format reservation still advances the local plain clock by
its entire positive width, so a later edit keeps its actual source ID. -/
theorem erase_issue_omitted (keep : Run → Bool) (network : Network) (session : Session) (width : Nat)
    (positive : 0 < width)
    (omitted : keep (NotionRunAllocation.reserve (network.peers session) session width) = false) :
    erase keep (NotionRunAllocation.issue network session width) =
      NotionRunAllocation.skip (erase keep network) session width := by
  have name : keep ⟨⟨(network.peers session).clock + 1,session⟩,width⟩ = false := omitted
  have last : (NotionRunAllocation.reserve (network.peers session) session width).last =
      (network.peers session).clock + width := by
    simp only [NotionRunAllocation.reserve,NotionRunAllocation.Run.last]
    omega
  apply network_ext
  · funext peer
    by_cases same : peer = session
    · subst peer
      simp only [erase,erasePeer,NotionRunAllocation.issue,NotionRunAllocation.skip,
        Function.update_self,NotionRunAllocation.receive,NotionRunAllocation.advance,last]
      simp only [NotionRunAllocation.reserve,List.filter_cons,name,Bool.false_eq_true,↓reduceIte]
      congr 1
      omega
    · simp [erase,erasePeer,NotionRunAllocation.issue,NotionRunAllocation.skip,same]
  · simp [erase,NotionRunAllocation.issue,NotionRunAllocation.skip,NotionRunAllocation.reserve,name]

#print axioms erase_import
#print axioms erase_issue_omitted

end Sal.MRDTs.Instances.NotionCoreRichCoreAllocation
