import Mathlib.Data.List.Flatten
import Sal.MRDTs.Instances.NotionCoreReconstruction
import Sal.MRDTs.Instances.NotionCoreMachinePrefix

/-! Canonical chronological prefixes and archive-ordered birth tables are
coupled by derived permutations, using actual transaction-key uniqueness.
Neither a row permutation nor birth uniqueness is supplied as a premise. -/
namespace Sal.MRDTs.Instances.NotionCoreArchiveOrder
open NotionRunAllocation (Run Session)
open NotionCorePayload
open NotionCorePayloadNetwork (State Entry Reach forget)
open NotionCoreReconstruction

 theorem archive_keys_unique (network : State) (reachable : Reach network) :
    ((network.entries.map Entry.tx).map Transaction.id).Nodup := by
  have issued := NotionCorePayloadNetwork.forget_reachable reachable
  have unique := NotionRunAllocation.reachable_transaction_keys_unique
    (NotionCoreIssuance.allocation_reachable issued)
  rw [← NotionCoreIssuance.record_runs issued] at unique
  simpa [forget, Entry.record, record, reservation, List.map_map, Function.comp_def] using unique

theorem version_prefix_transactions_perm (network : State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction)
    (position : transactionsFor network version = pre ++ suffix) :
    pre.Perm ((network.entries.map Entry.tx).filter (fun tx => reservation tx ∈ pre.map reservation)) := by
  let archived := network.entries.map Entry.tx
  have unique : (archived.map Transaction.id).Nodup := archive_keys_unique network reachable
  have preArchived : ∀ tx ∈ pre, tx ∈ archived := by
    intro tx member
    have inReplay : tx ∈ transactionsFor network version := position ▸ List.mem_append_left suffix member
    obtain ⟨⟨entry,present,same⟩,_⟩ := (transactionsFor_membership network version tx).mp inReplay
    exact List.mem_map.mpr ⟨entry,present,same⟩
  have replayUnique : ((transactionsFor network version).map Transaction.id).Nodup := by
    have perm := (List.mergeSort_perm
      ((network.entries.map Entry.tx).filter (fun tx => reservation tx ∈ version))
      (fun a b => decide (Ascending a b))).map Transaction.id
    exact perm.nodup_iff.mpr ((List.filter_sublist).map Transaction.id |>.nodup unique)
  have preUnique : pre.Nodup := List.Nodup.of_map Transaction.id
    ((List.nodup_append.mp (by simpa only [position,List.map_append] using replayUnique)).1)
  have selectedUnique := (List.Nodup.of_map Transaction.id unique).filter
    (fun tx => decide (reservation tx ∈ pre.map reservation))
  apply (List.perm_ext_iff_of_nodup preUnique selectedUnique).mpr
  intro tx
  constructor
  · intro present
    exact List.mem_filter.mpr ⟨preArchived tx present, by simpa only [decide_eq_true_eq] using List.mem_map.mpr ⟨tx,present,rfl⟩⟩
  · intro selected
    obtain ⟨present,selected⟩ := List.mem_filter.mp selected
    have runMember : reservation tx ∈ pre.map reservation := by simpa using selected
    obtain ⟨previous,inPre,same⟩ := List.mem_map.mp runMember
    have idSame : previous.id = tx.id := congrArg Run.first same
    have equal := List.inj_on_of_nodup_map unique (preArchived previous inPre) present idSame
    exact equal ▸ inPre

theorem version_prefix_rows_perm (network : State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction)
    (position : transactionsFor network version = pre ++ suffix) (inst : BlockKey)
    (deleted : BlockKey → NotionRunAllocation.Id → Bool) :
    (pre.flatMap (fun tx => NotionCoreMachinePrefix.transactionRows tx inst deleted)).Perm
      (NotionCorePayloadParents.prefixRows network.entries (pre.map reservation) inst deleted) := by
  have perm := (version_prefix_transactions_perm network reachable version pre suffix position).flatMap_right
    (fun tx => NotionCoreMachinePrefix.transactionRows tx inst deleted)
  simpa only [NotionCorePayloadParents.prefixRows, NotionCoreMachinePrefix.transactionRows,
    List.filter_map, List.flatMap_map, Function.comp_def] using perm

/-- Canonical birth IDs are globally unique, even across different instances. -/
theorem version_prefix_birth_ids_unique (network : State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction)
    (position : transactionsFor network version = pre ++ suffix)
    (deleted : BlockKey → NotionRunAllocation.Id → Bool) :
    (pre.flatMap (fun tx => (births tx deleted).map birthId)).Nodup := by
  have perm := (version_prefix_transactions_perm network reachable version pre suffix position).flatMap_right
    (fun tx => (births tx deleted).map birthId)
  have subset :
      (((network.entries.map Entry.tx).filter (fun tx => reservation tx ∈ pre.map reservation)).flatMap
        (fun tx => (births tx deleted).map birthId)).Sublist
      (NotionCoreReplayGraph.allIds network.entries deleted) := by
    simpa [NotionCoreReplayGraph.allIds, List.flatMap_map, Function.comp_def] using
      (List.filter_sublist (p := fun tx => decide (reservation tx ∈ pre.map reservation))
        (l := network.entries.map Entry.tx)).flatMap (fun tx => (births tx deleted).map birthId)
  exact perm.nodup_iff.mpr (subset.nodup (NotionCoreReplayGraph.all_births_unique reachable deleted))

theorem canonical_prefix_transactions_perm (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) :
    pre.Perm ((network.entries.map Entry.tx).filter (fun tx => reservation tx ∈ pre.map reservation)) :=
  version_prefix_transactions_perm network reachable _ pre suffix position

theorem canonical_prefix_rows_perm (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix) (inst : BlockKey)
    (deleted : BlockKey → NotionRunAllocation.Id → Bool) :
    (pre.flatMap (fun tx => NotionCoreMachinePrefix.transactionRows tx inst deleted)).Perm
      (NotionCorePayloadParents.prefixRows network.entries (pre.map reservation) inst deleted) :=
  version_prefix_rows_perm network reachable _ pre suffix position inst deleted

theorem canonical_prefix_birth_ids_unique (network : State) (reachable : Reach network)
    (peer : Session) (pre suffix : List Transaction)
    (position : transactions network peer = pre ++ suffix)
    (deleted : BlockKey → NotionRunAllocation.Id → Bool) :
    (pre.flatMap (fun tx => (births tx deleted).map birthId)).Nodup :=
  version_prefix_birth_ids_unique network reachable _ pre suffix position deleted

#print axioms version_prefix_transactions_perm
#print axioms version_prefix_rows_perm
#print axioms version_prefix_birth_ids_unique
#print axioms canonical_prefix_rows_perm
#print axioms canonical_prefix_birth_ids_unique
end Sal.MRDTs.Instances.NotionCoreArchiveOrder
