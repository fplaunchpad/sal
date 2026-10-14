import Sal.MRDTs.Paper1.FugueMaxOriginForest

/-! Lift an identity/origin forest schedule to a permutation of the original
source events. No generated replacement events enter the witness. -/
namespace Sal.MRDTs.Paper1.FugueMaxOriginEventWitness
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax

theorem lift_pairs {Event : Type} (id origin : Event → Nat) (parent : Nat → Nat)
    (events : List Event) (pairs : List (Nat × Nat))
    (ids : (pairs.map Prod.fst).Perm (events.map id))
    (pairShape : ∀ pair ∈ pairs, pair.2 = parent pair.1)
    (eventShape : ∀ event ∈ events, origin event = parent (id event)) :
    ∃ replay : List Event, replay.Perm events ∧ replay.map (fun event => (id event,origin event)) = pairs := by
  have lifted : Relation.Comp (fun xs ys => xs = ys.map id) List.Perm
      (pairs.map Prod.fst) events := by
    rw [List.eq_map_comp_perm]
    exact ids
  obtain ⟨replay,same,perm⟩ := lifted
  refine ⟨replay,perm,?_⟩
  calc
    replay.map (fun event => (id event,origin event)) =
        replay.map (fun event => (id event,parent (id event))) := by
      apply List.map_congr_left
      intro event member
      rw [eventShape event (perm.mem_iff.mp member)]
    _ = (replay.map id).map (fun id => (id,parent id)) := by simp only [List.map_map,Function.comp_def]
    _ = (pairs.map Prod.fst).map (fun id => (id,parent id)) := by rw [same]
    _ = pairs := by
      rw [List.map_map]
      calc
        _ = pairs.map (fun pair => pair) := by
          apply List.map_congr_left
          intro pair member
          exact Prod.ext rfl (pairShape pair member).symm
        _ = pairs := List.map_id' pairs

/-- KInv's unique source record lookup supplies the origin of each original
insertion. The resulting replay contains exactly those original insertions. -/
theorem source_insertion_permutation {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (events : List (Op Payload)) (inv : KInv Γ (events.map recordOf))
    (pairs : List (Nat × Nat))
    (ids : (pairs.map Prod.fst).Perm
      ((events.filter (fun e => mIsIns (recordOf e))).map Op.time))
    (pairShape : ∀ pair ∈ pairs, pair.2 = mLoOf (events.map recordOf) pair.1) :
    ∃ replay : List (Op Payload), replay.Perm (events.filter (fun e => mIsIns (recordOf e))) ∧
      replay.map (fun e => (e.time,(recordOf e).lo)) = pairs := by
  apply lift_pairs Op.time (fun e => (recordOf e).lo)
    (mLoOf (events.map recordOf)) _ pairs ids pairShape
  intro event member
  obtain ⟨member,inserted⟩ := List.mem_filter.mp member
  exact (mLoOf_eq (mRecOfId_of_mem inv
    (List.mem_map.mpr ⟨event,member,rfl⟩) inserted)).symm

theorem minted_ids_eq_event_times (events : List (Op Payload)) :
    mMintedIds (events.map recordOf) =
      (events.filter (fun e => mIsIns (recordOf e))).map Op.time := by
  simp only [mMintedIds,mMinted,List.filter_map,List.map_map]
  rfl

/-- A permanent source identity list enumerates precisely the original
insertion events. Source timestamp uniqueness is retained through KInv. -/
theorem source_ids_permutation {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (events : List (Op Payload)) (inv : KInv Γ (events.map recordOf))
    (uniqueEvents : events.Nodup) (ids : List Nat) (uniqueIds : ids.Nodup)
    (enumerates : ∀ id, id ∈ ids ↔ id ∈ mMintedIds (events.map recordOf)) :
    ids.Perm ((events.filter (fun e => mIsIns (recordOf e))).map Op.time) := by
  have timestampUnique :
      ((events.filter (fun e => mIsIns (recordOf e))).map Op.time).Nodup := by
    apply (uniqueEvents.filter _).map_on
    intro a ha b hb same
    obtain ⟨amember,ainserted⟩ := List.mem_filter.mp ha
    obtain ⟨bmember,binserted⟩ := List.mem_filter.mp hb
    have recordSame := inv.uniq (recordOf a) (List.mem_map.mpr ⟨a,amember,rfl⟩)
      (recordOf b) (List.mem_map.mpr ⟨b,bmember,rfl⟩) ainserted binserted same
    have originalSame := congrArg eventOf recordSame
    simpa only [eventOf_recordOf] using originalSame
  apply (List.perm_ext_iff_of_nodup uniqueIds timestampUnique).mpr
  intro id
  rw [← minted_ids_eq_event_times]
  exact enumerates id

#print axioms lift_pairs
#print axioms source_insertion_permutation
#print axioms source_ids_permutation
end Sal.MRDTs.Paper1.FugueMaxOriginEventWitness
