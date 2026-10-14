import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreMachineTables

/-! Fresh actual create preserves the all-owned-reference physical partition.
Freshness is explicit here; derivation from canonical creator provenance is
separate. Empty title cells are retained, not discarded as invisible. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePartitionCreate
open NotionCoreMachine
open NotionCoreMachinePartition
open NotionCoreForestRefs (ownedRefs)
open NotionCoreSliceForest (titleRef freshTitle)
open NotionCorePartition (Cell flatten)
open NotionCorePayload (BlockKey)

theorem create_preserves_partitioned (state result : State) (block : BlockKey)
    (afterBlock : Option BlockKey) (prior : Partitioned state)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName block)
    (accepted : applyOperation state (.create block afterBlock) = some result) : Partitioned result := by
  let bid := blockName block
  have absentInstance : state.instances.any (fun entry => entry.1 == bid) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨entry,member,equal⟩ := List.any_eq_true.mp found
    exact freshInstance entry member (by simpa using equal)
  have absentBlock : state.forest.any (fun old => old.id == bid) = false := by
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨old,member,equal⟩ := List.any_eq_true.mp found
    exact freshBlock old member (by simpa using equal)
  have same : result = {instances := state.instances ++ [(bid,{})], forest := state.forest ++ [⟨bid,freshTitle bid⟩], display := NotionCoreDisplayOrder.insert (state.display.filter (· != bid)) bid (afterBlock.map blockName)} := by
    simpa [applyOperation, bid, absentInstance, absentBlock, putInstance] using accepted.symm
  subst result
  let next : State := {instances := state.instances ++ [(bid,{})], forest := state.forest ++ [⟨bid,freshTitle bid⟩], display := NotionCoreDisplayOrder.insert (state.display.filter (· != bid)) bid (afterBlock.map blockName)}
  change Partitioned next
  have references : ownedRefs next.forest = ownedRefs state.forest ++ [(bid,titleRef bid)] :=
    NotionCoreForestRefs.ownedRefs_create state.forest bid
  have getNext (inst : Nat) : getInstance next inst =
      if inst = bid then {} else getInstance state inst := by
    have stored : next.instances = (putInstance state bid {}).instances := by
      simp [next,putInstance,absentInstance]
    calc
      getInstance next inst = getInstance (putInstance state bid {}) inst := by
        unfold getInstance
        rw [stored]
      _ = _ := NotionCoreMachineTables.getInstance_put state bid inst {}

  have physicalNext (inst : Nat) : physical next inst =
      if inst = bid then NotionCoreSliceForest.emptyPhysical bid else physical state inst := by
    by_cases selected : inst = bid
    · subst inst
      simp [physical,getNext,NotionCoreMachine.traversal,NotionCorePhysicalReplay.physical,
        NotionCorePhysicalReplay.start,NotionCoreSliceForest.emptyPhysical]
    · simp [physical,getNext,selected]
  have oldNotFresh : ∀ owned ∈ ownedRefs state.forest, owned.2.start.1 ≠ bid := by
    intro owned member same
    obtain ⟨entry,present,instanceEq⟩ := prior.refsExist owned member
    exact freshInstance entry present (instanceEq.trans same)
  constructor
  · intro owned member
    rw [references] at member
    rcases List.mem_append.mp member with old | newest
    · obtain ⟨entry,present,equal⟩ := prior.refsExist owned old
      exact ⟨entry,List.mem_append_left _ present,equal⟩
    · have equal := List.mem_singleton.mp newest
      subst owned
      exact ⟨(bid,{}),by simp [next],rfl⟩
  · intro inst existsInstance
    obtain ⟨entry,present,equal⟩ := existsInstance
    change entry ∈ state.instances ++ [(bid,({} : Instance))] at present
    by_cases selected : inst = bid
    · clear equal
      subst inst
      refine ⟨[NotionCorePartition.initialCell bid bid],?_,by simp,?_⟩
      · simp [physicalNext,flatten,NotionCorePartition.Cell.physical,
          NotionCorePartition.initialCell,NotionCoreSliceForest.emptyPhysical]
      · have oldFilter : (ownedRefs state.forest).filter (fun owned => owned.2.start.1 == bid) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro owned member
          simp [oldNotFresh owned member]
        simp [references,List.filter_append,oldFilter,cellRefs,NotionCorePartition.initialCell,titleRef]
    · have oldExists : ∃ old ∈ state.instances, old.1 = inst := by
        rcases List.mem_append.mp present with old | new
        · exact ⟨entry,old,equal⟩
        · have pair := Prod.mk.inj (List.mem_singleton.mp new)
          exact False.elim (selected (equal.symm.trans pair.1))
      obtain ⟨cells,physicalEq,owners,permutation⟩ := prior.partitions inst oldExists
      refine ⟨cells,?_,owners,?_⟩
      · simpa [physicalNext,selected] using physicalEq
      · simpa [references,List.filter_append,titleRef,Ne.symm selected] using permutation

/-- Fresh create has actual executable success, not an assumed next-step
acceptance guard. Fresh instance/block names are the remaining explicit inputs. -/
theorem create_partitioned (state : State) (block : BlockKey) (afterBlock : Option BlockKey)
    (prior : Partitioned state)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ blockName block)
    (freshBlock : ∀ old ∈ state.forest, old.id ≠ blockName block) :
    ∃ result, applyOperation state (.create block afterBlock) = some result ∧ Partitioned result := by
  have total : ∃ result, applyOperation state (.create block afterBlock) = some result := by
    simp only [applyOperation]
    split <;> exact ⟨_,rfl⟩
  obtain ⟨result,accepted⟩ := total
  exact ⟨result,accepted,create_preserves_partitioned state result block afterBlock prior
    freshInstance freshBlock accepted⟩

private def emptyTitleState : State :=
  {instances := [(0,{})],forest := [⟨0,freshTitle 0⟩],display := [0]}

/-- Empty physical intervals still require their owned title reference. -/
theorem empty_title_control : Partitioned emptyTitleState ∧
    ownedRefs emptyTitleState.forest = [(0,titleRef 0)] ∧
    ownedRefs emptyTitleState.forest ≠ [] := by
  refine ⟨?_,by decide +kernel,by decide +kernel⟩
  exact create_preserves_partitioned {} emptyTitleState .initial none initial_partitioned
    (by simp) (by simp) (by rfl)

/-- Removing the empty title violates the actual partition invariant, even
though it changes no visible text. This is a structural read-side falsifier. -/
theorem missing_empty_title_invalid :
    ¬ Partitioned ({instances := [(0,{})],forest := [],display := [0]} : State) := by
  intro claimed
  obtain ⟨cells,physicalEq,_,permutation⟩ := claimed.partitions 0
    ⟨(0,{}),by simp,rfl⟩
  simp only [ownedRefs,List.flatMap_nil,List.filter_nil] at permutation
  have noRefs := List.Perm.nil_eq permutation
  cases cells with
  | nil => simp [physical,getInstance,traversal,NotionCorePhysicalReplay.physical,flatten] at physicalEq
  | cons cell rest => simp [cellRefs] at noRefs

#print axioms create_partitioned
#print axioms empty_title_control
#print axioms missing_empty_title_invalid
#print axioms create_preserves_partitioned
end Sal.MRDTs.Instances.NotionCoreMachinePartitionCreate
