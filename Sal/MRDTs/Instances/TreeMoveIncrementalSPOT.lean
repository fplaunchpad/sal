import Sal.MRDTs.Instances.TreeMoveIncrementalCertificate
import Sal.MRDTs.Instances.TreeMoveIncrementalReadSide

/-! Hand-derived PASS+FAIL traces for actual source undo/insert/redo. In the
cycle trace, a later move first succeeds, but must become rejected after an
earlier concurrent move arrives. Both target parents already exist at issuance.
The metadata trace checks recomputation of oldParent, not just tree equality. -/
namespace Sal.MRDTs.Instances.TreeMove.Incremental.SPOT
open Sal.MRDTs.Foundation

def birth2 : Event := (1,0,⟨0,20,2⟩)
def birth3 : Event := (2,0,⟨0,30,3⟩)
def lower : Event := (3,0,⟨2,31,3⟩)
def higher : Event := (4,1,⟨3,21,2⟩)
def writeLower : Event := (3,0,⟨0,21,2⟩)
def writeHigher : Event := (4,1,⟨0,22,2⟩)

def tree2 : Tree := setParent emptyTree 2 0 20
def baseTree : Tree := setParent tree2 3 0 30
def lowerTree : Tree := setParent baseTree 3 2 31
def higherTree : Tree := setParent baseTree 2 3 21
def writtenTree : Tree := setParent baseTree 2 0 22

private theorem tree2_safe : TreeSafe tree2 := by
  apply safe_of_rank tree2 id
  rintro a b ⟨v,h⟩
  simp only [tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all

private theorem base_safe : TreeSafe baseTree := by
  apply safe_of_rank baseTree id
  rintro a b ⟨v,h⟩
  simp only [baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all

private theorem lower_safe : TreeSafe lowerTree := by
  apply safe_of_rank lowerTree id
  rintro a b ⟨v,h⟩
  simp only [lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all

private theorem higher_safe : TreeSafe higherTree := by
  apply safe_of_rank higherTree (fun n => if n = 2 then 4 else n)
  rintro a b ⟨v,h⟩
  simp only [higherTree,baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all

private theorem written_safe (v : Nat) : TreeSafe (setParent baseTree 2 0 v) := by
  apply safe_of_rank _ id
  rintro a b ⟨m,h⟩
  simp only [baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all

private theorem first_step : sourceMove emptyTree birth2.op = tree2 :=
  sourceMove_accepts emptyTree_safe tree2_safe
private theorem second_step : sourceMove tree2 birth3.op = baseTree :=
  sourceMove_accepts tree2_safe base_safe
private theorem lower_step : sourceMove baseTree lower.op = lowerTree :=
  sourceMove_accepts base_safe lower_safe
private theorem higher_step : sourceMove baseTree higher.op = higherTree :=
  sourceMove_accepts base_safe higher_safe

private theorem higher_rejected : sourceMove lowerTree higher.op = lowerTree := by
  apply sourceMove_rejects
  left
  exact .single ⟨31,by simp [lowerTree,setParent,higher,Op.op]⟩

private theorem no_trash_base : visibleTree baseTree = baseTree := by
  apply visible_no_trash
  · simp [baseTree,tree2,setParent,emptyTree,trash]
  · intro a v
    simp only [baseTree,tree2,setParent,Function.update_apply,emptyTree]
    split_ifs <;> simp [trash]

private theorem no_trash_lower : visibleTree lowerTree = lowerTree := by
  apply visible_no_trash
  · simp [lowerTree,baseTree,tree2,setParent,emptyTree,trash]
  · intro a v
    simp only [lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree]
    split_ifs <;> simp [trash]

noncomputable def seed : State := update (update (encode ∅) birth2) birth3
noncomputable def late : State := update (update seed higher) lower
noncomputable def chronological : State := update (update seed lower) higher
noncomputable def merged : State := merge seed (update seed lower) (update seed higher)

private theorem seed_raw : seed.val = build [birth3,birth2] := by
  simp only [seed,update_encode]
  change canonical {birth3,birth2} = _
  have order : descendingEvents {birth3,birth2} = [birth3,birth2] := by
    have timestamps : [birth3,birth2].Pairwise (fun a b => b.1 < a.1) := by decide
    have sorted : [birth3,birth2].Pairwise descending :=
      timestamps.imp (fun {_ _} h => eventLE_of_timestamp_lt h)
    exact (List.toFinset_sort (r := descending) (by decide : [birth3,birth2].Nodup)).2 sorted
  rw [canonical,order]

private theorem seed_tree : seed.val.tree = baseTree := by
  rw [seed_raw]
  change sourceMove (sourceMove emptyTree birth2.op) birth3.op = _
  rw [first_step,second_step]

theorem concurrent_moves_issuable :
    canIssue lower seed ∧ canIssue higher seed ∧
    ¬ canIssue (5,0,⟨0,99,root⟩) seed := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨?_,by decide,by decide⟩
    intro old member
    simp [seed] at member
    rcases member with rfl | rfl <;> decide
  · refine ⟨?_,by decide,by decide⟩
    intro old member
    simp [seed] at member
    rcases member with rfl | rfl <;> decide
  · simp [canIssue,sourceApplicable,Op.op]

private theorem late_raw : late.val = build [higher,lower,birth3,birth2] := by
  simp only [late,seed,update_encode]
  change canonical {lower,higher,birth3,birth2} = _
  have order : descendingEvents {lower,higher,birth3,birth2} =
      [higher,lower,birth3,birth2] := by
    have timestamps : [higher,lower,birth3,birth2].Pairwise (fun a b => b.1 < a.1) := by decide
    have sorted : [higher,lower,birth3,birth2].Pairwise descending :=
      timestamps.imp (fun {_ _} h => eventLE_of_timestamp_lt h)
    have sets : ({lower,higher,birth3,birth2} : Finset Event) =
        [higher,lower,birth3,birth2].toFinset := by ext e; simp; tauto
    rw [sets]
    exact (List.toFinset_sort (r := descending) (by decide : [higher,lower,birth3,birth2].Nodup)).2 sorted
  rw [canonical,order]

private theorem late_tree : late.val.tree = lowerTree := by
  rw [late_raw]
  change sourceMove (sourceMove (sourceMove (sourceMove emptyTree birth2.op) birth3.op)
    lower.op) higher.op = _
  rw [first_step,second_step,lower_step,higher_rejected]

theorem late_delivery_reclassifies_cycle :
    query late 2 = some (0,20) ∧ query late 3 = some (2,31) ∧
    query late 2 ≠ some (3,21) := by
  simp only [query,late_tree,no_trash_lower]
  simp [lowerTree,baseTree,tree2,setParent]

theorem late_delivery_requires_undo :
    query late 2 = some (0,20) ∧
    (sourceMove higherTree lower.op) 2 = some (3,21) ∧
    query late 2 ≠ (sourceMove higherTree lower.op) 2 := by
  have rejects : sourceMove higherTree lower.op = higherTree := by
    apply sourceMove_rejects
    left
    exact .single ⟨21,by simp [higherTree,setParent,lower,Op.op]⟩
  rw [rejects]
  refine ⟨late_delivery_reclassifies_cycle.1,?_,?_⟩
  · simp [higherTree,setParent]
  · rw [late_delivery_reclassifies_cycle.1]
    simp [higherTree,setParent]

theorem delivery_order_exact_state : late = chronological ∧ late ≠ seed := by
  constructor
  · apply decode_injective
    simp only [late,chronological,decode_update]
    exact Finset.insert_comm _ _ _
  · intro equal
    have answer := congrArg (fun s => query s 3) equal
    dsimp only at answer
    rw [late_delivery_reclassifies_cycle.2.1] at answer
    simp only [query,seed_tree,no_trash_base] at answer
    simp [baseTree,setParent] at answer

theorem concurrent_merge_preserves_both_operations :
    merged = chronological ∧
    merged ≠ update seed higher ∧ merged ≠ update seed lower := by
  refine ⟨?_,?_,?_⟩
  · apply decode_injective
    simp only [merged,chronological,decode_merge,decode_update]
    ext x; simp <;> tauto
  · intro equal
    have decoded := congrArg decode equal
    have member : lower ∈ decode merged := by simp [merged]
    rw [decoded] at member
    simp [seed,birth2,birth3,lower,higher] at member
  · intro equal
    have decoded := congrArg decode equal
    have member : higher ∈ decode merged := by simp [merged]
    rw [decoded] at member
    simp [seed,birth2,birth3,lower,higher] at member

theorem rejected_move_retained_in_log :
    (late.val.log.map LogEntry.event) = [higher,lower,birth3,birth2] ∧
    (late.val.log.map LogEntry.event) ≠ [lower,birth3,birth2] := by
  rw [late_raw,build_events]
  constructor
  · rfl
  · decide

noncomputable def lateWrites : State := update (update seed writeHigher) writeLower

private theorem writes_raw : lateWrites.val = build [writeHigher,writeLower,birth3,birth2] := by
  simp only [lateWrites,seed,update_encode]
  change canonical {writeLower,writeHigher,birth3,birth2} = _
  have order : descendingEvents {writeLower,writeHigher,birth3,birth2} =
      [writeHigher,writeLower,birth3,birth2] := by
    have timestamps : [writeHigher,writeLower,birth3,birth2].Pairwise (fun a b => b.1 < a.1) := by decide
    have sorted : [writeHigher,writeLower,birth3,birth2].Pairwise descending :=
      timestamps.imp (fun {_ _} h => eventLE_of_timestamp_lt h)
    have sets : ({writeLower,writeHigher,birth3,birth2} : Finset Event) =
        [writeHigher,writeLower,birth3,birth2].toFinset := by ext e; simp; tauto
    rw [sets]
    exact (List.toFinset_sort (r := descending) (by decide : [writeHigher,writeLower,birth3,birth2].Nodup)).2 sorted
  rw [canonical,order]

private theorem lower_write_step : sourceMove baseTree writeLower.op = setParent baseTree 2 0 21 :=
  sourceMove_accepts base_safe (written_safe 21)
theorem redo_recomputes_old_parent_metadata :
    (lateWrites.val.log.head?).map LogEntry.oldParent = some (some (0,21)) ∧
    (lateWrites.val.log.head?).map LogEntry.oldParent ≠ some (some (0,20)) := by
  rw [writes_raw]
  simp only [build,push,initial,List.head?_cons,Option.map_some]
  change some ((sourceMove (sourceMove (sourceMove emptyTree birth2.op) birth3.op)
    writeLower.op) 2) = some (some (0,21)) ∧
    some ((sourceMove (sourceMove (sourceMove emptyTree birth2.op) birth3.op)
    writeLower.op) 2) ≠ some (some (0,20))
  rw [first_step,second_step,lower_write_step]
  simp [writeHigher,Op.op,setParent]

theorem self_move_is_rejected :
    sourceMove baseTree ⟨2,99,2⟩ = baseTree ∧
    sourceMove baseTree ⟨2,99,2⟩ ≠ setParent baseTree 2 2 99 := by
  have rejected : sourceMove baseTree ⟨2,99,2⟩ = baseTree :=
    sourceMove_rejects (Or.inr rfl)
  refine ⟨rejected,?_⟩
  rw [rejected]
  intro equal
  have at2 := congrFun equal 2
  simp [baseTree,tree2,setParent] at at2

def deletion : Event := (4,0,⟨trash,22,2⟩)
def rescue : Event := (5,1,⟨root,32,3⟩)
def restoration : Event := (6,0,⟨root,23,2⟩)
def deletedTree : Tree := setParent lowerTree 2 trash 22
def rescuedTree : Tree := setParent deletedTree 3 root 32
def restoredTree : Tree := setParent deletedTree 2 root 23
noncomputable def subtree : State := update seed lower
noncomputable def deleted : State := update subtree deletion
noncomputable def rescued : State := update deleted rescue
noncomputable def restored : State := update deleted restoration
noncomputable def deleteRescueMerge : State :=
  merge subtree (update subtree deletion) (update subtree rescue)

private theorem deleted_safe : TreeSafe deletedTree := by
  apply safe_of_rank deletedTree id
  rintro a b ⟨v,h⟩
  simp only [deletedTree,lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all [root,trash]

private theorem rescued_safe : TreeSafe rescuedTree := by
  apply safe_of_rank rescuedTree id
  rintro a b ⟨v,h⟩
  simp only [rescuedTree,deletedTree,lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all [root,trash]

private theorem restored_safe : TreeSafe restoredTree := by
  apply safe_of_rank restoredTree id
  rintro a b ⟨v,h⟩
  simp only [restoredTree,deletedTree,lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree] at h
  split_ifs at h <;> simp_all
  all_goals rcases h with ⟨rfl,rfl⟩ <;> simp_all [root,trash]

private theorem canonical_of_descending (ops : List Event) (unique : ops.Nodup)
    (timestamps : ops.Pairwise (fun a b => b.1 < a.1)) :
    canonical ops.toFinset = build ops := by
  unfold canonical descendingEvents
  rw [(List.toFinset_sort (r := descending) unique).2
    (timestamps.imp (fun {_ _} h => eventLE_of_timestamp_lt h))]

private theorem deleted_tree : deleted.val.tree = deletedTree := by
  have state : deleted = encode [deletion,lower,birth3,birth2].toFinset := by
    simp [deleted,subtree,seed]
  rw [state]
  change (canonical [deletion,lower,birth3,birth2].toFinset).tree = _
  rw [canonical_of_descending _ (by decide) (by decide)]
  change sourceMove (sourceMove (sourceMove (sourceMove emptyTree birth2.op) birth3.op)
    lower.op) deletion.op = _
  rw [first_step,second_step,lower_step]
  exact sourceMove_accepts lower_safe deleted_safe

private theorem rescued_tree : rescued.val.tree = rescuedTree := by
  have state : rescued = encode [rescue,deletion,lower,birth3,birth2].toFinset := by
    simp [rescued,deleted,subtree,seed]
  rw [state]
  change (canonical [rescue,deletion,lower,birth3,birth2].toFinset).tree = _
  rw [canonical_of_descending _ (by decide) (by decide)]
  change sourceMove (sourceMove (sourceMove (sourceMove (sourceMove emptyTree birth2.op)
    birth3.op) lower.op) deletion.op) rescue.op = _
  rw [first_step,second_step,lower_step,
    sourceMove_accepts (m := deletion.op) lower_safe deleted_safe]
  exact sourceMove_accepts deleted_safe rescued_safe

private theorem restored_tree : restored.val.tree = restoredTree := by
  have state : restored = encode [restoration,deletion,lower,birth3,birth2].toFinset := by
    simp [restored,deleted,subtree,seed]
  rw [state]
  change (canonical [restoration,deletion,lower,birth3,birth2].toFinset).tree = _
  rw [canonical_of_descending _ (by decide) (by decide)]
  change sourceMove (sourceMove (sourceMove (sourceMove (sourceMove emptyTree birth2.op)
    birth3.op) lower.op) deletion.op) restoration.op = _
  rw [first_step,second_step,lower_step,
    sourceMove_accepts (m := deletion.op) lower_safe deleted_safe]
  exact sourceMove_accepts deleted_safe restored_safe

theorem delete_and_hidden_moves_issuable :
    canIssue deletion subtree ∧ canIssue rescue deleted ∧ canIssue restoration deleted ∧
    ¬ canIssue (7,0,⟨root,99,trash⟩) deleted := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨?_,by decide,by decide⟩
    intro old member
    simp [subtree,seed] at member
    rcases member with rfl | rfl | rfl <;> decide
  · refine ⟨?_,by decide,by decide⟩
    intro old member
    simp [deleted,subtree,seed] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · refine ⟨?_,by decide,by decide⟩
    intro old member
    simp [deleted,subtree,seed] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · simp [canIssue,sourceApplicable,Op.op]

theorem forest_destination_issuable :
    canIssue (7,0,⟨99,40,4⟩) deleted ∧
    canIssue (7,0,⟨2,40,4⟩) deleted ∧
    ¬ canIssue (7,0,⟨99,40,root⟩) deleted := by
  have fresh : ∀ old ∈ decode deleted, (old.1,old.2.1) ≠ (7,0) := by
    intro old member
    simp [deleted,subtree,seed] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  exact ⟨⟨fresh,by decide,by decide⟩,⟨fresh,by decide,by decide⟩,
    by simp [canIssue,sourceApplicable,Op.op]⟩

theorem source_language_admits_deletion_and_restoration :
    sequentialSpec.Legal [birth2,birth3,lower,deletion,restoration] ∧
    ¬ sequentialSpec.Legal [birth2,(7,0,⟨root,99,trash⟩)] := by
  change SourceClientLegal _ ∧ ¬ SourceClientLegal _
  rw [sourceClientLegal_iff,sourceClientLegal_iff]
  constructor
  · refine ⟨⟨by decide,?_⟩,?_⟩
    · have times : [birth2,birth3,lower,deletion,restoration].Pairwise
          (fun a b => a.1 < b.1) := by decide
      exact times.imp (fun {_ _} h => eventLE_of_timestamp_lt h)
    · simp [birth2,birth3,lower,deletion,restoration,Op.op,root,trash]
  · simp [Op.op]

theorem deletion_hides_subtree_but_retains_descendants :
    query deleted 2 = none ∧ query deleted 3 = none ∧
    deleted.val.tree 3 = some (2,31) ∧ deleted.val.tree 3 ≠ none := by
  have hidden2 : underTrash deletedTree 2 := by
    right
    exact .single ⟨22,by simp [deletedTree,setParent]⟩
  have hidden3 : underTrash deletedTree 3 := by
    right
    have first : Relation.TransGen (edge deletedTree) 3 2 :=
      .single ⟨31,by simp [deletedTree,lowerTree,setParent]⟩
    exact first.tail ⟨22,by simp [deletedTree,setParent]⟩
  change visibleTree deleted.val.tree 2 = none ∧ visibleTree deleted.val.tree 3 = none ∧
    deleted.val.tree 3 = some (2,31) ∧ deleted.val.tree 3 ≠ none
  rw [deleted_tree]
  simp only [visibleTree,if_pos hidden2,if_pos hidden3]
  simp [deletedTree,lowerTree,setParent]

theorem hidden_descendant_can_be_rescued :
    query rescued 3 = some (root,32) ∧ query rescued 2 = none ∧
    query rescued 3 ≠ none := by
  have visible : visibleTree rescuedTree 3 = some (root,32) :=
    visible_at_root (by decide) (by simp [rescuedTree,setParent])
      (by simp [rescuedTree,deletedTree,lowerTree,baseTree,tree2,setParent,emptyTree,root])
  have hidden : underTrash rescuedTree 2 := by
    right
    exact .single ⟨22,by simp [rescuedTree,deletedTree,setParent]⟩
  simp only [query,rescued_tree,visible]
  simp [visibleTree,hidden]

theorem restoring_parent_restores_retained_subtree :
    query restored 2 = some (root,23) ∧ query restored 3 = some (2,31) ∧
    query restored 3 ≠ none := by
  have visible : visibleTree restoredTree = restoredTree := by
    apply visible_no_trash
    · simp [restoredTree,deletedTree,lowerTree,baseTree,tree2,setParent,emptyTree,trash]
    · intro a v
      simp only [restoredTree,deletedTree,lowerTree,baseTree,tree2,setParent,Function.update_apply,emptyTree]
      split_ifs <;> simp [root,trash]
  simp only [query,restored_tree,visible]
  simp [restoredTree,deletedTree,lowerTree,setParent]

theorem concurrent_delete_rescue_preserves_rescue :
    deleteRescueMerge = rescued ∧
    merge subtree (update subtree rescue) (update subtree deletion) = rescued ∧
    query deleteRescueMerge 3 = some (root,32) ∧
    deleteRescueMerge ≠ deleted := by
  have equal : deleteRescueMerge = rescued := by
    apply decode_injective
    simp only [deleteRescueMerge,rescued,deleted,decode_merge,decode_update]
    ext x; simp <;> tauto
  refine ⟨equal,?_,by rw [equal]; exact hidden_descendant_can_be_rescued.1,?_⟩
  · apply decode_injective
    simp only [rescued,deleted,decode_merge,decode_update]
    ext x; simp <;> tauto
  · intro degenerate
    have at3 := congrArg (fun s => query s 3) degenerate
    change query deleteRescueMerge 3 = query deleted 3 at at3
    rw [equal,hidden_descendant_can_be_rescued.1,
      deletion_hides_subtree_but_retains_descendants.2.1] at at3
    cases at3

end Sal.MRDTs.Instances.TreeMove.Incremental.SPOT
