import Sal.MRDTs.Instances.TreeMove
import Mathlib.Data.Finset.Sort

/-! Fig. 4 of Kleppmann et al.'s tree-move algorithm. The maintained log is
newest first and includes rejected moves. Each entry stores the old parent
and metadata; late delivery restores these values before insertion and redo.
The finite-event model is used only by the refinement proofs. -/
namespace Sal.MRDTs.Instances.TreeMove.Incremental
open Sal.MRDTs.Foundation
open Classical

/-- Source ancestor test, with edges directed from child to parent. -/
def Rejects (t : Tree) (m : Move) : Prop :=
  Relation.TransGen (edge t) m.parent m.child ∨ m.child = m.parent

noncomputable def sourceMove (t : Tree) (m : Move) : Tree :=
  if Rejects t m then t else setParent t m.child m.parent m.metadata

private theorem edge_setParent {t : Tree} {m : Move} {a b : Node} :
    edge (setParent t m.child m.parent m.metadata) a b →
      edge t a b ∨ (a = m.child ∧ b = m.parent) := by
  rintro ⟨v,h⟩
  by_cases same : a = m.child
  · subst a
    simp [setParent] at h
    exact Or.inr ⟨rfl,h.1.symm⟩
  · exact Or.inl ⟨v,by simpa [setParent,same] using h⟩

private theorem patched_path {β : Type} {R S : β → β → Prop} {c p a b : β}
    (edges : ∀ a b, S a b → R a b ∨ (a = c ∧ b = p))
    (noReturn : ¬ Relation.ReflTransGen R p c)
    (path : Relation.TransGen S a b) :
    Relation.TransGen R a b ∨
      (Relation.ReflTransGen R a c ∧ Relation.ReflTransGen R p b) := by
  induction path with
  | single e =>
    rcases edges _ _ e with old | ⟨rfl,rfl⟩
    · exact Or.inl (.single old)
    · exact Or.inr ⟨.refl,.refl⟩
  | @tail b d path e ih =>
    rcases edges _ _ e with old | ⟨rfl,rfl⟩
    · rcases ih with oldPath | ⟨left,right⟩
      · exact Or.inl (.tail oldPath old)
      · exact Or.inr ⟨left,.tail right old⟩
    · rcases ih with oldPath | ⟨left,right⟩
      · exact Or.inr ⟨oldPath.to_reflTransGen,.refl⟩
      · exact False.elim (noReturn right)

private theorem path_to_child_preserved {t : Tree} {m : Move} {a : Node}
    (safe : TreeSafe t) (path : Relation.TransGen (edge t) a m.child) :
    Relation.TransGen (edge (setParent t m.child m.parent m.metadata)) a m.child := by
  induction path using Relation.TransGen.head_induction_on with
  | @single a e =>
    have different : a ≠ m.child := by
      intro same; subst a; exact safe m.child (.single e)
    apply Relation.TransGen.single
    obtain ⟨v,h⟩ := e
    exact ⟨v,by simpa [setParent,different] using h⟩
  | @head a b e path ih =>
    have different : a ≠ m.child := by
      intro same; subst a; exact safe m.child (path.head e)
    apply ih.head
    obtain ⟨v,h⟩ := e
    exact ⟨v,by simpa [setParent,different] using h⟩

theorem candidate_safe_iff (t : Tree) (safe : TreeSafe t) (m : Move) :
    TreeSafe (setParent t m.child m.parent m.metadata) ↔ ¬ Rejects t m := by
  constructor
  · intro candidate rejected
    rcases rejected with path | same
    · apply candidate m.child
      exact (path_to_child_preserved safe path).head
        ⟨m.metadata,by simp [setParent]⟩
    · rw [same] at candidate
      exact selfMove_unsafe t m.parent m.metadata candidate
  · intro allowed node cycle
    have noReturn : ¬ Relation.ReflTransGen (edge t) m.parent m.child := by
      intro path
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with same | path
      · exact allowed (Or.inr same)
      · exact allowed (Or.inl path)
    rcases patched_path (fun _ _ => edge_setParent) noReturn cycle with old | ⟨left,right⟩
    · exact safe node old
    · exact noReturn (right.trans left)

theorem sourceMove_eq_doMove (t : Tree) (safe : TreeSafe t) (m : Move) :
    sourceMove t m = doMove t m := by
  dsimp only [sourceMove,doMove]
  rw [candidate_safe_iff t safe m]
  by_cases h : Rejects t m <;> simp [h]

structure LogEntry where
  event : Event
  oldParent : Option (Node × Metadata)
deriving DecidableEq, Repr

structure RawState where
  log : List LogEntry
  tree : Tree

noncomputable def initial : RawState := ⟨[],emptyTree⟩

/-- Fig. 4 do_op/redo_op: recompute oldParent even for an ignored move. -/
noncomputable def push (s : RawState) (e : Event) : RawState :=
  ⟨⟨e,s.tree e.op.child⟩ :: s.log,sourceMove s.tree e.op⟩

/-- Fig. 4 undo_op: restore the prior edge or remove the newly created one. -/
def undo (entry : LogEntry) (t : Tree) : Tree :=
  Function.update t entry.event.op.child entry.oldParent

theorem undo_push (s : RawState) (e : Event) :
    undo ⟨e,s.tree e.op.child⟩ (push s e).tree = s.tree := by
  funext n
  unfold undo push sourceMove
  by_cases reject : Rejects s.tree e.op <;> simp only [reject,ite_true,ite_false]
  · by_cases same : n = e.op.child <;> simp [same]
  · by_cases same : n = e.op.child <;> simp [setParent,same]

/-- Fig. 4 apply_op. Recursion consumes the descending log. Comparing the
full event key totalizes raw timestamp collisions; fresh supported timestamps
give exactly the source's timestamp comparison. -/
noncomputable def applyRaw (e : Event) : List LogEntry → Tree → RawState
  | [], t => push ⟨[],t⟩ e
  | entry :: rest, t =>
    if eventKey e < eventKey entry.event then
      push (applyRaw e rest (undo entry t)) entry.event
    else push ⟨entry :: rest,t⟩ e

/-- Mathematical normal form: replay oldest first while recording each undo
edge. No operational update or query calls this function. -/
noncomputable def build : List Event → RawState
  | [] => initial
  | e :: rest => push (build rest) e

theorem build_events (ops : List Event) : (build ops).log.map LogEntry.event = ops := by
  induction ops with
  | nil => rfl
  | cons e rest ih => simpa [build,push] using congrArg (List.cons e) ih

theorem build_tree (ops : List Event) : (build ops).tree = replayList ops.reverse := by
  induction ops with
  | nil => rfl
  | cons e rest ih =>
    change sourceMove (build rest).tree e.op = _
    rw [ih,sourceMove_eq_doMove _ (replayList_safe _) _]
    simp [List.reverse_cons,replayList,List.foldl_append,Op.op]

def descending (a b : Event) : Prop := eventLE b a
instance : DecidableRel descending := fun _ _ => inferInstanceAs (Decidable (eventLE _ _))
instance : IsTrans Event descending := ⟨fun _ _ _ h k => le_trans k h⟩
instance : Std.Antisymm descending := ⟨fun _ _ h k => eventKey_injective (le_antisymm k h)⟩
instance : Std.Total descending := ⟨fun a b => le_total (eventKey b) (eventKey a)⟩

def descendingEvents (E : Finset Event) : List Event := E.sort descending
noncomputable def canonical (E : Finset Event) : RawState := build (descendingEvents E)

theorem applyRaw_build (ops : List Event) (e : Event) :
    applyRaw e (build ops).log (build ops).tree =
      build (ops.orderedInsert descending e) := by
  induction ops with
  | nil => rfl
  | cons newest rest ih =>
    change (if eventKey e < eventKey newest then
        push (applyRaw e (build rest).log
          (undo ⟨newest,(build rest).tree newest.op.child⟩ (push (build rest) newest).tree)) newest
      else push (push (build rest) newest) e) = _
    rw [undo_push]
    by_cases earlier : eventKey e < eventKey newest
    · have notBefore : ¬ descending e newest := not_le_of_gt earlier
      simp [earlier,List.orderedInsert,notBefore,ih,build]
    · have before : descending e newest := le_of_not_gt earlier
      simp [earlier,List.orderedInsert,before,build]

theorem descending_insert (E : Finset Event) (e : Event) (fresh : e ∉ E) :
    descendingEvents (insert e E) = (descendingEvents E).orderedInsert descending e := by
  apply List.Perm.eq_of_pairwise' (r := descending)
  · exact Finset.pairwise_sort _ _
  · exact (Finset.pairwise_sort E descending).orderedInsert e _
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup _ _
    · apply (List.perm_orderedInsert (r := descending) e (descendingEvents E)).nodup_iff.mpr
      exact List.nodup_cons.mpr ⟨by simpa [descendingEvents] using fresh,Finset.sort_nodup _ _⟩
    · ext x; simp [descendingEvents,List.mem_orderedInsert]

def events (s : RawState) : Finset Event := (s.log.map LogEntry.event).toFinset

/-- Duplicate suppression belongs to the source delivery protocol. Merge
uses this wrapper to avoid reapplying shared operations. -/
noncomputable def receive (s : RawState) (e : Event) : RawState :=
  if e ∈ events s then s else applyRaw e s.log s.tree

theorem canonical_events (E : Finset Event) : events (canonical E) = E := by
  simp [events,canonical,build_events,descendingEvents]

theorem receive_canonical (E : Finset Event) (e : Event) :
    receive (canonical E) e = canonical (insert e E) := by
  unfold receive
  rw [canonical_events]
  by_cases fresh : e ∈ E
  · rw [if_pos fresh,Finset.insert_eq_of_mem fresh]
  · rw [if_neg fresh]
    unfold canonical
    rw [applyRaw_build,descending_insert E e fresh]

theorem descending_reverse (E : Finset Event) :
    (descendingEvents E).reverse = orderedEvents E := by
  apply List.Perm.eq_of_pairwise' (r := eventLE)
  · exact (Finset.pairwise_sort E descending).reverse
  · exact Finset.pairwise_sort _ _
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_reverse.mpr (Finset.sort_nodup E descending)
    · exact Finset.sort_nodup _ _
    · simp [descendingEvents,orderedEvents]

theorem canonical_tree (E : Finset Event) : (canonical E).tree = render E := by
  rw [canonical,build_tree,descending_reverse]
  rfl

end Sal.MRDTs.Instances.TreeMove.Incremental
