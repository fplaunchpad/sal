import Sal.MRDTs.Paper1.RGA

/-!
# Investigated live-anchor alternative

This alternative strengthens the allocating list language: insertions require a
currently visible anchor. It preserves the current application-operation API and
still allocates globally fresh identifiers independently of event metadata.

The crossed-delete scenario exposes a continuation obstruction. Starting with
live identifiers 1 and 2, one replica deletes 1 then inserts after 2; another
deletes 2 then inserts after 1. Each local insertion has a live anchor, but no
physical-list continuation can preserve both deletion-before-insertion orders.
This is an obstruction at a fixed shared abstract state, not yet a theorem that
all operation-only witnesses from the empty initial state are impossible.
-/
namespace Sal.MRDTs.Paper1.RGA.Strict
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA

/-- An independent allocator registry reserves deleted identifiers permanently. -/
def machine : HistoryMachine RGAOp Unit (List ℕ) where
  State := List ℕ × List ℕ
  initial := ([], [])
  transition state label next := match label with
    | .update (.addAfter anchor) =>
        (anchor = 0 ∨ anchor ∈ state.1) ∧
        ∃ id, id ∉ state.2 ∧
          next = (insertAfter anchor id state.1, state.2 ++ [id])
    | .update (.remove id) => next = (state.1.filter (· ≠ id), state.2)
    | .query _ answer => next = state ∧ answer = state.1

def spec : HistorySpec RGAOp Unit (List ℕ) := machine.toSpec

inductive Event where
  | deleteOne | addAfterTwo | deleteTwo | addAfterOne
  deriving DecidableEq, Repr

namespace Event

def op : Event → RGAOp
  | .deleteOne => .remove 1
  | .addAfterTwo => .addAfter 2
  | .deleteTwo => .remove 2
  | .addAfterOne => .addAfter 1

end Event

/-- Forget every identifier except the two initially live, reserved anchors. -/
def anchors (xs : List ℕ) : Bool × Bool := (decide (1 ∈ xs), decide (2 ∈ xs))

def step (state : Bool × Bool) : Event → Option (Bool × Bool)
  | .deleteOne => some (false, state.2)
  | .addAfterTwo => if state.2 then some state else none
  | .deleteTwo => some (state.1, false)
  | .addAfterOne => if state.1 then some state else none

def replay : Bool × Bool → List Event → Option (Bool × Bool)
  | s, [] => some s
  | s, e :: rest => (step s e).bind (fun t => replay t rest)

def events : List Event := [.deleteOne, .addAfterTwo, .deleteTwo, .addAfterOne]

/-- The two visible local program orders of the crossed-delete experiment. -/
def preservesLocalOrder (ops : List Event) : Prop :=
  ops.idxOf .deleteOne < ops.idxOf .addAfterTwo ∧
  ops.idxOf .deleteTwo < ops.idxOf .addAfterOne

/-- Exhaustive, kernel-reduced test of all 24 suffix permutations. -/
theorem crossed_orders_stuck :
    ∀ ops ∈ events.permutations', preservesLocalOrder ops →
      replay (true, true) ops = none := by
  unfold preservesLocalOrder
  decide +kernel

private theorem mem_insertAfter_iff {x id anchor : ℕ} (hne : x ≠ id)
    (xs : List ℕ) : x ∈ insertAfter anchor id xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [insertAfter, hne]
  | cons a xs ih =>
      unfold insertAfter
      split
      · simp [hne]
      · split <;> simp [hne, ih]

/-- Fresh insertion cannot resurrect either reserved anchor. -/
private theorem fresh_anchors (s : List ℕ × List ℕ) (id anchor : ℕ)
    (h1 : 1 ∈ s.2) (h2 : 2 ∈ s.2) (fresh : id ∉ s.2) :
    anchors (insertAfter anchor id s.1) = anchors s.1 := by
  have hn1 : 1 ≠ id := by intro h; subst id; exact fresh h1
  have hn2 : 2 ≠ id := by intro h; subst id; exact fresh h2
  simp only [anchors, mem_insertAfter_iff hn1, mem_insertAfter_iff hn2]

private theorem step_refines {s t : List ℕ × List ℕ} {e : Event}
    (h1 : 1 ∈ s.2) (h2 : 2 ∈ s.2)
    (h : machine.transition s (.update e.op) t) :
    step (anchors s.1) e = some (anchors t.1) ∧
      1 ∈ t.2 ∧ 2 ∈ t.2 := by
  cases e with
  | deleteOne =>
      change t = (s.1.filter (· ≠ 1), s.2) at h
      subst t
      simp [step, anchors, List.mem_filter, h1, h2]
  | deleteTwo =>
      change t = (s.1.filter (· ≠ 2), s.2) at h
      subst t
      simp [step, anchors, List.mem_filter, h1, h2]
  | addAfterOne =>
      obtain ⟨guard, id, fresh, rfl⟩ := h
      have live : 1 ∈ s.1 := by simpa using guard
      rw [fresh_anchors s id 1 h1 h2 fresh]
      simp [step, anchors, live, h1, h2]
  | addAfterTwo =>
      obtain ⟨guard, id, fresh, rfl⟩ := h
      have live : 2 ∈ s.1 := by simpa using guard
      rw [fresh_anchors s id 2 h1 h2 fresh]
      simp [step, anchors, live, h1, h2]

/-- Every strict-list suffix run is accepted by the finite live-anchor model. -/
theorem runs_refine {s t : List ℕ × List ℕ} (ops : List Event)
    (h1 : 1 ∈ s.2) (h2 : 2 ∈ s.2)
    (run : Runs machine.transition s (ops.map (fun e => .update e.op)) t) :
    replay (anchors s.1) ops = some (anchors t.1) := by
  induction ops generalizing s with
  | nil => cases run; rfl
  | cons e rest ih =>
      cases run with
      | cons hstep hrest =>
          obtain ⟨hs, h1', h2'⟩ := step_refines h1 h2 hstep
          simp only [replay, hs, Option.bind_some]
          exact ih h1' h2' hrest

/-- No allocating-list suffix permutation preserves both local orders. The
argument covers every fresh allocation choice, not a bounded ID enumeration. -/
theorem crossed_no_continuation (ops : List Event)
    (hperm : ops ∈ events.permutations') (horder : preservesLocalOrder ops) :
    ¬ ∃ final, Runs machine.transition ([2, 1], [1, 2])
      (ops.map (fun e => .update e.op)) final := by
  rintro ⟨final, run⟩
  have hr := runs_refine ops (by simp) (by simp) run
  have hc := crossed_orders_stuck ops hperm horder
  change replay (true, true) ops = some _ at hr
  rw [hc] at hr
  cases hr

/-- PASS+FAIL: insertions before the concurrent deletes produce a valid model
run; preserving the crossed local orders makes the model get stuck. -/
example : replay (true, true)
      [.addAfterOne, .addAfterTwo, .deleteOne, .deleteTwo] = some (false, false) ∧
    replay (true, true) events = none := by decide

namespace Trace

def rootOne : Op RGAOp := (1, 0, .addAfter 0)
def rootTwo : Op RGAOp := (2, 0, .addAfter 0)
def deleteOne : Op RGAOp := (3, 0, .remove 1)
def afterTwo : Op RGAOp := (4, 0, .addAfter 2)
def deleteTwo : Op RGAOp := (5, 1, .remove 2)
def afterOne : Op RGAOp := (6, 1, .addAfter 1)
def genesis : List (Op RGAOp) := [rootOne, rootTwo]
def all : List (Op RGAOp) := genesis ++ [deleteOne, afterTwo, deleteTwo, afterOne]

noncomputable def shared : RGAM.State := applySeq RGAM.toUpdateSig RGAM.init genesis

noncomputable def left : RGAM.State := RGAM.update (RGAM.update shared deleteOne) afterTwo
noncomputable def right : RGAM.State := RGAM.update (RGAM.update shared deleteTwo) afterOne

/-- Both crossed local insertions are honestly issuable after their local
other-anchor deletion. Distinct replica IDs identify the two branches. -/
theorem local_issuance :
    applicable deleteOne shared ∧
    applicable afterTwo (RGAM.update shared deleteOne) ∧
    applicable deleteTwo shared ∧
    applicable afterOne (RGAM.update shared deleteTwo) := by
  simp [applicable, shared, genesis, rootOne, rootTwo, deleteOne, afterTwo,
    deleteTwo, afterOne, applySeq, RGAM, rgaUpdate]

/-- The grow-only merge retains both child births and both parent deletions. -/
theorem merged_effects :
    let merged := RGAM.merge shared left right
    merged.1 (4, 2) = true ∧ merged.1 (6, 1) = true ∧
      merged.2 1 = true ∧ merged.2 2 = true ∧
      merged.2 4 = false ∧ merged.2 6 = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- PASS+FAIL: each branch may insert at its surviving anchor, while inserting
at its locally deleted anchor is rejected by the existing issuance policy. -/
example : applicable afterTwo (RGAM.update shared deleteOne) ∧
    ¬ applicable (4, 0, .addAfter 1) (RGAM.update shared deleteOne) := by
  constructor
  · exact local_issuance.2.1
  · simp [applicable, shared, genesis, rootOne, rootTwo, deleteOne,
      applySeq, RGAM, rgaUpdate]

/-- The empty-order criterion can place both insertions before both deletes.
This valid run returns the two children and physically removes the parents. -/
theorem unconstrained_suffix :
    Runs machine.transition ([2, 1], [1, 2])
      [.update (.addAfter 2), .update (.addAfter 1),
       .update (.remove 1), .update (.remove 2)]
      ([4, 6], [1, 2, 4, 6]) := by
  refine .cons (m := ([2, 4, 1], [1, 2, 4])) ?_ ?_
  · exact ⟨Or.inr (by decide), 4, by decide, rfl⟩
  refine .cons (m := ([2, 4, 1, 6], [1, 2, 4, 6])) ?_ ?_
  · exact ⟨Or.inr (by decide), 6, by decide, rfl⟩
  exact .cons (m := ([2, 4, 6], [1, 2, 4, 6])) rfl
    (.cons rfl (.nil _))

private theorem trace_wellFormed : VersionWellFormed {e | e ∈ all} := by
  constructor
  · intro a b ha hb ht
    simp only [Set.mem_setOf_eq, all, genesis, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
      rcases hb with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
      simp_all [rootOne, rootTwo, deleteOne, afterTwo, deleteTwo, afterOne]
  · intro ts r anchor he
    simp [all, genesis, rootOne, rootTwo, deleteOne, afterTwo,
      deleteTwo, afterOne] at he
    rcases he with h | h | h | h
    · exact Or.inl h.2.2
    · exact Or.inl h.2.2
    · right
      refine ⟨0, 0, ?_, ?_⟩ <;>
        simp_all [all, genesis, rootOne, rootTwo, deleteOne, afterTwo,
          deleteTwo, afterOne]
    · right
      refine ⟨0, 0, ?_, ?_⟩ <;>
        simp_all [all, genesis, rootOne, rootTwo, deleteOne, afterTwo,
          deleteTwo, afterOne]
  · intro ts r id he
    simp [all, genesis, rootOne, rootTwo, deleteOne, afterTwo,
      deleteTwo, afterOne] at he
    rcases he with h | h
    all_goals
      refine ⟨0, 0, ?_⟩
      simp_all [all, genesis, rootOne, rootTwo, deleteOne, afterTwo,
        deleteTwo, afterOne]

theorem merged_read : read (RGAM.merge shared left right) = [4, 6] := by
  have hmerge : RGAM.merge shared left right =
      applySeq RGAM.toUpdateSig RGAM.init all := by
    apply Prod.ext
    · funext p
      simp [shared, left, right, all, genesis, rootOne, rootTwo,
        deleteOne, afterTwo, deleteTwo, afterOne, applySeq, RGAM, rgaUpdate,
        Bool.or_assoc, Bool.or_left_comm]
    · funext p
      simp [shared, left, right, all, genesis, rootOne, rootTwo,
        deleteOne, afterTwo, deleteTwo, afterOne, applySeq, RGAM, rgaUpdate,
        Bool.or_assoc, Bool.or_left_comm]
  let ordered : List (Op RGAOp) :=
    [rootOne, rootTwo, afterTwo, afterOne, deleteOne, deleteTwo]
  have hp : all.Perm ordered := by decide
  have hperm : listPermOf ordered {e | e ∈ all} :=
    ⟨by decide, fun _ => hp.mem_iff.symm⟩
  have hsorted : canonical ordered = ordered :=
    List.mergeSort_of_pairwise (by decide)
  have href := canonical_refines_list hperm trace_wellFormed
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ordered)) =
    listSpec.run (canonical ordered) at href
  rw [hsorted] at href
  have hfold := applySeq_perm_of_all_comm (D' := RGAM.toUpdateSig)
    RGAM_all_comm hp RGAM.init
  rw [← hfold] at href
  rw [hmerge, href]
  rfl

/-- PASS+FAIL: merge displays the children, not the deleted roots or an empty
list; the strict physical-list witness loses both local program orders. -/
example : read (RGAM.merge shared left right) = [4, 6] ∧
    read (RGAM.merge shared left right) ≠ [] ∧
    ¬ preservesLocalOrder [.addAfterTwo, .addAfterOne, .deleteOne, .deleteTwo] := by
  rw [merged_read]
  unfold preservesLocalOrder
  decide

end Trace

#print axioms crossed_orders_stuck
#print axioms crossed_no_continuation
end Sal.MRDTs.Paper1.RGA.Strict
