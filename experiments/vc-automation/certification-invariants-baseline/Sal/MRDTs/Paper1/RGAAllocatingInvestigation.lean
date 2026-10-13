import Mathlib.Data.List.Permutation
import Sal.MRDTs.Paper1.RGAConflict
import Sal.MRDTs.Paper1.RGAStrict

/-!
# Investigating the specification-visible allocating RGA criterion

Candidate: every honestly issued RGA execution has an operation-only witness
respecting independent specification conflicts. Falsifier: two crossed child
families with two insertions per family, whose merge displays four children.
The independent allocator may rename births, so excluding the original ID
choices alone is insufficient. The finite projection below classifies arbitrary
fresh choices as anchor 1, anchor 2, or another identifier; it does not bound the
allocator's identifier domain.
-/
namespace Sal.MRDTs.Paper1.RGA.AllocatingInvestigation
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA

/-- The original one-child crossed scenario escapes the fixed-prefix argument
through fresh relabeling and one missing-anchor no-op. -/
theorem single_cross_relabeling :
    listHistorySpec.admits
      [.update (.addAfter 0), .update (.addAfter 0), .update (.remove 2),
       .update (.addAfter 1), .update (.remove 1), .update (.addAfter 2),
       .query () [4, 6]] := by
  refine ⟨([4, 6], [1, 4, 6, 0]), .cons (m := ([1], [1])) ?_
    (.cons (m := ([4, 1], [1, 4])) ?_
      (.cons (m := ([4, 1], [1, 4])) rfl
        (.cons (m := ([4, 1, 6], [1, 4, 6])) ?_
          (.cons (m := ([4, 6], [1, 4, 6])) rfl
            (.cons (m := ([4, 6], [1, 4, 6, 0])) ?_
              (.cons ⟨rfl, rfl⟩ (.nil _)))))))⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨0, by decide, rfl⟩

/-- FAIL companion: the same history with the concrete insertion IDs loses
one child. The admitted operation-only history does not preserve birth IDs. -/
theorem concrete_ids_single_cross_differ :
    listSpec.run [Strict.Trace.rootOne, Strict.Trace.rootTwo,
      Strict.Trace.deleteTwo, Strict.Trace.afterOne,
      Strict.Trace.deleteOne, Strict.Trace.afterTwo] = [6] ∧
    listSpec.run [Strict.Trace.rootOne, Strict.Trace.rootTwo,
      Strict.Trace.deleteTwo, Strict.Trace.afterOne,
      Strict.Trace.deleteOne, Strict.Trace.afterTwo] ≠ [4, 6] := by
  change ([6] : List Nat) = [6] ∧ [6] ≠ [4, 6]
  decide

inductive Action where
  | root | deleteOne | afterTwo | deleteTwo | afterOne
  deriving DecidableEq, Repr

namespace Action

def op : Action → RGAOp
  | .root => .addAfter 0
  | .deleteOne => .remove 1
  | .afterTwo => .addAfter 2
  | .deleteTwo => .remove 2
  | .afterOne => .addAfter 1

end Action

@[ext] structure ProjectedState where
  liveOne : Bool
  liveTwo : Bool
  reservedOne : Bool
  reservedTwo : Bool
  otherCount : Nat
  deriving DecidableEq, Repr

def initial : ProjectedState := ⟨false, false, false, false, 0⟩

def validAnchor (s : ProjectedState) : Action → Bool
  | .root => true
  | .afterOne => s.liveOne
  | .afterTwo => s.liveTwo
  | _ => false

/-- Three equality classes exhaust the unbounded allocation domain. -/
def allocationNext (s : ProjectedState) (valid : Bool) : List ProjectedState :=
  (if s.reservedOne then [] else
    [{s with reservedOne := true, liveOne := s.liveOne || valid}]) ++
  (if s.reservedTwo then [] else
    [{s with reservedTwo := true, liveTwo := s.liveTwo || valid}]) ++
  [{s with otherCount := s.otherCount + if valid then 1 else 0}]

def nextStates (s : ProjectedState) (a : Action) : List ProjectedState :=
  match a with
  | .deleteOne => [{s with liveOne := false}]
  | .deleteTwo => [{s with liveTwo := false}]
  | _ => allocationNext s (validAnchor s a)

def outcomes : ProjectedState → List Action → List ProjectedState
  | s, [] => [s]
  | s, a :: rest => (nextStates s a).flatMap (fun t => outcomes t rest)

/-- Final four-child query: both named anchors are absent and four other
identifiers are displayed. Their identities and list order strengthen this. -/
def fourChildren (s : ProjectedState) : Bool :=
  !s.liveOne && !s.liveTwo && decide (s.otherCount = 4)

/-- Generate every multiset ordering satisfying the two crossed local orders.
Repeated root and sibling insertion labels are intentionally indistinguishable. -/
def permittedWords : Nat → Nat → Nat → Nat → Bool → Bool → List (List Action)
  | 0, _, _, _, _, _ => [[]]
  | fuel + 1, roots, ones, twos, delOne, delTwo =>
      (if roots = 0 then [] else
        (permittedWords fuel (roots - 1) ones twos delOne delTwo).map (.root :: ·)) ++
      (if delOne then
        (permittedWords fuel roots ones twos false delTwo).map (.deleteOne :: ·) else []) ++
      (if delTwo then
        (permittedWords fuel roots ones twos delOne false).map (.deleteTwo :: ·) else []) ++
      (if ones = 0 || delTwo then [] else
        (permittedWords fuel roots (ones - 1) twos delOne delTwo).map (.afterOne :: ·)) ++
      (if twos = 0 || delOne then [] else
        (permittedWords fuel roots ones (twos - 1) delOne delTwo).map (.afterTwo :: ·))

def words : List (List Action) := permittedWords 8 2 2 2 true true

def projection (s : List Nat × List Nat) : ProjectedState where
  liveOne := decide (1 ∈ s.1)
  liveTwo := decide (2 ∈ s.1)
  reservedOne := decide (1 ∈ s.2)
  reservedTwo := decide (2 ∈ s.2)
  otherCount := (s.1.filter (fun x => x != 1 && x != 2)).length

private theorem mem_insert_exact (x anchor id : Nat) (xs : List Nat) :
    x ∈ insertAfter anchor id xs ↔
      x ∈ xs ∨ (x = id ∧ (anchor = 0 ∨ anchor ∈ xs)) := by
  induction xs with
  | nil =>
      by_cases h : anchor = 0 <;> simp [insertAfter, h]
  | cons y ys ih =>
      by_cases h0 : anchor = 0
      · subst anchor; simp [insertAfter]; tauto
      · by_cases hy : y = anchor
        · subst y; simp [insertAfter, h0]; tauto
        · simp [insertAfter, h0, hy, ih]
          grind

private theorem filtered_insert_length (anchor id : Nat) (xs : List Nat) :
    ((insertAfter anchor id xs).filter (fun x => x != 1 && x != 2)).length =
      (xs.filter (fun x => x != 1 && x != 2)).length +
        if (anchor = 0 ∨ anchor ∈ xs) ∧ id ≠ 1 ∧ id ≠ 2 then 1 else 0 := by
  induction xs with
  | nil =>
      by_cases h0 : anchor = 0 <;> by_cases h1 : id = 1 <;> by_cases h2 : id = 2 <;>
        simp_all [insertAfter]
  | cons y ys ih =>
      by_cases h0 : anchor = 0
      · subst anchor
        by_cases h1 : id = 1 <;> by_cases h2 : id = 2 <;> by_cases hy1 : y = 1 <;>
          by_cases hy2 : y = 2 <;> simp_all [insertAfter, Nat.add_assoc] <;> grind
      · by_cases hy : y = anchor
        · subst y
          by_cases h1 : id = 1 <;> by_cases h2 : id = 2 <;> by_cases ha1 : anchor = 1 <;>
            by_cases ha2 : anchor = 2 <;> simp_all [insertAfter, Nat.add_assoc] <;> grind
        · by_cases h1 : id = 1 <;> by_cases h2 : id = 2 <;> by_cases hy1 : y = 1 <;>
            by_cases hy2 : y = 2 <;> simp_all [insertAfter, Nat.add_assoc] <;> grind

private theorem projected_allocation (xs used : List Nat) (anchor id : Nat)
    (fresh : id ∉ used) :
    projection (insertAfter anchor id xs, used ++ [id]) ∈
      allocationNext (projection (xs, used)) (decide (anchor = 0 ∨ anchor ∈ xs)) := by
  by_cases h1 : id = 1
  · subst id
    have hf : 1 ∉ used := fresh
    apply List.mem_append_left
    apply List.mem_append_left
    simp only [allocationNext, projection, decide_eq_false hf, Bool.false_eq_true,
      ↓reduceIte, List.mem_singleton]
    apply ProjectedState.ext <;>
      simp [projection, mem_insert_exact, filtered_insert_length, hf, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  · by_cases h2 : id = 2
    · subst id
      have hf : 2 ∉ used := fresh
      apply List.mem_append_left
      apply List.mem_append_right
      simp only [projection, decide_eq_false hf, Bool.false_eq_true,
        ↓reduceIte, List.mem_singleton]
      apply ProjectedState.ext <;>
        simp [projection, mem_insert_exact, filtered_insert_length, hf, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    · apply List.mem_append_right
      simp only [List.mem_singleton]
      apply ProjectedState.ext <;>
        simp [projection, mem_insert_exact, filtered_insert_length, h1, h2, Ne.symm h1, Ne.symm h2]

private theorem other_filter_one (xs : List Nat) :
    (xs.filter (fun x => decide (x ≠ 1))).filter (fun x => x != 1 && x != 2) =
      xs.filter (fun x => x != 1 && x != 2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> simp_all

private theorem other_filter_two (xs : List Nat) :
    (xs.filter (fun x => decide (x ≠ 2))).filter (fun x => x != 1 && x != 2) =
      xs.filter (fun x => x != 1 && x != 2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> simp_all

/-- Every genuine transition with any fresh natural identifier is represented. -/
theorem transition_projects {s t : List Nat × List Nat} {a : Action}
    (h : allocationMachine.transition s (.update a.op) t) :
    projection t ∈ nextStates (projection s) a := by
  cases a with
  | root =>
      obtain ⟨id, fresh, rfl⟩ := h
      simpa [nextStates, validAnchor] using projected_allocation s.1 s.2 0 id fresh
  | afterOne =>
      obtain ⟨id, fresh, rfl⟩ := h
      simpa [nextStates, validAnchor, projection] using projected_allocation s.1 s.2 1 id fresh
  | afterTwo =>
      obtain ⟨id, fresh, rfl⟩ := h
      simpa [nextStates, validAnchor, projection] using projected_allocation s.1 s.2 2 id fresh
  | deleteOne =>
      change t = (s.1.filter (fun x => decide (x ≠ 1)), s.2) at h
      subst t
      simp only [nextStates, List.mem_singleton]
      apply ProjectedState.ext <;> dsimp [projection]
      all_goals first
      | exact congrArg List.length (other_filter_one s.1)
      | simp
  | deleteTwo =>
      change t = (s.1.filter (fun x => decide (x ≠ 2)), s.2) at h
      subst t
      simp only [nextStates, List.mem_singleton]
      apply ProjectedState.ext <;> dsimp [projection]
      all_goals first
      | exact congrArg List.length (other_filter_two s.1)
      | simp

/-- The finite projection overapproximates every run, without bounding IDs. -/
theorem runs_project {s t : List Nat × List Nat} {w : List Action}
    (h : Runs allocationMachine.transition s
      (w.map (fun a => SeqLabel.update a.op)) t) :
    projection t ∈ outcomes (projection s) w := by
  induction w generalizing s with
  | nil =>
      cases h
      simp [outcomes]
  | cons a w ih =>
      cases h with
      | cons step rest =>
          exact List.mem_flatMap.mpr ⟨_, transition_projects step, ih rest⟩

def safeOutcomes : ProjectedState → List Action → Bool
  | s, [] => !fourChildren s
  | s, a :: rest => (nextStates s a).all (fun t => safeOutcomes t rest)

private theorem safeOutcomes_sound {s t : ProjectedState} {w : List Action}
    (hs : safeOutcomes s w = true) (ht : t ∈ outcomes s w) :
    fourChildren t = false := by
  induction w generalizing s with
  | nil =>
      have he : t = s := List.mem_singleton.mp ht
      subst t
      simpa [safeOutcomes] using hs
  | cons a rest ih =>
      obtain ⟨m, hm, ht⟩ := List.mem_flatMap.mp ht
      exact ih (List.all_eq_true.mp hs m hm) ht

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
private theorem checked_outcomes : words.all (safeOutcomes initial) = true := by
  decide +kernel

/-- Exhaustive kernel calculation over allocation classes, not bounded IDs. -/
theorem projected_crossed_exclusion :
    ∀ w ∈ words, ∀ s ∈ outcomes initial w, fourChildren s = false := by
  intro w hw s hs
  exact safeOutcomes_sound (List.all_eq_true.mp checked_outcomes w hw) hs

abbrev Tag := Fin 8

def tagAction (i : Tag) : Action := match i.val with
  | 0 | 1 => .root
  | 2 => .deleteOne
  | 3 | 4 => .afterTwo
  | 5 => .deleteTwo
  | _ => .afterOne

def allTags : List Tag := [0,1,2,3,4,5,6,7]

def crossedOrder (w : List Tag) : Prop :=
  w.idxOf 2 < w.idxOf 3 ∧ w.idxOf 2 < w.idxOf 4 ∧
  w.idxOf 5 < w.idxOf 6 ∧ w.idxOf 5 < w.idxOf 7

instance (w : List Tag) : Decidable (crossedOrder w) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _))

def acceptsWord : Nat → Nat → Nat → Nat → Bool → Bool → List Action → Bool
  | 0, _, _, _, _, _, w => w.isEmpty
  | _ + 1, _, _, _, _, _, [] => false
  | fuel + 1, roots, ones, twos, delOne, delTwo, a :: rest => match a with
    | .root => roots != 0 && acceptsWord fuel (roots - 1) ones twos delOne delTwo rest
    | .deleteOne => delOne && acceptsWord fuel roots ones twos false delTwo rest
    | .deleteTwo => delTwo && acceptsWord fuel roots ones twos delOne false rest
    | .afterOne => !(ones = 0 || delTwo) &&
        acceptsWord fuel roots (ones - 1) twos delOne delTwo rest
    | .afterTwo => !(twos = 0 || delOne) &&
        acceptsWord fuel roots ones (twos - 1) delOne delTwo rest

private theorem accepts_mem (fuel roots ones twos : Nat) (d1 d2 : Bool)
    (w : List Action) (h : acceptsWord fuel roots ones twos d1 d2 w = true) :
    w ∈ permittedWords fuel roots ones twos d1 d2 := by
  induction fuel generalizing roots ones twos d1 d2 w with
  | zero =>
      cases w with
      | nil => simp [permittedWords]
      | cons a w => simp [acceptsWord] at h
  | succ fuel ih =>
      cases w with
      | nil => simp [acceptsWord] at h
      | cons a rest =>
          cases a <;> simp only [acceptsWord, Bool.and_eq_true] at h
          · simp only [permittedWords, List.mem_append]
            left; left; left; left
            rw [if_neg (by simpa using h.1)]
            exact List.mem_map.mpr ⟨rest, ih _ _ _ _ _ _ h.2, rfl⟩
          · simp only [permittedWords, List.mem_append]
            left; left; left; right
            rw [if_pos h.1]
            exact List.mem_map.mpr ⟨rest, ih _ _ _ _ _ _ h.2, rfl⟩
          · simp only [permittedWords, List.mem_append]
            right
            rw [if_neg (by simpa using h.1)]
            exact List.mem_map.mpr ⟨rest, ih _ _ _ _ _ _ h.2, rfl⟩
          · simp only [permittedWords, List.mem_append]
            left; left; right
            rw [if_pos h.1]
            exact List.mem_map.mpr ⟨rest, ih _ _ _ _ _ _ h.2, rfl⟩
          · simp only [permittedWords, List.mem_append]
            left; right
            rw [if_neg (by simpa using h.1)]
            exact List.mem_map.mpr ⟨rest, ih _ _ _ _ _ _ h.2, rfl⟩

def orderCheck (w : List Tag) : Bool :=
  !decide (crossedOrder w) || acceptsWord 8 2 2 2 true true (w.map tagAction)

def checkOrders : Nat → List Tag → List Tag → Bool
  | 0, pre, _ => orderCheck pre
  | fuel + 1, pre, remaining =>
      remaining.all (fun i => checkOrders fuel (pre ++ [i]) (remaining.erase i))

private theorem checkOrders_sound (fuel : Nat) (pre remaining w : List Tag)
    (hp : w.Perm remaining) (hl : w.length = fuel)
    (hc : checkOrders fuel pre remaining = true) : orderCheck (pre ++ w) = true := by
  induction fuel generalizing pre remaining w with
  | zero =>
      have hw : w = [] := List.length_eq_zero_iff.mp hl
      subst w
      simpa [checkOrders] using hc
  | succ fuel ih =>
      cases w with
      | nil => simp at hl
      | cons i rest =>
          have hm : i ∈ remaining := hp.mem_iff.mp (by simp)
          have hp' : rest.Perm (remaining.erase i) :=
            (hp.trans (List.perm_cons_erase hm)).cons_inv
          have hc' := List.all_eq_true.mp hc i hm
          have h := ih (pre ++ [i]) (remaining.erase i) rest hp' (by simpa using hl) hc'
          simpa [List.append_assoc] using h

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
private theorem checked_orders : checkOrders 8 [] allTags = true := by
  decide +kernel

private theorem enumerated_orders_accept (w : List Tag)
    (hp : w.Perm allTags) (ho : crossedOrder w) :
    acceptsWord 8 2 2 2 true true (w.map tagAction) = true := by
  have h := checkOrders_sound 8 [] allTags w hp (by simpa [allTags] using hp.length_eq)
    checked_orders
  simpa [orderCheck, ho] using h

/-- Covers every total order of the eight distinct events satisfying the
four required conflict-visibility edges. -/
theorem orders_project {w : List Tag} (hp : w.Perm allTags)
    (ho : crossedOrder w) : w.map tagAction ∈ words :=
  accepts_mem 8 2 2 2 true true _
    (enumerated_orders_accept w hp ho)

/-- No fresh allocator choices admit a four-child answer for any permitted
crossed order. The allocator is still over all natural identifiers. -/
theorem crossed_no_history {w : List Tag} (hp : w.Perm allTags)
    (ho : crossedOrder w) :
    ¬ listHistorySpec.admits
      ((w.map (fun i => SeqLabel.update (tagAction i).op)) ++
        [.query () [5,4,8,7]]) := by
  rintro ⟨final, run⟩
  obtain ⟨mid, pre, post⟩ := run.split
    (w.map (fun i => SeqLabel.update (tagAction i).op)) [.query () [5,4,8,7]]
  cases post with
  | cons query rest =>
      have hm : mid.1 = [5,4,8,7] := query.2.symm
      have pre' : Runs allocationMachine.transition ([], [])
          ((w.map tagAction).map (fun a => SeqLabel.update a.op)) mid := by
        simpa only [List.map_map] using pre
      have hs := runs_project pre'
      have hx := projected_crossed_exclusion _ (orders_project hp ho) _ hs
      have ht : fourChildren (projection mid) = true := by
        simp [fourChildren, projection, hm]
      exact Bool.false_ne_true (hx.symm.trans ht)

end Sal.MRDTs.Paper1.RGA.AllocatingInvestigation
