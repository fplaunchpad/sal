import Sal.MRDTs.Paper1.HistorySpec
import Sal.MRDTs.Instances.RGASequential

/-!
# RGA with an operation-only allocating list specification

The current `RGAOp.addAfter` carries an anchor, but no inserted identifier.
Consequently the specification allocates a fresh identifier nondeterministically.
Its data state is an ordinary list; an independent allocation registry prevents
identifier reuse after deletion. Its transition relation sees no event time or
replica. Missing anchors are no-ops, and deletion physically removes an identifier.

The bridge chooses the insertion event's identifier inside the proof. This does
not pass event metadata to the specification: the independently defined allocator
admits every fresh choice. The resulting language therefore specifies allocation,
not a deterministic function from operation labels to identifier lists.
-/

namespace Sal.MRDTs.Paper1.RGA

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA

/-- Application-only list transitions. Identifier allocation is a semantic choice. -/
def listMachine : HistoryMachine RGAOp Unit (List ℕ) where
  State := List ℕ
  initial := []
  transition xs label ys := match label with
    | .update (.addAfter anchor) =>
        ∃ id, id ∉ xs ∧ ys = insertAfter anchor id xs
    | .update (.remove id) => ys = xs.filter (· ≠ id)
    | .query _ answer => ys = xs ∧ answer = xs

def currentFreshHistorySpec : HistorySpec RGAOp Unit (List ℕ) := listMachine.toSpec

/-- Strip both metadata fields before presenting labels to the specification. -/
def labels (ops : List (Op RGAOp)) : List (SeqLabel RGAOp Unit (List ℕ)) :=
  ops.map (fun e => .update e.op)

@[simp] theorem labels_append (a b : List (Op RGAOp)) :
    labels (a ++ b) = labels a ++ labels b := by simp [labels]

private theorem mem_insertAfter {anchor id x : ℕ} {xs : List ℕ}
    (h : x ∈ insertAfter anchor id xs) : x = id ∨ x ∈ xs := by
  induction xs with
  | nil =>
      simp only [insertAfter] at h
      split at h <;> simp_all
  | cons a xs ih =>
      simp only [insertAfter] at h
      split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.mpr h)
      · split at h
        · simp only [List.mem_cons] at h
          rcases h with h | h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · simp only [List.mem_cons] at h
          rcases h with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · rcases ih h with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons.mpr (Or.inr h))

private theorem mem_list_run (ops : List (Op RGAOp)) {x : ℕ}
    (h : List.Mem x (listSpec.run ops)) : x ∈ ops.map Op.time := by
  induction ops using List.reverseRecOn with
  | nil => cases h
  | append_singleton ops e ih =>
      rw [SequentialSpec.run_append_single] at h
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor =>
          change x ∈ insertAfter anchor ts (listSpec.run ops) at h
          rcases mem_insertAfter h with rfl | h
          · simp [Op.time]
          · simpa only [List.map_append] using (List.mem_append_left [ts] (ih h))
      | remove id =>
          change x ∈ (listSpec.run ops).filter (· ≠ id) at h
          simpa only [List.map_append] using
            (List.mem_append_left [ts] (ih (List.mem_filter.mp h).1))

/-- Global event-time uniqueness supplies fresh allocations in the selected run. -/
theorem projected_run (ops : List (Op RGAOp))
    (fresh : (ops.map Op.time).Nodup) :
    Runs listMachine.transition [] (labels ops) (listSpec.run ops) := by
  induction ops using List.reverseRecOn with
  | nil => exact .nil []
  | append_singleton ops e ih =>
      have hnf : (ops.map Op.time ++ [e.time]).Nodup := by
        simpa only [List.map_append, List.map_singleton] using fresh
      have hn : (ops.map Op.time).Nodup ∧ e.time ∉ ops.map Op.time := by
        rw [List.nodup_append_comm] at hnf
        simpa [and_comm] using hnf
      rw [labels_append, SequentialSpec.run_append_single]
      apply Runs.append (ih hn.1)
      apply Runs.cons _ (.nil _)
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor =>
          exact ⟨ts, fun h => hn.2 (mem_list_run ops h), rfl⟩
      | remove id => exact rfl

/-- The canonical witness is admitted by a specification of application labels. -/
theorem currentFresh_canonical_admitted {ops : List (Op RGAOp)} {E : Set (Op RGAOp)}
    (hperm : listPermOf ops E) (hwf : VersionWellFormed E) :
    currentFreshHistorySpec.admits
      (labels (canonical ops) ++ [.query () (listSpec.run (canonical ops))]) := by
  have hcan := canonical_listPermOf hperm
  have hfresh : ((canonical ops).map Op.time).Nodup :=
    List.Nodup.map_on (fun a ha b hb he =>
      hwf.time_unique ((hcan.2 a).mp ha) ((hcan.2 b).mp hb) he) hcan.1
  exact ⟨_, (projected_run _ hfresh).append (.cons ⟨rfl, rfl⟩ (.nil _))⟩

/-- Honesty and causal closure connect the admitted allocation choices to the read. -/
theorem currentFresh_admitted_of_execution {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (hver : C.ver v = some (s, E)) {ops : List (Op RGAOp)}
    (hperm : listPermOf ops E)
    (hfold : applySeq RGAM.toUpdateSig RGAM.init ops = s) :
    currentFreshHistorySpec.admits
      (labels (canonical ops) ++ [.query () (RGAM.query s ())]) := by
  have hwf := versionWellFormed_of_execution exec hver
  have href := canonical_refines_list hperm hwf
  have hstate := (canonical_fold ops).trans hfold
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) =
    listSpec.run (canonical ops) at href
  rw [hstate] at href
  change currentFreshHistorySpec.admits
    (labels (canonical ops) ++ [.query () (read s)])
  rw [href]
  exact currentFresh_canonical_admitted hperm hwf

/-- The registry records abstract allocation choices, not event metadata. Physical
list deletion leaves identifiers reserved, so they cannot be allocated again. -/
def allocationMachine : HistoryMachine RGAOp Unit (List ℕ) where
  State := List ℕ × List ℕ
  initial := ([], [])
  transition state label next := match label with
    | .update (.addAfter anchor) =>
        ∃ id, id ∉ state.2 ∧
          next = (insertAfter anchor id state.1, state.2 ++ [id])
    | .update (.remove id) => next = (state.1.filter (· ≠ id), state.2)
    | .query _ answer => next = state ∧ answer = state.1

/-- Primary operation-only RGA specification: globally fresh allocation. -/
def listHistorySpec : HistorySpec RGAOp Unit (List ℕ) := allocationMachine.toSpec

private def allocated (ops : List (Op RGAOp)) : List ℕ :=
  (insertEntries ops).map Prod.fst

private theorem mem_allocated {ops : List (Op RGAOp)} {id : ℕ}
    (h : id ∈ allocated ops) : id ∈ ops.map Op.time := by
  obtain ⟨⟨i, anchor⟩, he, hi⟩ := List.mem_map.mp h
  change i = id at hi
  subst id
  obtain ⟨replica, hr⟩ := mem_insertEntries.mp he
  exact List.mem_map.mpr ⟨(i, replica, .addAfter anchor), hr, rfl⟩

/-- The concrete witness allocates globally unused IDs even after deletion. -/
theorem allocation_run (ops : List (Op RGAOp))
    (fresh : (ops.map Op.time).Nodup) :
    Runs allocationMachine.transition ([], []) (labels ops)
      (listSpec.run ops, allocated ops) := by
  induction ops using List.reverseRecOn with
  | nil => exact .nil ([], [])
  | append_singleton ops e ih =>
      have hnf : (ops.map Op.time ++ [e.time]).Nodup := by
        simpa only [List.map_append, List.map_singleton] using fresh
      have hn : (ops.map Op.time).Nodup ∧ e.time ∉ ops.map Op.time := by
        rw [List.nodup_append_comm] at hnf
        simpa [and_comm] using hnf
      rw [labels_append, SequentialSpec.run_append_single]
      apply Runs.append (ih hn.1)
      apply Runs.cons _ (.nil _)
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | addAfter anchor =>
          refine ⟨ts, fun h => hn.2 (mem_allocated h), ?_⟩
          simp [allocated, insertEntries, listSpec, listStep]
      | remove id =>
          simp [allocationMachine, allocated, insertEntries, listSpec, listStep, Op.op]

theorem canonical_admitted {ops : List (Op RGAOp)} {E : Set (Op RGAOp)}
    (hperm : listPermOf ops E) (hwf : VersionWellFormed E) :
    listHistorySpec.admits
      (labels (canonical ops) ++ [.query () (listSpec.run (canonical ops))]) := by
  have hcan := canonical_listPermOf hperm
  have hfresh : ((canonical ops).map Op.time).Nodup :=
    List.Nodup.map_on (fun a ha b hb he =>
      hwf.time_unique ((hcan.2 a).mp ha) ((hcan.2 b).mp hb) he) hcan.1
  exact ⟨_, (allocation_run _ hfresh).append (.cons ⟨rfl, rfl⟩ (.nil _))⟩

theorem admitted_of_execution {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (hver : C.ver v = some (s, E)) {ops : List (Op RGAOp)}
    (hperm : listPermOf ops E)
    (hfold : applySeq RGAM.toUpdateSig RGAM.init ops = s) :
    listHistorySpec.admits
      (labels (canonical ops) ++ [.query () (RGAM.query s ())]) := by
  have hwf := versionWellFormed_of_execution exec hver
  have href := canonical_refines_list hperm hwf
  have hstate := (canonical_fold ops).trans hfold
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ops)) =
    listSpec.run (canonical ops) at href
  rw [hstate] at href
  change listHistorySpec.admits
    (labels (canonical ops) ++ [.query () (read s)])
  rw [href]
  exact canonical_admitted hperm hwf

/-- Metadata stripping prevents the old deterministic list fold from factoring
through application labels. It does not prevent a nondeterministic allocator. -/
theorem old_list_run_does_not_factor :
    ¬ ∃ f : List RGAOp → List ℕ, ∀ ops : List (Op RGAOp),
      f (ops.map Op.op) = listSpec.run ops := by
  rintro ⟨f, hf⟩
  have h1 := hf [(1, 0, .addAfter 0)]
  have h2 := hf [(2, 1, .addAfter 0)]
  have he : ([1] : List ℕ) = [2] := h1.symm.trans h2
  cases he

/-- Two different allocation choices admit the same insertion label. Both are
visible; allocation does not admit the degenerate empty answer. -/
theorem singleton_add_admitted (id : ℕ) :
    listHistorySpec.admits [.update (.addAfter 0), .query () [id]] := by
  refine ⟨([id], [id]), .cons ?_ (.cons ⟨rfl, rfl⟩ (.nil _))⟩
  refine ⟨id, ?_⟩
  exact ⟨by simp [allocationMachine], rfl⟩

/-- Read-side inversion supplies the FAIL companion to allocation acceptance. -/
theorem singleton_add_not_empty :
    ¬ listHistorySpec.admits [.update (.addAfter 0), .query () []] := by
  rintro ⟨final, run⟩
  cases run with
  | cons hadd rest =>
      cases rest with
      | cons hquery _ =>
          obtain ⟨id, _, rfl⟩ := hadd
          have h : ([] : List ℕ) = [id] := hquery.2
          cases h

/-- Physical deletion does not release an allocated identifier. -/
theorem cannot_reallocate_deleted :
    ¬ allocationMachine.transition ([], [1]) (.update (.addAfter 0))
      ([1], [1, 1]) := by
  rintro ⟨id, hfresh, heq⟩
  have hid := congrArg Prod.fst heq
  have h : id = 1 := by simpa [insertAfter] using hid.symm
  subst id
  exact hfresh (by simp)

/-- PASS+FAIL: allocation is nondeterministic and the visible read is nonempty. -/
example : listHistorySpec.admits [.update (.addAfter 0), .query () [1]] ∧
    listHistorySpec.admits [.update (.addAfter 0), .query () [2]] ∧
    ¬ listHistorySpec.admits [.update (.addAfter 0), .query () []] :=
  ⟨singleton_add_admitted 1, singleton_add_admitted 2, singleton_add_not_empty⟩

/-- PASS+FAIL: deletion physically removes the chosen id, while its registry
reservation still prevents a later allocation of that same id. -/
example : allocationMachine.transition ([1], [1]) (.update (.remove 1))
    ([], [1]) ∧ ¬ allocationMachine.transition ([], [1])
      (.update (.addAfter 0)) ([1], [1, 1]) :=
  ⟨rfl, cannot_reallocate_deleted⟩

#print axioms canonical_admitted
#print axioms admitted_of_execution
#print axioms old_list_run_does_not_factor

end Sal.MRDTs.Paper1.RGA
