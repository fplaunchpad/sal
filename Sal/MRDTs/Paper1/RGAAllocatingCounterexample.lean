import Sal.MRDTs.Paper1.RGACrossedEvidence
import Sal.MRDTs.Paper1.RGAAllocatingInvestigation
import Sal.MRDTs.Paper1.RGAStrictInvestigation

/-! The unchanged eight-event RGA execution is honestly certified reachable,
yet no total order and no globally fresh allocator explains its final query
under the primary operation-only specification and specification visibility. -/
namespace Sal.MRDTs.Paper1.RGA.AllocatingCounterexample
open Foundation
open Sal.MRDTs.Instances.RGA
open CrossedExecution
open CrossedExecution.Evidence
open AllocatingInvestigation

private theorem event_injective' : Function.Injective event := by
  intro i j h
  have time : ∀ i : I, (event i).1 = i.val + 1 := by intro i; fin_cases i <;> rfl
  have ht := congrArg Prod.fst h
  rw [time,time] at ht
  exact Fin.ext (Nat.add_right_cancel ht)

private theorem tag_op (i : I) : (event i).op = (tagAction i).op := by
  fin_cases i <;> rfl

private theorem event_idxOf (w : List I) (i : I) :
    (w.map event).idxOf (event i) = w.idxOf i := by
  induction w with
  | nil => rfl
  | cons j w ih =>
      simp only [List.map_cons, List.idxOf_cons, cond_eq_ite, beq_iff_eq,
        event_injective'.eq_iff, ih]

private theorem exists_tags (π : List Event)
    (h : ∀ e ∈ π, ∃ i : I, event i = e) :
    ∃ w : List I, w.map event = π := by
  induction π with
  | nil => exact ⟨[], rfl⟩
  | cons e π ih =>
      obtain ⟨i, hi⟩ := h e (by simp)
      obtain ⟨w, hw⟩ := ih (by intro a ha; exact h a (by simp [ha]))
      exact ⟨i :: w, by simp [hi, hw]⟩

private theorem final_members (e : Event) :
    e ∈ (↑((records 10).2.image event) : Set Event) ↔ ∃ i : I, event i = e := by
  simp [records, indices]

private theorem tagged_perm {w : List I}
    (hp : listPermOf (w.map event) (↑((records 10).2.image event) : Set Event)) :
    w.Perm allTags := by
  apply (List.perm_ext_iff_of_nodup (List.Nodup.of_map event hp.1) (by decide)).mpr
  intro i
  have hall : i ∈ allTags := by fin_cases i <;> decide
  constructor
  · intro _; exact hall
  · intro _
    have he : event i ∈ w.map event := (hp.2 _).mpr ((final_members _).mpr ⟨i,rfl⟩)
    obtain ⟨j,hj,heq⟩ := List.mem_map.mp he
    exact (event_injective' heq) ▸ hj

private theorem crossed_spec_edge (i j : I)
    (h : (i = 2 ∧ (j = 3 ∨ j = 4)) ∨ (i = 5 ∧ (j = 6 ∨ j = 7))) :
    specVisibility listHistorySpec (config 10).replayContext (event i) (event j) := by
  rcases h with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl⟩
  all_goals
    constructor
    · change vis 10 _ _
      exact ⟨_, _, rfl, rfl, by decide⟩
    · intro hc
      first
      | exact anchor_two_insert_remove_one_not_commute (HistorySpec.commutes_symm hc)
      | exact anchor_one_insert_remove_two_not_commute (HistorySpec.commutes_symm hc)

private theorem tagged_crossed {w : List I}
    (hp : listPermOf (w.map event) (↑((records 10).2.image event) : Set Event))
    (hs : respects (w.map event) (specVisibility listHistorySpec (config 10).replayContext)) :
    crossedOrder w := by
  have hm (i : I) : event i ∈ w.map event :=
    (hp.2 _).mpr ((final_members _).mpr ⟨i,rfl⟩)
  have edge (i j : I) (hne : i ≠ j)
      (he : (i = 2 ∧ (j = 3 ∨ j = 4)) ∨ (i = 5 ∧ (j = 6 ∨ j = 7))) :
      w.idxOf i < w.idxOf j := by
    have hi := Strict.Investigation.respects_idxOf hs (hm i) (hm j)
      (fun hij => hne (event_injective' hij)) (crossed_spec_edge i j he)
    simpa only [event_idxOf] using hi
  exact ⟨edge 2 3 (by decide) (by simp), edge 2 4 (by decide) (by simp),
    edge 5 6 (by decide) (by simp), edge 5 7 (by decide) (by simp)⟩

/-- Refutes every permissible witness, not only a chosen canonical order. -/
theorem not_specificationRA :
    ¬ SpecificationRALinearizable RGAM emptyPolicy listHistorySpec (config 10) := by
  intro h
  have hh : (config 10).head 0 = some 10 := by rfl
  have hv : (config 10).ver 10 =
      some ((records 10).1, (↑((records 10).2.image event) : Set Event)) := by
    simp [config, ver]
  obtain ⟨π,hp,_,hs,ha⟩ := h 0 10 (records 10).1 _ hh hv ()
  obtain ⟨w,rfl⟩ := exists_tags π (fun e he => (final_members e).mp ((hp.2 e).mp he))
  have heq : projectedUpdates (D := RGAM) (w.map event) =
      w.map (fun i => SeqLabel.update (tagAction i).op) := by
    simp only [projectedUpdates, List.map_map]
    apply List.map_congr_left
    intro i _
    exact congrArg SeqLabel.update (tag_op i)
  have reject := crossed_no_history (tagged_perm hp) (tagged_crossed hp hs)
  exact reject (by simpa only [heq, final_read] using ha)

/-- A fully honestly certified reachable counterexample for the unchanged RGA
and unchanged primary operation-only allocating specification. -/
theorem certified_counterexample :
    MintCertifiedReach RGAM generation (config 10) ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy listHistorySpec (config 10) :=
  ⟨mint_certified, not_specificationRA⟩

#print axioms not_specificationRA
#print axioms certified_counterexample
end Sal.MRDTs.Paper1.RGA.AllocatingCounterexample
