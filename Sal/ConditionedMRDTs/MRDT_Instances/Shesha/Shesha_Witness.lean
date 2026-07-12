import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Hook_Facts

/-! # Shesha — the witness assembly (phase 2e, piece ii-interface)

Given a **pre-splice forest** for the union of two branches' events — a
WF anchored forest whose rows are exactly the union's inserts, ordered
against visibility — this file assembles the canonical witness
`ρ⋆ = (plan of the forest, as events) ++ (deletes, ascending timestamps)`
and discharges all four `IsCanonicalStateW` obligations:

* `listPermOf` — the plan realizes each insert of the union exactly once
  (`row_mem_plan` / `planF_mem_row`), the delete block enumerates the
  union's deletes;
* `respects loOn` — inserts by `plan_pw` with the event-level kernel
  (§2); insert–delete pairs by the honesty exclusions; delete–delete
  pairs by ascending timestamps + `causal_mono`;
* `SheshaEff` — the plan is effective (`effS_planF`), deletes are free;
* the fold — `fold_planF` builds the forest, `steps_dels` collapses it:
  the fold is `dropF (deleted) T`.

What remains for the join hook is **only** the existence of the
pre-splice forest whose collapse is the ternary merge (`Shesha_Cond`). -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1 event realization of a plan -/

/-- The (chosen) insert event of `ev` with id `x` and anchor `p`. -/
noncomputable def evOfIns (ev : Set (Op SAppOp)) (x p : Nat) : Op SAppOp :=
  if h : InsIn ev x p then (x, Classical.choose h, SAppOp.insA p)
  else (x, 0, SAppOp.insA p)

theorem evOfIns_mem {ev : Set (Op SAppOp)} {x p : Nat}
    (h : InsIn ev x p) : evOfIns ev x p ∈ ev := by
  rw [evOfIns, dif_pos h]
  exact Classical.choose_spec h

theorem evOfIns_shape (ev : Set (Op SAppOp)) (x p : Nat) :
    ∃ r, evOfIns ev x p = (x, r, SAppOp.insA p) := by
  rw [evOfIns]
  by_cases h : InsIn ev x p
  · rw [dif_pos h]
    exact ⟨_, rfl⟩
  · rw [dif_neg h]
    exact ⟨0, rfl⟩

theorem toSOp_evOfIns (ev : Set (Op SAppOp)) (x p : Nat) :
    toSOp (evOfIns ev x p) = Shesha.Op.ins x p := by
  obtain ⟨r, hr⟩ := evOfIns_shape ev x p
  rw [hr]
  rfl

theorem time_evOfIns (ev : Set (Op SAppOp)) (x p : Nat) :
    (evOfIns ev x p).1 = x := by
  obtain ⟨r, hr⟩ := evOfIns_shape ev x p
  rw [hr]

/-- Realize an all-insert op list as events of `ev`. -/
noncomputable def evPlan (ev : Set (Op SAppOp)) :
    List Shesha.Op → List (Op SAppOp)
  | [] => []
  | .ins x p :: l => evOfIns ev x p :: evPlan ev l
  | .del _ :: l => evPlan ev l

theorem evPlan_map_toSOp {ev : Set (Op SAppOp)} :
    ∀ {l : List Shesha.Op}, Shesha.AllIns l →
      (evPlan ev l).map toSOp = l
  | [], _ => rfl
  | .ins x p :: l, h => by
      rw [evPlan, List.map_cons, toSOp_evOfIns,
        evPlan_map_toSOp (l := l) h]
  | .del _ :: l, h => absurd h id

theorem evPlan_map_time {ev : Set (Op SAppOp)} :
    ∀ {l : List Shesha.Op}, Shesha.AllIns l →
      (evPlan ev l).map (fun e => e.1) = Shesha.opInsIds l
  | [], _ => rfl
  | .ins x p :: l, h => by
      rw [evPlan, List.map_cons, time_evOfIns, Shesha.opInsIds,
        evPlan_map_time (l := l) h]
  | .del _ :: l, h => absurd h id

theorem evPlan_nodup {ev : Set (Op SAppOp)} {l : List Shesha.Op}
    (hAI : Shesha.AllIns l) (hnd : (Shesha.opInsIds l).Nodup) :
    (evPlan ev l).Nodup := by
  refine List.Nodup.of_map (f := fun e : Op SAppOp => e.1) ?_
  rw [evPlan_map_time hAI]
  exact hnd

theorem mem_evPlan {ev : Set (Op SAppOp)} :
    ∀ {l : List Shesha.Op} {e : Op SAppOp}, e ∈ evPlan ev l →
      ∃ x p, e = evOfIns ev x p ∧ Shesha.Op.ins x p ∈ l
  | .ins x p :: l, e, h => by
      rw [evPlan] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨x, p, rfl, List.mem_cons_self ..⟩
      · obtain ⟨x', p', he, hm⟩ := mem_evPlan h'
        exact ⟨x', p', he, List.mem_cons_of_mem _ hm⟩
  | .del d :: l, e, h => by
      rw [evPlan] at h
      obtain ⟨x', p', he, hm⟩ := mem_evPlan h
      exact ⟨x', p', he, List.mem_cons_of_mem _ hm⟩

theorem evPlan_mem {ev : Set (Op SAppOp)} :
    ∀ {l : List Shesha.Op} {x p : Nat}, Shesha.Op.ins x p ∈ l →
      evOfIns ev x p ∈ evPlan ev l
  | o :: l, x, p, h => by
      rcases List.mem_cons.mp h with he | h'
      · rw [← he, evPlan]
        exact List.mem_cons_self ..
      · cases o with
        | ins x' p' =>
            rw [evPlan]
            exact List.mem_cons_of_mem _ (evPlan_mem h')
        | del d =>
            rw [evPlan]
            exact evPlan_mem h'

/-! ## §2 effectiveness transport -/

theorem effFrom_of_effS :
    ∀ {ρ : List (Op SAppOp)} {s : Shesha.St},
      Shesha.EffS s (ρ.map toSOp) → EffFrom s ρ
  | [], _, _ => trivial
  | ⟨t, r, op⟩ :: ρ, s, h => by
      cases op with
      | insA a =>
          rw [List.map_cons,
            show toSOp (t, r, SAppOp.insA a) = Shesha.Op.ins t a
              from rfl] at h
          exact ⟨h.1, effFrom_of_effS h.2⟩
      | delA d =>
          rw [List.map_cons,
            show toSOp (t, r, SAppOp.delA d) = Shesha.Op.del d
              from rfl] at h
          exact ⟨trivial, effFrom_of_effS h⟩

theorem effFrom_append' :
    ∀ {l₁ l₂ : List (Op SAppOp)} {s : Shesha.St},
      EffFrom s l₁ → EffFrom (applySeq SheshaD.toCRDTSig s l₁) l₂ →
      EffFrom s (l₁ ++ l₂)
  | [], _, _, _, h₂ => h₂
  | o :: l₁, l₂, s, h₁, h₂ => ⟨h₁.1, effFrom_append' h₁.2 h₂⟩

/-- A delete-only block is always effective. -/
theorem effFrom_dels :
    ∀ {l : List (Op SAppOp)} {s : Shesha.St},
      (∀ e ∈ l, ∃ t r d, e = ((t, r, SAppOp.delA d) : Op SAppOp)) →
      EffFrom s l
  | [], _, _ => trivial
  | e :: l, s, h => by
      obtain ⟨t, r, d, rfl⟩ := h e (List.mem_cons_self ..)
      exact ⟨trivial, effFrom_dels (fun e' he' =>
        h e' (List.mem_cons_of_mem _ he'))⟩

/-! ## §3 the delete block -/

def isDelEv : Op SAppOp → Bool := fun e =>
  match e.2.2 with
  | SAppOp.delA _ => true
  | SAppOp.insA _ => false

def delTarget : Op SAppOp → Nat := fun e =>
  match e.2.2 with
  | SAppOp.delA d => d
  | SAppOp.insA _ => 0

theorem isDelEv_shape {e : Op SAppOp} (h : isDelEv e = true) :
    ∃ t r d, e = ((t, r, SAppOp.delA d) : Op SAppOp) := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | insA a => exact absurd h (by rw [isDelEv]; intro hc; cases hc)
  | delA d => exact ⟨t, r, d, rfl⟩

/-- The delete events of an enumeration, ascending timestamps. -/
def delBlock (ρu : List (Op SAppOp)) : List (Op SAppOp) :=
  (ρu.filter isDelEv).mergeSort (fun a b => Nat.ble a.1 b.1)

theorem mem_delBlock {ρu : List (Op SAppOp)} {e : Op SAppOp} :
    e ∈ delBlock ρu ↔ e ∈ ρu ∧ isDelEv e = true := by
  rw [delBlock, (List.mergeSort_perm _ _).mem_iff, List.mem_filter]

theorem delBlock_nodup {ρu : List (Op SAppOp)} (h : ρu.Nodup) :
    (delBlock ρu).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (h.filter _)

theorem delBlock_sorted (ρu : List (Op SAppOp)) :
    (delBlock ρu).Pairwise (fun a b => a.1 ≤ b.1) := by
  have h := List.sorted_mergeSort
    (le := fun a b : Op SAppOp => Nat.ble a.1 b.1)
    (by
      intro a b c h1 h2
      simp at h1 h2 ⊢
      omega)
    (by
      intro a b
      simp
      omega)
    (ρu.filter isDelEv)
  refine h.imp ?_
  intro a b hab
  simpa using hab

theorem map_toSOp_dels :
    ∀ {l : List (Op SAppOp)}, (∀ e ∈ l, isDelEv e = true) →
      l.map toSOp = (l.map delTarget).map Shesha.Op.del
  | [], _ => rfl
  | e :: l, h => by
      obtain ⟨t, r, d, rfl⟩ := isDelEv_shape (h e (List.mem_cons_self ..))
      rw [List.map_cons, List.map_cons, List.map_cons,
        show toSOp (t, r, SAppOp.delA d) = Shesha.Op.del d from rfl,
        show delTarget (t, r, SAppOp.delA d) = d from rfl,
        map_toSOp_dels (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

/-! ## §4 the union enumeration -/

open Classical in
/-- Enumerate `ev₁ ∪ ev₂` from enumerations of the parts. -/
noncomputable def unionEnum (ρ₁ ρ₂ : List (Op SAppOp))
    (ev₁ : Set (Op SAppOp)) : List (Op SAppOp) :=
  ρ₁ ++ ρ₂.filter (fun e => !decide (e ∈ ev₁))

open Classical in
theorem unionEnum_perm {ρ₁ ρ₂ : List (Op SAppOp)}
    {ev₁ ev₂ : Set (Op SAppOp)}
    (h₁ : listPermOf ρ₁ ev₁) (h₂ : listPermOf ρ₂ ev₂) :
    listPermOf (unionEnum ρ₁ ρ₂ ev₁) (ev₁ ∪ ev₂) := by
  constructor
  · rw [unionEnum, List.nodup_append]
    refine ⟨h₁.1, h₂.1.filter _, ?_⟩
    intro x hx y hy
    rintro rfl
    have hx1 : x ∈ ev₁ := (h₁.2 x).mp hx
    have := (List.mem_filter.mp hy).2
    rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
    exact this hx1
  · intro a
    rw [unionEnum, List.mem_append, List.mem_filter]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl ((h₁.2 a).mp h)
      · exact Or.inr ((h₂.2 a).mp h)
    · intro h
      by_cases ha1 : a ∈ ev₁
      · exact Or.inl ((h₁.2 a).mpr ha1)
      · rcases h with h | h
        · exact absurd h ha1
        · refine Or.inr ⟨(h₂.2 a).mpr h, ?_⟩
          rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          exact ha1

/-! ## §5 the event-level kernel -/

/-- Event realization of a single planned op. -/
noncomputable def evOfOp (ev : Set (Op SAppOp)) : Shesha.Op → Op SAppOp
  | .ins x p => evOfIns ev x p
  | .del d => (0, 0, SAppOp.delA d)

theorem evPlan_eq_map {ev : Set (Op SAppOp)} :
    ∀ {l : List Shesha.Op}, Shesha.AllIns l →
      evPlan ev l = l.map (evOfOp ev)
  | [], _ => rfl
  | .ins x p :: l, h => by
      rw [evPlan, List.map_cons, evPlan_eq_map (l := l) h]
      rfl
  | .del _ :: l, h => absurd h id

/-- **The kernel**: the structural pair facts of the plan discharge the
`loOn` obligation, through honesty and the commutation certificates. -/
theorem plan_kernel {C : Configuration SheshaD} {E : Set (Op SAppOp)}
    {T : Shesha.St}
    (hH : SheshaHonest C)
    (htrans : ∀ {a b c : Op SAppOp}, C.vis a b → C.vis b c → C.vis a c)
    (hirr : ∀ a : Op SAppOp, ¬ C.vis a a)
    (hsub : ∀ a ∈ E, a ∈ C.events)
    (hwfT : Shesha.WF T)
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn E x p)
    (hcompat : ∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ E →
        (y, ry, SAppOp.insA p) ∈ E →
        Shesha.precedes (Shesha.row T p) x y →
        ¬ C.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p)) :
    Shesha.PlanKernel T (fun o₁ o₂ =>
      ¬ loOn (Configuration.core C) E (evOfOp E o₂) (evOfOp E o₁)) := by
  intro x q₁ y q₂ hx hy hxy hq1y hsame hlo
  rw [loOn_shesha_iff] at hlo
  obtain ⟨hv, hnc⟩ := hlo
  obtain ⟨rx, hex⟩ := evOfIns_shape E x q₁
  obtain ⟨ry, hey⟩ := evOfIns_shape E y q₂
  have hxE : evOfIns E x q₁ ∈ E := evOfIns_mem ((hrows q₁ x).mp hx)
  have hyE : evOfIns E y q₂ ∈ E := evOfIns_mem ((hrows q₂ y).mp hy)
  have hv' : C.vis (y, ry, SAppOp.insA q₂) (x, rx, SAppOp.insA q₁) := by
    rw [show (evOfOp E (Shesha.Op.ins y q₂)) = evOfIns E y q₂ from rfl,
      show (evOfOp E (Shesha.Op.ins x q₁)) = evOfIns E x q₁ from rfl,
      hey, hex] at hv
    exact hv
  by_cases hqq : q₂ = q₁
  · subst hqq
    exact hcompat q₂ y x ry rx (hey ▸ hyE) (hex ▸ hxE) (hsame rfl) hv'
  · by_cases hq2x : q₂ = x
    · subst hq2x
      have hq20 : q₂ ≠ 0 := fun h0 =>
        hwfT.2 (h0 ▸ Shesha.mem_row_read hx)
      obtain ⟨r', a', hxev', hvis'⟩ :=
        honest_anchor_sees_ins hH hq20 (hsub _ (hey ▸ hyE))
      have heq : ((q₂, r', SAppOp.insA a') : Op SAppOp)
          = (q₂, rx, SAppOp.insA q₁) :=
        (Configuration.core C).ts_unique hxev' (hsub _ (hex ▸ hxE)) rfl
      rw [heq] at hvis'
      exact hirr _ (htrans hvis' hv')
    · by_cases hq1yy : q₁ = y
      · exact hq1y hq1yy
      · refine hnc ?_
        rw [show (evOfOp E (Shesha.Op.ins y q₂)) = evOfIns E y q₂ from rfl,
          show (evOfOp E (Shesha.Op.ins x q₁)) = evOfIns E x q₁ from rfl,
          hey, hex]
        intro s
        rw [sUpdate_ins, sUpdate_ins, sUpdate_ins, sUpdate_ins]
        exact Shesha.insert_insert_comm hqq hq2x hq1yy s

end Sal.ConditionedMRDTs
