import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Hook_Facts

/-! # Shesha — the witness assembly

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

/-! ## §6 the assembly -/

open Classical in
/-- **The witness assembly**, explicit-witness form: a pre-splice forest
for `E` — WF, rows = `E`'s inserts, row order against visibility —
realizes the state `dropF (deleted E) T` as a `W`-canonical state of `E`
via the witness `plan of the forest ++ deletes ascending`. -/
theorem presplice_canonical_wit {C : Configuration SheshaD}
    {E : Set (Op SAppOp)} {ρu : List (Op SAppOp)}
    (hH : SheshaHonest C)
    (htrans : ∀ {a b c : Op SAppOp}, C.vis a b → C.vis b c → C.vis a c)
    (hirr : ∀ a : Op SAppOp, ¬ C.vis a a)
    (hsub : ∀ a ∈ E, a ∈ C.events)
    (hpermu : listPermOf ρu E)
    (T : Shesha.St)
    (hwfT : Shesha.WF T)
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn E x p)
    (hcompat : ∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ E →
        (y, ry, SAppOp.insA p) ∈ E →
        Shesha.precedes (Shesha.row T p) x y →
        ¬ C.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p)) :
    IsCanonWitness SheshaEff (Configuration.core C) E
      (Shesha.dropF (fun u => decide (DelIn E u)) T)
      (evPlan E (Shesha.planF 0 T) ++ delBlock ρu) := by
  have hAI := Shesha.allIns_planF 0 T
  have hIdsNodup : (Shesha.opInsIds (Shesha.planF 0 T)).Nodup :=
    Shesha.nodup_of_count_le_one (fun u => by
      rw [Shesha.opInsIds_planF_count 0 u T]
      exact Shesha.count_le_one_of_nodup hwfT.1 u)
  -- membership of plan ops in rows
  have hplan_row : ∀ {x p : Nat}, Shesha.Op.ins x p ∈ Shesha.planF 0 T →
      x ∈ Shesha.row T p := by
    intro x p h
    obtain ⟨z, w, heq, hz⟩ := Shesha.planF_mem_row hwfT T
      (fun _ ht => Shesha.mem_subF_of_mem ht)
      (fun t ht => by
        rw [Shesha.row, if_pos rfl]
        exact List.mem_map.mpr ⟨t, ht, rfl⟩) h
    injection heq with h1 h2
    rw [h1, h2]
    exact hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- nodup
    rw [List.nodup_append]
    refine ⟨evPlan_nodup hAI hIdsNodup, delBlock_nodup hpermu.1, ?_⟩
    intro a ha b hb
    rintro rfl
    obtain ⟨x, p, rfl, -⟩ := mem_evPlan ha
    obtain ⟨rx, hex⟩ := evOfIns_shape E x p
    have := (mem_delBlock.mp hb).2
    rw [hex] at this
    exact absurd this (by rw [isDelEv]; intro hc; cases hc)
  · -- membership
    intro a
    rw [List.mem_append]
    constructor
    · rintro (ha | ha)
      · obtain ⟨x, p, rfl, hins⟩ := mem_evPlan ha
        exact evOfIns_mem ((hrows p x).mp (hplan_row hins))
      · exact (hpermu.2 a).mp (mem_delBlock.mp ha).1
    · intro ha
      rcases a with ⟨t, r, op⟩
      cases op with
      | insA p =>
          refine Or.inl ?_
          have hins : Shesha.Op.ins t p ∈ Shesha.planF 0 T :=
            Shesha.row_mem_plan ((hrows p t).mpr ⟨r, ha⟩)
          have hmem := evPlan_mem (ev := E) hins
          have heq : evOfIns E t p = ((t, r, SAppOp.insA p) : Op SAppOp) := by
            obtain ⟨r', he⟩ := evOfIns_shape E t p
            rw [he]
            exact (Configuration.core C).ts_unique
              (hsub _ (he ▸ evOfIns_mem ⟨r, ha⟩)) (hsub _ ha) rfl
          rw [← heq]
          exact hmem
      | delA d =>
          exact Or.inr (mem_delBlock.mpr ⟨(hpermu.2 _).mpr ha, rfl⟩)
  · -- respects loOn
    rw [respects, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- within the insert block
      rw [evPlan_eq_map hAI, List.pairwise_map]
      exact Shesha.plan_pw hwfT
        (plan_kernel hH (fun h1 h2 => htrans h1 h2) hirr hsub hwfT
          hrows hcompat)
    · -- within the delete block: ascending timestamps
      refine (delBlock_sorted ρu).imp ?_
      intro a b hab hlo
      rw [loOn_shesha_iff] at hlo
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (C.causal_mono hlo.1) hab)
    · -- insert–delete cross pairs
      intro a ha b hb hlo
      rw [loOn_shesha_iff] at hlo
      obtain ⟨hv, hnc⟩ := hlo
      obtain ⟨x, p, rfl, hins⟩ := mem_evPlan ha
      obtain ⟨rx, hex⟩ := evOfIns_shape E x p
      obtain ⟨td, rd, d, rfl⟩ := isDelEv_shape (mem_delBlock.mp hb).2
      have haE : evOfIns E x p ∈ E :=
        evOfIns_mem ((hrows p x).mp (hplan_row hins))
      have hbE : ((td, rd, SAppOp.delA d) : Op SAppOp) ∈ E :=
        (hpermu.2 _).mp (mem_delBlock.mp hb).1
      rw [hex] at hv haE
      by_cases hdx : d = x
      · subst hdx
        have hvis := honest_ins_vis_del hH (hsub _ haE) (hsub _ hbE)
        exact hirr _ (htrans hvis hv)
      · by_cases hdp : d = p
        · subst hdp
          have hd0 : d ≠ 0 := honest_del_nonzero hH (hsub _ hbE)
          exact honest_no_del_anchor_vis_ins hH hd0 (hsub _ hbE) hv
        · refine hnc ?_
          rw [hex]
          intro s
          rw [sUpdate_del, sUpdate_ins, sUpdate_ins, sUpdate_del]
          exact (Shesha.delete_insert_comm hdx hdp s).symm
  · -- effectiveness
    refine effFrom_append' ?_ ?_
    · refine effFrom_of_effS ?_
      rw [evPlan_map_toSOp hAI]
      exact Shesha.effS_planF 0 T ([] : Shesha.St) hwfT.1 hwfT.2
        (fun u _ => rfl) (fun u hu h0 => hwfT.2 (h0 ▸ hu)) (Or.inl rfl)
    · exact effFrom_dels (fun e he => isDelEv_shape (mem_delBlock.mp he).2)
  · -- the fold
    rw [applySeq_toSOp, List.map_append, evPlan_map_toSOp hAI,
      map_toSOp_dels (fun e he => (mem_delBlock.mp he).2),
      Shesha.steps_append,
      show Shesha.steps SheshaD.init (Shesha.planF 0 T)
        = Shesha.fold (Shesha.planF 0 T) from rfl,
      Shesha.fold_planF T hwfT.1 hwfT.2,
      Shesha.steps_dels]
    refine Shesha.dropF_congr (fun u => ?_) T
    by_cases hd : DelIn E u
    · rw [decide_eq_true hd]
      obtain ⟨t, r, hm⟩ := hd
      refine List.contains_iff_mem.mpr ?_
      refine List.mem_map.mpr ⟨(t, r, SAppOp.delA u), ?_, rfl⟩
      exact mem_delBlock.mpr ⟨(hpermu.2 _).mpr hm, rfl⟩
    · rw [decide_eq_false hd]
      rcases hc : ((delBlock ρu).map delTarget).contains u with _ | _
      · rfl
      · obtain ⟨e, he, hte⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        obtain ⟨t, r, d, rfl⟩ := isDelEv_shape (mem_delBlock.mp he).2
        have hdu : d = u := hte
        exact absurd ⟨t, r, hdu ▸ (hpermu.2 _).mp (mem_delBlock.mp he).1⟩ hd

open Classical in
/-- **The witness assembly**, existential form. -/
theorem presplice_canonical {C : Configuration SheshaD}
    {E : Set (Op SAppOp)} {ρu : List (Op SAppOp)}
    (hH : SheshaHonest C)
    (htrans : ∀ {a b c : Op SAppOp}, C.vis a b → C.vis b c → C.vis a c)
    (hirr : ∀ a : Op SAppOp, ¬ C.vis a a)
    (hsub : ∀ a ∈ E, a ∈ C.events)
    (hpermu : listPermOf ρu E)
    (T : Shesha.St)
    (hwfT : Shesha.WF T)
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn E x p)
    (hcompat : ∀ p x y rx ry, (x, rx, SAppOp.insA p) ∈ E →
        (y, ry, SAppOp.insA p) ∈ E →
        Shesha.precedes (Shesha.row T p) x y →
        ¬ C.vis (x, rx, SAppOp.insA p) (y, ry, SAppOp.insA p)) :
    IsCanonicalStateW SheshaEff (Configuration.core C) E
      (Shesha.dropF (fun u => decide (DelIn E u)) T) :=
  (presplice_canonical_wit hH htrans hirr hsub hpermu T hwfT
    hrows hcompat).isCanonicalStateW

/-! ## §7 slot alignment: towards the M0–M2 hypotheses at the join

The live set of a normal-form slot is `inserted ∖ deleted` — pure event
bookkeeping. With timestamp uniqueness this realigns the three slots:
common liveness (`ModelOK.common`) and the anchor-chain closure that
`LRowsOK` needs. -/

open Classical in
/-- The live set of a slot in normal form. -/
theorem read_nf {T : Shesha.St} {E : Set (Op SAppOp)}
    (hreads : ∀ u, u ∈ Shesha.read T ↔ ∃ p, InsIn E u p) (u : Nat) :
    u ∈ Shesha.read (Shesha.dropF (fun v => decide (DelIn E v)) T)
      ↔ (∃ p, InsIn E u p) ∧ ¬ DelIn E u := by
  rw [Shesha.read_dropF, List.mem_filter, hreads]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hd
    rw [decide_eq_true hd] at h2
    cases h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [decide_eq_false h2]
    rfl

/-- **Common liveness** (`ModelOK.common`-shape): an id live in both
branches is live at the LCA — its unique insert is common past, and no
common delete targets it. -/
theorem nf_common {C : Configuration SheshaD}
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C.events)
    {u : Nat}
    (h₁ : (∃ p, InsIn ev₁ u p) ∧ ¬ DelIn ev₁ u)
    (h₂ : (∃ p, InsIn ev₂ u p) ∧ ¬ DelIn ev₂ u) :
    (∃ p, InsIn (ev₁ ∩ ev₂) u p) ∧ ¬ DelIn (ev₁ ∩ ev₂) u := by
  obtain ⟨⟨p₁, r₁, hm₁⟩, hd₁⟩ := h₁
  obtain ⟨⟨p₂, r₂, hm₂⟩, hd₂⟩ := h₂
  have heq : ((u, r₂, SAppOp.insA p₂) : Op SAppOp)
      = (u, r₁, SAppOp.insA p₁) :=
    (Configuration.core C).ts_unique (hsub₂ _ hm₂) (hsub₁ _ hm₁) rfl
  refine ⟨⟨p₁, r₁, hm₁, heq ▸ hm₂⟩, ?_⟩
  rintro ⟨t, r, hm⟩
  exact hd₁ ⟨t, r, hm.1⟩

/-- **Anchor lift**: a common insert's (nonroot) anchor is itself a
common insert — the anchor's insert is visible and non-commuting, so
both closure hypotheses pull it in. -/
theorem anchor_lift {C : Configuration SheshaD} (hH : SheshaHonest C)
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events)
    (hclosed₁ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {y q : Nat} {ry : Replica}
    (hy : (y, ry, SAppOp.insA q) ∈ ev₁ ∩ ev₂) (hq0 : q ≠ 0) :
    ∃ rq aq, (q, rq, SAppOp.insA aq) ∈ ev₁ ∩ ev₂ := by
  obtain ⟨rq, aq, hqev, hqvis⟩ :=
    honest_anchor_sees_ins hH hq0 (hsub₁ _ hy.1)
  have hnc : ¬ SheshaD.toCRDTSig.commutes
      (q, rq, SAppOp.insA aq) (y, ry, SAppOp.insA q) :=
    ncomm_ins_anchor_child hq0 (honest_ins_ne_anchor hH hqev)
  exact ⟨rq, aq, hclosed₁ _ _ hqvis hnc hy.1, hclosed₂ _ _ hqvis hnc hy.2⟩

/-- One row step of the lift: a common insert's row owner in a branch
forest is the root or itself a common insert. -/
theorem row_step {C : Configuration SheshaD} (hH : SheshaHonest C)
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events)
    (hclosed₁ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T : Shesha.St}
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn ev₁ x p)
    {c q : Nat} (hcq : c ∈ Shesha.row T q)
    (hc : ∃ rc ac, (c, rc, SAppOp.insA ac) ∈ ev₁ ∩ ev₂) :
    q = 0 ∨ ∃ rq aq, (q, rq, SAppOp.insA aq) ∈ ev₁ ∩ ev₂ := by
  obtain ⟨rc, ac, hcm⟩ := hc
  obtain ⟨r', hcm'⟩ := (hrows q c).mp hcq
  have heq : ((c, r', SAppOp.insA q) : Op SAppOp)
      = (c, rc, SAppOp.insA ac) :=
    (Configuration.core C).ts_unique (hsub₁ _ hcm') (hsub₁ _ hcm.1) rfl
  have hq_ac : q = ac := by
    injection heq with h1 h2
    injection h2 with h3 h4
    injection h4 with h5
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · refine Or.inr (anchor_lift hH hsub₁ hclosed₁ hclosed₂
      (y := c) (ry := rc) ?_ hq0)
    rw [hq_ac]
    exact hcm

/-- **Chain lift**: climbing a dead-descent chain of a branch forest from
a common insert reaches the root or a common insert — the intermediates
are deleted (hence nonzero, hence anchored inserts) and the closure pulls
each anchor into the common past. -/
theorem chain_lift {C : Configuration SheshaD} (hH : SheshaHonest C)
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events)
    (hclosed₁ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T : Shesha.St} {D : Nat → Bool}
    (hrows : ∀ p x, x ∈ Shesha.row T p ↔ InsIn ev₁ x p)
    (hDdel : ∀ u, D u = true → DelIn ev₁ u)
    {q w : Nat} (hch : Shesha.RowChain T D q w)
    (hw : ∃ rw aw, (w, rw, SAppOp.insA aw) ∈ ev₁ ∩ ev₂) :
    q = 0 ∨ ∃ rq aq, (q, rq, SAppOp.insA aq) ∈ ev₁ ∩ ev₂ := by
  induction hch with
  | direct hwq =>
      exact row_step hH hsub₁ hclosed₁ hclosed₂ hrows hwq hw
  | @through q c w' hcq hDc hsub ih =>
      rcases ih hw with hc0 | hc
      · obtain ⟨td, rd, hdm⟩ := hDdel c hDc
        exact absurd (hc0 ▸ honest_del_nonzero hH (hsub₁ _ hdm)) (fun f => f rfl)
      · exact row_step hH hsub₁ hclosed₁ hclosed₂ hrows hcq hc

open Classical in
/-- **`ModelOK` at the join**: the three normal-form slots satisfy the
M0–M2 model hypotheses — well-formed, with common liveness. -/
theorem slots_modelOK {C : Configuration SheshaD}
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events) (hsub₂ : ∀ a ∈ ev₂, a ∈ C.events)
    {T₀ T₁ T₂ : Shesha.St}
    (hwf₀ : Shesha.WF T₀) (hwf₁ : Shesha.WF T₁) (hwf₂ : Shesha.WF T₂)
    (hreads₀ : ∀ u, u ∈ Shesha.read T₀ ↔ ∃ p, InsIn (ev₁ ∩ ev₂) u p)
    (hreads₁ : ∀ u, u ∈ Shesha.read T₁ ↔ ∃ p, InsIn ev₁ u p)
    (hreads₂ : ∀ u, u ∈ Shesha.read T₂ ↔ ∃ p, InsIn ev₂ u p) :
    Shesha.ModelOK
      (Shesha.dropF (fun u => decide (DelIn (ev₁ ∩ ev₂) u)) T₀)
      (Shesha.dropF (fun u => decide (DelIn ev₁ u)) T₁)
      (Shesha.dropF (fun u => decide (DelIn ev₂ u)) T₂) :=
  ⟨Shesha.wf_dropF hwf₀ _, Shesha.wf_dropF hwf₁ _, Shesha.wf_dropF hwf₂ _,
    fun u hA hB => (read_nf hreads₀ u).mpr
      (nf_common hsub₁ hsub₂
        ((read_nf hreads₁ u).mp hA) ((read_nf hreads₂ u).mp hB))⟩

open Classical in
/-- **`LRowsOK` at the join**: in a branch slot, an LCA-live node's row
owner is the root or LCA-live — via the dead-descent chain and the
anchor-chain closure. -/
theorem slots_LRowsOK {C : Configuration SheshaD} (hH : SheshaHonest C)
    {ev₁ ev₂ : Set (Op SAppOp)}
    (hsub₁ : ∀ a ∈ ev₁, a ∈ C.events)
    (hclosed₁ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₁ → a ∈ ev₁)
    (hclosed₂ : ∀ a b, C.vis a b → ¬ SheshaD.toCRDTSig.commutes a b →
      b ∈ ev₂ → a ∈ ev₂)
    {T₀ TX : Shesha.St} (hwfX : Shesha.WF TX)
    (hreads₀ : ∀ u, u ∈ Shesha.read T₀ ↔ ∃ p, InsIn (ev₁ ∩ ev₂) u p)
    (hrowsX : ∀ p x, x ∈ Shesha.row TX p ↔ InsIn ev₁ x p) :
    Shesha.LRowsOK
      (Shesha.dropF (fun u => decide (DelIn (ev₁ ∩ ev₂) u)) T₀)
      (Shesha.dropF (fun u => decide (DelIn ev₁ u)) TX) := by
  intro w q hwL hwX
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · have hqX : q ∈ Shesha.read
        (Shesha.dropF (fun u => decide (DelIn ev₁ u)) TX) :=
      Shesha.row_parent_mem hq0 hwX
    have hqD : decide (DelIn ev₁ q) = false := by
      rw [Shesha.read_dropF, List.mem_filter] at hqX
      rcases hd : decide (DelIn ev₁ q) with _ | _
      · rfl
      · rw [hd] at hqX
        rcases hqX with ⟨-, hc⟩
        cases hc
    have hch := Shesha.mem_row_dropF hwfX hqD hwX
    have hwc := (read_nf hreads₀ w).mp hwL
    obtain ⟨p, rw', hwm⟩ := hwc.1
    rcases chain_lift hH hsub₁ hclosed₁ hclosed₂ hrowsX
        (fun u hu => of_decide_eq_true hu) hch ⟨rw', p, hwm⟩ with
      h0 | ⟨rq, aq, hqm⟩
    · exact Or.inl h0
    · refine Or.inr ((read_nf hreads₀ q).mpr ⟨⟨aq, rq, hqm⟩, ?_⟩)
      rintro ⟨t, r, hdm⟩
      have : decide (DelIn ev₁ q) = true := decide_eq_true ⟨t, r, hdm.1⟩
      rw [hqD] at this
      cases this

end Sal.ConditionedMRDTs
