import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Skeleton3
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_GenDisc_Peel

/-!
# hEnum DISCHARGED — the delta enum from the join context

*Additive; modifies no existing file; 0 `sorry`.*

Skeleton 3's `hEnum` leaf, discharged at `HonJ := rgaHonJ`:

* `rgaHonJ vis events` — the RGA's join context: SOME configuration presents `(vis, events)`
  (its `vis` is exactly `vis` restricted to `events`-pairs) and satisfies the generation
  discipline + nonzero ids.  **At a real reachable config the witness is `C.core` itself**
  (`vis_src`/`vis_tgt` give the restriction for free), so no synthetic configuration is ever
  built — `hHon`'s eventual discharge is `genDisc2C_of_born` at the real core.
* `rga_hEnum_discharged` — the delta enumeration: list the delta from the branch enums, sort it
  by the configuration's `vis` (a strict order), and conclude:
  - `respects (loOnEq …)` at the bare `vis` — every backward `loOnEq` edge is a backward
    restricted-`vis` edge (`loOnEq_imp_vis` + membership);
  - `CanonFoldOK ρ₀ (fold ρ₀) π₀` — **K1** (`K1_canonFoldOK`), with `GenDisc2C` restricted from
    `events` to the union via `isDepPreC_of_restrict` (the union is closed under `loOnA`-preds).
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGAK1Delta

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.ConditionedMRDTs.RGALoOnEqCausal (loOnEq_imp_vis)
open Sal.ConditionedMRDTs.RGADeltaEnum (exists_min_of_irrefl_trans)
open Sal.ConditionedMRDTs.ConditionedExecutionModel.ConditionedConfiguration (exists_respecting)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonFoldOK)
open Sal.ConditionedMRDTs.RGACanonFoldOK

/-- **The RGA's join context.**  Some configuration presents `(vis, events)` — its visibility is
exactly `vis` restricted to `events`-pairs — and carries the generation discipline and nonzero
ids.  A real reachable config supplies its own core as the witness. -/
def rgaHonJ (vis : op_t → op_t → Prop) (events : Set op_t) : Prop :=
  ∃ Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig,
    (∀ a b : op_t, Cfg.vis a b ↔ (vis a b ∧ a ∈ events ∧ b ∈ events)) ∧
    GenDisc2C Cfg events ∧
    (∀ o ∈ events, o.1 ≠ 0) ∧
    (∀ a b : op_t, a ∈ events → b ∈ events → vis a b → a.1 < b.1) ∧
    (∀ (t r x : ℕ) (p : List ℕ), (t, r, app_op_t.Del p x) ∈ events → x ≠ 0)

/-- **Skeleton 3's `hEnum`, discharged at `HonJ := rgaHonJ`.** -/
theorem rga_hEnum_discharged :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        rgaHonJ vis events →
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ →
        fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          CanonFoldOK [] init_st ρ₀ →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          CanonFoldOK [] init_st ρ₁ →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          CanonFoldOK [] init_st ρ₂ →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ hHonJ htr hirr hdts hev1 hev2 hcl1 hcl2
    h₀p _h₀r h₀OK h₁p _h₁r _h₁OK h₂p _h₂r _h₂OK
  obtain ⟨Cfg, hviseq, hGen, hids0, _hmono, _hdel0⟩ := hHonJ
  -- union members are events
  have hUmem : ∀ x ∈ ev₁ ∪ ev₂, x ∈ events := by
    intro x hx
    rcases hx with h | h
    · exact hev1 x h
    · exact hev2 x h
  -- the delta listing, carved branchwise (the branch deltas are disjoint)
  set l₁ := ρ₁.filter (fun z => decide (z ∉ ev₁ ∩ ev₂)) with hl₁
  set l₂ := ρ₂.filter (fun z => decide (z ∉ ev₁ ∩ ev₂)) with hl₂
  have hmem1 : ∀ x, x ∈ l₁ ↔ x ∈ ev₁ ∧ x ∉ ev₁ ∩ ev₂ := by
    intro x
    rw [hl₁, List.mem_filter]
    constructor
    · rintro ⟨hx, hd⟩; exact ⟨(h₁p.2 x).mp hx, of_decide_eq_true hd⟩
    · rintro ⟨hx, hnI⟩; exact ⟨(h₁p.2 x).mpr hx, decide_eq_true hnI⟩
  have hmem2 : ∀ x, x ∈ l₂ ↔ x ∈ ev₂ ∧ x ∉ ev₁ ∩ ev₂ := by
    intro x
    rw [hl₂, List.mem_filter]
    constructor
    · rintro ⟨hx, hd⟩; exact ⟨(h₂p.2 x).mp hx, of_decide_eq_true hd⟩
    · rintro ⟨hx, hnI⟩; exact ⟨(h₂p.2 x).mpr hx, decide_eq_true hnI⟩
  have hmemD : ∀ x, x ∈ l₁ ++ l₂ ↔ x ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) := by
    intro x
    rw [List.mem_append]
    constructor
    · rintro (h | h)
      · exact ⟨Set.mem_union_left _ ((hmem1 x).mp h).1, ((hmem1 x).mp h).2⟩
      · exact ⟨Set.mem_union_right _ ((hmem2 x).mp h).1, ((hmem2 x).mp h).2⟩
    · rintro ⟨hu, hnI⟩
      rcases hu with h | h
      · exact Or.inl ((hmem1 x).mpr ⟨h, hnI⟩)
      · exact Or.inr ((hmem2 x).mpr ⟨h, hnI⟩)
  have hndD : (l₁ ++ l₂).Nodup := by
    refine List.nodup_append.mpr ⟨h₁p.1.filter _, h₂p.1.filter _, ?_⟩
    intro a ha b hb heq
    subst heq
    exact ((hmem1 a).mp ha).2 ⟨((hmem1 a).mp ha).1, ((hmem2 a).mp hb).1⟩
  -- the restricted visibility is a strict order
  have htr' : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c := by
    intro a b c h1 h2
    have h1' := (hviseq a b).mp h1
    have h2' := (hviseq b c).mp h2
    exact (hviseq a c).mpr ⟨htr h1'.1 h2'.1, h1'.2.1, h2'.2.2⟩
  have hirr' : ∀ a : op_t, ¬ Cfg.vis a a :=
    fun a h => hirr a ((hviseq a a).mp h).1
  -- sort the delta by the restricted visibility
  obtain ⟨π₀, hπperm, hπpw⟩ := exists_respecting Cfg.vis (l₁ ++ l₂).length (l₁ ++ l₂) rfl
    (fun l' _ hne => exists_min_of_irrefl_trans Cfg.vis (@htr') hirr' l' hne)
  have hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) :=
    ⟨hπperm.nodup_iff.mpr hndD, fun a => by rw [hπperm.mem_iff]; exact hmemD a⟩
  have hDev : ∀ x ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂), x ∈ events := fun x hx => hUmem x hx.1
  refine ⟨π₀, hπp, ?_, ?_⟩
  · -- respects loOnEq at the bare vis
    refine hπpw.imp_of_mem ?_
    intro a b ha hb hn hlo
    have haE : a ∈ events := hDev a ((hπp.2 a).mp ha)
    have hbE : b ∈ events := hDev b ((hπp.2 b).mp hb)
    have hvba : vis b a := loOnEq_imp_vis WfOpA vis _ b a hlo
    exact hn ((hviseq b a).mpr ⟨hvba, hbE, haE⟩)
  · -- K1: the delta discipline continued from the LCA fold
    have hcl1' : ∀ a b : op_t, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁ :=
      fun a b h hb => hcl1 a b ((hviseq a b).mp h).1 hb
    have hcl2' : ∀ a b : op_t, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂ :=
      fun a b h hb => hcl2 a b ((hviseq a b).mp h).1 hb
    have hdts' : ∀ a b : op_t, a ∈ ev₁ ∪ ev₂ → b ∈ ev₁ ∪ ev₂ → a ≠ b → a.1 ≠ b.1 :=
      fun a b ha hb => hdts a b (hUmem a ha) (hUmem b hb)
    have hids0' : ∀ x ∈ ev₁ ∪ ev₂, x.1 ≠ 0 := fun x hx => hids0 x (hUmem x hx)
    -- the union is loOnA-pred-closed in events, so the discipline restricts
    have hGen' : GenDisc2C Cfg (ev₁ ∪ ev₂) := by
      intro o ho d hd
      refine hGen o (hUmem o ho) d
        (isDepPreC_of_restrict Cfg events (ev₁ ∪ ev₂) hUmem ?_ o ho d hd)
      intro x hx z _hz hlo
      have hvis := loOnA_imp_vis Cfg events z x hlo
      have hv' := (hviseq z x).mp hvis
      rcases hx with h | h
      · exact Set.mem_union_left _ (hcl1 z x hv'.1 h)
      · exact Set.mem_union_right _ (hcl2 z x hv'.1 h)
    have hπrA : respects π₀ (loOnA RGACondSig Cfg (ev₁ ∪ ev₂)) :=
      hπpw.imp (fun hn hlo => hn (loOnA_imp_vis Cfg _ _ _ hlo))
    exact K1_canonFoldOK Cfg ev₁ ev₂ htr' hirr' hcl1' hcl2' hdts' hids0' hGen'
      ρ₀ π₀ h₀p hπp hπrA h₀OK

/-! ## Axiom audit -/

#print axioms rga_hEnum_discharged

end Sal.ConditionedMRDTs.RGAK1Delta
