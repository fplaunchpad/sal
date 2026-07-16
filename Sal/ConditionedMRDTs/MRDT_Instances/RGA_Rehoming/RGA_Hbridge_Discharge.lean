import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_HEnum_Discharge
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeCanon_Fix
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_BranchCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_FiltEq

/-!
# hbridge DISCHARGED — per-survivor `CanonBirthBridge` from the join context

*Additive; modifies no existing file; 0 `sorry`.*

The per-survivor bridge of `hMergeInputs`, discharged at `HonJ := rgaHonJ` GIVEN the sibling
`hcaus` bundle (the per-id causal set-algebra — a separate leaf; its merge-domain consequence
`merge_domain_clause` is what identifies the merge survivor set with the union-fold domain).

The assembly, per union-survivor `t` with recorded chain `a :: p`:

1. **Home determination.**  `t`'s insert lives in `ρ₀`, `ρ₁`, or `ρ₂`; whichever fold contains
   `t` first in `birthAnc`'s if-chain is `t`'s *home*, and `birthAnc … t = anc σ_home t`.
   A survivor is never union-deleted, hence never home-deleted, so `t` is home-live and its
   home `CanonInv` gives the home `LiveChain`: `anc σ_home t` heads `liveSub σ_home (a :: p)`.
2. **Home-dead ⟹ F-dead** (`home_dead_F_dead`).  Recorded-chain entries are dependencies of
   `t`'s insert (`chain_entries_mem` at the ambient enumeration); a survivor's dependencies land
   in its home enum by causal closure (`hdepsh`), so a home-dead entry is home-DELETED, hence
   union-deleted, hence `¬ survP F`.
3. **`liveSub σ_home (a :: p) = []`** — the birth anchor is `0`: the whole record is `F`-dead
   (`liveSub_nil_all_dead` + step 2), so `canonAnc F (a :: p) = 0` (`canonAnc_dead_eq_zero`)
   and `CanonBirthBridge` holds directly (the live half is vacuous at the unstored root).
4. **`liveSub σ_home (a :: p) = bw :: _`** — split the record at `bw` (`first_live_split`;
   the prefix is home-dead, hence `F`-dead by step 2) and close with
   `canonBirthBridge_via_branchCanon`, whose `hin` is the discharged record-coherence kernel
   `hin_of_genDisc` and whose `hD` is `merge_domain_clause` + the union-fold `CanonMatch`.

Everything runs at the ambient `E := ev₁ ∪ ev₂` (listable as `ρ₀ ++ π₀`; `GenDisc2C` restricts
from `events` exactly as in the `hEnum` discharge).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGAK1Delta

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.ConditionedMRDTs.RGADeltaEnum (exists_min_of_irrefl_trans)
open Sal.ConditionedMRDTs.ConditionedExecutionModel.ConditionedConfiguration (exists_respecting)
open Sal.ConditionedMRDTs.RGAMergeCanon (merge_domain_clause)
open RGABranchCanon (canonBirthBridge_via_branchCanon)
open RGACanonBirthBridge (canonAnc_neg)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonInv CanonFoldOK canonAnc survP insertedIn deletedIn CanonMatch)
open RGAMergeFoldChain (CanonBirthBridge)
open Sal.ConditionedMRDTs.RGACanonFoldOK

/-! ## §1  Small bricks -/

/-- Two Booleans agreeing on truth are equal. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `canonAnc` of an all-`F`-dead chain is the root. -/
theorem canonAnc_dead_eq_zero (F : List (op_t α)) :
    ∀ L : List ℕ, (∀ c ∈ L, ¬ survP F c) → canonAnc F L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hdead
    rw [canonAnc_neg F c cs (hdead c (by simp))]
    exact ih fun c' hc' => hdead c' (List.mem_cons_of_mem c hc')

/-- An empty live-filter means every entry is dead. -/
theorem liveSub_nil_all_dead (s : concrete_st α) :
    ∀ L : List ℕ, liveSub s L = [] → ∀ c ∈ L, contains s c = false := by
  intro L
  induction L with
  | nil => intro _ c hc; simp at hc
  | cons q qs ih =>
    intro h c hc
    cases hq : contains s q with
    | true =>
      exfalso
      have hstep : liveSub s (q :: qs) = q :: liveSub s qs := by
        simp only [liveSub, List.filter_cons]
        rw [if_pos hq]
      rw [hstep] at h
      exact List.cons_ne_nil _ _ h
    | false =>
      have hqne : ¬ contains s q = true := by rw [hq]; simp
      have hstep : liveSub s (q :: qs) = liveSub s qs := by
        simp only [liveSub, List.filter_cons]
        rw [if_neg hqne]
      rw [hstep] at h
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hq
      · exact ih h c hc'

/-- **Split a chain at its first live entry**: the prefix is all-dead. -/
theorem first_live_split (s : concrete_st α) :
    ∀ (L : List ℕ) (b : ℕ) (rest : List ℕ), liveSub s L = b :: rest →
      ∃ pre suf, L = pre ++ b :: suf ∧ (∀ c ∈ pre, contains s c = false) ∧
        liveSub s suf = rest := by
  intro L
  induction L with
  | nil => intro b rest h; exact absurd h (by simp [liveSub])
  | cons q qs ih =>
    intro b rest h
    cases hq : contains s q with
    | true =>
      have hstep : liveSub s (q :: qs) = q :: liveSub s qs := by
        simp only [liveSub, List.filter_cons]
        rw [if_pos hq]
      rw [hstep] at h
      injection h with hqb hrest
      subst hqb
      exact ⟨[], qs, rfl, by simp, hrest⟩
    | false =>
      have hqne : ¬ contains s q = true := by rw [hq]; simp
      have hstep : liveSub s (q :: qs) = liveSub s qs := by
        simp only [liveSub, List.filter_cons]
        rw [if_neg hqne]
      rw [hstep] at h
      obtain ⟨pre, suf, hL, hpre, hsuf⟩ := ih b rest h
      refine ⟨q :: pre, suf, by rw [hL]; rfl, ?_, hsuf⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hq
      · exact hpre c hc'

/-! ## §2  Home-dead chain entries are F-dead (shared across the three homes) -/

/-- A survivor's home-dead recorded-chain entries are union-dead: chain entries are dependencies
of the insert (`chain_entries_mem` at the ambient enumeration); a survivor's dependencies land in
its home enum by causal closure (`hdepsh`), so home-dead means home-DELETED, hence union-deleted. -/
theorem home_dead_F_dead (Cfg : Sal.Emulation.Configuration (RGACondSig α).toCRDTSig)
    (E : Set (op_t α))
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (U : List (op_t α)) (hUp : listPermOf U E)
    (hUr : respects U (loOnA (RGACondSig α) Cfg E))
    (F : List (op_t α)) (hFp : listPermOf F E)
    (ρh : List (op_t α)) (hρhsub : ∀ x ∈ ρh, x ∈ E)
    (hinvh : CanonInv ρh (applySeqR (init_st (α := α)) ρh))
    (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ) (htE : (t, r, app_op_t.Ins e p a) ∈ E)
    (hdepsh : ∀ z : op_t α, z ∈ E → z ≠ (t, r, app_op_t.Ins e p a) →
        DepC Cfg E z (t, r, app_op_t.Ins e p a) → z ∈ ρh) :
    ∀ c ∈ a :: p, contains (applySeqR (init_st (α := α)) ρh) c = false → ¬ survP F c := by
  intro c hc hcdead hsvF
  rcases chain_entries_mem Cfg E hGen U (goodEnum_of_perm Cfg E U hUp hUr)
      t r e a p ((hUp.2 _).mpr htE) c hc with h0 | hins
  · -- the root is never the id of an event
    obtain ⟨r', e', p', a', hm'⟩ := hsvF.1
    exact hids0 _ ((hFp.2 _).mp hm') (h0 ▸ rfl)
  · -- a dependency of the insert lives in the home enum, so home-dead ⟹ home-deleted ⟹ F-dead
    obtain ⟨r', e', p', a', hm'⟩ := hins
    obtain ⟨hxU, hxne, hxdep⟩ := mem_depList.mp hm'
    have hinρh : (c, r', app_op_t.Ins e' p' a') ∈ ρh :=
      hdepsh _ ((hUp.2 _).mp hxU) hxne hxdep
    have hinsh : insertedIn ρh c := ⟨r', e', p', a', hinρh⟩
    have hnsvh : ¬ survP ρh c := fun hs => by
      have hlive := (hinvh.2.2.1 c).mpr hs
      rw [hcdead] at hlive
      exact Bool.noConfusion hlive
    have hdel : deletedIn ρh c := by
      by_contra hnd
      exact hnsvh ⟨hinsh, hnd⟩
    obtain ⟨t', r'', p'', hm''⟩ := hdel
    have hdelF : (t', r'', app_op_t.Del p'' c) ∈ F :=
      (hFp.2 _).mpr (hρhsub _ hm'')
    exact hsvF.2 ⟨t', r'', p'', hdelF⟩

/-! ## §3  The per-survivor bridge -/

/-- **hbridge, discharged at `HonJ := rgaHonJ`** — GIVEN the sibling `hcaus` bundle (the per-id
causal set-algebra, a separate `hMergeInputs` leaf): per union-survivor `CanonBirthBridge`. -/
theorem rga_hbridge_discharged
    (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α))
    (hHonJ : rgaHonJ vis events)
    (htr : ∀ {a b c : op_t α}, vis a b → vis b c → vis a c) (hirr : ∀ a : op_t α, ¬ vis a a)
    (hdts : ∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hev1 : ∀ a ∈ ev₁, a ∈ events) (hev2 : ∀ a ∈ ev₂, a ∈ events)
    (hcl1 : fullClosureRel (D := (RGACondSig' α)) vis ev₁)
    (hcl2 : fullClosureRel (D := (RGACondSig' α)) vis ev₂)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂)) (h₁p : listPermOf ρ₁ ev₁) (h₂p : listPermOf ρ₂ ev₂)
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (h₀OK : CanonFoldOK [] (init_st (α := α)) ρ₀) (h₁OK : CanonFoldOK [] (init_st (α := α)) ρ₁)
    (h₂OK : CanonFoldOK [] (init_st (α := α)) ρ₂)
    (hπOK : CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀)
    (hcaus : ∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
        ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
        ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
        ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
        ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c)) :
    ∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ),
      (t, r, app_op_t.Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
      CanonBirthBridge (applySeqR (init_st (α := α)) ρ₀) (ρ₀ ++ π₀)
        (birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t)
        (a :: p) := by
  intro t r e a p htF hsvF
  obtain ⟨Cfg, hviseq, hGenE, hids0E, _hmono, _hdel0⟩ := hHonJ
  -- ambient E := ev₁ ∪ ev₂ and its restricted facts (as in the hEnum discharge)
  have hUmem : ∀ x ∈ ev₁ ∪ ev₂, x ∈ events := by
    intro x hx
    rcases hx with h | h
    · exact hev1 x h
    · exact hev2 x h
  have hdts' : ∀ a b : op_t α, a ∈ ev₁ ∪ ev₂ → b ∈ ev₁ ∪ ev₂ → a ≠ b → a.1 ≠ b.1 :=
    fun a b ha hb => hdts a b (hUmem a ha) (hUmem b hb)
  have hids0' : ∀ x ∈ ev₁ ∪ ev₂, x.1 ≠ 0 := fun x hx => hids0E x (hUmem x hx)
  have htr' : ∀ {a b c : op_t α}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c := by
    intro a b c h1 h2
    have h1' := (hviseq a b).mp h1
    have h2' := (hviseq b c).mp h2
    exact (hviseq a c).mpr ⟨htr h1'.1 h2'.1, h1'.2.1, h2'.2.2⟩
  have hirr' : ∀ a : op_t α, ¬ Cfg.vis a a :=
    fun a h => hirr a ((hviseq a a).mp h).1
  have hGen' : GenDisc2C Cfg (ev₁ ∪ ev₂) := by
    intro o ho d hd
    refine hGenE o (hUmem o ho) d
      (isDepPreC_of_restrict Cfg events (ev₁ ∪ ev₂) hUmem ?_ o ho d hd)
    intro x hx z _hz hlo
    have hv' := (hviseq z x).mp (loOnA_imp_vis Cfg events z x hlo)
    rcases hx with h | h
    · exact Set.mem_union_left _ (hcl1 z x hv'.1 h)
    · exact Set.mem_union_right _ (hcl2 z x hv'.1 h)
  -- the union listing ρ₀ ++ π₀ is a perm of E
  have hmemρ : ∀ x ∈ ρ₀, x ∈ ev₁ ∩ ev₂ := fun x hx => (h₀p.2 x).mp hx
  have hmemπ : ∀ x ∈ π₀, x ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) := fun x hx => (hπp.2 x).mp hx
  have hFp : listPermOf (ρ₀ ++ π₀) (ev₁ ∪ ev₂) := by
    refine ⟨?_, ?_⟩
    · refine List.nodup_append.mpr ⟨h₀p.1, hπp.1, ?_⟩
      intro x hx y hy heq
      exact (hmemπ y hy).2 (heq ▸ hmemρ x hx)
    · intro x
      rw [List.mem_append]
      constructor
      · rintro (h | h)
        · exact Set.mem_union_left _ (hmemρ x h).1
        · exact (hmemπ x h).1
      · intro hx
        by_cases hI : x ∈ ev₁ ∩ ev₂
        · exact Or.inl ((h₀p.2 x).mpr hI)
        · exact Or.inr ((hπp.2 x).mpr ⟨hx, hI⟩)
  -- a loOnA-respecting ambient enumeration of E
  obtain ⟨U, hUperm, hUpw⟩ := exists_respecting Cfg.vis (ρ₀ ++ π₀).length (ρ₀ ++ π₀) rfl
    (fun l' _ hne => exists_min_of_irrefl_trans Cfg.vis (@htr') hirr' l' hne)
  have hUp : listPermOf U (ev₁ ∪ ev₂) :=
    ⟨hUperm.nodup_iff.mpr hFp.1, fun x => by rw [hUperm.mem_iff]; exact hFp.2 x⟩
  have hUr : respects U (loOnA (RGACondSig α) Cfg (ev₁ ∪ ev₂)) :=
    hUpw.imp (fun hn hlo => hn (loOnA_imp_vis Cfg _ _ _ hlo))
  -- canonical invariants at the four folds
  have hinv0 : CanonInv ρ₀ (applySeqR (init_st (α := α)) ρ₀) := by
    have h := RGACanonConvergence.canon_fold ρ₀ [] (init_st (α := α))
      RGACanonConvergence.canonInv_init h₀OK
    rwa [List.nil_append] at h
  have hinv1 : CanonInv ρ₁ (applySeqR (init_st (α := α)) ρ₁) := by
    have h := RGACanonConvergence.canon_fold ρ₁ [] (init_st (α := α))
      RGACanonConvergence.canonInv_init h₁OK
    rwa [List.nil_append] at h
  have hinv2 : CanonInv ρ₂ (applySeqR (init_st (α := α)) ρ₂) := by
    have h := RGACanonConvergence.canon_fold ρ₂ [] (init_st (α := α))
      RGACanonConvergence.canonInv_init h₂OK
    rwa [List.nil_append] at h
  have hcatOK : CanonFoldOK [] (init_st (α := α)) (ρ₀ ++ π₀) :=
    Sal.ConditionedMRDTs.RGACorrectedResidual.canonFoldOK_concat ρ₀ [] (init_st (α := α)) π₀ h₀OK hπOK
  have hinvF : CanonInv (ρ₀ ++ π₀) (applySeqR (init_st (α := α)) (ρ₀ ++ π₀)) := by
    have h := RGACanonConvergence.canon_fold (ρ₀ ++ π₀) [] (init_st (α := α))
      RGACanonConvergence.canonInv_init hcatOK
    rwa [List.nil_append] at h
  have hcmF : CanonMatch (ρ₀ ++ π₀) (applySeqR (init_st (α := α)) (ρ₀ ++ π₀)) :=
    RGACanonConvergence.canonMatch_of_canonInv (ρ₀ ++ π₀) _ hinvF
  have htE : (t, r, app_op_t.Ins e p a) ∈ ev₁ ∪ ev₂ := (hFp.2 _).mp htF
  -- op identity by id-uniqueness
  have hopEq : ∀ {o o' : op_t α}, o ∈ ev₁ ∪ ev₂ → o' ∈ ev₁ ∪ ev₂ → o.1 = o'.1 → o = o' := by
    intro o o' ho ho' hid
    by_contra hne
    exact hdts' o o' ho ho' hne hid
  -- part memberships and the survivor's never-deleted transfers
  have hsub0 : ∀ x ∈ ρ₀, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_left _ (hmemρ x hx).1
  have hsub1 : ∀ x ∈ ρ₁, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_left _ ((h₁p.2 x).mp hx)
  have hsub2 : ∀ x ∈ ρ₂, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_right _ ((h₂p.2 x).mp hx)
  have hnd_of_sub : ∀ ρ : List (op_t α), (∀ x ∈ ρ, x ∈ ev₁ ∪ ev₂) → ¬ deletedIn ρ t := by
    intro ρ hsub hdel
    obtain ⟨t', r', p', hm'⟩ := hdel
    exact hsvF.2 ⟨t', r', p', (hFp.2 _).mpr (hsub _ hm')⟩
  -- closures at the restricted visibility (for the record-coherence kernel)
  have hcl1' : ∀ x y : op_t α, Cfg.vis x y → y ∈ ev₁ → x ∈ ev₁ :=
    fun x y h hy => hcl1 x y ((hviseq x y).mp h).1 hy
  have hcl2' : ∀ x y : op_t α, Cfg.vis x y → y ∈ ev₂ → x ∈ ev₂ :=
    fun x y h hy => hcl2 x y ((hviseq x y).mp h).1 hy
  have hsubI : ∀ x ∈ ev₁ ∩ ev₂, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_left _ hx.1
  -- hD: the merge survivor set IS the union-fold domain (via the hcaus bundle)
  have hD : ∀ j, survivors (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
      (applySeqR (init_st (α := α)) ρ₂) j = contains (applySeqR (init_st (α := α)) (ρ₀ ++ π₀)) j := by
    intro j
    obtain ⟨hI0, hD1I, hD2I, hD01, hD02, hIu, hDu⟩ := hcaus j
    have hdomm := merge_domain_clause (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
      (applySeqR (init_st (α := α)) ρ₂) ρ₀ π₀ ρ₁ ρ₂ j
      (hinv0.2.2.1 j) (hinv1.2.2.1 j) (hinv2.2.2.1 j) hI0 hD1I hD2I hD01 hD02 hIu hDu
    rw [contains_merge] at hdomm
    exact bool_eq_of_iff (hdomm.trans (hcmF.1 j).symm)
  -- the generic home argument: t home-live with its insert and dependencies in ρ_home
  have hbridge_from_home : ∀ ρh : List (op_t α),
      (∀ x ∈ ρh, x ∈ ev₁ ∪ ev₂) →
      CanonFoldOK [] (init_st (α := α)) ρh →
      (t, r, app_op_t.Ins e p a) ∈ ρh →
      (∀ z : op_t α, z ∈ ev₁ ∪ ev₂ → z ≠ (t, r, app_op_t.Ins e p a) →
          DepC Cfg (ev₁ ∪ ev₂) z (t, r, app_op_t.Ins e p a) → z ∈ ρh) →
      birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t
        = anc (applySeqR (init_st (α := α)) ρh) t →
      CanonBirthBridge (applySeqR (init_st (α := α)) ρ₀) (ρ₀ ++ π₀)
        (birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t)
        (a :: p) := by
    intro ρh hρhsub hhOK htρh hdepsh hba
    have hinvh : CanonInv ρh (applySeqR (init_st (α := α)) ρh) := by
      have h := RGACanonConvergence.canon_fold ρh [] (init_st (α := α))
        RGACanonConvergence.canonInv_init hhOK
      rwa [List.nil_append] at h
    have hdead := home_dead_F_dead Cfg (ev₁ ∪ ev₂) hids0' hGen' U hUp hUr
      (ρ₀ ++ π₀) hFp ρh hρhsub hinvh t r e a p htE hdepsh
    -- t's home LiveChain
    have hsvh : survP ρh t := ⟨⟨r, e, p, a, htρh⟩, hnd_of_sub ρh hρhsub⟩
    have hlc := (hinvh.2.2.2 t r e p a htρh hsvh).2
    have hlcPath : IsAncPath (applySeqR (init_st (α := α)) ρh) t
        (liveSub (applySeqR (init_st (α := α)) ρh) (a :: p)) := hlc.2.2
    cases hLS : liveSub (applySeqR (init_st (α := α)) ρh) (a :: p) with
    | nil =>
      -- birth anchor 0: the whole record is home-dead, canonAnc collapses to the root
      rw [hLS] at hlcPath
      have hanc0 : anc (applySeqR (init_st (α := α)) ρh) t = 0 := hlcPath
      have hAllDead : ∀ c ∈ a :: p, ¬ survP (ρ₀ ++ π₀) c := fun c hc =>
        hdead c hc (liveSub_nil_all_dead (applySeqR (init_st (α := α)) ρh) (a :: p) hLS c hc)
      rw [hba, hanc0]
      refine ⟨?_, ?_⟩
      · intro h0live
        rw [hinv0.1] at h0live
        exact absurd h0live (by simp)
      · intro _
        exact canonAnc_dead_eq_zero (ρ₀ ++ π₀) (a :: p) hAllDead
    | cons bw rest =>
      -- birth anchor bw ≠ 0: split the record and reduce through the branch canon
      rw [hLS] at hlcPath
      have hancbw : anc (applySeqR (init_st (α := α)) ρh) t = bw := hlcPath.1
      have hbwlive : contains (applySeqR (init_st (α := α)) ρh) bw = true := hlcPath.2.1
      have hbw0 : bw ≠ 0 := by
        rintro rfl
        rw [hinvh.1] at hbwlive
        exact absurd hbwlive (by simp)
      have hbaBW : birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
          (applySeqR (init_st (α := α)) ρ₂) t = bw := hba.trans hancbw
      obtain ⟨rcPre, rcSuf, hsplit, hpreDead, _⟩ :=
        first_live_split (applySeqR (init_st (α := α)) ρh) (a :: p) bw rest hLS
      have hpreDeadF : ∀ c ∈ rcPre, ¬ survP (ρ₀ ++ π₀) c := fun c hc =>
        hdead c (by rw [hsplit]; exact List.mem_append_left _ hc) (hpreDead c hc)
      have hsv : survivors (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
          (applySeqR (init_st (α := α)) ρ₂) t = true := by
        rw [hD t]
        exact (hcmF.1 t).mpr hsvF
      have hin : contains (applySeqR (init_st (α := α)) ρ₀) (birthAnc (applySeqR (init_st (α := α)) ρ₀)
          (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t) = true →
          ∃ cw, IsAncPath (applySeqR (init_st (α := α)) ρ₀) (birthAnc (applySeqR (init_st (α := α)) ρ₀)
            (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂) t) cw ∧
            canonAnc (ρ₀ ++ π₀) cw = canonAnc (ρ₀ ++ π₀) rcSuf := by
        rw [hbaBW]
        intro hbwσ
        exact hin_of_genDisc Cfg (ev₁ ∪ ev₂) hdts' hids0' hGen' htr' hirr' U hUp hUr
          ev₁ ev₂ hcl1' hcl2' hsubI ρ₀ (ρ₀ ++ π₀) h₀p hFp h₀OK t r e a p htE
          bw hbw0 rcPre rcSuf hsplit hbwσ
      exact canonBirthBridge_via_branchCanon (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
        (applySeqR (init_st (α := α)) ρ₂) (ρ₀ ++ π₀) (applySeqR (init_st (α := α)) (ρ₀ ++ π₀)) t
        (a :: p) rcPre rcSuf
        (fun y hy => hinv0.2.1 y hy) (fun y hy => hinv1.2.1 y hy)
        (fun y hy => hinv2.2.1 y hy)
        hD hcmF hsv (by rw [hbaBW]; exact hbw0) (by rw [hbaBW]; exact hsplit) hpreDeadF hin
  -- home determination: birthAnc's if-chain
  by_cases h0t : contains (applySeqR (init_st (α := α)) ρ₀) t = true
  · -- home = the LCA
    have hsv0 : survP ρ₀ t := (hinv0.2.2.1 t).mp h0t
    obtain ⟨r', e', p', a', hm⟩ := hsv0.1
    have heq : ((t, r', app_op_t.Ins e' p' a') : op_t α) = (t, r, app_op_t.Ins e p a) :=
      hopEq (hsub0 _ hm) htE rfl
    rw [heq] at hm
    have htI : (t, r, app_op_t.Ins e p a) ∈ ev₁ ∩ ev₂ := hmemρ _ hm
    have hba : birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
        (applySeqR (init_st (α := α)) ρ₂) t = anc (applySeqR (init_st (α := α)) ρ₀) t := by
      unfold birthAnc
      rw [if_pos h0t]
    refine hbridge_from_home ρ₀ hsub0 h₀OK hm ?_ hba
    intro z hz hzne hdep
    have hvz : Cfg.vis z (t, r, app_op_t.Ins e p a) :=
      depC_imp_vis Cfg (ev₁ ∪ ev₂) htr' _ _ hdep
    have hv : vis z (t, r, app_op_t.Ins e p a) := ((hviseq _ _).mp hvz).1
    exact (h₀p.2 z).mpr ⟨hcl1 z _ hv htI.1, hcl2 z _ hv htI.2⟩
  · by_cases h1t : contains (applySeqR (init_st (α := α)) ρ₁) t = true
    · -- home = branch 1
      have hsv1 : survP ρ₁ t := (hinv1.2.2.1 t).mp h1t
      obtain ⟨r', e', p', a', hm⟩ := hsv1.1
      have heq : ((t, r', app_op_t.Ins e' p' a') : op_t α) = (t, r, app_op_t.Ins e p a) :=
        hopEq (hsub1 _ hm) htE rfl
      rw [heq] at hm
      have htI1 : (t, r, app_op_t.Ins e p a) ∈ ev₁ := (h₁p.2 _).mp hm
      have hba : birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
          (applySeqR (init_st (α := α)) ρ₂) t = anc (applySeqR (init_st (α := α)) ρ₁) t := by
        unfold birthAnc
        rw [if_neg h0t, if_pos h1t]
      refine hbridge_from_home ρ₁ hsub1 h₁OK hm ?_ hba
      intro z hz hzne hdep
      have hvz : Cfg.vis z (t, r, app_op_t.Ins e p a) :=
        depC_imp_vis Cfg (ev₁ ∪ ev₂) htr' _ _ hdep
      have hv : vis z (t, r, app_op_t.Ins e p a) := ((hviseq _ _).mp hvz).1
      exact (h₁p.2 z).mpr (hcl1 z _ hv htI1)
    · -- home = branch 2 (forced: t's insert can live nowhere else)
      have hm2 : (t, r, app_op_t.Ins e p a) ∈ ρ₂ := by
        rcases List.mem_append.mp htF with h | h
        · exact absurd ((hinv0.2.2.1 t).mpr ⟨⟨r, e, p, a, h⟩, hnd_of_sub ρ₀ hsub0⟩) h0t
        · rcases (hmemπ _ h).1 with h1 | h2
          · exact absurd ((hinv1.2.2.1 t).mpr
              ⟨⟨r, e, p, a, (h₁p.2 _).mpr h1⟩, hnd_of_sub ρ₁ hsub1⟩) h1t
          · exact (h₂p.2 _).mpr h2
      have htI2 : (t, r, app_op_t.Ins e p a) ∈ ev₂ := (h₂p.2 _).mp hm2
      have hba : birthAnc (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁)
          (applySeqR (init_st (α := α)) ρ₂) t = anc (applySeqR (init_st (α := α)) ρ₂) t := by
        unfold birthAnc
        rw [if_neg h0t, if_neg h1t]
      refine hbridge_from_home ρ₂ hsub2 h₂OK hm2 ?_ hba
      intro z hz hzne hdep
      have hvz : Cfg.vis z (t, r, app_op_t.Ins e p a) :=
        depC_imp_vis Cfg (ev₁ ∪ ev₂) htr' _ _ hdep
      have hv : vis z (t, r, app_op_t.Ins e p a) := ((hviseq _ _).mp hvz).1
      exact (h₂p.2 z).mpr (hcl2 z _ hv htI2)

/-! ## Axiom audit -/

#print axioms bool_eq_of_iff
#print axioms canonAnc_dead_eq_zero
#print axioms liveSub_nil_all_dead
#print axioms first_live_split
#print axioms home_dead_F_dead
#print axioms rga_hbridge_discharged

end Sal.ConditionedMRDTs.RGAK1Delta
