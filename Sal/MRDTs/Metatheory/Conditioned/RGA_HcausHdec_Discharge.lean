import Sal.MRDTs.Metatheory.Conditioned.RGA_Hbridge_Discharge

/-!
# hcaus + Hdec DISCHARGED — hMergeInputs COMPLETE at `HonJ := rgaHonJ`

*Additive; modifies no existing file; 0 `sorry`.*

The two remaining `hMergeInputs` leaves, and the assembled `hMergeInputs` itself:

* **`rga_hcaus_discharged`** — the per-id causal set-algebra.  Five of the seven clauses are
  pure membership algebra over the enum perms (`ρ₀ ~ ev₁ ∩ ev₂` etc., with id-uniqueness
  identifying same-id inserts across branches).  The two with content — *a branch-deleted id is
  branch-inserted* — are dependency-fold provenance (`del_target_inserted`): the delete is
  `accurate` at its dependency fold (`GenDisc2C`, restricted to the branch), its target is
  nonzero (`rgaHonJ`'s no-root-deletes), so the target is LIVE there, and ids enter a fold only
  by their own `Ins` (`insertedIn_of_contains_fold`).
* **`rga_Hdec_discharged`** — σ₀ id-monotonicity, WITHOUT any fold induction: the stored anchor
  is `canonAnc` of the insert's recorded chain (`CanonMatch` at the LCA fold), `canonAnc` picks a
  chain entry or `0` (`canonAnc_mem`), chain entries are dependencies of the insert
  (`chain_entries_mem`), dependencies are `vis`-past (`depC_imp_vis`), and `vis` is
  Lamport-monotone (`rgaHonJ`'s clock clause).
* **`rga_hMergeInputs_discharged`** — `{Hdec, hcaus, hbridge}` assembled: the FULL
  `hMergeInputs` premise of `hCanon_of_leaves3`, at `HonJ := rgaHonJ`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGAK1Delta

open Sal.Emulation
open Sal.Metatheory.RGASig (RGACondSig)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open Sal.Metatheory.GenericEqQuotient (loOnEq fullClosureRel)
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.Metatheory.RGADeltaEnum (exists_min_of_irrefl_trans)
open Sal.Metatheory.ConditionedExecutionModel.ConditionedConfiguration (exists_respecting)
open RGACanonBirthBridge (canonAnc_pos canonAnc_neg)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonInv CanonFoldOK canonAnc survP insertedIn deletedIn CanonMatch)
open RGAMergeFoldChain (CanonBirthBridge)
open Sal.Metatheory.RGACanonFoldOK

/-! ## §1  Bricks -/

/-- `canonAnc` picks a chain entry or the root. -/
theorem canonAnc_mem (F : List op_t) :
    ∀ L : List ℕ, canonAnc F L = 0 ∨ canonAnc F L ∈ L := by
  intro L
  induction L with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    by_cases h : survP F c
    · right
      rw [canonAnc_pos F c cs h]
      simp
    · rw [canonAnc_neg F c cs h]
      rcases ih with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem c hm)

/-- **A deleted nonzero id is inserted** — dependency-fold provenance: the delete is `accurate`
at its dependency fold (`GenDisc2C`), so its nonzero target is live there, and ids enter a fold
only by their own `Ins`. -/
theorem del_target_inserted (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hGen : GenDisc2C Cfg E)
    (U : List op_t) (hUp : listPermOf U E)
    (hUr : respects U (loOnA RGACondSig Cfg E))
    (t' r' c : ℕ) (p' : List ℕ) (hdE : (t', r', app_op_t.Del p' c) ∈ E)
    (hc0 : c ≠ 0) :
    ∃ (rc ec : ℕ) (pc : List ℕ) (ac : ℕ), (c, rc, app_op_t.Ins ec pc ac) ∈ E := by
  have hpre := isDepPreC_depList Cfg E U (t', r', app_op_t.Del p' c)
    (fun x hx => (hUp.2 x).mp hx) hUp.1 hUr
    (fun z hz _ _ => (hUp.2 z).mpr hz)
  have hacc := hGen _ hdE _ hpre
  rcases hacc with ⟨h0, _⟩ | ⟨hlive, _⟩
  · exact absurd (show c = 0 by simpa using h0) hc0
  · have hins : insertedIn (depList Cfg E U (t', r', app_op_t.Del p' c)) c :=
      insertedIn_of_contains_fold _ c (by simpa using hlive)
    obtain ⟨rc, ec, pc, ac, hm⟩ := hins
    exact ⟨rc, ec, pc, ac, (hUp.2 _).mp (mem_depList.mp hm).1⟩

/-! ## §2  Hdec — σ₀ id-monotonicity, no fold induction -/

/-- **Hdec, discharged**: the LCA fold's stored anchors strictly decrease.  The anchor is
`canonAnc` of the recorded chain (`CanonMatch`); chain entries are dependencies of the insert;
dependencies are `vis`-past; `vis` is Lamport-monotone. -/
theorem rga_Hdec_discharged
    (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ : List op_t)
    (hHonJ : rgaHonJ vis events)
    (htr : ∀ {a b c : op_t}, vis a b → vis b c → vis a c) (hirr : ∀ a : op_t, ¬ vis a a)
    (hev1 : ∀ a ∈ ev₁, a ∈ events) (_hev2 : ∀ a ∈ ev₂, a ∈ events)
    (hcl1 : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl2 : fullClosureRel (D := RGACondSig') vis ev₂)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (h₀OK : CanonFoldOK [] init_st ρ₀) :
    ∀ y, contains (applySeqR init_st ρ₀) y = true → y ≠ 0 →
      anc (applySeqR init_st ρ₀) y < y := by
  obtain ⟨Cfg, hviseq, hGenE, _hids0, hmono, _hdel0⟩ := hHonJ
  have hsubI : ∀ x ∈ ev₁ ∩ ev₂, x ∈ events := fun x hx => hev1 _ hx.1
  have htr' : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c := by
    intro a b c h1 h2
    have h1' := (hviseq a b).mp h1
    have h2' := (hviseq b c).mp h2
    exact (hviseq a c).mpr ⟨htr h1'.1 h2'.1, h1'.2.1, h2'.2.2⟩
  have hirr' : ∀ a : op_t, ¬ Cfg.vis a a :=
    fun a h => hirr a ((hviseq a a).mp h).1
  have hGen0 : GenDisc2C Cfg (ev₁ ∩ ev₂) := by
    intro o ho d hd
    refine hGenE o (hsubI o ho) d
      (isDepPreC_of_restrict Cfg events (ev₁ ∩ ev₂) hsubI ?_ o ho d hd)
    intro x hx z _hz hlo
    have hv' := (hviseq z x).mp (loOnA_imp_vis Cfg events z x hlo)
    exact ⟨hcl1 z x hv'.1 hx.1, hcl2 z x hv'.1 hx.2⟩
  obtain ⟨U₀, hU₀perm, hU₀pw⟩ := exists_respecting Cfg.vis ρ₀.length ρ₀ rfl
    (fun l' _ hne => exists_min_of_irrefl_trans Cfg.vis (@htr') hirr' l' hne)
  have hU₀p : listPermOf U₀ (ev₁ ∩ ev₂) :=
    ⟨hU₀perm.nodup_iff.mpr h₀p.1, fun x => by rw [hU₀perm.mem_iff]; exact h₀p.2 x⟩
  have hU₀r : respects U₀ (loOnA RGACondSig Cfg (ev₁ ∩ ev₂)) :=
    hU₀pw.imp (fun hn hlo => hn (loOnA_imp_vis Cfg _ _ _ hlo))
  have hinv0 : CanonInv ρ₀ (applySeqR init_st ρ₀) := by
    have h := RGACanonConvergence.canon_fold ρ₀ [] init_st
      RGACanonConvergence.canonInv_init h₀OK
    rwa [List.nil_append] at h
  have hcm0 : CanonMatch ρ₀ (applySeqR init_st ρ₀) :=
    RGACanonConvergence.canonMatch_of_canonInv ρ₀ _ hinv0
  intro y hy hy0
  have hsvy : survP ρ₀ y := (hinv0.2.2.1 y).mp hy
  obtain ⟨ry, ey, py, ay, hmy⟩ := hsvy.1
  have hanc : anc (applySeqR init_st ρ₀) y = canonAnc ρ₀ (ay :: py) :=
    (hcm0.2 y ry ey py ay hmy hsvy).2
  rcases canonAnc_mem ρ₀ (ay :: py) with h0 | hmem
  · rw [hanc, h0]
    exact Nat.pos_of_ne_zero hy0
  · -- the picked anchor is a chain entry: a dependency of y's insert, hence Lamport-below y
    rcases chain_entries_mem Cfg (ev₁ ∩ ev₂) hGen0 U₀
        (goodEnum_of_perm Cfg (ev₁ ∩ ev₂) U₀ hU₀p hU₀r)
        y ry ey ay py ((hU₀p.2 _).mpr ((h₀p.2 _).mp hmy))
        (canonAnc ρ₀ (ay :: py)) hmem with hc0 | hcins
    · rw [hanc, hc0]
      exact Nat.pos_of_ne_zero hy0
    · obtain ⟨rc, ec, pc, ac, hmc⟩ := hcins
      obtain ⟨hcU, _hcne, hcdep⟩ := mem_depList.mp hmc
      have hvz := depC_imp_vis Cfg (ev₁ ∩ ev₂) htr' _ _ hcdep
      have hv := (hviseq _ _).mp hvz
      have hlt := hmono _ _ hv.2.1 hv.2.2 hv.1
      rw [hanc]
      exact hlt

/-! ## §3  hcaus — the per-id causal set-algebra -/

/-- **hcaus, discharged**: five clauses are membership algebra over the enum perms; the two
branch `del ⟹ ins` clauses are `del_target_inserted` at the branch's restricted discipline. -/
theorem rga_hcaus_discharged
    (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t)
    (hHonJ : rgaHonJ vis events)
    (htr : ∀ {a b c : op_t}, vis a b → vis b c → vis a c) (hirr : ∀ a : op_t, ¬ vis a a)
    (hdts : ∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hev1 : ∀ a ∈ ev₁, a ∈ events) (hev2 : ∀ a ∈ ev₂, a ∈ events)
    (hcl1 : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl2 : fullClosureRel (D := RGACondSig') vis ev₂)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂)) (h₁p : listPermOf ρ₁ ev₁) (h₂p : listPermOf ρ₂ ev₂)
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) :
    ∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
      ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
      ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
      ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
      ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c) := by
  obtain ⟨Cfg, hviseq, hGenE, _hids0, _hmono, hdel0⟩ := hHonJ
  have htr' : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c := by
    intro a b c h1 h2
    have h1' := (hviseq a b).mp h1
    have h2' := (hviseq b c).mp h2
    exact (hviseq a c).mpr ⟨htr h1'.1 h2'.1, h1'.2.1, h2'.2.2⟩
  have hirr' : ∀ a : op_t, ¬ Cfg.vis a a :=
    fun a h => hirr a ((hviseq a a).mp h).1
  -- restricted disciplines and sorted listings at the two branches
  have hGen1 : GenDisc2C Cfg ev₁ := by
    intro o ho d hd
    refine hGenE o (hev1 o ho) d
      (isDepPreC_of_restrict Cfg events ev₁ hev1 ?_ o ho d hd)
    intro x hx z _hz hlo
    have hv' := (hviseq z x).mp (loOnA_imp_vis Cfg events z x hlo)
    exact hcl1 z x hv'.1 hx
  have hGen2 : GenDisc2C Cfg ev₂ := by
    intro o ho d hd
    refine hGenE o (hev2 o ho) d
      (isDepPreC_of_restrict Cfg events ev₂ hev2 ?_ o ho d hd)
    intro x hx z _hz hlo
    have hv' := (hviseq z x).mp (loOnA_imp_vis Cfg events z x hlo)
    exact hcl2 z x hv'.1 hx
  obtain ⟨U₁, hU₁perm, hU₁pw⟩ := exists_respecting Cfg.vis ρ₁.length ρ₁ rfl
    (fun l' _ hne => exists_min_of_irrefl_trans Cfg.vis (@htr') hirr' l' hne)
  have hU₁p : listPermOf U₁ ev₁ :=
    ⟨hU₁perm.nodup_iff.mpr h₁p.1, fun x => by rw [hU₁perm.mem_iff]; exact h₁p.2 x⟩
  have hU₁r : respects U₁ (loOnA RGACondSig Cfg ev₁) :=
    hU₁pw.imp (fun hn hlo => hn (loOnA_imp_vis Cfg _ _ _ hlo))
  obtain ⟨U₂, hU₂perm, hU₂pw⟩ := exists_respecting Cfg.vis ρ₂.length ρ₂ rfl
    (fun l' _ hne => exists_min_of_irrefl_trans Cfg.vis (@htr') hirr' l' hne)
  have hU₂p : listPermOf U₂ ev₂ :=
    ⟨hU₂perm.nodup_iff.mpr h₂p.1, fun x => by rw [hU₂perm.mem_iff]; exact h₂p.2 x⟩
  have hU₂r : respects U₂ (loOnA RGACondSig Cfg ev₂) :=
    hU₂pw.imp (fun hn hlo => hn (loOnA_imp_vis Cfg _ _ _ hlo))
  -- union memberships and id-uniqueness
  have hFmem : ∀ x : op_t, x ∈ ρ₀ ++ π₀ ↔ x ∈ ev₁ ∪ ev₂ := by
    intro x
    rw [List.mem_append]
    constructor
    · rintro (h | h)
      · exact Set.mem_union_left _ ((h₀p.2 x).mp h).1
      · exact ((hπp.2 x).mp h).1
    · intro hx
      by_cases hI : x ∈ ev₁ ∩ ev₂
      · exact Or.inl ((h₀p.2 x).mpr hI)
      · exact Or.inr ((hπp.2 x).mpr ⟨hx, hI⟩)
  have hUmem : ∀ x ∈ ev₁ ∪ ev₂, x ∈ events := by
    intro x hx
    rcases hx with h | h
    · exact hev1 x h
    · exact hev2 x h
  have hopEq : ∀ {o o' : op_t}, o ∈ ev₁ ∪ ev₂ → o' ∈ ev₁ ∪ ev₂ → o.1 = o'.1 → o = o' := by
    intro o o' ho ho' hid
    by_contra hne
    exact hdts o o' (hUmem o ho) (hUmem o' ho') hne hid
  intro c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- LCA-inserted ↔ inserted in both branches
    constructor
    · rintro ⟨r0, e0, p0, a0, hm⟩
      have hI : (c, r0, app_op_t.Ins e0 p0 a0) ∈ ev₁ ∩ ev₂ := (h₀p.2 _).mp hm
      exact ⟨⟨r0, e0, p0, a0, (h₁p.2 _).mpr hI.1⟩, ⟨r0, e0, p0, a0, (h₂p.2 _).mpr hI.2⟩⟩
    · rintro ⟨⟨r1, e1, p1, a1, hm1⟩, ⟨r2, e2, p2, a2, hm2⟩⟩
      have h1E : (c, r1, app_op_t.Ins e1 p1 a1) ∈ ev₁ := (h₁p.2 _).mp hm1
      have h2E : (c, r2, app_op_t.Ins e2 p2 a2) ∈ ev₂ := (h₂p.2 _).mp hm2
      have heq : ((c, r2, app_op_t.Ins e2 p2 a2) : op_t) = (c, r1, app_op_t.Ins e1 p1 a1) :=
        hopEq (Set.mem_union_right _ h2E) (Set.mem_union_left _ h1E) rfl
      exact ⟨r1, e1, p1, a1, (h₀p.2 _).mpr ⟨h1E, heq ▸ h2E⟩⟩
  · -- branch-1 deleted ⟹ branch-1 inserted (provenance)
    rintro ⟨t', r', p', hm⟩
    have hdE : (t', r', app_op_t.Del p' c) ∈ ev₁ := (h₁p.2 _).mp hm
    have hc0 : c ≠ 0 := hdel0 t' r' c p' (hev1 _ hdE)
    obtain ⟨rc, ec, pc, ac, hmE⟩ :=
      del_target_inserted Cfg ev₁ hGen1 U₁ hU₁p hU₁r t' r' c p' hdE hc0
    exact ⟨rc, ec, pc, ac, (h₁p.2 _).mpr hmE⟩
  · -- branch-2 deleted ⟹ branch-2 inserted (provenance)
    rintro ⟨t', r', p', hm⟩
    have hdE : (t', r', app_op_t.Del p' c) ∈ ev₂ := (h₂p.2 _).mp hm
    have hc0 : c ≠ 0 := hdel0 t' r' c p' (hev2 _ hdE)
    obtain ⟨rc, ec, pc, ac, hmE⟩ :=
      del_target_inserted Cfg ev₂ hGen2 U₂ hU₂p hU₂r t' r' c p' hdE hc0
    exact ⟨rc, ec, pc, ac, (h₂p.2 _).mpr hmE⟩
  · -- LCA-deleted ⟹ branch-1 deleted
    rintro ⟨t', r', p', hm⟩
    exact ⟨t', r', p', (h₁p.2 _).mpr ((h₀p.2 _).mp hm).1⟩
  · -- LCA-deleted ⟹ branch-2 deleted
    rintro ⟨t', r', p', hm⟩
    exact ⟨t', r', p', (h₂p.2 _).mpr ((h₀p.2 _).mp hm).2⟩
  · -- union-inserted ↔ inserted in a branch
    constructor
    · rintro ⟨r0, e0, p0, a0, hm⟩
      rcases List.mem_append.mp hm with h | h
      · exact Or.inl ⟨r0, e0, p0, a0, (h₁p.2 _).mpr ((h₀p.2 _).mp h).1⟩
      · rcases ((hπp.2 _).mp h).1 with h1 | h2
        · exact Or.inl ⟨r0, e0, p0, a0, (h₁p.2 _).mpr h1⟩
        · exact Or.inr ⟨r0, e0, p0, a0, (h₂p.2 _).mpr h2⟩
    · rintro (⟨r1, e1, p1, a1, hm1⟩ | ⟨r2, e2, p2, a2, hm2⟩)
      · exact ⟨r1, e1, p1, a1,
          (hFmem _).mpr (Set.mem_union_left _ ((h₁p.2 _).mp hm1))⟩
      · exact ⟨r2, e2, p2, a2,
          (hFmem _).mpr (Set.mem_union_right _ ((h₂p.2 _).mp hm2))⟩
  · -- union-deleted ↔ deleted in a branch
    constructor
    · rintro ⟨t', r', p', hm⟩
      rcases List.mem_append.mp hm with h | h
      · exact Or.inl ⟨t', r', p', (h₁p.2 _).mpr ((h₀p.2 _).mp h).1⟩
      · rcases ((hπp.2 _).mp h).1 with h1 | h2
        · exact Or.inl ⟨t', r', p', (h₁p.2 _).mpr h1⟩
        · exact Or.inr ⟨t', r', p', (h₂p.2 _).mpr h2⟩
    · rintro (⟨t', r', p', hm1⟩ | ⟨t', r', p', hm2⟩)
      · exact ⟨t', r', p',
          (hFmem _).mpr (Set.mem_union_left _ ((h₁p.2 _).mp hm1))⟩
      · exact ⟨t', r', p',
          (hFmem _).mpr (Set.mem_union_right _ ((h₂p.2 _).mp hm2))⟩

/-! ## §4  hMergeInputs COMPLETE -/

/-- **The full `hMergeInputs` of `hCanon_of_leaves3`, discharged at `HonJ := rgaHonJ`**:
`{Hdec, hcaus, hbridge}` assembled from the three leaf discharges. -/
theorem rga_hMergeInputs_discharged :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        rgaHonJ vis events →
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ → CanonFoldOK [] init_st ρ₁ → CanonFoldOK [] init_st ρ₂ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        (∀ y, contains (applySeqR init_st ρ₀) y = true → y ≠ 0 →
            anc (applySeqR init_st ρ₀) y < y)
        ∧ (∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
            ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
            ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
            ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
            ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            CanonBirthBridge (applySeqR init_st ρ₀) (ρ₀ ++ π₀)
                (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁)
                  (applySeqR init_st ρ₂) t) (a :: p)) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hirr hdts hev1 hev2 hcl1 hcl2
    h₀p h₁p h₂p hπp _hπr h₀OK h₁OK h₂OK hπOK
  have hcaus := rga_hcaus_discharged vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hirr hdts
    hev1 hev2 hcl1 hcl2 h₀p h₁p h₂p hπp
  exact ⟨rga_Hdec_discharged vis events ev₁ ev₂ ρ₀ hHonJ htr hirr hev1 hev2 hcl1 hcl2
      h₀p h₀OK,
    hcaus,
    rga_hbridge_discharged vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hirr hdts hev1 hev2
      hcl1 hcl2 h₀p h₁p h₂p hπp h₀OK h₁OK h₂OK hπOK hcaus⟩

/-! ## Axiom audit -/

#print axioms canonAnc_mem
#print axioms del_target_inserted
#print axioms rga_Hdec_discharged
#print axioms rga_hcaus_discharged
#print axioms rga_hMergeInputs_discharged

end Sal.Metatheory.RGAK1Delta
