import Sal.MRDTs.Metatheory.Development.RGA_GenDisc_Assembly

/-!
# hFiltEq DISCHARGED — record coherence from the generation discipline

*Additive; modifies no existing file; 0 `sorry`.*

The last deep leaf of the raw-≈ capstone: for a union survivor `t` with recorded chain `a :: p`
split at an LCA-live birth anchor `bw`, the recorded suffix and `bw`'s own LCA chain have the same
first-`F`-survivor (`hin` of `canonBirthBridge_via_branchCanon`).

**The discovery that makes this a THEOREM of the existing stack, with no new engine invariant:**
the coherence statement is `F`-static (it never mentions a fold state), so it need only be
ESTABLISHED once — and the right place is `t`'s DEPENDENCY fold `s_d`, where the generation
discipline (`GenDisc2C`, discharged from born accuracy) makes `t`'s ENTIRE recorded chain live:

1. accuracy at `s_d` ⟹ `IsAncPath s_d a p` ⟹ the suffix after `bw` is a genuine `s_d`-chain of
   `bw` (`isAncPath_suffix`);
2. `bw` is an `s_d`-survivor, so `CanonInv` at the dep fold gives its `LiveChain`:
   `liveSub s_d (ab :: pb)` is ALSO `bw`'s `s_d`-chain — by `isAncPath_unique`,
   `rcSuf = liveSub s_d (ab :: pb)`;
3. entries dropped by the `s_d`-filter are dep-deleted ⟹ union-deleted ⟹ `¬ survP F`
   (`canonAnc_liveSub_of_deadF`) — so `canonAnc F rcSuf = canonAnc F (ab :: pb)`;
4. the same drop-argument at the LCA fold turns `bw`'s record into its σ₀' chain
   (`cw := liveSub σ₀' (ab :: pb)`, from `bw`'s LCA `LiveChain`), closing
   `canonAnc F cw = canonAnc F rcSuf`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGAK1Delta

open Sal.Emulation
open Sal.Metatheory.G2Probe (RGACondSig)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonInv canonAnc survP insertedIn deletedIn CanonFoldOK)
open Sal.Metatheory.RGACanonFoldOK

/-! ## §1  Chain surgery -/

/-- Every entry of a genuine ancestor chain is live. -/
theorem isAncPath_live (s : concrete_st) :
    ∀ (L : List ℕ) (x : ℕ), IsAncPath s x L → ∀ c ∈ L, contains s c = true := by
  intro L
  induction L with
  | nil => intro x _ c hc; simp at hc
  | cons q qs ih =>
    intro x h c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.2.1
    · exact ih q h.2.2 c hc

/-- The suffix of a genuine chain after any entry is that entry's genuine chain. -/
theorem isAncPath_suffix (s : concrete_st) :
    ∀ (l₁ l₂ : List ℕ) (x y : ℕ), IsAncPath s x (l₁ ++ y :: l₂) → IsAncPath s y l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ x y h; exact h.2.2
  | cons q l₁' ih => intro l₂ x y h; exact ih l₂ q y h.2.2

/-- **`canonAnc` sees through a live-filter whose drops are `F`-dead.** -/
theorem canonAnc_liveSub_of_deadF (F : List op_t) (s : concrete_st) :
    ∀ L : List ℕ, (∀ c ∈ L, contains s c = false → ¬ survP F c) →
      canonAnc F L = canonAnc F (liveSub s L) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hdead
    have htail := ih (fun c' hc' => hdead c' (List.mem_cons_of_mem c hc'))
    show canonAnc F (c :: cs) = canonAnc F ((c :: cs).filter (fun k => contains s k))
    rw [List.filter_cons]
    cases hc : contains s c with
    | true =>
      rw [if_pos (show (true : Bool) = true from rfl)]
      show (if survP F c then c else canonAnc F cs)
          = (if survP F c then c else canonAnc F (cs.filter (fun k => contains s k)))
      by_cases hsv : survP F c
      · rw [if_pos hsv, if_pos hsv]
      · rw [if_neg hsv, if_neg hsv]
        exact htail
    | false =>
      rw [if_neg (show ¬ (false : Bool) = true by simp)]
      have hnsv : ¬ survP F c := hdead c (by simp) hc
      show (if survP F c then c else canonAnc F cs) = _
      rw [if_neg hnsv]
      exact htail

/-! ## §2  Record coherence at the dependency fold -/

/-- Membership transfer: a dep of a dep is a dep. -/
theorem depList_trans_mem (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t, ¬ Cfg.vis a a)
    (U : List op_t) (w o : op_t) (hw : w ∈ depList Cfg E U o)
    (x : op_t) (hx : x ∈ depList Cfg E U w) : x ∈ depList Cfg E U o := by
  obtain ⟨hwU, hwo, hwdep⟩ := mem_depList.mp hw
  obtain ⟨hxU, hxw, hxdep⟩ := mem_depList.mp hx
  have hdep : DepC Cfg E x o := Relation.TransGen.trans hxdep hwdep
  have hxo : x ≠ o := by
    rintro rfl
    exact depC_irrefl Cfg E htr hirr _ (Relation.TransGen.trans hwdep hxdep)
  exact mem_depList.mpr ⟨hxU, hxo, hdep⟩

/-- **Record coherence.**  For a delivered insert `t` with `bw ≠ 0` on its recorded chain, the
first-`F`-survivor of the recorded suffix after `bw` equals that of `bw`'s own recorded chain —
established at `t`'s dependency fold, where the generation discipline makes the whole chain live. -/
theorem canonAnc_record_coherence (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t, ¬ Cfg.vis a a)
    (U : List op_t) (hUp : listPermOf U E)
    (hUr : respects U (loOnA RGACondSig Cfg E))
    (F : List op_t) (hFp : listPermOf F E)
    (t r e a : ℕ) (p : List ℕ) (htE : (t, r, app_op_t.Ins e p a) ∈ E)
    (bw rb eb ab : ℕ) (pb : List ℕ) (hbwF : (bw, rb, app_op_t.Ins eb pb ab) ∈ E)
    (hbw0 : bw ≠ 0)
    (rcPre rcSuf : List ℕ) (hsplit : a :: p = rcPre ++ bw :: rcSuf) :
    canonAnc F rcSuf = canonAnc F (ab :: pb) := by
  -- t's dependency package
  set d := depList Cfg E U (t, r, app_op_t.Ins e p a) with hd
  have hinvD : CanonInv d (applySeqR init_st d) :=
    canonInv_depList_of_perm Cfg E hdts hids0 hGen htr hirr U hUp hUr _
  have hacc : accurate (t, r, app_op_t.Ins e p a) (applySeqR init_st d) :=
    hGen _ htE d (isDepPreC_depList_of_perm Cfg E U hUp hUr _)
  set sD := applySeqR init_st d with hsD
  -- accuracy: the whole recorded chain is live at the dep fold
  simp only [accurate, opLeaf, opPath] at hacc
  rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
  · -- degenerate root record: `bw` would be `0`
    exfalso
    have : bw ∈ a :: p := hsplit ▸ List.mem_append_right _ (by simp)
    rw [ha0, hp0] at this
    rcases List.mem_singleton.mp this with rfl
    exact hbw0 rfl
  · -- the live case
    have hchain : IsAncPath sD a p := hpath
    -- the suffix after `bw` is a genuine sD-chain of `bw`
    have hSuf : IsAncPath sD bw rcSuf := by
      cases rcPre with
      | nil =>
        have h1 : a = bw ∧ p = rcSuf := by
          have := hsplit
          simp only [List.nil_append, List.cons.injEq] at this
          exact this
        rw [← h1.1, ← h1.2]; exact hchain
      | cons q rcPre' =>
        have h1 : a = q ∧ p = rcPre' ++ bw :: rcSuf := by
          have := hsplit
          simp only [List.cons_append, List.cons.injEq] at this
          exact this
        exact isAncPath_suffix sD rcPre' rcSuf a bw (h1.2 ▸ hchain)
    -- bw is an sD-survivor; its insert is in d; its LiveChain at sD
    have hbwLive : contains sD bw = true := by
      have hmem : bw ∈ a :: p := hsplit ▸ List.mem_append_right _ (by simp)
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hal
      · exact isAncPath_live sD p a hchain bw hmem
    have hbwSurv : survP d bw := (hinvD.2.2.1 bw).mp hbwLive
    -- identify bw's insert in d with the given record (id-uniqueness)
    obtain ⟨rb', eb', pb', ab', hm⟩ := hbwSurv.1
    have hmE : (bw, rb', app_op_t.Ins eb' pb' ab') ∈ E :=
      (hUp.2 _).mp (mem_depList.mp hm).1
    have hopEq : (bw, rb', app_op_t.Ins eb' pb' ab') = (bw, rb, app_op_t.Ins eb pb ab) := by
      by_contra hne
      exact hdts _ _ hmE hbwF hne rfl
    rw [hopEq] at hm
    -- LiveChain: bw's sD-chain is the sD-live filter of its record
    have hlc := (hinvD.2.2.2 bw rb eb pb ab hm hbwSurv).2
    have hlcPath : IsAncPath sD bw (liveSub sD (ab :: pb)) := hlc.2.2
    -- chain uniqueness pins the suffix
    have hEq : rcSuf = liveSub sD (ab :: pb) :=
      isAncPath_unique sD hinvD.1 rcSuf _ bw hSuf hlcPath
    -- the sD-drops of bw's record are F-dead
    have hdead : ∀ c ∈ ab :: pb, contains sD c = false → ¬ survP F c := by
      intro c hc hcdead hsvF
      rcases chain_entries_mem Cfg E hGen U (goodEnum_of_perm Cfg E U hUp hUr)
          bw rb eb ab pb ((hUp.2 _).mpr hbwF) c hc with h0 | hins
      · -- c = 0: nothing with id 0 is inserted
        obtain ⟨r', e', p', a', hm'⟩ := hsvF.1
        have : (c, r', app_op_t.Ins e' p' a') ∈ E := (hFp.2 _).mp hm'
        exact hids0 _ this (h0 ▸ rfl)
      · -- c inserted among bw's deps ⊆ t's deps; sD-dead ⟹ dep-deleted ⟹ F-deleted
        have hinsD : insertedIn d c := by
          obtain ⟨r', e', p', a', hm'⟩ := hins
          exact ⟨r', e', p', a',
            depList_trans_mem Cfg E htr hirr U _ _ hm _ hm'⟩
        have hnsvD : ¬ survP d c := fun hs => by
          have := (hinvD.2.2.1 c).mpr hs
          rw [hcdead] at this
          exact Bool.noConfusion this
        have hdel : deletedIn d c := by
          by_contra hnd
          exact hnsvD ⟨hinsD, hnd⟩
        obtain ⟨t', r', p', hm'⟩ := hdel
        have : (t', r', app_op_t.Del p' c) ∈ F :=
          (hFp.2 _).mpr ((hUp.2 _).mp (mem_depList.mp hm').1)
        exact hsvF.2 ⟨t', r', p', this⟩
    -- assemble
    rw [hEq]
    exact (canonAnc_liveSub_of_deadF F sD (ab :: pb) hdead).symm

/-! ## §3  The `hin` producer — the bridge's last input, discharged -/

/-- **`hin` of `canonBirthBridge_via_branchCanon`, discharged.**  For a union survivor `t` with an
LCA-live birth anchor `bw` on its recorded chain: `bw`'s LCA chain is the σ₀'-live filter of `bw`'s
own record (its LCA `LiveChain`), whose `F`-first-survivor equals the record's (Step 1: σ₀'-drops
are LCA-deleted ⟹ `F`-dead, since an LCA op's dependencies live in BOTH branches by closure),
which equals the recorded suffix's (`canonAnc_record_coherence`, Step 2). -/
theorem hin_of_genDisc (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ x ∈ E, x.1 ≠ 0)
    (hGen : GenDisc2C Cfg E)
    (htr : ∀ {a b c : op_t}, Cfg.vis a b → Cfg.vis b c → Cfg.vis a c)
    (hirr : ∀ a : op_t, ¬ Cfg.vis a a)
    (U : List op_t) (hUp : listPermOf U E)
    (hUr : respects U (loOnA RGACondSig Cfg E))
    (ev₁ ev₂ : Set op_t)
    (hcl1 : ∀ a b : op_t, Cfg.vis a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl2 : ∀ a b : op_t, Cfg.vis a b → b ∈ ev₂ → a ∈ ev₂)
    (hsubI : ∀ x ∈ ev₁ ∩ ev₂, x ∈ E)
    (ρ₀ F : List op_t) (hρ₀p : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hFp : listPermOf F E)
    (h₀OK : CanonFoldOK [] init_st ρ₀)
    (t r e a : ℕ) (p : List ℕ) (htE : (t, r, app_op_t.Ins e p a) ∈ E)
    (bw : ℕ) (hbw0 : bw ≠ 0)
    (rcPre rcSuf : List ℕ) (hsplit : a :: p = rcPre ++ bw :: rcSuf)
    (hbwσ : contains (applySeqR init_st ρ₀) bw = true) :
    ∃ cw, IsAncPath (applySeqR init_st ρ₀) bw cw ∧
      canonAnc F cw = canonAnc F rcSuf := by
  set σ₀ := applySeqR init_st ρ₀ with hσ₀
  have hinv0 : CanonInv ρ₀ σ₀ := by
    have h := RGACanonConvergence.canon_fold ρ₀ [] init_st
      RGACanonConvergence.canonInv_init h₀OK
    rwa [List.nil_append] at h
  -- bw's insert in ρ₀, with its record
  have hbwSurv : survP ρ₀ bw := (hinv0.2.2.1 bw).mp hbwσ
  obtain ⟨rb, eb, pb, ab, hmb⟩ := hbwSurv.1
  have hbwE : (bw, rb, app_op_t.Ins eb pb ab) ∈ E := hsubI _ ((hρ₀p.2 _).mp hmb)
  -- bw's LCA LiveChain: its σ₀ chain is the σ₀-live filter of its record
  have hlc := (hinv0.2.2.2 bw rb eb pb ab hmb hbwSurv).2
  refine ⟨liveSub σ₀ (ab :: pb), hlc.2.2, ?_⟩
  -- Step 2: record coherence at the dependency fold
  have hrc : canonAnc F rcSuf = canonAnc F (ab :: pb) :=
    canonAnc_record_coherence Cfg E hdts hids0 hGen htr hirr U hUp hUr F hFp
      t r e a p htE bw rb eb ab pb hbwE hbw0 rcPre rcSuf hsplit
  -- Step 1: the σ₀-drops of bw's record are F-dead
  have hdead : ∀ c ∈ ab :: pb, contains σ₀ c = false → ¬ survP F c := by
    intro c hc hcdead hsvF
    rcases chain_entries_mem Cfg E hGen U (goodEnum_of_perm Cfg E U hUp hUr)
        bw rb eb ab pb ((hUp.2 _).mpr hbwE) c hc with h0 | hins
    · obtain ⟨r', e', p', a', hm'⟩ := hsvF.1
      exact hids0 _ ((hFp.2 _).mp hm') (h0 ▸ rfl)
    · -- a dependency of an LCA op lives in both branches, hence in ρ₀
      obtain ⟨r', e', p', a', hm'⟩ := hins
      obtain ⟨_hxU, _hxbw, hxdep⟩ := mem_depList.mp hm'
      have hvis : Cfg.vis (c, r', app_op_t.Ins e' p' a') (bw, rb, app_op_t.Ins eb pb ab) :=
        depC_imp_vis Cfg E htr _ _ hxdep
      have hbwI : (bw, rb, app_op_t.Ins eb pb ab) ∈ ev₁ ∩ ev₂ := (hρ₀p.2 _).mp hmb
      have hcI : (c, r', app_op_t.Ins e' p' a') ∈ ev₁ ∩ ev₂ :=
        ⟨hcl1 _ _ hvis hbwI.1, hcl2 _ _ hvis hbwI.2⟩
      have hins0 : insertedIn ρ₀ c := ⟨r', e', p', a', (hρ₀p.2 _).mpr hcI⟩
      have hnsv0 : ¬ survP ρ₀ c := fun hs => by
        have hlive := (hinv0.2.2.1 c).mpr hs
        rw [hcdead] at hlive
        exact Bool.noConfusion hlive
      have hdel : deletedIn ρ₀ c := by
        by_contra hnd
        exact hnsv0 ⟨hins0, hnd⟩
      obtain ⟨t', r'', p'', hm''⟩ := hdel
      have hdelF : (t', r'', app_op_t.Del p'' c) ∈ F :=
        (hFp.2 _).mpr (hsubI _ ((hρ₀p.2 _).mp hm''))
      exact hsvF.2 ⟨t', r'', p'', hdelF⟩
  rw [hrc]
  exact (canonAnc_liveSub_of_deadF F σ₀ (ab :: pb) hdead).symm

/-! ## Axiom audit -/

#print axioms isAncPath_live
#print axioms isAncPath_suffix
#print axioms canonAnc_liveSub_of_deadF
#print axioms depList_trans_mem
#print axioms canonAnc_record_coherence
#print axioms hin_of_genDisc

end Sal.Metatheory.RGAK1Delta
