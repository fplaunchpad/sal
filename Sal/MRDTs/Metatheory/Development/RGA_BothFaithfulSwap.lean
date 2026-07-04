import Sal.MRDTs.Metatheory.Development.RGA_GeneralSwap

/-!
# Task #13 · Milestone 1b — the BOTH-`Faithful` update-side swap VC

Extends `RGA_GeneralSwap.general_swap` (VERIFIED) by REPLACING `accurate b s`
with the weaker `Faithful b s` (plus the symmetric `NoFreshClash b a`).  The
resulting `general_swap_bothFaithful` needs NEITHER op to be `accurate`: both may
be staled-but-`Faithful`.  Same conclusion, same four-way op dispatch.

## What each combo needs beyond `general_swap`

* **Ins/Ins** (`swap_InsIns_faithful`): NO faithfulness at all.  Both staled inserts
  are single `upd`s to their own climb-targets; they commute given `NoFreshClash a b`
  (`t2 ∉ a1::p1`) AND `NoFreshClash b a` (`t1 ∉ a2::p2`), plus `t1 ≠ t2`.
* **Ins/Del** (`swap_InsDel_faithful`): the three uses of `accurate b` in the parent
  `swap_InsDel` are all recovered from `Faithful b` + `NoFreshClash b a`:
  `t1 ∉ p2 ∧ t1 ≠ x2` from the clash; `resolve s p2 = anc s x2` from
  `DelTargetFaithful b`; the `x2`-not-live branch is now VACUOUS via `x2 ≠ 0`
  (`Faithful b`) — a not-live climb-target would force `x2 = 0`.
* **Del/Ins**: the mirror of Ins/Del, obtained by `eq_symm` from
  `swap_InsDel_faithful` with the roles of `a`/`b` exchanged.
* **Del/Del** (`swap_DelDel_faithful`): `Faithful b` directly supplies `ClimbFaithful b`,
  `DelTargetFaithful b`, `xb ≠ 0`.  `b`'s target-liveness (`contains s xb`), used by
  the parent `swap_DelDel`, is recovered LOCALLY per branch: from `anc s k = xb` on a
  live `k` via `wf`+`xb≠0`, or from `resolve s pa = xb` via `xb≠0`.  `id_mono` is still
  used only for acyclicity (`xa ↔ xb`).

## Verdict on risk (C)
The RGA DOES support a both-`Faithful` update-side swap.  So Route A's swap fires at
EVERY bubble state whose two swapped events are each `Faithful` and mutually
non-clashing — neither need be `accurate`.  No both-staled counterexample arises: the
`naive_general_swap_false` obstruction was precisely a `NoFreshClash` violation, which
`general_swap_bothFaithful` rules out by hypothesis.

## Axiom status
Every headline decl here is kernel-clean (`propext, Classical.choice, Quot.sound`);
no `sorryAx`, no `native_decide`.  `Merge_Linearization`'s sorries are not touched.
-/

set_option maxHeartbeats 4000000

namespace Sal.Metatheory.RGAGeneralSwap

/-! ## Ins/Ins — both staled inserts, NO faithfulness

Each insert is a single `upd` to its own climb-target `resolve s (a::p)`.  Adding the
other's fresh non-clashing node leaves each climb-target invariant
(`resolve_upd_notMem`), so both orders reduce to the same pair of commuting `upd`s. -/
theorem swap_InsIns_faithful (s : concrete_st) (t1 r1 e1 a1 : ℕ) (p1 : List ℕ)
    (t2 r2 e2 a2 : ℕ) (p2 : List ℕ)
    (hdist : t1 ≠ t2)
    (hclash_ab : t2 ∉ (a1 :: p1))
    (hclash_ba : t1 ∉ (a2 :: p2)) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Ins e2 p2 a2))
       (do_ (do_ s (t2, r2, .Ins e2 p2 a2)) (t1, r1, .Ins e1 p1 a1)) := by
  have hL : do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Ins e2 p2 a2)
          = upd (upd s t1 (e1, resolve s (a1 :: p1))) t2 (e2, resolve s (a2 :: p2)) := by
    simp only [do_]
    rw [resolve_upd_notMem s t1 (e1, resolve s (a1 :: p1)) (a2 :: p2) hclash_ba]
  have hR : do_ (do_ s (t2, r2, .Ins e2 p2 a2)) (t1, r1, .Ins e1 p1 a1)
          = upd (upd s t2 (e2, resolve s (a2 :: p2))) t1 (e1, resolve s (a1 :: p1)) := by
    simp only [do_]
    rw [resolve_upd_notMem s t2 (e2, resolve s (a2 :: p2)) (a1 :: p1) hclash_ab]
  rw [hL, hR, upd_comm s t1 t2 (e1, resolve s (a1 :: p1)) (e2, resolve s (a2 :: p2)) hdist]
  intro k; exact ⟨rfl, fun _ => rfl⟩

/-! ## Ins/Del — staled re-anchoring insert vs staled-but-`Faithful` delete

Adapts `swap_InsDel`: the delete `b` need only be `Faithful` (`DelTargetFaithful` +
`xb ≠ 0`); `t1 ∉ p2` and `t1 ≠ x2` come from `NoFreshClash b a` (= `t1 ∉ x2::p2`). -/
theorem swap_InsDel_faithful (s : concrete_st) (t1 r1 e1 a1 : ℕ) (p1 : List ℕ)
    (t2 r2 x2 : ℕ) (p2 : List ℕ)
    (_h0 : contains s 0 = false)
    (hxb0 : x2 ≠ 0)
    (hdtf : DelTargetFaithful s p2 x2)
    (hfa : fresh_ts (t1, r1, .Ins e1 p1 a1) s)
    (hcf : ClimbFaithful s (a1 :: p1))
    (hclash : t1 ∉ (x2 :: p2)) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Del p2 x2))
       (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Ins e1 p1 a1)) := by
  simp only [fresh_ts] at hfa
  obtain ⟨ht1_0, ht1_dom⟩ := hfa
  unfold ClimbFaithful at hcf
  unfold DelTargetFaithful at hdtf
  have ht1x2 : t1 ≠ x2 := by intro e; apply hclash; rw [e]; simp
  have ht1p2 : t1 ∉ p2 := fun hm => hclash (List.mem_cons_of_mem x2 hm)
  have hInsL : do_ s (t1, r1, .Ins e1 p1 a1) = upd s t1 (e1, resolve s (a1 :: p1)) := by
    simp only [do_]
  set US : concrete_st := upd s t1 (e1, resolve s (a1 :: p1)) with hUS
  set DS : concrete_st := do_ s (t2, r2, .Del p2 x2) with hDS
  have rUSp2 : resolve US p2 = resolve s p2 := by
    rw [hUS]; exact resolve_upd_notMem s t1 (e1, resolve s (a1 :: p1)) p2 ht1p2
  -- THE KEY equation: a's final anchor agrees on both orders
  have key : (if resolve s (a1 :: p1) = x2 then resolve s p2 else resolve s (a1 :: p1))
           = resolve s ((a1 :: p1).filter (fun c => c != x2)) := by
    by_cases hvx : resolve s (a1 :: p1) = x2
    · rw [if_pos hvx]
      by_cases hx2live : contains s x2 = true
      · -- x2 live: both sides equal anc s x2 (DelTargetFaithful + ClimbFaithful)
        have hRp2 : resolve s p2 = anc s x2 := hdtf hx2live
        have hlive : contains s (resolve s (a1 :: p1)) = true := by rw [hvx]; exact hx2live
        have hcfr := hcf hlive
        rw [hvx] at hcfr
        rw [hRp2]; exact hcfr.symm
      · -- x2 not live ⟹ climb-target is 0 ⟹ x2 = 0, contradicting Faithful's x2 ≠ 0
        simp only [Bool.not_eq_true] at hx2live
        have hres0 : resolve s (a1 :: p1) = 0 := by
          rcases resolve_zero_or_live s (a1 :: p1) with h | h
          · exact h
          · rw [hvx] at h; rw [hx2live] at h; exact absurd h (by simp)
        exact absurd (hvx.symm.trans hres0) hxb0
    · rw [if_neg hvx]
      exact (resolve_filter_ne s x2 (a1 :: p1) hvx).symm
  have hRHS : do_ DS (t1, r1, .Ins e1 p1 a1)
            = upd DS t1 (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))) := by
    have hresDS : resolve DS (a1 :: p1)
                = resolve s ((a1 :: p1).filter (fun c => c != x2)) := by
      rw [hDS]; exact resolve_doDel s t2 r2 x2 p2 (a1 :: p1)
    simp only [do_]; rw [hresDS]
  rw [hInsL, hRHS]
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_doDel US t2 r2 x2 p2 k,
        lemma_InDomUpd1 DS t1 k (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))),
        hDS, contains_doDel s t2 r2 x2 p2 k, hUS, lemma_InDomUpd1]
    by_cases hk : k = t1
    · subst hk; simpa using ht1x2
    · have htk : ¬ (t1 = k) := fun e => hk e.symm
      simp [htk]
  · intro _
    rw [sel_doDel US t2 r2 x2 p2 k, rUSp2]
    by_cases hk : k = t1
    · subst hk
      have hanc : anc US k = resolve s (a1 :: p1) := by
        rw [hUS]; simp only [anc]; rw [lemma_SelUpd1]
      have hel : el US k = e1 := by
        rw [hUS]; simp only [el]; rw [lemma_SelUpd1]
      have hsel : sel US k = (e1, resolve s (a1 :: p1)) := by rw [hUS, lemma_SelUpd1]
      rw [hanc, hel, hsel, lemma_SelUpd1]
      by_cases hvx : resolve s (a1 :: p1) = x2
      · rw [if_pos hvx]
        have := key; rw [if_pos hvx] at this; rw [this]
      · rw [if_neg hvx]
        have := key; rw [if_neg hvx] at this; rw [this]
    · have hne : (t1 : ℕ) != k := by simp [Ne.symm hk]
      have hanck : anc US k = anc s k := by
        rw [hUS]; simp only [anc]
        rw [lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne]
      have helk : el US k = el s k := by
        rw [hUS]; simp only [el]
        rw [lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne]
      have hselk : sel US k = sel s k :=
        lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne
      rw [hanck, helk, hselk,
          lemma_SelUpd2 DS k t1 (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))) hne,
          hDS, sel_doDel s t2 r2 x2 p2 k]

/-! ## Del/Del — both staled-but-`Faithful` deletes

Adapts `swap_DelDel`: `b`'s target-liveness is recovered locally per branch, so `b`
need only be `Faithful` (not `accurate`).  `id_mono` still rules out the `xa ↔ xb`
2-cycle only. -/
theorem swap_DelDel_faithful (s : concrete_st) (t1 r1 xa : ℕ) (pa : List ℕ)
    (t2 r2 xb : ℕ) (pb : List ℕ)
    (_h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hxa0 : xa ≠ 0) (hxb0 : xb ≠ 0)
    (hcf : ClimbFaithful s pa) (hdtf : DelTargetFaithful s pa xa)
    (hcfb : ClimbFaithful s pb) (hdtf_b : DelTargetFaithful s pb xb) :
    eq (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb))
       (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) := by
  unfold ClimbFaithful at hcf hcfb
  unfold DelTargetFaithful at hdtf hdtf_b
  intro k
  refine ⟨?_, ?_⟩
  · simp only [contains_doDel]; rw [Bool.and_right_comm]
  · intro hcontain
    have hks : contains s k = true := by
      rw [contains_doDel, contains_doDel] at hcontain
      simp only [Bool.and_eq_true] at hcontain
      exact hcontain.1.1
    have hel : el (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb)) k
             = el (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) k := by
      simp only [el_doDel]
    have han : anc (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb)) k
             = anc (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) k := by
      simp only [anc_doDel, resolve_doDel]
      by_cases h1 : anc s k = xa
      · by_cases h2 : anc s k = xb
        · -- (d)  xa = xb
          have hxab : xa = xb := h1.symm.trans h2
          have hxblive : contains s xb = true := by
            rcases hwf k hks with h | h
            · rw [h2] at h; exact absurd h hxb0
            · rw [h2] at h; exact h
          have hResPb : resolve s pb = anc s xb := hdtf_b hxblive
          have hxalive : contains s xa = true := by rw [hxab]; exact hxblive
          have hRa : resolve s pa = anc s xa := hdtf hxalive
          have hne1 : ¬ (anc s xa = xb) := by
            rw [← hxab]; rcases hmono xa hxalive with h | h
            · rw [h]; exact fun e => hxa0 e.symm
            · omega
          have hne2 : ¬ (anc s xb = xa) := by
            rw [hxab]; rcases hmono xb hxblive with h | h
            · rw [h]; exact fun e => hxb0 e.symm
            · omega
          simp only [if_pos h1, if_pos h2]
          rw [hRa, hResPb, if_neg hne1, if_neg hne2, hxab]
        · -- (b)  anc s k = xa, ≠ xb
          simp only [if_pos h1, if_neg h2]
          by_cases hA : resolve s pa = xb
          · rw [if_pos hA]
            have hxblive : contains s xb = true := by
              have hzl := resolve_zero_or_live s pa
              rw [hA] at hzl
              rcases hzl with h | h
              · exact absurd h hxb0
              · exact h
            have hResPb : resolve s pb = anc s xb := hdtf_b hxblive
            have hancxb_ne : anc s xb ≠ xa := by
              intro he
              have hxal : contains s xa = true := by
                rcases hwf xb hxblive with h | h
                · rw [he] at h; exact absurd h hxa0
                · rw [he] at h; exact h
              have hRaval : resolve s pa = anc s xa := hdtf hxal
              rw [hA] at hRaval
              have h_axa := hmono xa hxal
              have h_axb := hmono xb hxblive
              rcases h_axa with e1 | e1
              · rw [← hRaval] at e1; exact hxb0 e1
              rcases h_axb with e2 | e2
              · rw [he] at e2; exact hxa0 e2
              rw [← hRaval] at e1; rw [he] at e2; omega
            have hRHS : resolve s (pa.filter (fun c => c != xb)) = anc s xb := by
              have hcfr := hcf (by rw [hA]; exact hxblive)
              rw [hA] at hcfr; exact hcfr
            have hLHS : resolve s (pb.filter (fun c => c != xa)) = anc s xb := by
              rw [resolve_filter_ne s xa pb (by rw [hResPb]; exact hancxb_ne)]; exact hResPb
            rw [hLHS, hRHS]
          · rw [if_neg hA]; exact (resolve_filter_ne s xb pa hA).symm
      · by_cases h2 : anc s k = xb
        · -- (c)  anc s k = xb, ≠ xa
          simp only [if_neg h1, if_pos h2]
          have hxblive : contains s xb = true := by
            rcases hwf k hks with h | h
            · rw [h2] at h; exact absurd h hxb0
            · rw [h2] at h; exact h
          have hResPb : resolve s pb = anc s xb := hdtf_b hxblive
          by_cases hB : resolve s pb = xa
          · rw [if_pos hB]
            have hxal : contains s xa = true := by
              rw [hResPb] at hB
              rcases hwf xb hxblive with h | h
              · rw [hB] at h; exact absurd h hxa0
              · rw [hB] at h; exact h
            have hLHS : resolve s (pb.filter (fun c => c != xa)) = anc s xa := by
              have hcfr := hcfb (by rw [hB]; exact hxal)
              rw [hB] at hcfr; exact hcfr
            have hancxa_ne : anc s xa ≠ xb := by
              intro he
              rw [hResPb] at hB
              have h_axa := hmono xa hxal
              have h_axb := hmono xb hxblive
              rcases h_axa with e1 | e1
              · rw [e1] at he; exact hxb0 he.symm
              rcases h_axb with e2 | e2
              · rw [hB] at e2; exact hxa0 e2
              rw [he] at e1; rw [hB] at e2; omega
            have hRHS : resolve s (pa.filter (fun c => c != xb)) = anc s xa := by
              rw [resolve_filter_ne s xb pa (by rw [hdtf hxal]; exact hancxa_ne)]; exact hdtf hxal
            rw [hLHS, hRHS]
          · rw [if_neg hB]; exact resolve_filter_ne s xa pb hB
        · -- (a)  neither
          simp only [if_neg h1, if_neg h2]
    exact Prod.ext_iff.mpr ⟨hel, han⟩

/-! ## The bundled BOTH-`Faithful` general swap VC

Neither op need be `accurate` — both may be staled-but-`Faithful` — provided each is
mutually non-clashing (`NoFreshClash` in both directions).  Same four-way dispatch as
`general_swap`; Del/Ins is the `eq_symm` mirror of `swap_InsDel_faithful`. -/
theorem general_swap_bothFaithful (s : concrete_st) (a b : op_t)
    (hdist : a.1 ≠ b.1) (h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hfa : fresh_ts a s) (hfb : fresh_ts b s)
    (hfaith_a : Faithful a s) (hfaith_b : Faithful b s)
    (hclash_ab : NoFreshClash a b) (hclash_ba : NoFreshClash b a) :
    eq (do_ (do_ s a) b) (do_ (do_ s b) a) := by
  obtain ⟨t1, r1, op1⟩ := a
  obtain ⟨t2, r2, op2⟩ := b
  simp only at hdist
  cases op1 with
  | Ins e1 p1 a1 =>
    simp only [Faithful] at hfaith_a
    cases op2 with
    | Ins e2 p2 a2 =>
        simp only [NoFreshClash] at hclash_ab hclash_ba
        exact swap_InsIns_faithful s t1 r1 e1 a1 p1 t2 r2 e2 a2 p2 hdist hclash_ab hclash_ba
    | Del p2 x2 =>
        simp only [Faithful] at hfaith_b
        simp only [NoFreshClash] at hclash_ba
        exact swap_InsDel_faithful s t1 r1 e1 a1 p1 t2 r2 x2 p2 h0
          hfaith_b.2.2 hfaith_b.2.1 hfa hfaith_a hclash_ba
  | Del p1 x1 =>
    simp only [Faithful] at hfaith_a
    cases op2 with
    | Ins e2 p2 a2 =>
        simp only [Faithful] at hfaith_b
        simp only [NoFreshClash] at hclash_ab
        exact eq_symm _ _ (swap_InsDel_faithful s t2 r2 e2 a2 p2 t1 r1 x1 p1 h0
          hfaith_a.2.2 hfaith_a.2.1 hfb hfaith_b hclash_ab)
    | Del p2 x2 =>
        simp only [Faithful] at hfaith_b
        exact swap_DelDel_faithful s t1 r1 x1 p1 t2 r2 x2 p2 h0 hwf hmono
          hfaith_a.2.2 hfaith_b.2.2 hfaith_a.1 hfaith_a.2.1 hfaith_b.1 hfaith_b.2.1

/-! ## Axiom audit -/
#print axioms swap_InsIns_faithful
#print axioms swap_InsDel_faithful
#print axioms swap_DelDel_faithful
#print axioms general_swap_bothFaithful

end Sal.Metatheory.RGAGeneralSwap
