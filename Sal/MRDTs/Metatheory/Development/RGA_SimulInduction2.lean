import Sal.MRDTs.Metatheory.Development.RGA_SimulInduction
import Sal.MRDTs.Metatheory.Conditioned.RGA_Faithful_PBT

/-!
# Rehoming-aware simultaneous induction (attempt 2): the in-place Faith step

Mechanizes `REHOMING_AWARE_DESIGN.md`: replace `RGA_SimulInduction`'s Faith step
(deps-first reorder, needing the REFUTED `DepComp`, `RGA_DepComp_Gate.lean`) by an
in-place thread of `ChainFaithful (recList o)` along the ACTUAL enumeration `ρ`,
each step certified from IH-`Faith` at the prefix-set `Tᵢ = {x₁..xᵢ} ⊊ S`.

`DepComp` appears NOWHERE in this file.  What closes and what does not:

* §1 `prefix_depClosed` — the design's crux order lemma: a prefix of a
  `loOnA`-respecting enumeration of a dependency-closed set is dependency-closed,
  WITHOUT any transitivity/`DepComp` (prefix-closure ≠ contiguous-reorder).  CLOSED.
* §2 `faithful_at_split` — the IH consumption at each split of `ρ`:
  `Faithful xᵢ (fold [x₁..xᵢ₋₁])` from `Faith Tᵢ`.  CLOSED.
* §3 the Faith step with the in-place thread: the concurrent-fresh-`Ins` and `Del`
  (incl. rehoming) arms are CLOSED; the ancestor-`Ins` arm is carried as the
  remaining `GoodStep` obligation of `faith_last_of_ancestor_goodSteps`.
* §4 `conv_step2` — the Conv step, verbatim from `RGA_SimulInduction.conv_step`
  MINUS the (there unused) `DepComp` binder.  CLOSED, `DepComp`-free.
* §5 THE GATE (`ancestorIns_step_refuted`): the ancestor-`Ins` arm's goal is FALSE —
  a 5-event rehoming trace reaches a mid-fold state where EVERYTHING the design says
  the IH supplies holds (`Faithful xᵢ`, even `RecPathFaithful xᵢ`, `fresh_ts`,
  `wf`/`id_mono`/root-free, and the threaded `ChainFaithful (recList o)`), yet
  `ChainFaithful (do_ s xᵢ) (recList o)` FAILS.  So the stuck arm is not merely
  unproven: the design's threading INVARIANT is refuted mid-fold, and neither
  `Faithful xᵢ` nor the `RecPathFaithful`-third-conjunct fallback can close it.
  The invariant heals by the end of `ρ` (§5 also proves the healed end state), so
  `Faith S` itself is untouched — the in-place PROOF METHOD is what fails.

See the STATUS block at the end for the exact stuck goal and the repair direction.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGASimulInduction2

open Sal.Emulation
open Sal.Metatheory.RGAGeneralSwap (Faithful ClimbFaithful DelTargetFaithful NoFreshClash)
open Sal.Metatheory.RGABubbleWiring
  (recList ChainFaithful ChainFaithfulAux climbFaithful_of_chain)
open Sal.Metatheory.RGAConditionedConvergence
  (applySeqR applySeqR_append applySeqR_cons applySeqR_nil do_eq_congr resolve_eq_congr
   EqSwap eqSwap_of_bothFaithful bubble_eq)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open Sal.Metatheory.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.Metatheory.RGASig (RGACondSig isAncPath_not_mem)
open RGAInterleavedThreading
  (GoodStep GoodFold AncInsLink chainFaithful_goodFold chainFaithful_init_recList)
open Sal.Metatheory.RGAGenDischarge
  (NonDegen ReachInv noFreshClash_of_accurate_fresh freshId_not_mem_recList)
open Sal.Metatheory.RGAGenDischarge2 (IsDepPre GenDisc2)
open Sal.Metatheory.RGAUpdateConvergenceFinal
  (fresh_ts_config goodFold_of_stepwise goodStep_ins_concurrent)
open Sal.Metatheory.RGASimulInduction
  (DC Conv Faith faithful_of_ih respects_sublist respects_cross respects_append
   respects_concat pred_mem_left faithful_del_of_chain faithful_eq_congr)
open RGAFaithfulPBT (chainFaithfulB chainFaithfulB_iff)
open RGARecPathFaithful (RecPathFaithful target recPath)

variable (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (E : Set op_t)

/-! ## §1  The crux order lemma: prefixes of a respecting enumeration are
dependency-closed — NO transitivity

For `ρ = pfx ++ x :: rest` (a respecting enumeration of `S \ {o}`, `o` last), every
`loOnA`-predecessor `z` of a member `y` of `pfx ++ [x]` lies in `pfx`: `z ∈ S` by
dependency-closure of `S` (ONE edge, no composition), `z ≠ o` because `o` is last
(an edge `z = o → y` would violate `respects (ρ ++ [o])`), hence `z ∈ ρ`; and a
predecessor sits strictly LEFT of `y` in the respecting `ρ`, hence in `pfx`.  This
is the fact the OLD Faith step bought with `DepComp` (to make the deps-first
reorder respecting) and the design gets for FREE from prefix-closure. -/
theorem prefix_depClosed (S : Finset op_t) (hdc : DC Cfg E S) (o : op_t)
    (ρ : List op_t) (hρmem : ∀ a, a ∈ ρ ↔ a ∈ ↑(S.erase o))
    (hresp : respects (ρ ++ [o]) (loOnA RGACondSig Cfg E))
    (pfx : List op_t) (x : op_t) (rest : List op_t) (hsplit : ρ = pfx ++ x :: rest) :
    ∀ y ∈ pfx ++ [x], ∀ z ∈ E, z ≠ y → loOnA RGACondSig Cfg E z y → z ∈ pfx := by
  intro y hy z hzE hzy hlo
  have hyρ : y ∈ ρ := by
    rw [hsplit]
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · rw [List.mem_singleton] at h
      subst h
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hyS : y ∈ S :=
    Finset.mem_of_mem_erase (Finset.mem_coe.mp ((hρmem y).mp hyρ))
  have hzS : z ∈ S := hdc.2 y hyS z hzE hzy hlo
  -- z ≠ o: o is LAST, so no member of ρ has o as a predecessor
  have hzo : z ≠ o := by
    rintro rfl
    exact respects_cross hresp y hyρ z (List.mem_singleton_self z) hlo
  have hzρ : z ∈ ρ :=
    (hρmem z).mpr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzo, hzS⟩))
  -- a predecessor sits strictly left of y
  rcases List.mem_append.mp hy with hypfx | hyx
  · obtain ⟨u, v, huv⟩ := List.append_of_mem hypfx
    have hre : ρ ++ [o] = u ++ y :: (v ++ x :: rest ++ [o]) := by
      rw [hsplit, huv]; simp [List.append_assoc]
    have hz' : z ∈ u ++ y :: (v ++ x :: rest ++ [o]) := by
      rw [← hre]; exact List.mem_append.mpr (Or.inl hzρ)
    have hzu := pred_mem_left (hre ▸ hresp) hz' hlo hzy
    rw [huv]
    exact List.mem_append.mpr (Or.inl hzu)
  · rw [List.mem_singleton] at hyx
    subst hyx
    have hre : ρ ++ [o] = pfx ++ y :: (rest ++ [o]) := by
      rw [hsplit]; simp [List.append_assoc]
    have hz' : z ∈ pfx ++ y :: (rest ++ [o]) := by
      rw [← hre]; exact List.mem_append.mpr (Or.inl hzρ)
    exact pred_mem_left (hre ▸ hresp) hz' hlo hzy

/-! ## §2  The IH consumption at each split of `ρ`

`Faith Tᵢ` at the prefix-set `Tᵢ = {x₁..xᵢ} ⊊ S` (strictly smaller because `o` is
excluded) gives each event its OWN faithfulness at the fold of the events before it —
packaged through the reused `faithful_of_ih` with the excluded witness `w := o` and
the §1 closure. -/
theorem faithful_at_split (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S)
    (o : op_t) (ho : o ∈ S) (ρ : List op_t)
    (hρp : listPermOf ρ ↑(S.erase o))
    (hresp : respects (ρ ++ [o]) (loOnA RGACondSig Cfg E))
    (pfx : List op_t) (x : op_t) (rest : List op_t) (hsplit : ρ = pfx ++ x :: rest) :
    Faithful x (applySeqR init_st pfx) := by
  obtain ⟨hρnd, hρmem⟩ := hρp
  have hρS : ∀ z ∈ ρ, z ∈ S := fun z hz =>
    Finset.mem_of_mem_erase (Finset.mem_coe.mp ((hρmem z).mp hz))
  have hρneo : ∀ z ∈ ρ, z ≠ o := fun z hz =>
    (Finset.mem_erase.mp (Finset.mem_coe.mp ((hρmem z).mp hz))).1
  have hxρ : x ∈ ρ := by
    rw [hsplit]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hpfxρ : ∀ z ∈ pfx, z ∈ ρ := fun z hz => by
    rw [hsplit]; exact List.mem_append.mpr (Or.inl hz)
  have hnd' : (pfx ++ x :: rest).Nodup := hsplit ▸ hρnd
  have hpfxnd : pfx.Nodup := (List.nodup_append.mp hnd').1
  have hxpfx : x ∉ pfx := fun h =>
    (List.nodup_append.mp hnd').2.2 x h x List.mem_cons_self rfl
  have hopfx : o ∉ pfx := fun h => hρneo o (hpfxρ o h) rfl
  have hρresp : respects ρ (loOnA RGACondSig Cfg E) :=
    respects_sublist (List.sublist_append_left ρ [o]) hresp
  have hss : (pfx ++ [x]).Sublist ρ := by
    rw [hsplit]
    exact List.Sublist.append_left
      (List.cons_sublist_cons.mpr (List.nil_sublist rest)) pfx
  exact faithful_of_ih Cfg E n ih S hcard hdc pfx x o (fun z hz => hρS z (hpfxρ z hz))
    (hρS x hxρ) ho (hρneo x hxρ) hopfx hxpfx hpfxnd
    (respects_sublist hss hρresp)
    (prefix_depClosed Cfg E S hdc o ρ hρmem hresp pfx x rest hsplit)

/-! ## §3  The rehoming-aware Faith step, threaded in place

Thread `ChainFaithful (recList o)` along the ACTUAL `ρ` from the vacuous base
(`chainFaithful_init_recList`), stepping by `GoodStep` cases and projecting to
`Faithful o` at the end.  TWO of the three arms are discharged here, DepComp-free:

* concurrent fresh `Ins` (`id ∉ recList o`): `goodStep_ins_concurrent` — no IH;
* `Del` — INCLUDING a delete of `o`'s target or ancestor (the rehoming case):
  `Faithful xᵢ` from §2 (IH-Faith at `Tᵢ`), `contains 0/wf` from `ReachInv`;
  `chainFaithful_doDel_faithful` (inside `GoodStep`'s `Del` arm) imposes NO
  relation between the deleted node and `recList o`.

The ancestor-`Ins` arm (`id ∈ recList o`) is carried as the hypothesis `hanc` in the
existing `GoodStep` vocabulary.  §5 REFUTES that arm: its goal is genuinely false at
a reachable split even with all IH-supplied facts in hand, so it is a located FALSE
obligation, not a residual to discharge (see the STATUS block). -/
theorem faith_last_of_ancestor_goodSteps
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E)
    (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S)
    (o : op_t) (ho : o ∈ S) (ρ : List op_t)
    (hρp : listPermOf ρ ↑(S.erase o))
    (hresp : respects (ρ ++ [o]) (loOnA RGACondSig Cfg E))
    (hanc : ∀ (pfx : List op_t) (t r e : ℕ) (p : List ℕ) (a : ℕ) (rest : List op_t),
      ρ = pfx ++ (t, r, .Ins e p a) :: rest → t ∈ recList o →
      GoodStep (applySeqR init_st pfx) (recList o) (t, r, .Ins e p a)) :
    Faithful o (applySeqR init_st ρ) := by
  classical
  obtain ⟨hρnd, hρmem⟩ := hρp
  have hρS : ∀ z ∈ ρ, z ∈ S := fun z hz =>
    Finset.mem_of_mem_erase (Finset.mem_coe.mp ((hρmem z).mp hz))
  have hρsubE : ∀ z ∈ ρ, z ∈ E := fun z hz => hdc.1 z (hρS z hz)
  have hoE : o ∈ E := hdc.1 o ho
  have hρresp : respects ρ (loOnA RGACondSig Cfg E) :=
    respects_sublist (List.sublist_append_left ρ [o]) hresp
  -- the in-place thread: every split of ρ is a GoodStep for recList o
  have hgf : GoodFold (recList o) init_st ρ := by
    apply goodFold_of_stepwise (recList o) ρ init_st
    intro pfx x rest hsplit
    obtain ⟨t, rr, op⟩ := x
    cases op with
    | Ins e p a =>
      by_cases htL : t ∈ recList o
      · -- ancestor-Ins arm: the carried (§5-refuted) obligation
        exact hanc pfx t rr e p a rest hsplit htL
      · -- concurrent fresh Ins
        have hxρ : (t, rr, .Ins e p a) ∈ ρ := by
          rw [hsplit]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        exact goodStep_ins_concurrent _ (recList o) t rr e a p
          (hids0 _ (hρsubE _ hxρ)) htL
    | Del p xx =>
      -- Del (staled or not, incl. rehoming): Faithful from IH-Faith at the prefix-set
      have hss : pfx.Sublist ρ := by
        rw [hsplit]; exact List.sublist_append_left pfx (_ :: rest)
      have hpfxsubE : ∀ z ∈ pfx, z ∈ E := fun z hz => hρsubE z (hss.subset hz)
      have hpfxnd : pfx.Nodup := List.Nodup.sublist hss hρnd
      have hpfxresp := respects_sublist hss hρresp
      obtain ⟨h0, hwf, _⟩ := hInv pfx hpfxsubE hpfxnd hpfxresp
      exact ⟨h0, hwf, faithful_at_split Cfg E n ih S hcard hdc o ho ρ ⟨hρnd, hρmem⟩
        hresp pfx _ rest hsplit⟩
  have hcf : ChainFaithful (applySeqR init_st ρ) (recList o) :=
    chainFaithful_goodFold (recList o) ρ init_st hgf (chainFaithful_init_recList o)
  obtain ⟨h0ρ, _, _⟩ := hInv ρ hρsubE hρnd hρresp
  -- project to Faithful o
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | Ins e p an =>
    exact climbFaithful_of_chain _ (an :: p) h0ρ hcf
  | Del p xx =>
    -- xx ≠ 0 and xx ∉ p from GenDisc2's accuracy at o's dependency prefix
    -- (built as the filter of ρ — dep-complete by DC, respecting as a sublist)
    obtain ⟨hND, haccf⟩ := hGen (t, rr, .Del p xx) hoE
    have hxx0 : xx ≠ 0 := hND
    set P : op_t → Bool :=
      fun z => decide (loOnA RGACondSig Cfg E z (t, rr, .Del p xx)) with hP
    set d : List op_t := ρ.filter P with hd
    have hd_mem : ∀ z, z ∈ d ↔
        (z ∈ ρ ∧ loOnA RGACondSig Cfg E z (t, rr, .Del p xx)) := by
      intro z
      simp only [hd, hP, List.mem_filter, decide_eq_true_iff]
    have hdsub : d.Sublist ρ := by rw [hd]; exact List.filter_sublist
    have hdsubE : ∀ z ∈ d, z ∈ E := fun z hz => hρsubE z (hdsub.subset hz)
    have hdnd : d.Nodup := List.Nodup.sublist hdsub hρnd
    have hdresp := respects_sublist hdsub hρresp
    have hdep : IsDepPre Cfg E (t, rr, .Del p xx) d := by
      refine ⟨hdsubE, hdnd, hdresp, ?_, fun z hz => ((hd_mem z).mp hz).2⟩
      intro z hzE hzo hlo
      have hzS : z ∈ S := hdc.2 _ ho z hzE hzo hlo
      have hzρ : z ∈ ρ :=
        (hρmem z).mpr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzo, hzS⟩))
      exact (hd_mem z).mpr ⟨hzρ, hlo⟩
    have hacc := haccf d hdep
    obtain ⟨h0d, _, _⟩ := hInv d hdsubE hdnd hdresp
    have hpath : IsAncPath (applySeqR init_st d) xx p := by
      simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨hl0, _⟩ | ⟨_, hp⟩
      · exact absurd hl0 hxx0
      · exact hp
    have hxxp : xx ∉ p := isAncPath_not_mem _ h0d xx p hpath
    exact faithful_del_of_chain _ t rr xx p h0ρ hxx0 hxxp hcf

/-! ## §4  The Conv step, `DepComp`-free

Verbatim `RGA_SimulInduction.conv_step` with the `DepComp` binder DELETED — that
hypothesis was already unused there (`_hDep`), machine-confirming the design's
"Conv never needed `DepComp`" claim: adjacent-incomparable swaps
(`eqSwap_of_bothFaithful`, both `Faithful`s from IH-`Faith` at sets excluding the
other operand) preserve `respects` without any edge composition. -/
theorem conv_step2 (C : ConditionedConfiguration RGACondSig)
    (hE : C.BackClosed E) (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E)
    (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S) :
    Conv Cfg E S := by
  classical
  intro π₁ π₂ h₁p h₂p h₁r h₂r
  rcases List.eq_nil_or_concat π₁ with rfl | ⟨ρ₁, m, hcat⟩
  · -- π₁ = [] : S is empty, so π₂ = [] too
    obtain ⟨_, hm₁⟩ := h₁p
    obtain ⟨_, hm₂⟩ := h₂p
    have hπ₂ : π₂ = [] := by
      cases hπ : π₂ with
      | nil => rfl
      | cons a l =>
        exact absurd ((hm₁ a).mpr ((hm₂ a).mp (by rw [hπ]; exact List.mem_cons_self)))
          List.not_mem_nil
    rw [hπ₂]
    exact Sal.Metatheory.RGAConditionedConvergence.eq_refl _
  · rw [List.concat_eq_append] at hcat
    subst hcat
    obtain ⟨h₁nd, h₁mem⟩ := h₁p
    obtain ⟨h₂nd, h₂mem⟩ := h₂p
    have hmS : m ∈ S := Finset.mem_coe.mp ((h₁mem m).mp
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self m))))
    have hmE : m ∈ E := hdc.1 m hmS
    have hmρ₁ : m ∉ ρ₁ := fun h =>
      (List.nodup_append.mp h₁nd).2.2 m h m (List.mem_singleton_self m) rfl
    -- quasi-maximality of m in S (m is last in the respects-enumeration π₁)
    have hmax : ∀ z ∈ S, z ≠ m → ¬ loOnA RGACondSig Cfg E m z := by
      intro z hz hzm
      have hzρ : z ∈ ρ₁ := by
        rcases List.mem_append.mp ((h₁mem z).mpr (Finset.mem_coe.mpr hz)) with h | h
        · exact h
        · rw [List.mem_singleton] at h; exact absurd h hzm
      exact respects_cross h₁r z hzρ m (List.mem_singleton_self m)
    have h₁resp : respects ρ₁ (loOnA RGACondSig Cfg E) :=
      respects_sublist (List.sublist_append_left ρ₁ [m]) h₁r
    have hρ₁perm : listPermOf ρ₁ ↑(S.erase m) := by
      refine ⟨(List.nodup_append.mp h₁nd).1, fun a => ?_⟩
      constructor
      · intro ha
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_coe.mp
          ((h₁mem a).mp (List.mem_append.mpr (Or.inl ha)))⟩)
        rintro rfl; exact hmρ₁ ha
      · intro ha
        have haS := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
        rcases List.mem_append.mp ((h₁mem a).mpr (Finset.mem_coe.mpr haS.2)) with h | h
        · exact h
        · rw [List.mem_singleton] at h; exact absurd h haS.1
    -- split π₂ at m
    obtain ⟨σ, τ, hπ₂⟩ := List.append_of_mem ((h₂mem m).mpr (Finset.mem_coe.mpr hmS))
    subst hπ₂
    have h₂nd' := List.nodup_append.mp h₂nd
    have hmσ : m ∉ σ := fun h => h₂nd'.2.2 m h m List.mem_cons_self rfl
    have hmτ : m ∉ τ := (List.nodup_cons.mp h₂nd'.2.1).1
    have hστnd : (σ ++ τ).Nodup := by
      rw [List.nodup_append]
      exact ⟨h₂nd'.1, (List.nodup_cons.mp h₂nd'.2.1).2,
        fun a ha b hb => h₂nd'.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
    have hστperm : listPermOf (σ ++ τ) ↑(S.erase m) := by
      refine ⟨hστnd, fun a => ?_⟩
      constructor
      · intro ha
        have haπ₂ : a ∈ σ ++ m :: τ := by
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
        have hane : a ≠ m := by
          rintro rfl
          rcases List.mem_append.mp ha with h | h
          · exact hmσ h
          · exact hmτ h
        exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
          ⟨hane, Finset.mem_coe.mp ((h₂mem a).mp haπ₂)⟩)
      · intro ha
        have haS := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
        rcases List.mem_append.mp ((h₂mem a).mpr (Finset.mem_coe.mpr haS.2)) with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' haS.1
          · exact List.mem_append.mpr (Or.inr h')
    have hστresp : respects (σ ++ τ) (loOnA RGACondSig Cfg E) :=
      respects_sublist (List.Sublist.append_left (List.sublist_cons_self m τ) σ) h₂r
    -- bubble m to the very end of π₂, up to eq
    have hbubble : eq (applySeqR (applySeqR init_st σ) (τ ++ [m]))
        (applySeqR (applySeqR init_st σ) (m :: τ)) := by
      have hsw : ∀ α β y, τ = α ++ y :: β →
          EqSwap y m (applySeqR (applySeqR init_st σ) α) := by
        intro α β y hτ
        subst hτ
        rw [← applySeqR_append]
        have hyτ : y ∈ α ++ y :: β := List.mem_append.mpr (Or.inr List.mem_cons_self)
        have hyπ₂ : y ∈ σ ++ m :: (α ++ y :: β) :=
          List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hyτ))
        have hyS : y ∈ S := Finset.mem_coe.mp ((h₂mem y).mp hyπ₂)
        have hyE : y ∈ E := hdc.1 y hyS
        have hym : y ≠ m := by rintro rfl; exact hmτ hyτ
        have hpre_subS : ∀ z ∈ σ ++ α, z ∈ S := by
          intro z hz
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) := by
            rcases List.mem_append.mp hz with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inl h))))
          exact Finset.mem_coe.mp ((h₂mem z).mp hzπ₂)
        have hpre_subE : ∀ z ∈ σ ++ α, z ∈ E := fun z hz => hdc.1 z (hpre_subS z hz)
        have hpre_ss : (σ ++ α).Sublist (σ ++ m :: (α ++ y :: β)) :=
          List.Sublist.append_left
            (List.Sublist.cons m (List.sublist_append_left α (y :: β))) σ
        have hpre_nd : (σ ++ α).Nodup := List.Nodup.sublist hpre_ss h₂nd
        have hpre_resp := respects_sublist hpre_ss h₂r
        obtain ⟨h0, hwf, hmono⟩ := hInv (σ ++ α) hpre_subE hpre_nd hpre_resp
        have hynpre : y ∉ σ ++ α := by
          intro h
          rcases List.mem_append.mp h with h1 | h2
          · exact h₂nd'.2.2 y h1 y (List.mem_cons_of_mem _ hyτ) rfl
          · have hτnd : (α ++ y :: β).Nodup := (List.nodup_cons.mp h₂nd'.2.1).2
            exact (List.nodup_append.mp hτnd).2.2 y h2 y List.mem_cons_self rfl
        have hmnpre : m ∉ σ ++ α := by
          intro h
          rcases List.mem_append.mp h with h1 | h2
          · exact hmσ h1
          · exact hmτ (List.mem_append.mpr (Or.inl h2))
        -- dependency closure of the visited prefix σ ++ α (positional, from respects π₂)
        have hcl : ∀ g ∈ σ ++ α, ∀ z ∈ E, z ≠ g →
            loOnA RGACondSig Cfg E z g → z ∈ σ ++ α := by
          intro g hg z hzE hzg hlo
          have hgS : g ∈ S := hpre_subS g hg
          have hzS : z ∈ S := hdc.2 g hgS z hzE hzg hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          rcases List.mem_append.mp hg with hgσ | hgα
          · obtain ⟨u, v, huv⟩ := List.append_of_mem hgσ
            have hre : σ ++ m :: (α ++ y :: β)
                = u ++ g :: (v ++ m :: (α ++ y :: β)) := by
              rw [huv]; simp [List.append_assoc]
            have hzu := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzg
            exact List.mem_append.mpr (Or.inl (by
              rw [huv]; exact List.mem_append.mpr (Or.inl hzu)))
          · obtain ⟨u, v, huv⟩ := List.append_of_mem hgα
            have hgm : g ≠ m := by
              rintro rfl; exact hmτ (List.mem_append.mpr (Or.inl hgα))
            have hre : σ ++ m :: (α ++ y :: β)
                = (σ ++ m :: u) ++ g :: (v ++ y :: β) := by
              rw [huv]; simp [List.append_assoc]
            have hzσmu := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzg
            rcases List.mem_append.mp hzσmu with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · rcases List.mem_cons.mp h with rfl | h'
              · exact absurd hlo (hmax g hgS hgm)
              · exact List.mem_append.mpr (Or.inr (by
                  rw [huv]; exact List.mem_append.mpr (Or.inl h')))
        -- predecessors of y land in σ ++ α
        have hcly : ∀ z ∈ E, z ≠ y → loOnA RGACondSig Cfg E z y → z ∈ σ ++ α := by
          intro z hzE hzy hlo
          have hzS : z ∈ S := hdc.2 y hyS z hzE hzy hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          have hre : σ ++ m :: (α ++ y :: β) = (σ ++ m :: α) ++ y :: β := by
            simp [List.append_assoc]
          have hzσmα := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzy
          rcases List.mem_append.mp hzσmα with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · rcases List.mem_cons.mp h with rfl | h'
            · exact absurd hlo (hmax y hyS hym)
            · exact List.mem_append.mpr (Or.inr h')
        -- predecessors of m land in σ
        have hclm : ∀ z ∈ E, z ≠ m → loOnA RGACondSig Cfg E z m → z ∈ σ ++ α := by
          intro z hzE hzm hlo
          have hzS : z ∈ S := hdc.2 m hmS z hzE hzm hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          exact List.mem_append.mpr (Or.inl (pred_mem_left h₂r hzπ₂ hlo hzm))
        -- Faithful y / Faithful m at the prefix fold — through the IH (Faith T),
        -- each packaged set excluding the OTHER swap operand (strictly smaller)
        have hFy : Faithful y (applySeqR init_st (σ ++ α)) := by
          refine faithful_of_ih Cfg E n ih S hcard hdc (σ ++ α) y m hpre_subS hyS hmS
            hym hmnpre hynpre hpre_nd ?_ ?_
          · refine respects_concat hpre_resp ?_
            intro g hg
            rcases List.mem_append.mp hg with h1 | h2
            · exact respects_cross h₂r g h1 y (List.mem_cons_of_mem _ hyτ)
            · have hτss : (α ++ y :: β).Sublist (σ ++ m :: (α ++ y :: β)) :=
                List.Sublist.trans (List.sublist_cons_self m _)
                  (List.sublist_append_right σ _)
              exact respects_cross (respects_sublist hτss h₂r) g h2 y List.mem_cons_self
          · intro g hg z hzE hzg hlo
            rcases List.mem_append.mp hg with h1 | h2
            · exact hcl g h1 z hzE hzg hlo
            · rw [List.mem_singleton] at h2; subst h2
              exact hcly z hzE hzg hlo
        have hFm : Faithful m (applySeqR init_st (σ ++ α)) := by
          refine faithful_of_ih Cfg E n ih S hcard hdc (σ ++ α) m y hpre_subS hmS hyS
            (Ne.symm hym) hynpre hmnpre hpre_nd ?_ ?_
          · refine respects_concat hpre_resp ?_
            intro g hg
            exact hmax g (hpre_subS g hg) (fun e => hmnpre (e ▸ hg))
          · intro g hg z hzE hzg hlo
            rcases List.mem_append.mp hg with h1 | h2
            · exact hcl g h1 z hzE hzg hlo
            · rw [List.mem_singleton] at h2; subst h2
              exact hclm z hzE hzg hlo
        -- freshness and distinct ids from the configuration
        have hfy : fresh_ts y (applySeqR init_st (σ ++ α)) :=
          fresh_ts_config C E hE hids0 (σ ++ α) hpre_subE y hyE hynpre
        have hfm : fresh_ts m (applySeqR init_st (σ ++ α)) :=
          fresh_ts_config C E hE hids0 (σ ++ α) hpre_subE m hmE hmnpre
        have hdist : y.1 ≠ m.1 := C.distinctTs E hE hyE hmE hym
        -- NoFreshClash both ways: accuracy at each operand's dependency prefix
        -- (GenDisc2) + the other's freshness there (live/dead separation)
        set dy : List op_t := (σ ++ α).filter
          (fun z => decide (loOnA RGACondSig Cfg E z y)) with hdy
        have hdy_mem : ∀ z, z ∈ dy ↔ (z ∈ σ ++ α ∧ loOnA RGACondSig Cfg E z y) := by
          intro z; simp only [hdy, List.mem_filter, decide_eq_true_iff]
        have hdysub : dy.Sublist (σ ++ α) := by rw [hdy]; exact List.filter_sublist
        have hdysubE : ∀ z ∈ dy, z ∈ E := fun z hz => hpre_subE z (hdysub.subset hz)
        have hdepy : IsDepPre Cfg E y dy := by
          refine ⟨hdysubE, List.Nodup.sublist hdysub hpre_nd,
            respects_sublist hdysub hpre_resp, ?_, fun z hz => ((hdy_mem z).mp hz).2⟩
          intro z hzE hzy hlo
          exact (hdy_mem z).mpr ⟨hcly z hzE hzy hlo, hlo⟩
        have haccy := (hGen y hyE).2 dy hdepy
        have hfrm : fresh_ts m (applySeqR init_st dy) :=
          fresh_ts_config C E hE hids0 dy hdysubE m hmE
            (fun h => hmnpre (hdysub.subset h))
        have hclash_ym : NoFreshClash y m :=
          noFreshClash_of_accurate_fresh y m _ haccy hfrm (hGen m hmE).1
        set dm : List op_t := (σ ++ α).filter
          (fun z => decide (loOnA RGACondSig Cfg E z m)) with hdm
        have hdm_mem : ∀ z, z ∈ dm ↔ (z ∈ σ ++ α ∧ loOnA RGACondSig Cfg E z m) := by
          intro z; simp only [hdm, List.mem_filter, decide_eq_true_iff]
        have hdmsub : dm.Sublist (σ ++ α) := by rw [hdm]; exact List.filter_sublist
        have hdmsubE : ∀ z ∈ dm, z ∈ E := fun z hz => hpre_subE z (hdmsub.subset hz)
        have hdepm : IsDepPre Cfg E m dm := by
          refine ⟨hdmsubE, List.Nodup.sublist hdmsub hpre_nd,
            respects_sublist hdmsub hpre_resp, ?_, fun z hz => ((hdm_mem z).mp hz).2⟩
          intro z hzE hzm hlo
          exact (hdm_mem z).mpr ⟨hclm z hzE hzm hlo, hlo⟩
        have haccm := (hGen m hmE).2 dm hdepm
        have hfry : fresh_ts y (applySeqR init_st dm) :=
          fresh_ts_config C E hE hids0 dm hdmsubE y hyE
            (fun h => hynpre (hdmsub.subset h))
        have hclash_my : NoFreshClash m y :=
          noFreshClash_of_accurate_fresh m y _ haccm hfry (hGen y hyE).1
        -- the faithful swap (NEITHER operand accurate)
        exact eqSwap_of_bothFaithful _ y m hdist h0 hwf hmono hfy hfm hFy hFm
          hclash_ym hclash_my
      have hb := bubble_eq m τ [] (applySeqR init_st σ) hsw
      rw [List.append_nil] at hb
      exact hb
    -- converge the m-less enumerations by (Conv (S \ {m})), and finish
    have hSmdc : DC Cfg E (S.erase m) := by
      refine ⟨fun z hz => hdc.1 z (Finset.mem_of_mem_erase hz), ?_⟩
      intro w hw z hz hzw hlo
      have hzS : z ∈ S := hdc.2 w (Finset.mem_of_mem_erase hw) z hz hzw hlo
      refine Finset.mem_erase.mpr ⟨?_, hzS⟩
      rintro rfl
      exact hmax w (Finset.mem_of_mem_erase hw) (Finset.mem_erase.mp hw).1 hlo
    have hSmcard : (S.erase m).card ≤ n := by
      rw [Finset.card_erase_of_mem hmS]; omega
    have hrec : eq (applySeqR init_st ρ₁) (applySeqR init_st (σ ++ τ)) :=
      (ih (S.erase m) hSmcard hSmdc).1 ρ₁ (σ ++ τ) hρ₁perm hστperm h₁resp hστresp
    have hstep : eq (do_ (applySeqR init_st ρ₁) m) (do_ (applySeqR init_st (σ ++ τ)) m) :=
      do_eq_congr _ _ hrec m
    have e₁ : applySeqR init_st (ρ₁ ++ [m]) = do_ (applySeqR init_st ρ₁) m := by
      rw [applySeqR_append]; rfl
    have e₂ : applySeqR init_st ((σ ++ τ) ++ [m]) = do_ (applySeqR init_st (σ ++ τ)) m := by
      rw [applySeqR_append]; rfl
    have e₃ : applySeqR init_st ((σ ++ τ) ++ [m])
        = applySeqR (applySeqR init_st σ) (τ ++ [m]) := by
      rw [List.append_assoc, applySeqR_append]
    have e₄ : applySeqR init_st (σ ++ m :: τ) = applySeqR (applySeqR init_st σ) (m :: τ) :=
      applySeqR_append init_st σ (m :: τ)
    rw [e₁, e₄]
    refine Sal.Metatheory.RGAConditionedConvergence.eq_trans _ _ _ hstep ?_
    rw [← e₂, e₃]
    exact hbubble

/-! ## §5  THE GATE — the ancestor-`Ins` arm's goal is FALSE mid-fold

The design (`REHOMING_AWARE_DESIGN.md` §Residual risk) flags exactly one risk: the
shape of `AncInsLink` versus what IH-`Faith` supplies.  The risk is REAL, and it is
not a shape mismatch but a REFUTATION.  The five-event rehoming trace

    w1 = (1,·, Ins 10 []  0)   -- node 1 at the root
    w2 = (2,·, Ins 20 []  1)   -- node 2 under 1
    wc = (3,·, Ins 30 [1] 2)   -- node 3 under 2       (concurrent with wd)
    wd = (4,·, Del    [1] 2)   -- delete node 2        (concurrent with wc)
    wo = (5,·, Ins 50 [1] 3)   -- the observed event: node 5 under 3, generated
                               -- AFTER all four, so its recorded chain of 3
                               -- SKIPS the deleted 2:  recList wo = [3, 1]

is GenDisc2-conformant (each event's recorded path is accurate at the fold of its
dependencies — §5c certifies all five, `wo`'s at BOTH dependency orders), and
`ρ = [w1, w2, wc, wd]` enumerates `wo`'s complement respecting the causal order
(`wc ∥ wd` are incomparable; everything else is ordered as listed).  Threading
`ChainFaithful (recList wo)` in place along `ρ` reaches the split
`ρ = [w1, w2] ++ wc :: [wd]` with the invariant INTACT and every fact the design
says the IH supplies IN HAND — and the step is FALSE:

* at `g2 = fold [w1, w2]` the pending list `[3, 1]` is `ChainFaithful` (§5a);
* `wc` is `Faithful`, `RecPathFaithful`, and fresh at `g2`; `g2` is root-free,
  `wf`, `id_mono` (all of `ReachInv`'s conjuncts) — §5a;
* yet `ChainFaithful (do_ g2 wc) [3, 1]` FAILS (§5b): `wc` stores `anc 3 = 2`
  (its recorded anchor `2` is still LIVE at `g2` — `wd` has not applied yet),
  while `recList wo` expects `3`'s next live entry to be `1`.  `AncInsLink`'s
  failing conjunct is exactly `resolve s R = anch` (`R = [1]` resolves to
  `1 ≠ 2`); its live-anchor conjunct `contains g2 2 = true` HOLDS.

The invariant is AHEAD of the state: `wo`'s recorded chain already accounts for
the delete `wd`, which the enumeration has not yet applied.  After `wd` the chain
HEALS (§5d): `ChainFaithful (fold ρ) [3, 1]` and `Faithful wo (fold ρ)` hold.  So
`Faith S` is TRUE on this trace while its stepwise in-place invariant is false —
the design's PROOF METHOD is refuted, not the statement.  And no strengthening of
the carried conjuncts of the form `P = Conv ∧ Faith (∧ RecPath)` helps:
`RecPathFaithful wc g2` HOLDS here and the step goal is still false. -/

namespace AncestorGate

def w1 : op_t := (1, 0, .Ins 10 [] 0)
def w2 : op_t := (2, 0, .Ins 20 [] 1)
def wc : op_t := (3, 0, .Ins 30 [1] 2)
def wd : op_t := (4, 0, .Del [1] 2)
def wo : op_t := (5, 0, .Ins 50 [1] 3)

def g1 : concrete_st := do_ init_st w1
def g2 : concrete_st := do_ g1 w2
def g4 : concrete_st := do_ (do_ g2 wc) wd
/-- The other dependency order of `wo`'s prefix (`wd` before `wc`): `wc` rehomes. -/
def g4' : concrete_st := do_ (do_ g2 wd) wc

theorem g2_is_fold : g2 = applySeqR init_st [w1, w2] := rfl
theorem g4_is_fold : g4 = applySeqR init_st [w1, w2, wc, wd] := rfl
theorem recList_wo : recList wo = [3, 1] := rfl

/-! ### §5a  The split state `g2`: everything the design's IH supplies HOLDS -/

theorem contains_g2_cases (t : ℕ) (h : contains g2 t = true) : t = 1 ∨ t = 2 := by
  simp only [g2, g1, w1, w2, do_, contains, upd, init_st, const_on, restrict, const,
    union, intersection, complement, empty, _root_.singleton, mem] at h
  grind

theorem root_free_g2 : contains g2 0 = false := by decide

theorem wf_g2 : wf g2 := by
  intro t ht
  rcases contains_g2_cases t ht with rfl | rfl <;> decide

theorem id_mono_g2 : id_mono g2 := by
  intro t ht
  rcases contains_g2_cases t ht with rfl | rfl <;> decide

/-- The threaded invariant is INTACT at the split. -/
theorem cf_g2 : ChainFaithful g2 (recList wo) :=
  (chainFaithfulB_iff g2 (recList wo)).mp (by decide)

/-- `wc` is `Faithful` at the split — what IH-`Faith` at `Tᵢ = {w1, w2, wc}` gives. -/
theorem faithful_wc_g2 : Faithful wc g2 := by
  show ClimbFaithful g2 [2, 1]
  intro _
  decide

/-- `wc` is even `RecPathFaithful` at the split (capture state `g2` itself,
`Reach.refl`) — so the design's `RecPathFaithful`-as-third-conjunct fallback
cannot rescue the step either. -/
theorem recPathFaithful_wc_g2 : RecPathFaithful wc g2 := by
  refine ⟨g2, by decide, by decide, ?_, Reach.refl⟩
  show anc g2 2 = 1 ∧ contains g2 1 = true ∧ anc g2 1 = 0
  exact ⟨by decide, by decide, by decide⟩

theorem fresh_wc_g2 : fresh_ts wc g2 := ⟨by decide, by decide⟩

/-! ### §5b  The ancestor-`Ins` step goal is FALSE -/

/-- `wc`'s recorded anchor `2` is still LIVE at the split (`AncInsLink`'s
live-anchor conjunct HOLDS — the failure is elsewhere)… -/
theorem anchor_live_g2 : contains g2 2 = true := by decide

/-- …but `recList wo`'s tail past `3` resolves to `1`, not to `wc`'s anchor `2`:
the ONE failing conjunct of `AncInsLink` (`resolve s R = anch`). -/
theorem resolve_tail_g2 : resolve g2 [1] = 1 := by decide

theorem not_ancInsLink_g2 : ¬ AncInsLink g2 (recList wo) 3 2 := by
  rintro ⟨D, R, hL, _hD, _htD, _htR, _htd, _hanch, hres⟩
  have hL2 : [3, 1] = D ++ 3 :: R := hL
  cases D with
  | nil =>
    have hR : [1] = R := by
      have h := hL2
      simp only [List.nil_append, List.cons.injEq] at h
      exact h.2
    rw [← hR] at hres
    exact absurd hres (by decide)
  | cons d D' =>
    have htl : [1] = D' ++ 3 :: R := by
      have h := hL2
      simp only [List.cons_append, List.cons.injEq] at h
      exact h.2
    have h3 : (3 : ℕ) ∈ ([1] : List ℕ) := by
      rw [htl]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    exact absurd h3 (by decide)

/-- Neither `GoodStep` arm fires: `3 ∈ recList wo` kills the concurrent-fresh arm,
`not_ancInsLink_g2` the ancestor arm. -/
theorem not_goodStep_wc_g2 : ¬ GoodStep g2 (recList wo) wc := by
  intro hg
  rcases hg with ⟨-, hnotmem⟩ | ⟨-, -, hlink⟩
  · exact hnotmem (by decide)
  · exact not_ancInsLink_g2 hlink

/-- **The raw step goal itself is FALSE** — so no side condition whatsoever can
close the ancestor-`Ins` arm at this split: after `wc`, `anc 3 = 2 ∉ [3, 1]` and
the live chain of `[3, 1]`'s head is broken until `wd` heals it. -/
theorem not_cf_after_wc : ¬ ChainFaithful (do_ g2 wc) (recList wo) := fun h =>
  absurd ((chainFaithfulB_iff (do_ g2 wc) (recList wo)).mpr h) (by decide)

/-! ### §5c  GenDisc2-conformance certificates: each event's recorded path is
accurate at the fold of its dependency set — `wo`'s in BOTH respecting orders of
`{w1, w2, wc, wd}` (`wc ∥ wd`).  The trace is inside the premises, not adversarial. -/

theorem acc_w1_init : accurate w1 init_st := Or.inl ⟨rfl, rfl⟩

theorem acc_w2_g1 : accurate w2 g1 :=
  Or.inr ⟨by decide, show anc g1 1 = 0 by decide⟩

theorem acc_wc_g2 : accurate wc g2 :=
  Or.inr ⟨by decide,
    show anc g2 2 = 1 ∧ contains g2 1 = true ∧ anc g2 1 = 0 from
      ⟨by decide, by decide, by decide⟩⟩

theorem acc_wd_g2 : accurate wd g2 :=
  Or.inr ⟨by decide,
    show anc g2 2 = 1 ∧ contains g2 1 = true ∧ anc g2 1 = 0 from
      ⟨by decide, by decide, by decide⟩⟩

theorem acc_wo_g4 : accurate wo g4 :=
  Or.inr ⟨by decide,
    show anc g4 3 = 1 ∧ contains g4 1 = true ∧ anc g4 1 = 0 from
      ⟨by decide, by decide, by decide⟩⟩

theorem acc_wo_g4' : accurate wo g4' :=
  Or.inr ⟨by decide,
    show anc g4' 3 = 1 ∧ contains g4' 1 = true ∧ anc g4' 1 = 0 from
      ⟨by decide, by decide, by decide⟩⟩

/-! ### §5d  The invariant HEALS at the end of `ρ` — `Faith` is true, the
stepwise method is what fails -/

theorem cf_g4_healed : ChainFaithful g4 (recList wo) :=
  (chainFaithfulB_iff g4 (recList wo)).mp (by decide)

theorem faithful_wo_g4 : Faithful wo g4 := by
  show ClimbFaithful g4 [3, 1]
  intro _
  decide

/-- **THE GATE VERDICT.**  A state reached by folding a causally-ordered prefix
(`g2 = fold [w1, w2]`), an observed event `o = wo`, and a pending ancestor-`Ins`
`x = wc` (`x`'s id `∈ recList o`) such that ALL facts the rehoming-aware design's
IH supplies hold — root-free, `wf`, `id_mono`, `fresh_ts x`, `Faithful x`, even
`RecPathFaithful x`, and the threaded `ChainFaithful (recList o)` — yet `x` is NOT
a `GoodStep` for `recList o`, and `ChainFaithful (do_ s x) (recList o)` is FALSE.
The in-place threading invariant of `REHOMING_AWARE_DESIGN.md` is refuted mid-fold. -/
theorem ancestorIns_step_refuted :
    ∃ (s : concrete_st) (o x : op_t),
      (∃ (t r e a : ℕ) (p : List ℕ), x = (t, r, .Ins e p a) ∧ t ∈ recList o) ∧
      contains s 0 = false ∧ wf s ∧ id_mono s ∧
      fresh_ts x s ∧ Faithful x s ∧ RecPathFaithful x s ∧
      ChainFaithful s (recList o) ∧
      ¬ GoodStep s (recList o) x ∧
      ¬ ChainFaithful (do_ s x) (recList o) :=
  ⟨g2, wo, wc,
    ⟨3, 0, 30, 2, [1], rfl, by decide⟩,
    root_free_g2, wf_g2, id_mono_g2, fresh_wc_g2, faithful_wc_g2,
    recPathFaithful_wc_g2, cf_g2, not_goodStep_wc_g2, not_cf_after_wc⟩

end AncestorGate

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — honest accounting of the rehoming-aware rebuild.

   WHAT CLOSED (0 sorry, kernel axioms only), all DepComp-FREE:
   • §1 `prefix_depClosed` — THE design crux: prefixes of a `loOnA`-respecting
     enumeration of a dependency-closed set are dependency-closed, proved with
     ONE dependency edge + position (`pred_mem_left`), NO transitivity, NO
     `DepComp`.  Prefix-closure really is free where contiguous-reorder is not.
   • §2 `faithful_at_split` — IH-Faith at the prefix-set `Tᵢ = {x₁..xᵢ} ⊊ S`
     gives `Faithful xᵢ (fold [x₁..xᵢ₋₁])`, packaged through the reused
     `faithful_of_ih` with excluded witness `o`.
   • §3 `faith_last_of_ancestor_goodSteps` — the in-place thread with the
     concurrent-fresh-`Ins` arm (`goodStep_ins_concurrent`) and the `Del` arm
     (incl. REHOMING deletes of `o`'s target/ancestors:
     `chainFaithful_doDel_faithful` inside `GoodStep`, `Faithful` from §2)
     both DISCHARGED; the `Del`-projection of the result closed via `GenDisc2`'s
     accuracy at the filter-built dependency prefix (`IsDepPre` from `DC` —
     no reorder, no `DepComp`).  The ancestor-`Ins` arm is carried as a
     `GoodStep` hypothesis in the EXISTING vocabulary (no new residual defined).
   • §4 `conv_step2` — the Conv step verbatim minus the `DepComp` binder it
     never used.  `DepComp` appears NOWHERE in this file.

   WHAT IS REFUTED (§5, `AncestorGate.ancestorIns_step_refuted`):
   the remaining arm's goal is FALSE.  The exact stuck goal of the design,

       ⊢ GoodStep (applySeqR init_st pfx) (recList o) (t, r, .Ins e p a)
         (t ∈ recList o), i.e. its only live disjunct
       ⊢ AncInsLink (applySeqR init_st pfx) (recList o) t a
         whose unmet conjunct is  ⊢ resolve s R = a,

   is refuted at `pfx = [w1, w2]`, `x = wc`, `o = wo` — with `Faithful x`,
   `RecPathFaithful x`, `fresh_ts x`, `wf`/`id_mono`/root-free, and the threaded
   `ChainFaithful (recList o)` ALL TRUE there, and even the RAW preservation goal
   `ChainFaithful (do_ s x) (recList o)` FALSE.  Consequence: the failure is not
   a missing side fact the IH could supply (the `RecPathFaithful`-third-conjunct
   fallback is also foreclosed) — the threading INVARIANT itself is wrong
   mid-fold.  `o`'s recorded chain already accounts for a concurrent `Del` (`wd`)
   that a legitimate `loOnA`-respecting enumeration may order AFTER `o`'s
   ancestor-`Ins` (`wc ∥ wd`): between them, the state's chain (`3 ← 2 ← 1`) is
   strictly finer than `recList wo = [3, 1]`, and it heals only when `wd` lands
   (§5d — `Faith` itself is TRUE on the trace).

   WHY THIS IS THE HONEST OUTCOME OF THE DESIGN, NOT A TRANSCRIPTION GAP:
   the design's ancestor-`Ins` step comment "(xᵢ's recorded anchor is the
   correct next entry)" is exactly the conjunct `resolve s R = anch` that fails —
   it presumes `o`'s recorded chain and `xᵢ`'s recorded anchor agree at the
   split, which rehoming-by-a-LATER-ordered-concurrent-`Del` breaks.  The old
   deps-first design dodged this by seating accuracy only AFTER all of `o`'s
   deps (no mid-dep invariant), at the price of the refuted `DepComp` reorder.

   REPAIR DIRECTION (out of scope here): thread a PENDING-AWARE invariant —
   `ChainFaithful s L'` where `L'` interleaves `recList o` with the ids whose
   deleting events are still in the enumeration's suffix (at `g2`:
   `L' = [3, 2, 1]`, which IS ChainFaithful, and `wc` IS its AncInsLink step) —
   i.e. an invariant indexed by the remaining suffix, healing by construction at
   each pending `Del`.  That is a new design, not this one.

   RESIDUALS UNCHANGED: merge-side `hBN`, the ≈-quotient (M5), satisfiability
   of `GenDisc2`/`ReachInv` from the execution model.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §6  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms prefix_depClosed
#print axioms faithful_at_split
#print axioms faith_last_of_ancestor_goodSteps
#print axioms conv_step2
#print axioms AncestorGate.ancestorIns_step_refuted
#print axioms AncestorGate.not_cf_after_wc
#print axioms AncestorGate.cf_g4_healed
#print axioms AncestorGate.faithful_wo_g4

end Sal.Metatheory.RGASimulInduction2
