import Sal.MRDTs.Metatheory.Development.RGA_ChainFaithful_doDel
import Sal.MRDTs.Metatheory.Development.RGA_Faithful_PBT

/-!
# The staled-`Del` gate — does `ChainFaithful` survive being threaded past a
non-`accurate` `Del`?

A DECISIVE gate for the free-canonicalization convergence bubble.  The σ-walk
reorders enumerations and visits prefix folds where an operation can be STALED
(non-`accurate`).  The threading needs `ChainFaithful` preserved across such steps,
but the proven preservation lemma `chainFaithful_doDel`
(`RGA_ChainFaithful_doDel.lean`) demands the `Del` be `accurate`.  This file decides
whether that hypothesis can be dropped.

Additive: modifies no existing file.  Counterexamples are mechanised (kernel
`decide`, transported through the proven `chainFaithfulB_iff` mirror); the positive
headline `chainFaithful_doDel_faithful` is `sorry`-free and kernel-clean (audited
below with `#print axioms`; no `sorryAx`, no `native_decide`).

## Verdicts

* **Part 1 (ancestor-`Ins` clash) — COUNTEREXAMPLE.**  `ChainFaithful s L` does NOT
  survive an `accurate`, `fresh_ts`, `id_mono`-respecting `Ins` whose fresh id lies
  IN `L`.  The `t ∉ L` hypothesis of `chainFaithful_doIns` is load-bearing, not a
  convenience — it is exactly the `NoFreshClash` guard, and dropping it breaks the
  invariant.  Witness `chainFaithful_not_preserved_under_clash_ins`.

* **Part 2 (staled `Del`) — the literal statement is REFUTED, but the boundary is
  sharp.**  `ChainFaithful s L → wf s → id_mono s → contains s 0 = false →
  ChainFaithful (do_ s (Del p x)) L` is FALSE without `accurate`:
  `chainFaithful_not_preserved_under_staled_del` exhibits a reachable-shaped `s`
  (chain `0←1←2←3` plus a live root-sibling `5`), a genuinely `ChainFaithful` list
  `[3,2,1]`, and a staled `Del [5] 2` (path `[5]` names the live sibling, NOT `2`'s
  true parent `1`) after which `ChainFaithful` fails: `2`'s child `3` is rehomed to
  the WRONG target `5`, so the top-level chain link `anc 3 = 1` becomes `anc 3 = 5`.

  The counterexample violates **exactly** `DelTargetFaithful` (`resolve s pre =
  anc s x`), i.e. the `Del`-half of `Faithful`.  And that is the whole story:
  `chainFaithful_doDel_faithful` PROVES `ChainFaithful` survives EVERY `Del`
  satisfying `Faithful` — `DelTargetFaithful` + `x ≠ 0` — WITHOUT `accurate` and
  WITHOUT `id_mono`, reusing the splice induction `core`/`addDeadBack`.  So a `Del`
  staled only by rootward deletion of its recorded chain (which keeps `resolve pre =
  anc x` by self-healing) preserves the invariant; only a `Del` whose recorded
  rehome target is genuinely wrong (not `Faithful`) breaks it.

## Fork this selects

The free bubble is salvageable **iff** the σ-walk threads `Faithful`, not raw
staleness.  Convergence may reorder through `Faithful` states (base-anchored /
delete-staled), where `chainFaithful_doDel_faithful` closes the threading; it may
NOT reorder freely into non-`Faithful` (wrong-rehome) `Del`s, which the raw
universal quantifier admits but a real delete-only execution never produces.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAStaledDelGate

open Sal.Metatheory.RGABubbleWiring
open Sal.Metatheory.RGAGeneralSwap
open Sal.Metatheory.RGAChainFaithfulDoDel
open RGAFaithfulPBT

/-! ## §1  The positive headline — `ChainFaithful` survives any `Faithful` `Del`

`chainFaithful_doDel` (proved) consumes `accurate`.  Its splice-induction core
(`RGAChainFaithfulDoDel.core`) actually only needs `resolve s pre = anc s x` at a
live target — i.e. `DelTargetFaithful`, which is strictly weaker than `accurate` and
is exactly the `Del`-half of `Faithful`.  We generalise the keystone accordingly. -/

/-- Congruence for `ChainFaithfulAux` needing `anc`-agreement only on LIVE nodes
(`ChainFaithfulAux` reads `anc` solely at live climb-targets).  Weaker `anc`
hypothesis than `RGAChainFaithfulDoDel.chainFaithfulAux_congr`; identical proof. -/
theorem chainFaithfulAux_congr_live (s₁ s₂ : concrete_st)
    (hc : ∀ k, contains s₁ k = contains s₂ k)
    (ha : ∀ k, contains s₁ k = true → anc s₁ k = anc s₂ k) :
    ∀ n M, ChainFaithfulAux s₁ n M → ChainFaithfulAux s₂ n M := by
  intro n
  induction n with
  | zero => intro M _; exact trivial
  | succ k ih =>
    intro M h
    have hres : resolve s₁ M = resolve s₂ M := resolve_dom_eq s₁ s₂ M (fun c _ => hc c)
    intro hlive2
    have hlive1 : contains s₁ (resolve s₁ M) = true := by rw [hres, hc]; exact hlive2
    simp only [ChainFaithfulAux] at h
    obtain ⟨heq, hrec⟩ := h hlive1
    refine ⟨?_, ?_⟩
    · rw [← hres, ← ha (resolve s₁ M) hlive1, ← heq]
      exact resolve_dom_eq s₂ s₁ _ (fun c _ => (hc c).symm)
    · rw [← hres]; exact ih _ hrec

/-- **`ChainFaithful` survives an arbitrary `Faithful` `Del` — no `accurate`, no
`id_mono`.**  This is the honest generalisation of `chainFaithful_doDel`: what the
σ-walk actually needs is that the `Del` remain `Faithful` (its recorded rehome target
is its target's true parent), which delete-only staling preserves — NOT full
accuracy.  Live-target case reuses the splice induction with `htgt` from
`DelTargetFaithful`; absent-target case is observationally inert under `wf`. -/
theorem chainFaithful_doDel_faithful (s : concrete_st) (t r x : ℕ) (pre L : List ℕ)
    (h0 : contains s 0 = false) (hwf : wf s)
    (hfaith : Faithful (t, r, .Del pre x) s)
    (hcf : ChainFaithful s L) :
    ChainFaithful (do_ s (t, r, .Del pre x)) L := by
  simp only [Faithful] at hfaith
  obtain ⟨_hclimb, hdtf, hx0⟩ := hfaith
  unfold ChainFaithful at hcf ⊢
  have h0' : contains (do_ s (t, r, .Del pre x)) 0 = false := by rw [contains_doDel, h0]; simp
  by_cases hxlive : contains s x = true
  · -- live target: `DelTargetFaithful` supplies the splice hypothesis
    have htgt : resolve s pre = anc s x := hdtf hxlive
    have hmain := core s t r x pre h0 hxlive htgt L.length L (le_refl _) hcf L.length
      (List.length_filter_le _ _)
    exact addDeadBack s t r x pre h0' L.length L (le_refl _) hmain
  · -- absent target: `wf` + `x ≠ 0` ⟹ state is observationally unchanged on live nodes
    have hxf : contains s x = false := by
      cases h : contains s x with
      | true => exact absurd h hxlive
      | false => rfl
    have hc : ∀ k, contains s k = contains (do_ s (t, r, .Del pre x)) k := by
      intro k
      rw [contains_doDel]
      by_cases hk : k = x
      · subst hk; rw [hxf]; simp
      · rw [show (k != x) = true by simp [hk], Bool.and_true]
    have ha : ∀ k, contains s k = true → anc s k = anc (do_ s (t, r, .Del pre x)) k := by
      intro k hk
      rw [anc_doDel]
      by_cases hax : anc s k = x
      · exfalso
        rcases hwf k hk with hz | hlv
        · exact hx0 (by rw [← hax]; exact hz)
        · rw [hax, hxf] at hlv; exact absurd hlv (by decide)
      · rw [if_neg hax]
    exact chainFaithfulAux_congr_live s (do_ s (t, r, .Del pre x)) hc ha L.length L hcf

/-! ## §2  Part 2 refutation — a staled (non-`Faithful`) `Del` breaks `ChainFaithful`

State `sDel`: chain `0←1←2←3` plus a live root-sibling `5`.  `[3,2,1]` is node `3`'s
true climb chain (genuinely `ChainFaithful`).  `Del [5] 2` claims `2`'s parent is the
live sibling `5` (it is really `1`) — a non-`accurate`, non-`Faithful` `Del`.  It
rehomes `2`'s child `3` to the wrong node `5`, so `ChainFaithful` fails. -/

/-- Chain `0←1←2←3` plus a live root-sibling `5`. -/
def sDel : concrete_st :=
  upd (upd (upd (upd init_st 1 (100, 0)) 2 (100, 1)) 3 (100, 2)) 5 (100, 0)

/-- Node `3`'s true climb chain. -/
def Lgood : List ℕ := [3, 2, 1]

/-- The staled delete: target `2`, path `[5]` (names the live sibling, not `2`'s true
parent `1`).  `t`/`r` are irrelevant to a `Del`. -/
def delBad : op_t := (0, 0, .Del [5] 2)

/-- Only the domain elements `{1,2,3,5}` are live in `sDel`. -/
theorem contains_sDel (t : ℕ) :
    contains sDel t = true → t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 5 := by
  intro h
  simp only [sDel, contains, upd, init_st, const_on, restrict, const,
    union, intersection, complement, empty, _root_.singleton, mem] at h
  grind

theorem wf_sDel : wf sDel := by
  intro t ht; rcases contains_sDel t ht with rfl | rfl | rfl | rfl <;> decide

theorem id_mono_sDel : id_mono sDel := by
  intro t ht; rcases contains_sDel t ht with rfl | rfl | rfl | rfl <;> decide

/-- `[3,2,1]` is genuinely `ChainFaithful` in `sDel` (live climb-target `3`, whose
whole chain `3←2←1←root` is recorded correctly). -/
theorem cf_sDel : ChainFaithful sDel Lgood :=
  (chainFaithfulB_iff sDel Lgood).mp (by decide)

/-- The `Del` is STALED (non-`accurate`): `2`'s recorded path `[5]` is wrong. -/
theorem staled_delBad : ¬ accurate delBad sDel := by
  intro hacc
  simp only [delBad, accurate, opLeaf, opPath] at hacc
  rcases hacc with ⟨h, _⟩ | ⟨_, hpath⟩
  · exact absurd h (by decide)
  · simp only [IsAncPath] at hpath
    exact absurd hpath.1 (by decide)

/-- After the staled `Del`, `ChainFaithful` FAILS: `3` is rehomed to the wrong `5`. -/
theorem not_cf_after_delBad : ¬ ChainFaithful (do_ sDel delBad) Lgood := by
  intro h
  have hb : chainFaithfulB (do_ sDel delBad) Lgood = true := (chainFaithfulB_iff _ _).mpr h
  revert hb; decide

/-- **DECISIVE (part 2): `ChainFaithful` is NOT preserved by an arbitrary staled
`Del`.**  There is a `wf`, `id_mono`, root-free state, a genuinely `ChainFaithful`
list, and a non-`accurate` `Del` after which `ChainFaithful` fails.  Hence the
`accurate` hypothesis of `chainFaithful_doDel` cannot be dropped for FREE (arbitrary)
staling — the free convergence bubble may not reorder through non-`Faithful` `Del`s.
Contrast `chainFaithful_doDel_faithful` (§1): the counterexample's `Del` violates
precisely `DelTargetFaithful`, which is what separates the two regimes. -/
theorem chainFaithful_not_preserved_under_staled_del :
    ∃ (s : concrete_st) (t r x : ℕ) (pre L : List ℕ),
      wf s ∧ id_mono s ∧ contains s 0 = false ∧
      ¬ accurate (t, r, .Del pre x) s ∧
      ChainFaithful s L ∧
      ¬ ChainFaithful (do_ s (t, r, .Del pre x)) L :=
  ⟨sDel, 0, 0, 2, [5], Lgood, wf_sDel, id_mono_sDel, by decide,
   staled_delBad, cf_sDel, not_cf_after_delBad⟩

/-! ## §3  Part 1 refutation — an ancestor-`Ins` clash breaks `ChainFaithful`

State `sIns`: two live root-children `2` and `8`.  `L = [8,5]` is `ChainFaithful`
(`5` is dead, so it is skipped; `8`'s parent is the root).  Insert the FRESH id `5`
(which is IN `L`) anchored at `2` — an `accurate`, `fresh_ts`, `id_mono`-respecting
`Ins`.  Now `5` is live with parent `2`, but `L` records `5` as `8`'s ancestor, so
re-resolving `[8,5]` below `8` lands on the live `5 ≠ 0 = anc 8`: `ChainFaithful`
fails.  This is the "ancestor-`Ins` clash" `chainFaithful_doIns` excludes via
`t ∉ L`; the exclusion is genuinely necessary. -/

/-- Two live root-children `2` and `8`. -/
def sIns : concrete_st := upd (upd init_st 2 (100, 0)) 8 (100, 0)

/-- The clash list: records the fresh id `5` as an ancestor of the live head `8`. -/
def Lclash : List ℕ := [8, 5]

/-- The clashing insert: fresh id `5 ∈ Lclash`, anchored at the live `2`. -/
def insClash : op_t := (5, 0, .Ins 100 [] 2)

theorem contains_sIns (t : ℕ) : contains sIns t = true → t = 2 ∨ t = 8 := by
  intro h
  simp only [sIns, contains, upd, init_st, const_on, restrict, const,
    union, intersection, complement, empty, _root_.singleton, mem] at h
  grind

theorem wf_sIns : wf sIns := by
  intro t ht; rcases contains_sIns t ht with rfl | rfl <;> decide

theorem id_mono_sIns : id_mono sIns := by
  intro t ht; rcases contains_sIns t ht with rfl | rfl <;> decide

theorem cf_sIns : ChainFaithful sIns Lclash :=
  (chainFaithfulB_iff sIns Lclash).mp (by decide)

theorem accurate_insClash : accurate insClash sIns := by
  refine Or.inr ⟨by decide, ?_⟩
  show IsAncPath sIns 2 []
  show anc sIns 2 = 0
  decide

theorem fresh_insClash : fresh_ts insClash sIns := by
  simp only [insClash, fresh_ts]; exact ⟨by decide, by decide⟩

theorem not_cf_after_insClash : ¬ ChainFaithful (do_ sIns insClash) Lclash := by
  intro h
  have hb : chainFaithfulB (do_ sIns insClash) Lclash = true := (chainFaithfulB_iff _ _).mpr h
  revert hb; decide

/-- **Part 1: `ChainFaithful` is NOT preserved by an `accurate` `Ins` whose fresh id
lies in `L`.**  Even with `accurate`, `fresh_ts`, `wf`, `id_mono` and root-freedom,
the ancestor-`Ins` clash breaks the invariant — so the `t ∉ L` side condition of
`chainFaithful_doIns` (the `NoFreshClash` guard) is load-bearing. -/
theorem chainFaithful_not_preserved_under_clash_ins :
    ∃ (s : concrete_st) (t r e a : ℕ) (pre L : List ℕ),
      wf s ∧ id_mono s ∧ contains s 0 = false ∧
      accurate (t, r, .Ins e pre a) s ∧ fresh_ts (t, r, .Ins e pre a) s ∧
      t ∈ L ∧ ChainFaithful s L ∧
      ¬ ChainFaithful (do_ s (t, r, .Ins e pre a)) L :=
  ⟨sIns, 5, 0, 100, 2, [], Lclash, wf_sIns, id_mono_sIns, by decide,
   accurate_insClash, fresh_insClash, by decide, cf_sIns, not_cf_after_insClash⟩

/-! ## §4  Axiom audit -/

#print axioms chainFaithfulAux_congr_live
#print axioms chainFaithful_doDel_faithful
#print axioms chainFaithful_not_preserved_under_staled_del
#print axioms chainFaithful_not_preserved_under_clash_ins

end Sal.Metatheory.RGAStaledDelGate
