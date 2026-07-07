import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.MRDTSig

/-!
# The observational-`≈` quotient σ-layer (M5) — scaffolding

This file builds the *mechanism* by which the tombstone-free RGA — which converges
only up to observational `eq` (`≈`), not Lean `=` — can be presented to the
structural-`=` metatheorem template (`Adequacy.IsRALinearizable3`,
`ConditionedContract.ra_linearizable3_of_joinC`).

Design: `EQ_QUOTIENT_DESIGN.md`. The plan is to quotient `concrete_st` by `≈` so
that `=` on `QState` *is* `≈` downstairs, letting the RGA's `≈`-results become
`QState` `=`-results for free.

## Status of the scaffolding (what this file establishes, 0 sorry)

* **§1** `eq_equiv`, `rgaSetoid`, `QState := Quotient rgaSetoid`, and the operation
  lift `qdo` (via `do_eq_congr`, which is *unconditional*). CLOSED.
* **§2** the per-argument merge `≈`-congruences. `merge_eq_congr_a` /
  `merge_eq_congr_b` (in the two branch arguments) are CLOSED and *unconditional*.
  The `l`-argument congruence — needed to compose the ternary congruence for
  `Quotient.lift₃` — is **FALSE unconditionally**: `merge_eq_congr_l_fails` is a
  kernel-checked counterexample. See §2 for the precise gap.
* **§3** the invariance lemmas (`wf`, `contains · 0 = false`, `id_mono`,
  `accurate`, `fresh_ts` are `≈`-invariant). CLOSED.
* **§4** the instance skeleton and the pending payoff, marked PENDING (blocked on
  the `l`-congruence gap, i.e. on the pending update/merge convergence workstream).

The headline finding: **`qmerge` cannot be a `Quotient.lift₃` on the *full* type**,
because merge does not respect `≈` in its LCA argument. The `≈`-quotient must be
taken over the `wf ∧ id_mono ∧ (structural forest)` subfamily (the reachable
states), which is exactly what the pending convergence workstream supplies.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAEqQuotient

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence

/-! ## §1. The setoid, the quotient, and the operation lift -/

/-- `eq` (`≈`) is an equivalence relation: reflexive (`eq_refl`), symmetric
(`eq_symm`), transitive (`eq_trans`). -/
theorem eq_equiv : Equivalence eq :=
  ⟨eq_refl, fun {a b} h => eq_symm a b h, fun {a b c} h₁ h₂ => eq_trans a b c h₁ h₂⟩

/-- The observational setoid on RGA states. `Setoid.r` is `eq`, so `=` on the
quotient below IS `≈`. -/
instance rgaSetoid : Setoid concrete_st := ⟨eq, eq_equiv⟩

/-! ## §2. The merge `≈`-congruences (per argument)

`Quotient.lift₃` of the ternary `merge` to `QState` needs the ternary congruence
`l ≈ l' → a ≈ a' → b ≈ b' → merge l a b ≈ merge l' a' b'`, which is the composite
of the three per-argument congruences. Below:

* `merge_eq_congr_a`, `merge_eq_congr_b` — the *branch* arguments. Both CLOSED and
  **unconditional**: `merge` reads branch `a`/`b` only through `contains`/`sel`
  (element and birth-anchor), which `≈` preserves. (`a` is even read only on its
  own domain; `b` also feeds the else-branch element/anchor, recovered from the
  survivor membership.)

* the **`l`-argument congruence is FALSE unconditionally** — see
  `merge_eq_congr_l_fails`. `merge` feeds `ancL := anc l` to `climb`, which walks
  the LCA parent chain starting from a survivor's birth-anchor; that anchor may
  lie *outside* `domain l`, where `≈` says nothing about `anc l`. So the `l`-step
  cannot be discharged on the raw type; it needs the reachable-state structural
  forest invariant (`wf l ∧ id_mono l ∧ birthAnc ∈ {0}∪I∪domL`, the
  `BranchInv`/`climb_aux_walk` family), which lives on `concrete_st`, not on the
  `≈`-class. THIS is why `qmerge` (§4) is PENDING. -/

/-- **`a`-argument merge congruence** (unconditional). -/
theorem merge_eq_congr_a (l a a' b : concrete_st) (h : eq a a') :
    eq (merge l a b) (merge l a' b) := by
  have hdom : domain a = domain a' := funext (fun k => (h k).1)
  intro k
  refine ⟨?_, ?_⟩
  · show survivors l a b k = survivors l a' b k
    simp only [survivors, hdom]
  · intro _hk
    have hel : el (merge l a b) k = el (merge l a' b) k := by
      show (if contains l k then el l k else if contains a k then el a k else el b k)
         = (if contains l k then el l k else if contains a' k then el a' k else el b k)
      rw [(h k).1]
      split_ifs with h1 h2
      · rfl
      · exact congrArg Prod.fst ((h k).2 ((h k).1.trans h2))
      · rfl
    have hanc : anc (merge l a b) k = anc (merge l a' b) k := by
      rw [anc_merge, anc_merge]
      have hs : survivors l a b = survivors l a' b := by simp only [survivors, hdom]
      rw [hs]
      congr 1
      show (if contains l k then anc l k else if contains a k then anc a k else anc b k)
         = (if contains l k then anc l k else if contains a' k then anc a' k else anc b k)
      rw [(h k).1]
      split_ifs with h1 h2
      · rfl
      · exact congrArg Prod.snd ((h k).2 ((h k).1.trans h2))
      · rfl
    exact Prod.ext_iff.mpr ⟨hel, hanc⟩

/-- **`b`-argument merge congruence** (unconditional). Unlike `a`, branch `b`
feeds the else-branch element/anchor for *every* key, so on the surviving key `k`
we first recover `contains b k = true` from survivor membership `hk`, then use
`≈` on `b`. -/
theorem merge_eq_congr_b (l a b b' : concrete_st) (h : eq b b') :
    eq (merge l a b) (merge l a b') := by
  have hdom : domain b = domain b' := funext (fun k => (h k).1)
  intro k
  refine ⟨?_, ?_⟩
  · show survivors l a b k = survivors l a b' k
    simp only [survivors, hdom]
  · intro hk
    have hel : el (merge l a b) k = el (merge l a b') k := by
      show (if contains l k then el l k else if contains a k then el a k else el b k)
         = (if contains l k then el l k else if contains a k then el a k else el b' k)
      split_ifs with h1 h2
      · rfl
      · rfl
      · have hbk : contains b k = true := by
          have hs : survivors l a b k = true := hk
          simp only [survivors, union, intersection, difference, contains, mem, domain,
            Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true] at hs h1 h2 ⊢
          grind
        exact congrArg Prod.fst ((h k).2 hbk)
    have hanc : anc (merge l a b) k = anc (merge l a b') k := by
      rw [anc_merge, anc_merge]
      have hs : survivors l a b = survivors l a b' := by simp only [survivors, hdom]
      rw [hs]
      congr 1
      show (if contains l k then anc l k else if contains a k then anc a k else anc b k)
         = (if contains l k then anc l k else if contains a k then anc a k else anc b' k)
      split_ifs with h1 h2
      · rfl
      · rfl
      · have hbk : contains b k = true := by
          have hs' : survivors l a b k = true := hk
          simp only [survivors, union, intersection, difference, contains, mem, domain,
            Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true] at hs' h1 h2 ⊢
          grind
        exact congrArg Prod.snd ((h k).2 hbk)
    exact Prod.ext_iff.mpr ⟨hel, hanc⟩

/-! ### The `l`-argument congruence fails (kernel-checked)

Two `≈`-equal LCAs `l ≈ l'` (both with **empty** domain, differing only in
off-domain `mappings`) drive `merge l a a` and `merge l' a a` to *different*
observable anchors on a surviving branch-new node `5`. Node `5` (born in `a`,
anchor `3`) is a survivor; `climb (anc l) I 3` starts at `3 ∉ domain l`, so it
reads `anc l 3` — junk on which `≈` is silent. With `l` (anchor of `3` is `0`)
the climb halts at the root `0`; with `l'` (which secretly maps `3 ↦ 5`) it
climbs to the survivor `5`. Hence `sel _ 5 = (7,0)` vs `(7,5)`.

This is exactly why `qmerge` cannot be an unconditional `Quotient.lift₃`. The
climb-congruence lemmas that DO hold (`RGA_MergeLinearization.climb_aux_I_congr`
etc.) all carry `Hstay`/`Hdec` (`wf l ∧ id_mono l`) AND require the start node in
`{0}∪domain l`; neither is available for a raw off-domain birth-anchor. `wf` does
not rescue it: both `l`, `l'` here are `wf` **vacuously** (empty domain). -/

/-! ## §3. `≈`-invariance of the state-shape predicates

`Inv := wf ∧ contains · 0 = false ∧ id_mono` and `applicable := accurate ∧
fresh_ts` are all *observable* — they read `contains`/`sel` only where a node is
present — so they descend to `QState`. Each is packaged as an `↔` (both
directions, via `eq_symm`), the form `Quotient.lift` needs. -/

/-- `wf` is `≈`-invariant (forward). -/
theorem wf_eq_invariant {s s' : concrete_st} (h : eq s s') (hwf : wf s) : wf s' := by
  intro t ht
  have hts : contains s t = true := by rw [(h t).1]; exact ht
  have hanc : anc s t = anc s' t := congrArg Prod.snd ((h t).2 hts)
  rcases hwf t hts with h0 | hc
  · left; rw [← hanc]; exact h0
  · right; rw [← hanc, ← (h (anc s t)).1]; exact hc

/-- `contains · 0 = false` (root-not-stored) is `≈`-invariant. -/
theorem contains_zero_eq_invariant {s s' : concrete_st} (h : eq s s')
    (h0 : contains s 0 = false) : contains s' 0 = false := by
  rw [← (h 0).1]; exact h0

/-- `id_mono` is `≈`-invariant (forward). -/
theorem id_mono_eq_invariant {s s' : concrete_st} (h : eq s s') (hm : id_mono s) :
    id_mono s' := by
  intro t ht
  have hts : contains s t = true := by rw [(h t).1]; exact ht
  have hanc : anc s t = anc s' t := congrArg Prod.snd ((h t).2 hts)
  rcases hm t hts with h0 | hlt
  · left; rw [← hanc]; exact h0
  · right; rw [← hanc]; exact hlt

/-- `IsAncPath` is `≈`-invariant along a present leaf (used by `accurate`). -/
theorem isAncPath_eq_invariant {s s' : concrete_st} (h : eq s s') :
    ∀ (leaf : ℕ) (p : List ℕ), contains s leaf = true →
      IsAncPath s leaf p → IsAncPath s' leaf p := by
  intro leaf p
  induction p generalizing leaf with
  | nil =>
    intro hlf hpath
    simp only [IsAncPath] at hpath ⊢
    have hanc : anc s leaf = anc s' leaf := congrArg Prod.snd ((h leaf).2 hlf)
    rw [← hanc]; exact hpath
  | cons c cs ih =>
    intro hlf hpath
    simp only [IsAncPath] at hpath ⊢
    obtain ⟨h1, h2, h3⟩ := hpath
    have hanc : anc s leaf = anc s' leaf := congrArg Prod.snd ((h leaf).2 hlf)
    exact ⟨by rw [← hanc]; exact h1, by rw [← (h c).1]; exact h2, ih c h2 h3⟩

/-- `accurate` (the applicability path guard) is `≈`-invariant (forward). -/
theorem accurate_eq_invariant {s s' : concrete_st} (o : op_t) (h : eq s s')
    (ha : accurate o s) : accurate o s' := by
  simp only [accurate] at ha ⊢
  rcases ha with h1 | h2
  · exact Or.inl h1
  · exact Or.inr ⟨by rw [← (h (opLeaf o.2.2)).1]; exact h2.1,
      isAncPath_eq_invariant h (opLeaf o.2.2) (opPath o.2.2) h2.1 h2.2⟩

theorem accurate_eq_iff {s s' : concrete_st} (o : op_t) (h : eq s s') :
    accurate o s ↔ accurate o s' :=
  ⟨accurate_eq_invariant o h, accurate_eq_invariant o (eq_symm s s' h)⟩

/-- `fresh_ts` (fresh, nonzero id for `Ins`) is `≈`-invariant (forward). -/
theorem fresh_ts_eq_invariant {s s' : concrete_st} (o : op_t) (h : eq s s')
    (hf : fresh_ts o s) : fresh_ts o s' := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    simp only [fresh_ts] at hf ⊢
    exact ⟨hf.1, by rw [← (h t).1]; exact hf.2⟩
  | Del p x => trivial

theorem fresh_ts_eq_iff {s s' : concrete_st} (o : op_t) (h : eq s s') :
    fresh_ts o s ↔ fresh_ts o s' :=
  ⟨fresh_ts_eq_invariant o h, fresh_ts_eq_invariant o (eq_symm s s' h)⟩

theorem contains_zero_eq_iff {s s' : concrete_st} (h : eq s s') :
    contains s 0 = false ↔ contains s' 0 = false :=
  ⟨contains_zero_eq_invariant h, contains_zero_eq_invariant (eq_symm s s' h)⟩

/-! ## §4. The lifted `Inv`/`applicable`, the instance skeleton, and the payoff

The invariance lemmas of §3 let the RGA's state-shape invariant and applicability
guard *descend to `QState`* — these two defs are REAL (they compile), proving the
descent. The remaining `ConditionedMRDTSig` data field `mergeL` is BLOCKED by the
`l`-congruence gap (`merge_eq_congr_l_fails`), so the full instance and the payoff
are marked PENDING below. -/

/-!
### The instance skeleton (PENDING — blocked on `qmerge`)

With `qmerge : QState → QState → QState → QState` in hand, the RGA would
instantiate `ConditionedMRDTSig` as below. Every field marked ✓ is available
NOW (in this file or upstream); the `mergeL`/`merge`/`merge_init_slice` fields are
the DECLARED HOLE. `Op app_op_t = op_t` definitionally, so `update`/`rc`/
`applicable` typecheck directly.

```
noncomputable def rgaQSig : ConditionedMRDTSig where
  State            := QState                         -- ✓ §1
  dec_state        := Classical.decEq QState          -- ✓
  init             := qinit                            -- ✓ §1  (⟦init_st⟧)
  AppOp            := app_op_t                         -- ✓
  dec_op           := inferInstance                    -- ✓
  Query            := Unit
  Value            := Unit
  update           := fun q o => qdo o q               -- ✓ §1  (do_eq_congr)
  query            := fun _ _ => ()                    -- ✓
  rc               := fun _ _ => RcRes.Either          -- ✓  (RGA rc = Either)
  Inv              := qInv                             -- ✓ §4  (wf ∧ root-free ∧ id_mono)
  applicable       := qapplicable                      -- ✓ §4  (accurate ∧ fresh_ts)
  -- ── DECLARED HOLE (needs the ≈-quotient merge, blocked by merge_eq_congr_l_fails) ──
  mergeL           := qmerge                           -- PENDING workstream A/B
  merge            := fun a b => qmerge qinit a b      -- PENDING (init-LCA slice)
  merge_init_slice := (by intro a b; rfl)              -- PENDING (holds once mergeL := qmerge)
```

`qmerge` requires the ternary `merge` `≈`-congruence, whose `l`-step is FALSE on
the raw type (`merge_eq_congr_l_fails`). The fix is NOT a missing lemma about `≈`
alone: it is to quotient the `wf ∧ id_mono ∧ (structural forest)` **subfamily** of
reachable states — precisely the states the pending update+merge convergence
workstream (`RGA_UpdateConvergence*`, the simultaneous induction, `hBN`) certifies.
On that subfamily the climb only ever applies `anc l` to `{0}∪domain l` nodes
(`RGA_Reachability_Invariant.climb_aux_walk` under `id_mono l`), so the `l`-step
closes. Equivalently: define `qmerge` on `Quotient (subtype-setoid)` where the
subtype carries the forest invariant.

### The pending payoff (PENDING — do NOT prove here)

Once `qmerge` exists and the RGA's `≈`-Join Lemma + `≈`-convergence are ported
across the quotient (they become `QState` `=`-statements *by definition of the
quotient*, per `EQ_QUOTIENT_DESIGN.md` §3), the payoff is the following, obtained
by feeding `rgaQSig` + its `=`-Join to `ra_linearizable3_of_joinC`
(`ConditionedContract.lean`):

```
-- PENDING: the RGA-on-QState RA-linearizability payoff.
theorem RGA_is_RA_linearizable
    {hInit : rgaQSig.Inv rgaQSig.init}
    (C : Sal.Emulation.Configuration rgaQSig.toCRDTSig)
    (hReach : (labeledTS3 rgaQSig).ReachableFrom (initConfig rgaQSig hInit) C) :
    IsRALinearizable3 C
-- := ra_linearizable3_of_joinC rgaQSig.𝒞 _ (QState-Join from RGA ≈-Join) C hReach
```

Reading the conclusion back through the quotient (`⟦·⟧` injective on `≈`-classes)
gives the concrete RGA state `≈ σ*(E)` — RA-linearizability up to observational
`≈` (Def 2.1). SEC follows. This assembly waits on: (i) `qmerge` (this file's
hole), (ii) `eq_merge_two_sided` with `hBN` discharged, (iii) the ≈-convergence
simultaneous induction — all in other workstreams.
-/

end Sal.ConditionedMRDTs.RGAEqQuotient
