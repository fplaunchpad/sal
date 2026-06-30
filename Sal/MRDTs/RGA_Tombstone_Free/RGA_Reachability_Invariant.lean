import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT

/-!
# Tombstone-free RGA: the conditioning predicates as a reachable-state invariant

This file instantiates the **keystone** of `Sal/Metatheory/BLUEPRINT.md` for the
flagship tombstone-free RGA (`RGA_Tombstone_Free_MRDT.lean`):

> *A conditioned VC is sound iff its conditioning predicate is a reachable-state
> invariant under `do_`/`merge`.*

The flagship's commutation VC `rc_non_comm'` is conditioned on three premises
(`commutes_with'`):

* `contains s 0 = false` — the root sentinel is never a stored key;
* `wf s`              — the *forest invariant*
  `∀ t, contains s t → (anc s t = 0 ∨ contains s (anc s t))`;
* `accurate o s` / `fresh_ts o s` — the op's path is the true ancestor chain,
  and an `Ins` uses a fresh nonzero id.

The candidate **state** invariant is `RgaInv s := (contains s 0 = false) ∧ wf s`
(named `RgaInv` in code to avoid Mathlib's `Inv` typeclass; "`Inv`" below is this).
`accurate`/`fresh_ts` are *op-generation* conditions (they relate an op to a
state, not a state to itself), so they are NOT part of the state invariant; they
enter the inductive steps as hypotheses, exactly as they would be discharged from
the execution model (Phase 0) at the point an event is generated.

## Results (see the VERDICT block at the bottom for the full write-up)

* `Inv_init`, `Inv_doIns`, `Inv_doDel` — **PRIMARY, closed, `sorry`-free.**
  `Inv` is inductive under `init_st` and under both `do_` cases.  The `Del`
  case is the load-bearing **R2** test: `Del x` physically removes `x` yet
  rehomes its children to `resolve s pre = anc s x`, which is `0`-or-live (by
  `wf`) and `≠ x` (by `isAncPath_self`), so `wf` survives the removal.  This
  confirms R2: carry the *forest invariant* and recover positions, rather than
  "every op's path stays accurate" (which deletes falsify).

* `merge_breaks_wf` — **a machine-checked refutation**: `wf` is *not* preserved
  by `merge` from `Inv l/a/b` alone.  `climb`'s fuel (`= the node id`) is only
  sufficient when anchor ids strictly decrease along the LCA chain; without that
  the climb stops on a deleted, non-root node.  See the VERDICT.

* `Inv_merge` — **STRETCH, `sorry` on the `wf` conjunct** (the `contains 0`
  conjunct is closed).  The `sorry` is *documented-false*: it is refuted by
  `merge_breaks_wf` and needs extra hypotheses (id-monotone anchors on `l`, plus
  cross-branch anchor compatibility of `a`,`b` into `l`'s forest) that `Inv`
  alone does not provide.
-/

set_option maxHeartbeats 1000000

/-- The candidate reachable-state invariant: the root sentinel is never stored,
and the anchor pointers form a valid live forest.

Named `RgaInv` rather than `Inv` to avoid a clash with Mathlib's `Inv` typeclass
(the `⁻¹` class), which otherwise shadows a bare `Inv` in some binder positions. -/
def RgaInv (s : concrete_st) : Prop := contains s 0 = false ∧ wf s

/-! ## PRIMARY 1 — `init_st` -/

/-- `Inv` holds at the initial (empty) state: `wf` is vacuous and `0 ∉ dom`. -/
theorem Inv_init : RgaInv init_st := by
  refine ⟨?_, ?_⟩
  · simp [init_st]
  · intro t ht
    simp [init_st] at ht

/-! ## PRIMARY 2 — `do_` of an `Ins`

New key `t ≠ 0` (by `fresh_ts`) keeps `contains 0` false; the stored anchor
`resolve s (a :: pre)` is the live anchor `a` (or `0` when `a = 0`), so `wf`
is preserved; every existing node is left untouched by the `upd`. -/
theorem Inv_doIns (s : concrete_st) (t r e a : ℕ) (pre : List ℕ) (h : RgaInv s)
    (hacc : accurate (t, r, .Ins e pre a) s) (hfr : fresh_ts (t, r, .Ins e pre a) s) :
    RgaInv (do_ s (t, r, .Ins e pre a)) := by
  obtain ⟨h0, hwf⟩ := h
  simp only [fresh_ts] at hfr
  obtain ⟨ht0, _htdom⟩ := hfr
  simp only [accurate, opLeaf, opPath] at hacc
  -- reduce the effect to a path-free `upd`
  have hdo : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  rw [hdo]
  set v := resolve s (a :: pre) with hv
  -- the stored anchor is `0`-or-live in `s`
  have hvlive : v = 0 ∨ contains s v = true := by
    rcases hacc with ⟨ha0, hpnil⟩ | ⟨halive, _hpath⟩
    · left;  rw [hv, resolve_cons_eq s a pre (Or.inl ⟨ha0, hpnil, h0⟩)]; exact ha0
    · right; rw [hv, resolve_cons_eq s a pre (Or.inr halive)]; exact halive
  refine ⟨?_, ?_⟩
  · -- root sentinel stays absent
    rw [lemma_InDomUpd1, h0, Bool.or_false]
    simp [ht0]
  · -- forest invariant preserved
    intro k hk
    by_cases hkt : k = t
    · -- the freshly inserted node: its anchor is `v`, which is `0`-or-live
      have hanck : anc (upd s t (e, v)) k = v := by
        rw [hkt]; simp only [anc]; rw [lemma_SelUpd1]
      rw [hanck]
      rcases hvlive with hv0 | hvl
      · exact Or.inl hv0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hvl]; simp only [Bool.or_true]
    · -- an existing node: anchor and containment carried from `s`
      have htk : t ≠ k := fun e' => hkt e'.symm
      have hck : contains s k = true := by
        rw [lemma_InDomUpd1] at hk
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
        rcases hk with hh | hh
        · exact absurd hh htk
        · exact hh
      have hanck : anc (upd s t (e, v)) k = anc s k := by
        simp only [anc]
        rw [lemma_SelUpd2 s k t (e, v) (by simp only [bne_iff_ne, ne_eq]; exact htk)]
      rw [hanck]
      rcases hwf k hck with hanc0 | hancl
      · exact Or.inl hanc0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hancl]; simp only [Bool.or_true]

/-! ## PRIMARY 3 — `do_` of a `Del` (the load-bearing R2 test)

`Del x` physically removes `x` from the domain.  Under `accurate` the reparent
target is `resolve s pre = anc s x` (`isAncPath_resolve`), which by `wf s` is
`0`-or-live and by `isAncPath_self` is `≠ x` (since `x` is live and `0 ∉ dom`),
so it *survives* the removal.  Every child of `x` is rehomed to that survivor and
every other node keeps a still-live (or `0`) anchor: `wf` is preserved despite the
physical deletion.  This is R2 — the forest invariant is maintained under
rehoming, NOT by keeping paths accurate. -/
theorem Inv_doDel (s : concrete_st) (t r x : ℕ) (pre : List ℕ) (h : RgaInv s)
    (hacc : accurate (t, r, .Del pre x) s) :
    RgaInv (do_ s (t, r, .Del pre x)) := by
  obtain ⟨h0, hwf⟩ := h
  simp only [accurate, opLeaf, opPath] at hacc
  refine ⟨?_, ?_⟩
  · -- root sentinel stays absent (`x`'s removal cannot add `0`)
    rw [contains_doDel s t r x pre 0, h0, Bool.false_and]
  · -- forest invariant preserved
    intro k hk
    rw [contains_doDel s t r x pre k] at hk
    rw [Bool.and_eq_true] at hk
    obtain ⟨hck, _hkx⟩ := hk
    rw [anc_doDel s t r x pre k]
    -- the reparent target survives the deletion (`= 0`, or live and `≠ x`)
    have hRsurvive :
        resolve s pre = 0
          ∨ contains (do_ s (t, r, .Del pre x)) (resolve s pre) = true := by
      rcases hacc with ⟨_hx0, hpnil⟩ | ⟨hxlive, hxpath⟩
      · left; simp [hpnil]
      · have hRanc : resolve s pre = anc s x := isAncPath_resolve s x pre hxpath
        have hxne0 : x ≠ 0 := contains_ne_zero s x h0 hxlive
        have hRx : resolve s pre ≠ x := by
          rw [hRanc]; intro he; exact hxne0 (isAncPath_self s pre x hxpath he)
        rcases hwf x hxlive with hax0 | haxl
        · left; rw [hRanc]; exact hax0
        · right
          rw [contains_doDel s t r x pre (resolve s pre), Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · rw [hRanc]; exact haxl
          · simp only [bne_iff_ne, ne_eq]; exact hRx
    by_cases hax : anc s k = x
    · -- `k` was a child of the deleted `x`: rehomed to the surviving target
      rw [if_pos hax]; exact hRsurvive
    · -- `k`'s anchor is untouched: still `0`-or-live, and `≠ x` so it survives
      rw [if_neg hax]
      rcases hwf k hck with hanc0 | hancl
      · exact Or.inl hanc0
      · refine Or.inr ?_
        rw [contains_doDel s t r x pre (anc s k), Bool.and_eq_true]
        exact ⟨hancl, by simp only [bne_iff_ne, ne_eq]; exact hax⟩

#print axioms Inv_init
#print axioms Inv_doIns
#print axioms Inv_doDel

/-! ## The merge refutation (the headline merge finding)

`merge` recovers each survivor's anchor by `climb (anc l) I (betaf k)`, where
`climb ancL I x = climb_aux ancL I x x` walks the LCA's parent chain with **fuel
equal to the starting id `x`**.  That fuel is sufficient only when anchor ids
strictly decrease along the chain (then the chain from `x` has length `≤ x`).
`wf` does NOT entail decreasing ids (a node may anchor at a larger id), so the
climb can run out of fuel on a deleted, non-root node — producing an anchor that
is neither `0` nor a survivor, i.e. violating `wf`.

The witness below makes this concrete and machine-checked.  In `lCex` the chain
`1 → 2 → 9 → 8 → 7 → 0` has *increasing* ids near the leaf.  Only `1` survives the
merge (`a`,`b` keep `1`, drop `2,9,8`).  `betaf 1 = anc l 1 = 2`, and
`climb (anc l) {1} 2` runs `2 → 9 → 8` then exhausts its fuel (`= 2`) at `8`,
which is not a survivor and not `0`. -/

def lCex : concrete_st := mk [(1, 100, 2), (2, 100, 9), (9, 100, 8), (8, 100, 7), (7, 100, 0)]
def aCex : concrete_st := mk [(1, 100, 0), (7, 100, 0)]
def bCex : concrete_st := mk [(1, 100, 0)]

-- The three inputs each satisfy `Inv` (contains 0 = false ∧ wf):
#eval decide (contains lCex 0 = false)   -- true
#eval decide (contains aCex 0 = false)   -- true
#eval decide (contains bCex 0 = false)   -- true
-- Sanity dump: the merged survivor `1` ends up anchored at the dead node `8`.
#eval dump (merge lCex aCex bCex) [1,2,7,8,9]
#eval (anc (merge lCex aCex bCex) 1, contains (merge lCex aCex bCex) 8)  -- (8, false)

/-- **`wf` is not a merge invariant from `Inv l/a/b` alone.**  Even though each of
`lCex, aCex, bCex` is well-formed with `0 ∉ dom`, the merge leaves survivor `1`
anchored at `8`, which is absent and non-root.  (Uses `native_decide`: this is an
analysis artifact, not one of the primary theorems.) -/
theorem merge_breaks_wf : ¬ wf (merge lCex aCex bCex) := by
  intro hwf
  have h1 : contains (merge lCex aCex bCex) 1 = true := by native_decide
  rcases hwf 1 h1 with hz | hc
  · exact absurd hz (by native_decide)
  · exact absurd hc (by native_decide)

#print axioms merge_breaks_wf   -- uses `Lean.ofReduceBool` (native_decide); analysis-only

/-! ## STRETCH 4 — `Inv_merge`

The `contains 0 = false` conjunct holds from `Inv l/a/b` (a node `0` could only
be in the merged domain `I` if it were in some input domain, which it is not).
The `wf` conjunct is **not** provable from `Inv l/a/b`: it is exactly the property
refuted by `merge_breaks_wf` above.

What the `wf` conjunct genuinely needs, on top of `Inv l/a/b`:

1. `id_mono l : ∀ t, contains l t → (anc l t = 0 ∨ anc l t < t)` — id-monotone
   anchors on the LCA, so that `climb`'s fuel (`= the node id`) always reaches a
   `0`-or-survivor before running out; AND
2. cross-branch compatibility: every `betaf`-chain of a survivor enters `l`'s
   forest (so walking `anc l` is meaningful for nodes added in `a`/`b`).

Neither follows from `wf`, and (1) is *not even a `do_`-invariant* under the
abstract `fresh_ts` (inserting a small id anchored at a larger live node breaks
it).  It is a *generation-time* property of monotone timestamp allocation — a
Phase-0 execution-model condition, not a state invariant.  The `sorry` below marks
exactly this gap (and is, per `merge_breaks_wf`, *false* as stated). -/
theorem Inv_merge (l a b : concrete_st) (hl : RgaInv l) (ha : RgaInv a) (hb : RgaInv b) :
    RgaInv (merge l a b) := by
  obtain ⟨hl0, _hlwf⟩ := hl
  obtain ⟨ha0, _hawf⟩ := ha
  obtain ⟨hb0, _hbwf⟩ := hb
  refine ⟨?_, ?_⟩
  · -- root sentinel absent: closed from `Inv l/a/b`
    simp only [merge, contains, domain, mem] at hl0 ha0 hb0 ⊢
    grind
  · -- forest invariant: NOT provable from `Inv l/a/b` — refuted by `merge_breaks_wf`.
    -- Reduces to: for every survivor `k`, `climb (anc l) I (betaf k)` lands in
    -- `{0} ∪ I`.  This needs `id_mono l` + cross-branch compatibility (see above).
    sorry

#print axioms Inv_merge

/-! ## VERDICT — the three ANALYSIS questions

**(i) Does the keystone hold for this RGA — is `Inv` genuinely inductive under
`do_`/`merge`?**

Partly, and the partition is sharp:

* Under `init_st` and `do_` (both `Ins` and `Del`): **YES**, machine-checked,
  `sorry`-free (`Inv_init`, `Inv_doIns`, `Inv_doDel`).  `Inv = (contains 0 =
  false) ∧ wf` is inductive for the local effect.
* Under `merge`: **NO**, from `Inv l/a/b` alone.  `merge_breaks_wf` is a
  machine-checked counterexample.  `wf`-preservation under `merge` requires an
  auxiliary id-monotonicity invariant on the LCA (so `climb`'s fuel suffices) plus
  cross-branch anchor compatibility.  So the keystone's *do_* half is validated
  for this RGA, but its *merge* half needs a strictly stronger invariant than the
  one the conditioning names.

**(ii) Which conditioning is a state-invariant vs. an op-generation condition?**

* *State invariants* (relate a state to itself; live in `Inv`): `contains s 0 =
  false` and `wf s`.  Both are inductive under `do_` (proved here).
* *Op-generation conditions* (relate an op to the state it is applied to; need the
  execution model / Phase 0): `accurate o s` and `fresh_ts o s`.  These are NOT
  state predicates and cannot be "preserved" — they are discharged at the moment
  an event is generated (the `apply` rule's premises), and appear here precisely
  as hypotheses of `Inv_doIns`/`Inv_doDel`.  This matches the blueprint's
  `applicable` (= `accurate ∧ fresh_ts`) vs. `Inv` (= the forest invariant) split.

**(iii) Is R2 validated?**

For the **`do_` layer: YES, decisively.**  The `Del` case (`Inv_doDel`) is the
exact R2 scenario: a delete physically removes a node, and `wf` is preserved not
because any op's path "stays accurate" but because the rehoming target
`resolve s pre = anc s x` is itself a live-or-root survivor (`wf` + `isAncPath_self`).
Carrying the forest invariant `wf` is the right design; "paths stay accurate" is
falsified by deletes (the blueprint's §5.4 staleness risk), and is not needed.

For the **`merge` layer: R2 is too optimistic as literally stated.**  The
blueprint (§5.4 R2) claims the forest invariant is "preserved under update and
merge including Del-rehoming."  The *update* half is confirmed; the *merge* half
is **refuted** by `merge_breaks_wf`: `climb`'s fixed fuel makes `wf`-preservation
depend on monotone anchor ids, which `wf` does not supply and which `fresh_ts`
does not even make a `do_`-invariant.  The corrected statement: the conditioning
predicate `wf` is a reachable-state invariant under `do_`, but its preservation
under `merge` requires the additional generation-time discipline of monotone
timestamp allocation (id-decreasing anchors).  Establishing that as a genuine
reachable invariant is the precise remaining obligation for closing the RGA
soundness composition — a sharper research target than the blueprint anticipated.
-/
