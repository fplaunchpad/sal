import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant

/-!
# `RgaInv` is preserved on any FRESH op — accuracy is NOT needed (option 2)

`Inv_doIns`/`Inv_doDel` in `RGA_Reachability_Invariant.lean` are *stated* with
`accurate`, but for **invariant preservation** the accuracy hypothesis is only
ever consumed to learn that the resolved anchor/target is `0`-or-live.  That fact
is **unconditional** — `resolve` returns the first live entry or `0` by
definition (`resolve_zero_or_live`).  So `RgaInv` preservation needs only
*freshness*, never accuracy.

* `inv_doIns_fresh` — `Inv_doIns` with `accurate` DROPPED; `hvlive` supplied by
  `resolve_zero_or_live`.  Needs only `fresh_ts` (in fact only `t ≠ 0`).
* `inv_doDel_free` — `Inv_doDel` with `accurate` DROPPED.  Del needs **one genuine
  path fact** that freshness does not supply: `resolve s pre ≠ x` (the reparent
  target differs from the node being removed).  See the finding block at the end:
  `resolve s pre = x` really does break `wf` (a child of `x` is rehomed onto the
  now-deleted `x`), and `fresh_ts` for `Del` is `True`, so it cannot rule it out.
  This is the minimal condition, strictly weaker than `accurate`.
* `WfOp` / `rgaInv_doOp_fresh` — the combined "well-formed op" precondition the RGA
  supplies to the framework: `RgaInv s → WfOp o s → RgaInv (do_ s o)`.
-/

set_option maxHeartbeats 1000000

/-- `RgaInv` is preserved by an `Ins` from **freshness alone** (only `t ≠ 0` is
used).  This is `Inv_doIns` with the `accurate` hypothesis removed: the
`0`-or-live fact about the stored anchor comes from `resolve_zero_or_live`, not
from accuracy. -/
theorem inv_doIns_fresh (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (h : RgaInv s) (hfr : fresh_ts (t, r, .Ins e pre a) s) :
    RgaInv (do_ s (t, r, .Ins e pre a)) := by
  obtain ⟨h0, hwf⟩ := h
  simp only [fresh_ts] at hfr
  obtain ⟨ht0, _htdom⟩ := hfr
  have hdo : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  rw [hdo]
  set v := resolve s (a :: pre) with hv
  -- the stored anchor is `0`-or-live in `s` — UNCONDITIONALLY (no accuracy)
  have hvlive : v = 0 ∨ contains s v = true := by
    rw [hv]; exact resolve_zero_or_live s (a :: pre)
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

#print axioms inv_doIns_fresh

/-- `RgaInv` is preserved by a `Del` **without accuracy**, under the one genuinely
needed path fact `resolve s pre ≠ x`: the reparent target differs from the node
being physically removed.  Given that, `resolve_zero_or_live` makes the target
`0`-or-live in `s`, and `≠ x` lets it survive the deletion, so every rehomed child
lands on a live-or-root anchor and `wf` is preserved.  This is `Inv_doDel` with
`accurate` replaced by the strictly weaker `resolve s pre ≠ x`. -/
theorem inv_doDel_free (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (h : RgaInv s) (hRx : resolve s pre ≠ x) :
    RgaInv (do_ s (t, r, .Del pre x)) := by
  obtain ⟨h0, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · -- root sentinel stays absent (`x`'s removal cannot add `0`)
    rw [contains_doDel s t r x pre 0, h0, Bool.false_and]
  · -- forest invariant preserved
    intro k hk
    rw [contains_doDel s t r x pre k] at hk
    rw [Bool.and_eq_true] at hk
    obtain ⟨hck, _hkx⟩ := hk
    rw [anc_doDel s t r x pre k]
    -- the reparent target survives: `0`-or-live (resolve totality) AND `≠ x` (hRx)
    have hRsurvive :
        resolve s pre = 0
          ∨ contains (do_ s (t, r, .Del pre x)) (resolve s pre) = true := by
      rcases resolve_zero_or_live s pre with hz | hl
      · left; exact hz
      · right
        rw [contains_doDel s t r x pre (resolve s pre), Bool.and_eq_true]
        exact ⟨hl, by simp only [bne_iff_ne, ne_eq]; exact hRx⟩
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

#print axioms inv_doDel_free

/-- The **well-formed op** precondition the RGA supplies to the framework for
invariant preservation (option 2).  For `Ins` it is exactly `fresh_ts`
(`t ≠ 0 ∧ contains s t = false`; only `t ≠ 0` is actually consumed).  For `Del`
it is the single path fact `resolve s pre ≠ x` — freshness (`= True` for `Del`)
is NOT enough, see the finding block below. -/
def WfOp (o : op_t) (s : concrete_st) : Prop :=
  match o with
  | (t, _, .Ins _ _ _) => t ≠ 0 ∧ contains s t = false
  | (_, _, .Del pre x) => resolve s pre ≠ x

/-- **Invariant preserved on any well-formed op — accuracy irrelevant.**
`RgaInv s → WfOp o s → RgaInv (do_ s o)`.  The `Ins` case is pure freshness; the
`Del` case is the minimal path fact `resolve s pre ≠ x`. -/
theorem rgaInv_doOp_fresh (s : concrete_st) (o : op_t)
    (h : RgaInv s) (hw : WfOp o s) : RgaInv (do_ s o) := by
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a =>
    refine inv_doIns_fresh s t r e a pre h ?_
    simp only [WfOp] at hw
    simp only [fresh_ts]
    exact hw
  | Del pre x =>
    refine inv_doDel_free s t r x pre h ?_
    simp only [WfOp] at hw
    exact hw

#print axioms rgaInv_doOp_fresh

/-! ## FINDING — Del genuinely needs a path fact beyond freshness

`inv_doIns_fresh` closes with **freshness only** (indeed only `t ≠ 0`): accuracy is
fully removable for `Ins`, exactly as option 2 predicts.

For `Del` the story is sharper.  Invariant preservation needs `resolve s pre ≠ x`,
and `fresh_ts (_, _, .Del _ _) s = True` cannot supply it.  The failure is real:
if `resolve s pre = x` (the claimed prefix's first live node is the very node being
deleted, e.g. `Del [x] x` on a state where `x` is live) then every child `k` of `x`
(`anc s k = x`) is rehomed onto `x` (`sel_doDel`), after which `x` is physically
removed — leaving `k` live with `anc k = x` while `contains x = false` and `x ≠ 0`,
i.e. `wf` broken.  `accurate` rules this out because `IsAncPath s x pre` forces
`resolve s pre = anc s x ≠ x` (`isAncPath_resolve` + `isAncPath_self`); but the
*whole* of accuracy is not needed — `resolve s pre ≠ x` alone suffices and is
strictly weaker.

So the WfOp shape the RGA needs is NOT "id ≠ 0" uniformly: it is
`Ins → fresh_ts` (really `t ≠ 0`) **and** `Del → resolve s pre ≠ x`.  Option 2
holds unconditionally for `Ins`; for `Del` it holds under this one path-distinctness
side condition, which is a `do_`-time consequence of a correct prefix but is not a
freshness fact.
-/
