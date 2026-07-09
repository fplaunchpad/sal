import Sal.MRDTs.RGA.RGA_Tombstone_Free_MRDT

/-!
# Tombstone-free RGA: the conditioning predicates as a reachable-state invariant

This file instantiates the **keystone** of `Sal/MRDTs/Metatheory/Development/BLUEPRINT.md` for the
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
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]

/-- The candidate reachable-state invariant: the root sentinel is never stored,
and the anchor pointers form a valid live forest.

Named `RgaInv` rather than `Inv` to avoid a clash with Mathlib's `Inv` typeclass
(the `⁻¹` class), which otherwise shadows a bare `Inv` in some binder positions. -/
def RgaInv (s : concrete_st α) : Prop := contains s 0 = false ∧ wf s

/-! ## PRIMARY 1 — `init_st` -/

/-- `Inv` holds at the initial (empty) state: `wf` is vacuous and `0 ∉ dom`. -/
theorem Inv_init [Inhabited α] : RgaInv (init_st (α := α)) := by
  refine ⟨?_, ?_⟩
  · simp [init_st]
  · intro t ht
    simp [init_st] at ht

/-! ## PRIMARY 2 — `do_` of an `Ins`

New key `t ≠ 0` (by `fresh_ts`) keeps `contains 0` false; the stored anchor
`resolve s (a :: pre)` is the live anchor `a` (or `0` when `a = 0`), so `wf`
is preserved; every existing node is left untouched by the `upd`. -/
theorem Inv_doIns (s : concrete_st α) (t r : ℕ) (e : α) (a : ℕ) (pre : List ℕ) (h : RgaInv s)
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
theorem Inv_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ) (h : RgaInv s)
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

/-! ## The id-monotone invariant and the fuel-sufficiency lemma

`merge_breaks_wf` isolates the missing ingredient: `climb`'s fuel (`= the node
id`) suffices exactly when anchor ids strictly *decrease* along the LCA's parent
chain.  We name that discipline `id_mono` and prove it is precisely enough (with
`wf l`) to close `wf (merge l a b)`. -/

/-- Id-monotone anchors: every live node's immediate anchor is the root `0` or a
strictly smaller id.  This is a **generation-time** property (monotone timestamp
allocation), NOT derivable from state shape: `merge_breaks_wf` exhibits a `wf`
state that violates it, and inserting a small id under a larger live anchor
breaks it under the abstract `fresh_ts`.  It is established below as a reachable
invariant of monotone allocation (`id_mono_init`/`id_mono_doIns`/`id_mono_doDel`/
`id_mono_merge`). -/
def id_mono (s : concrete_st α) : Prop :=
  ∀ t, contains s t → (anc s t = 0 ∨ anc s t < t)

/-- The merged survivor set `I` (OR-set survival on identities), matching `merge`. -/
def survivors (l a b : concrete_st α) : set ℕ :=
  union (intersection (intersection (domain l) (domain a)) (domain b))
        (union (difference (domain a) (domain l)) (difference (domain b) (domain l)))

/-- Each survivor's birth-anchor, read from whichever branch it lives in
(matching `merge`'s `betaf`). -/
def birthAnc (l a b : concrete_st α) (t : ℕ) : ℕ :=
  if contains l t then anc l t else if contains a t then anc a t else anc b t

/-- `contains (merge …)` is survivor-set membership (definitional). -/
theorem contains_merge (l a b : concrete_st α) (t : ℕ) :
    contains (merge l a b) t = survivors l a b t := rfl

/-- `anc (merge …)` is the `climb` of the birth-anchor (definitional). -/
theorem anc_merge (l a b : concrete_st α) (t : ℕ) :
    anc (merge l a b) t
      = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b t) := rfl

/-- **Fuel-sufficiency for `climb`.**  Under id-monotone anchors (`Hdec`: the id
strictly drops along `anc l`) and the forest invariant (`Hstay`: `anc l` stays in
`{0} ∪ dom l`), a walk started at a node that is `0`, a survivor (`I`), or
live-in-`l` (a) **lands in `{0} ∪ I`** and (b) **never climbs above its start**.
The walk only ever applies `anc l` to live-in-`l` nodes — it halts first on `0`
and on survivors — so `id_mono l` (which only constrains live-in-`l` nodes) is
exactly enough.  Since the id strictly decreases at each `anc l` step, the fuel
`= start id` always suffices; this is the ingredient `merge_breaks_wf` shows `wf`
lacks. -/
theorem climb_aux_walk (l : concrete_st α) (I : set ℕ)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true)) :
    ∀ (fuel x : ℕ), x ≤ fuel → (x = 0 ∨ I x = true ∨ contains l x = true) →
      (climb_aux (fun y => anc l y) I fuel x = 0
        ∨ I (climb_aux (fun y => anc l y) I fuel x) = true)
      ∧ climb_aux (fun y => anc l y) I fuel x ≤ x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hx _
    have hx0 : x = 0 := Nat.le_zero.mp hx
    subst hx0
    exact ⟨Or.inl rfl, le_refl 0⟩
  | succ fuel ih =>
    intro x hx hs
    by_cases hx0 : x = 0
    · subst hx0
      have h0fix : climb_aux (fun y => anc l y) I (fuel + 1) 0 = 0 := by
        simp only [climb_aux]; simp
      rw [h0fix]; exact ⟨Or.inl rfl, le_refl 0⟩
    · by_cases hIx : I x = true
      · have hfix : climb_aux (fun y => anc l y) I (fuel + 1) x = x := by
          simp only [climb_aux]; simp [hIx]
        rw [hfix]; exact ⟨Or.inr hIx, le_refl x⟩
      · have hlx : contains l x = true := by
          rcases hs with h | h | h
          · exact absurd h hx0
          · exact absurd h (by simp [hIx])
          · exact h
        have hIxf : I x = false := by
          cases hI : I x with
          | true => exact absurd hI hIx
          | false => rfl
        have hcondF : (decide (x = 0) || I x) = false := by simp [hx0, hIxf]
        have hstep : climb_aux (fun y => anc l y) I (fuel + 1) x
                   = climb_aux (fun y => anc l y) I fuel (anc l x) := by
          simp only [climb_aux]
          rw [if_neg (by rw [hcondF]; simp)]
        rw [hstep]
        have hdec := Hdec x hlx hx0
        have hstay := Hstay x hlx
        have hle_fuel : anc l x ≤ fuel := by omega
        have hstart' : anc l x = 0 ∨ I (anc l x) = true ∨ contains l (anc l x) = true := by
          rcases hstay with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        have IHres := ih (anc l x) hle_fuel hstart'
        exact ⟨IHres.1, le_trans IHres.2 (le_of_lt hdec)⟩

/-- **The start condition is free from `wf l/a/b`.**  Every survivor's
birth-anchor is `0`, itself a survivor, or live-in-`l` — so no separate
cross-branch premise is needed.  Key fact: a node new in `a` (`da \ dl`) is
*automatically* a survivor, so a chain of new `a`-nodes halts the climb at the
first survivor rather than escaping `l`'s forest. -/
theorem betaf_start (l a b : concrete_st α)
    (hlwf : ∀ t, contains l t = true → (anc l t = 0 ∨ contains l (anc l t) = true))
    (hawf : ∀ t, contains a t = true → (anc a t = 0 ∨ contains a (anc a t) = true))
    (hbwf : ∀ t, contains b t = true → (anc b t = 0 ∨ contains b (anc b t) = true))
    (t : ℕ) (ht : survivors l a b t = true) :
    birthAnc l a b t = 0 ∨ survivors l a b (birthAnc l a b t) = true
      ∨ contains l (birthAnc l a b t) = true := by
  unfold birthAnc
  by_cases hlt : contains l t = true
  · rw [if_pos hlt]
    rcases hlwf t hlt with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rw [if_neg hlt]
    by_cases hat : contains a t = true
    · rw [if_pos hat]
      rcases hawf t hat with h | h
      · exact Or.inl h
      · by_cases hla : contains l (anc a t) = true
        · exact Or.inr (Or.inr hla)
        · refine Or.inr (Or.inl ?_)
          simp only [survivors, union, intersection, difference, contains, domain, mem] at h hla ⊢
          grind
    · rw [if_neg hat]
      have hbt : contains b t = true := by
        simp only [survivors, union, intersection, difference, contains, domain, mem] at ht hlt hat
        grind
      rcases hbwf t hbt with h | h
      · exact Or.inl h
      · by_cases hlb : contains l (anc b t) = true
        · exact Or.inr (Or.inr hlb)
        · refine Or.inr (Or.inl ?_)
          simp only [survivors, union, intersection, difference, contains, domain, mem] at h hlb ⊢
          grind

/-! ## STRETCH 4 — `Inv_merge`, now CLOSED under `id_mono l`

The `contains 0 = false` conjunct holds from `Inv l/a/b`.  The `wf` conjunct —
refuted from `Inv l/a/b` alone by `merge_breaks_wf` — goes through under the
single extra premise `id_mono l`: the id-monotone anchors on the LCA make
`climb`'s fuel sufficient (`climb_aux_walk`), and the start condition for every
survivor's birth-anchor is supplied for free by `wf l/a/b` (`betaf_start`).  No
separate cross-branch premise is needed. -/
set_option maxHeartbeats 4000000 in
theorem Inv_merge (l a b : concrete_st α)
    (hl : RgaInv l) (ha : RgaInv a) (hb : RgaInv b) (ml : id_mono l) :
    RgaInv (merge l a b) := by
  obtain ⟨hl0, hlwf⟩ := hl
  obtain ⟨ha0, hawf⟩ := ha
  obtain ⟨hb0, hbwf⟩ := hb
  simp only [wf] at hlwf hawf hbwf
  refine ⟨?_, ?_⟩
  · -- root sentinel absent: closed from `Inv l/a/b`
    simp only [merge, contains, domain, mem] at hl0 ha0 hb0 ⊢
    grind
  · -- forest invariant: closed via `climb_aux_walk` + `betaf_start` under `id_mono l`
    intro t ht
    rw [contains_merge] at ht
    rw [anc_merge, contains_merge]
    have Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
      intro y hy hy0; rcases ml y hy with h | h
      · omega
      · exact h
    have hstart := betaf_start l a b hlwf hawf hbwf t ht
    have hwalk := climb_aux_walk l (survivors l a b) Hdec hlwf
                    (birthAnc l a b t) (birthAnc l a b t) (le_refl _) hstart
    simp only [climb]
    exact hwalk.1

#print axioms Inv_merge

/-! ## Establishing `id_mono` as a reachable invariant of monotone allocation

`id_mono` is not a `do_`-invariant on its own (a small id inserted under a larger
live anchor breaks it); it needs the *allocation discipline* that a fresh `Ins`
timestamp exceeds every live id.  We package that as `mono_alloc` and show
`RgaInv ∧ id_mono` is jointly preserved by `init_st`/`do_`/`merge`. -/

/-- Any `resolve` result is the root `0` or a live node — regardless of accuracy. -/
theorem resolve_zero_or_live (s : concrete_st α) (cands : List ℕ) :
    resolve s cands = 0 ∨ contains s (resolve s cands) = true := by
  induction cands with
  | nil => left; rfl
  | cons c rest ih =>
    simp only [resolve]
    by_cases hc : contains s c = true
    · rw [if_pos hc]; right; exact hc
    · rw [if_neg hc]; exact ih

/-- Monotone allocation discipline: an `Ins` timestamp exceeds every live id
(so its live anchor is strictly smaller); `Del` allocates nothing. -/
def mono_alloc (o : op_t α) (s : concrete_st α) : Prop :=
  match o with
  | (t, _, .Ins _ _ _) => ∀ k, contains s k = true → k < t
  | (_, _, .Del _ _)   => True

/-- `id_mono` holds vacuously at the empty initial state. -/
theorem id_mono_init [Inhabited α] : id_mono (init_st (α := α)) := by
  intro t ht
  simp [init_st] at ht

/-- `Ins` preserves `id_mono` under monotone allocation: the freshly stored anchor
`resolve s (a :: pre)` is `0`-or-live, and every live id is `< t` by `mono_alloc`;
existing nodes keep their (already id-monotone) anchor. -/
theorem id_mono_doIns (s : concrete_st α) (t r : ℕ) (e : α) (a : ℕ) (pre : List ℕ)
    (hmono : id_mono s) (halloc : mono_alloc (t, r, .Ins e pre a) s) :
    id_mono (do_ s (t, r, .Ins e pre a)) := by
  simp only [mono_alloc] at halloc
  intro k hk
  have hdo : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  rw [hdo] at hk ⊢
  by_cases hkt : k = t
  · subst hkt
    have hanc : anc (upd s k (e, resolve s (a :: pre))) k = resolve s (a :: pre) := by
      simp only [anc]; rw [lemma_SelUpd1]
    rw [hanc]
    rcases resolve_zero_or_live s (a :: pre) with h | hl
    · left; exact h
    · right; exact halloc (resolve s (a :: pre)) hl
  · have htk : t ≠ k := fun e' => hkt e'.symm
    have hck : contains s k = true := by
      rw [lemma_InDomUpd1] at hk
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      rcases hk with h | h
      · exact absurd h htk
      · exact h
    have hanc : anc (upd s t (e, resolve s (a :: pre))) k = anc s k := by
      simp only [anc]
      rw [lemma_SelUpd2 s k t (e, resolve s (a :: pre))
            (by simp only [bne_iff_ne, ne_eq]; exact htk)]
    rw [hanc]
    exact hmono k hck

/-- `Del` preserves `id_mono` under `accurate` and `contains s 0 = false`.  For an
untouched node the anchor (hence its id-monotonicity) is carried from `s`.  For a
rehomed child `k` (whose parent was `x = anc s k`), the new anchor is
`resolve s pre = anc s x`, and `id_mono s` gives `anc s x < x = anc s k < k`, so
monotonicity survives the reparent. -/
theorem id_mono_doDel (s : concrete_st α) (t r x : ℕ) (pre : List ℕ)
    (h0 : contains s 0 = false) (hmono : id_mono s)
    (hacc : accurate (t, r, .Del pre x) s) :
    id_mono (do_ s (t, r, .Del pre x)) := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro k hk
  rw [contains_doDel] at hk
  rw [Bool.and_eq_true] at hk
  obtain ⟨hck, _hkx⟩ := hk
  rw [anc_doDel]
  by_cases hax : anc s k = x
  · rw [if_pos hax]
    rcases hacc with ⟨_hx0, hpnil⟩ | ⟨hxlive, hxpath⟩
    · subst hpnil; left; rfl
    · have hres : resolve s pre = anc s x := isAncPath_resolve s x pre hxpath
      rw [hres]
      have hxne0 : x ≠ 0 := contains_ne_zero s x h0 hxlive
      rcases hmono k hck with hk0 | hklt
      · exact absurd (hax.symm.trans hk0) hxne0
      · have hxltk : x < k := by rw [← hax]; exact hklt
        rcases hmono x hxlive with hx0' | hxlt'
        · left; exact hx0'
        · right; exact lt_trans hxlt' hxltk
  · rw [if_neg hax]
    exact hmono k hck

/-- `merge` preserves `id_mono` when all three inputs are id-monotone well-formed:
each merged anchor is `climb (anc l) I (betaf t) ≤ betaf t`, and `betaf t` is `0`
or `< t` by the owning branch's `id_mono`, so the climb result is `0` or `< t`. -/
theorem id_mono_merge (l a b : concrete_st α)
    (hl : RgaInv l) (ha : RgaInv a) (hb : RgaInv b)
    (ml : id_mono l) (ma : id_mono a) (mb : id_mono b) :
    id_mono (merge l a b) := by
  obtain ⟨_, hlwf⟩ := hl
  obtain ⟨_, hawf⟩ := ha
  obtain ⟨_, hbwf⟩ := hb
  simp only [wf] at hlwf hawf hbwf
  intro t ht
  rw [contains_merge] at ht
  rw [anc_merge]
  have Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
    intro y hy hy0; rcases ml y hy with h | h
    · omega
    · exact h
  have hstart := betaf_start l a b hlwf hawf hbwf t ht
  have hwalk := climb_aux_walk l (survivors l a b) Hdec hlwf
                  (birthAnc l a b t) (birthAnc l a b t) (le_refl _) hstart
  simp only [climb]
  have hle := hwalk.2
  have hbeta_lt : birthAnc l a b t = 0 ∨ birthAnc l a b t < t := by
    unfold birthAnc
    by_cases hlt : contains l t = true
    · rw [if_pos hlt]; exact ml t hlt
    · rw [if_neg hlt]
      by_cases hat : contains a t = true
      · rw [if_pos hat]; exact ma t hat
      · rw [if_neg hat]
        have hbt : contains b t = true := by
          simp only [survivors, union, intersection, difference, contains, domain, mem] at ht hlt hat
          grind
        exact mb t hbt
  rcases hbeta_lt with h0 | hlt
  · left; rw [h0] at hle; omega
  · right; omega

#print axioms id_mono_init
#print axioms id_mono_doIns
#print axioms id_mono_doDel
#print axioms id_mono_merge

/-! ## VERDICT — the three ANALYSIS questions

**(i) Does the keystone hold for this RGA — is `Inv` genuinely inductive under
`do_`/`merge`?**

Partly, and the partition is sharp:

* Under `init_st` and `do_` (both `Ins` and `Del`): **YES**, machine-checked,
  `sorry`-free (`Inv_init`, `Inv_doIns`, `Inv_doDel`).  `Inv = (contains 0 =
  false) ∧ wf` is inductive for the local effect.
* Under `merge`: **NO** from `Inv l/a/b` alone (`merge_breaks_wf` is a
  machine-checked counterexample), but **YES** once the LCA is id-monotone.
  `Inv_merge` is now closed, `sorry`-free, under the single extra premise
  `id_mono l`: `climb_aux_walk` proves that id-monotone anchors make `climb`'s
  fuel (`= the node id`) sufficient, and `betaf_start` shows the walk's start
  condition for every survivor's birth-anchor is supplied *for free* by `wf l/a/b`
  — no separate cross-branch anchor-compatibility premise is needed (a node new in
  a branch is automatically a survivor, so the climb halts on it).  And `id_mono`
  is itself a reachable invariant of monotone allocation: `id_mono_init`,
  `id_mono_doIns` (under `mono_alloc`), `id_mono_doDel` (under `accurate`), and
  `id_mono_merge` are all closed.  So `RgaInv ∧ id_mono` is a reachable-state
  invariant under `init_st`/`do_`/`merge`, and it discharges merge soundness — the
  *merge* half requiring exactly the generation-time id-monotonicity.

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

For the **`merge` layer: R2 holds once conditioned on monotone allocation.**  The
blueprint (§5.4 R2) claims the forest invariant is "preserved under update and
merge including Del-rehoming."  The *update* half is confirmed unconditionally;
the *merge* half is **refuted from `wf` alone** by `merge_breaks_wf` — `climb`'s
fixed fuel makes `wf`-preservation depend on monotone anchor ids, which `wf` does
not supply and which `fresh_ts` does not even make a `do_`-invariant — but is
**recovered** under the generation-time discipline of monotone timestamp
allocation (id-decreasing anchors), captured by `id_mono` + `mono_alloc`.  That
obligation, flagged in the original write-up as "the precise remaining obligation
for closing the RGA soundness composition", is now **discharged**: `id_mono` is
established as a genuine reachable-execution invariant (`id_mono_init`/
`id_mono_doIns`/`id_mono_doDel`/`id_mono_merge`) and it closes `Inv_merge`.  The
headline: **`RgaInv ∧ id_mono` is a reachable invariant under monotone
allocation, and it discharges merge soundness for the tombstone-free RGA** — the
answer to the conditioning question, with the merge half requiring precisely the
generation-time id-monotonicity that `merge_breaks_wf` predicted.
-/
