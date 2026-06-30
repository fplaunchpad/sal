import Sal.Interfaces.Map_Extended

/-!
# Impossibility of a prefix-free, tombstone-free RGA under `rc = Either`

This file generalises the single concrete witness `prefixfree_diverges` from
`RGA_Tombstone_Free_MRDT.lean` into a *parameterised* impossibility theorem for
the `rc = Either` / `do_`-commutation route.

## What is abstracted

State is the tombstone-free `map ℕ (ℕ × ℕ)` (`id ↦ (element, immediate-anchor)`,
`0` the root). The operations are **prefix-free**: an insert carries only its
immediate anchor, a delete only its target. We abstract their *local* semantics
over two functions:

* `f : concrete_st → ℕ → ℕ` — the anchor an insert stores, computed from the
  current state `s` and the immediate anchor `a`:  `doIns f s t e a = upd s t (e, f s a)`.
* `g : concrete_st → ℕ → ℕ` — the reparent target a delete uses for `x`'s
  children, computed from the current state and the target `x`:
  `doDel g s x = del (reparent-children-of-x-to-(g s x)) x`.

This is the most general *local, prefix-free, tombstone-free* operation pair: the
stored anchor / reparent target is an arbitrary function of the **live** state and
the immediate argument, with no carried ancestor path.

## The three side conditions on (f, g)

For the result to be about a genuine RGA (not a degenerate "everything anchors at
root" CRDT) we ask only:

* `f_faithful`  — a *live* anchor is stored verbatim: `contains s a → f s a = a`.
  (The new node sits immediately after its anchor; this is what makes the
  sequence read correctly.)
* `g_faithful`  — deleting `x` reparents its children to `x`'s *live* parent:
  `contains s x → contains s (anc s x) → g s x = anc s x`.
  (Preserves the children's relative order under the surviving parent.)
* `f_respects`  — the insert is genuinely tombstone-free: it cannot read deleted
  records.  Formally it respects the framework's domain-relative state equality
  `eq` (it is a congruence for `eq`).  This is the precise content of
  "tombstone-free": `del` only shrinks the domain, so a well-defined operation
  must not depend on the stale off-domain mappings of removed keys.

## The theorem

`prefixfree_tombstonefree_noncomm`: for **every** `f, g` satisfying the three
conditions, the universal `do_`-commutation of an insert against a delete
(`commutes_all`, which `rc = Either` would force via `rc_non_comm'`) is **false**.

## Why (the impossibility, stated precisely)

We exhibit two states `s1, s2` that differ only in the parent pointer of a single
leaf `x = 2` (`anc s1 2 = 1`, `anc s2 2 = 4`, both parents live). Because `x` is a
leaf, `do_(Del x)` simply removes it and reparents nothing, so the two post-delete
states are `eq` — the erased parent leaves *no trace* (tombstone-free).

* In the **Del; Ins** order the insert observes the (`eq`-identical) post-delete
  state, so by `f_respects` it stores the **same** anchor `v := f (doDel g s1 2) 2`
  in both scenarios.
* In the **Ins; Del** order the insert observes `x` live, anchors at it, and the
  subsequent `Del x` reparents the new node to `x`'s genuine parent — `1` for
  `s1`, `4` for `s2` (by `f_faithful` + `g_faithful`).

`do_`-commutation would force `v = 1` (from `s1`) and `v = 4` (from `s2`); since
`1 ≠ 4`, no `f, g` can satisfy both. The obstruction rests on exactly three
facts: (1) tombstone-free erasure leaves the post-delete states `eq`; (2)
prefix-freedom forces the insert to recompute its anchor from that erased state;
(3) `rc = Either` demands commutation for *all* states, including both witnesses.

This is the parameterised form of `prefixfree_diverges`; the path-carrying design
of the sibling module escapes it precisely by *not* being prefix-free.
-/

namespace PrefixFreeImpossible

/-- State: `id ↦ (element, immediate-anchor)`; `0` is the root. Tombstone-free. -/
abbrev concrete_st := map ℕ (ℕ × ℕ)

@[simp] def el (s : concrete_st) (t : ℕ) : ℕ := (sel s t).1
@[simp] def anc (s : concrete_st) (t : ℕ) : ℕ := (sel s t).2
@[simp] def init_st : concrete_st := const_on empty (0, 0)

/-- The framework's domain-relative state equality. -/
@[simp] def eq (a b : concrete_st) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

/-! ## Parameterised local, prefix-free, tombstone-free semantics -/

/-- Prefix-free insert: new id `t ↦ (e, f s a)`, the stored anchor a function of
the *live* state and the immediate anchor `a` (no carried path). -/
def doIns (f : concrete_st → ℕ → ℕ) (s : concrete_st) (t e a : ℕ) : concrete_st :=
  upd s t (e, f s a)

/-- Prefix-free, tombstone-free delete: reparent `x`'s children to `g s x` (a
function of the live state and target), then physically remove `x`. -/
def doDel (g : concrete_st → ℕ → ℕ) (s : concrete_st) (x : ℕ) : concrete_st :=
  del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, g s x) else ea) s) x

/-! ## The three side conditions -/

/-- A live anchor is stored verbatim (insert places the node after its anchor). -/
def f_faithful (f : concrete_st → ℕ → ℕ) : Prop :=
  ∀ s a, contains s a = true → f s a = a

/-- Deleting `x` reparents its children to `x`'s live parent. -/
def g_faithful (g : concrete_st → ℕ → ℕ) : Prop :=
  ∀ s x, contains s x = true → contains s (anc s x) = true → g s x = anc s x

/-- The insert is genuinely tombstone-free: it respects domain-relative `eq`
(cannot read deleted records). -/
def f_respects (f : concrete_st → ℕ → ℕ) : Prop :=
  ∀ s1 s2 a, eq s1 s2 → f s1 a = f s2 a

/-- `rc = Either` for the insert/delete pair forces them to `do_`-commute for
*every* state with the framework's freshness/root side conditions. -/
def commutes_all (f g : concrete_st → ℕ → ℕ) : Prop :=
  ∀ (s : concrete_st), contains s 0 = false →
    ∀ (t e a x : ℕ), t ≠ 0 → t ≠ x → contains s t = false →
      eq (doDel g (doIns f s t e a) x) (doIns f (doDel g s x) t e a)

/-! ## `doDel` state algebra (ported from the flagship `*_doDel` lemmas) -/

theorem contains_doDel' (g : concrete_st → ℕ → ℕ) (s : concrete_st) (x k : ℕ) :
    contains (doDel g s x) k = (contains s k && k != x) := by
  simp only [doDel, del, iter_upd, contains, domain, remove, mem]
  grind

theorem sel_doDel' (g : concrete_st → ℕ → ℕ) (s : concrete_st) (x k : ℕ) :
    sel (doDel g s x) k = (if anc s k = x then (el s k, g s x) else sel s k) := by
  simp only [doDel, del, iter_upd, sel, el, anc]

theorem el_doDel' (g : concrete_st → ℕ → ℕ) (s : concrete_st) (x k : ℕ) :
    el (doDel g s x) k = el s k := by
  show (sel (doDel g s x) k).1 = el s k
  rw [sel_doDel']
  by_cases h : anc s k = x
  · rw [if_pos h]
  · rw [if_neg h]; rfl

theorem anc_doDel' (g : concrete_st → ℕ → ℕ) (s : concrete_st) (x k : ℕ) :
    anc (doDel g s x) k = if anc s k = x then g s x else anc s k := by
  show (sel (doDel g s x) k).2 = if anc s k = x then g s x else anc s k
  rw [sel_doDel']
  by_cases h : anc s k = x
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; rfl

/-! ## The two witness states

`base12` holds two live root-children `1` and `4`.  `s1` and `s2` add the same
leaf `2`, differing **only** in its parent pointer (`1` vs `4`). -/

def base12 : concrete_st := upd (upd init_st 1 (70, 0)) 4 (60, 0)
def s1 : concrete_st := upd base12 2 (80, 1)
def s2 : concrete_st := upd base12 2 (80, 4)

/-! ## Core extraction lemma

For a witness `sw` whose leaf `2` has live parent `v`, IF the Ins;Del and Del;Ins
orders are `eq`, then the prefix-free insert *must* have stored `v` as the new
node's anchor while reading the post-delete state (in which `2` and its parent
pointer are gone). This is the information the prefix-free insert cannot have. -/
theorem delins_anchor_of_eq
    (f g : concrete_st → ℕ → ℕ) (hf : f_faithful f) (hg : g_faithful g)
    (sw : concrete_st) (v : ℕ)
    (hsw2 : contains sw 2 = true) (hswv : contains sw v = true) (hancv : anc sw 2 = v)
    (hcomm : eq (doDel g (doIns f sw 3 99 2) 2) (doIns f (doDel g sw 2) 3 99 2)) :
    f (doDel g sw 2) 2 = v := by
  -- inner Ins reduces to a path-free `upd`
  have hf2 : f sw 2 = 2 := hf sw 2 hsw2
  have hu_eq : doIns f sw 3 99 2 = upd sw 3 (99, 2) := by simp only [doIns, hf2]
  -- facts about `u := upd sw 3 (99,2)`
  have hsel_u3 : sel (upd sw 3 (99, 2)) 3 = (99, 2) := lemma_SelUpd1 sw 3 (99, 2)
  have hanc_u3 : anc (upd sw 3 (99, 2)) 3 = 2 := by simp only [anc, hsel_u3]
  have hsel_u2 : sel (upd sw 3 (99, 2)) 2 = sel sw 2 :=
    lemma_SelUpd2 sw 2 3 (99, 2) (by decide)
  have hanc_u2 : anc (upd sw 3 (99, 2)) 2 = v := by simp only [anc, hsel_u2]; exact hancv
  have hcu2 : contains (upd sw 3 (99, 2)) 2 = true := by rw [lemma_InDomUpd1, hsw2]; simp
  have hcuv : contains (upd sw 3 (99, 2)) v = true := by rw [lemma_InDomUpd1, hswv]; simp
  -- order A (Ins; Del) reparents the new node to `g u 2 = v`
  have hg_u : g (upd sw 3 (99, 2)) 2 = v := by
    have h := hg (upd sw 3 (99, 2)) 2 hcu2 (by rw [hanc_u2]; exact hcuv)
    rw [h, hanc_u2]
  have hselA : sel (doDel g (upd sw 3 (99, 2)) 2) 3 = (99, v) := by
    rw [sel_doDel', if_pos hanc_u3, hg_u]
    simp only [el, hsel_u3]
  have hcontA : contains (doDel g (upd sw 3 (99, 2)) 2) 3 = true := by
    rw [contains_doDel']
    have h3 : contains (upd sw 3 (99, 2)) 3 = true := by rw [lemma_InDomUpd1]; simp
    rw [h3]; decide
  -- order B (Del; Ins) stores `f (doDel g sw 2) 2`
  have hselB : sel (doIns f (doDel g sw 2) 3 99 2) 3 = (99, f (doDel g sw 2) 2) := by
    simp only [doIns]; exact lemma_SelUpd1 (doDel g sw 2) 3 (99, f (doDel g sw 2) 2)
  -- `eq` forces the two anchors equal
  rw [hu_eq] at hcomm
  have hval := (hcomm 3).2 hcontA
  rw [hselA, hselB] at hval
  have hsnd := congrArg Prod.snd hval
  simpa using hsnd.symm

/-- The two post-delete states are `eq` (domain-relative equal): deleting the
leaf `2` erases its differing parent pointer without a trace. This is the formal
content of *tombstone-free*: the surviving live state cannot distinguish the two
deleted parents. -/
theorem postdelete_eq (g : concrete_st → ℕ → ℕ) :
    eq (doDel g s1 2) (doDel g s2 2) := by
  intro k
  refine ⟨?_, ?_⟩
  · have hc : contains s1 k = contains s2 k := by
      simp only [s1, s2, lemma_InDomUpd1]
    rw [contains_doDel', contains_doDel', hc]
  · intro hlive
    rw [contains_doDel', Bool.and_eq_true] at hlive
    obtain ⟨hck, hk2b⟩ := hlive
    have hkne2 : k ≠ 2 := by simpa [bne_iff_ne] using hk2b
    have hselk : sel s1 k = sel s2 k := by
      simp only [s1, s2, sel, upd]
      rw [if_neg hkne2, if_neg hkne2]
    have hkey : k = 1 ∨ k = 4 := by
      have hmem : contains s1 k = true := hck
      simp [s1, base12, init_st] at hmem
      omega
    have hanc1 : ¬ (anc s1 k = 2) := by rcases hkey with h | h <;> subst h <;> decide
    have hanc2 : ¬ (anc s2 k = 2) := by rcases hkey with h | h <;> subst h <;> decide
    rw [sel_doDel', sel_doDel', if_neg hanc1, if_neg hanc2, hselk]

/-! ## Main results -/

/-- **No local, prefix-free, tombstone-free RGA semantics can make insert and
delete `do_`-commute.** Hence the `rc = Either` route (which would demand exactly
this universal commutation via `rc_non_comm'`) is closed: any `f, g` faithful to
the RGA intent and respecting tombstone-free erasure refute `commutes_all`. -/
theorem prefixfree_tombstonefree_noncomm
    (f g : concrete_st → ℕ → ℕ)
    (hf : f_faithful f) (hg : g_faithful g) (hfr : f_respects f) :
    ¬ commutes_all f g := by
  intro H
  -- the two witnesses force `f (post-delete) 2` to be both 1 and 4
  have hk1 : f (doDel g s1 2) 2 = 1 :=
    delins_anchor_of_eq f g hf hg s1 1 (by decide) (by decide) (by decide)
      (H s1 (by decide) 3 99 2 2 (by decide) (by decide) (by decide))
  have hk2 : f (doDel g s2 2) 2 = 4 :=
    delins_anchor_of_eq f g hf hg s2 4 (by decide) (by decide) (by decide)
      (H s2 (by decide) 3 99 2 2 (by decide) (by decide) (by decide))
  -- but the two post-delete states are `eq`, so `f_respects` ties the anchors
  have hfeq : f (doDel g s1 2) 2 = f (doDel g s2 2) 2 := hfr _ _ 2 (postdelete_eq g)
  rw [hk1, hk2] at hfeq
  exact absurd hfeq (by decide)

/-- **The underlying generic `do_`-divergence.** For *any* faithful, tombstone-
free, prefix-free `f, g`, insert and delete fail to commute on at least one of the
two concrete reachable witnesses. This single fact closes **both** of Sal's
routes for the conflicting insert/delete pair:

* `rc = Either`: `rc_non_comm'` demands unconditional `do_`-commutation — refuted
  directly (`prefixfree_tombstonefree_noncomm`).
* `rc` orders the pair: `cond_comm_base` requires the swap `o1;o2 ≡ o2;o1` under a
  trailing ordered `o3`; since the diverging node is created by the swapped pair
  and is untouched by `o3`, that obligation reduces to this very divergence — as
  the concrete `RGA_Splice_Counterexample.cond_comm_base_violated` witnesses for
  the natural `f, g`. -/
theorem prefixfree_doDivergence
    (f g : concrete_st → ℕ → ℕ)
    (hf : f_faithful f) (hg : g_faithful g) (hfr : f_respects f) :
    (¬ eq (doDel g (doIns f s1 3 99 2) 2) (doIns f (doDel g s1 2) 3 99 2))
    ∨ (¬ eq (doDel g (doIns f s2 3 99 2) 2) (doIns f (doDel g s2 2) 3 99 2)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hk1 : f (doDel g s1 2) 2 = 1 :=
    delins_anchor_of_eq f g hf hg s1 1 (by decide) (by decide) (by decide) h1
  have hk2 : f (doDel g s2 2) 2 = 4 :=
    delins_anchor_of_eq f g hf hg s2 4 (by decide) (by decide) (by decide) h2
  have hfeq : f (doDel g s1 2) 2 = f (doDel g s2 2) 2 := hfr _ _ 2 (postdelete_eq g)
  rw [hk1, hk2] at hfeq
  exact absurd hfeq (by decide)

end PrefixFreeImpossible
