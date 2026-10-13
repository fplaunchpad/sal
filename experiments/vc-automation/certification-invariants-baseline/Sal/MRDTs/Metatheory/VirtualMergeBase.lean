import Sal.MRDTs.Metatheory.StoreInvariant
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold

/-! # Canonical virtual merge base

The framework-owned recursive maximal-common-ancestor fold. This module is
independent of datatype generation and safety certificates.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

variable {D : MRDTSig}

section VirtualState

variable (ver : Version → Option (D.State × Set (Op D.AppOp)))
variable (parents : Version → List Version)

/-- The state registered at `v`, defaulting to `σ₀` (total-function style; canonicity
theorems carry the allocation hypotheses that make the default unreachable). -/
noncomputable def stateD (v : Version) : D.State :=
  ((ver v).map Prod.fst).getD D.init

open Classical in
/-- The maximal elements among common ancestors of `w` and any member of `S`,
as a `Finset`. Every such ancestor reaches `w`, so ranks are bounded by `w` and
the `range` bound needs no additional hypothesis. -/
noncomputable def maximalCommonAncestorsWithAny
    (S : Finset Version) (w : Version) : Finset Version :=
  (Finset.range (w + 1)).filter
    (fun m => IsMaximalCommonAncestorWithAny parents (↑S) w m)

open Classical in
theorem mem_maximalCommonAncestorsWithAny {S : Finset Version} {w m : Version}
    (hm : m ∈ maximalCommonAncestorsWithAny parents S w) :
    IsMaximalCommonAncestorWithAny parents (↑S) w m :=
  (Finset.mem_filter.mp hm).2

open Classical in
theorem maximalCommonAncestorsWithAny_le {S : Finset Version} {w m : Version}
    (hm : m ∈ maximalCommonAncestorsWithAny parents S w) : m ≤ w :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

open Classical in
/-- Full membership characterization (the rank bound is derivable from `hlt`). -/
theorem mem_maximalCommonAncestorsWithAny_iff (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w m : Version} :
    m ∈ maximalCommonAncestorsWithAny parents S w ↔
      IsMaximalCommonAncestorWithAny parents (↑S) w m := by
  refine ⟨mem_maximalCommonAncestorsWithAny parents, fun h => Finset.mem_filter.mpr ⟨?_, h⟩⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (reaches_le hlt h.1.2))

open Classical in
/-- The joint real support of a finite version set: everything reaching a member
(ranks bounded by the members' maximum, again intrinsically). -/
noncomputable def supportOf (X : Finset Version) : Finset Version :=
  (Finset.range (X.sup id + 1)).filter (fun x => ∃ u ∈ X, Reaches parents x u)

open Classical in
theorem mem_supportOf_of (hlt : ∀ v p, p ∈ parents v → p < v)
    {X : Finset Version} {x u : Version} (hu : u ∈ X)
    (hr : Reaches parents x u) : x ∈ supportOf parents X := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), u, hu, hr⟩
  exact Nat.le_trans (reaches_le hlt hr) (Finset.le_sup (f := id) hu)

open Classical in
theorem exists_of_mem_supportOf {X : Finset Version} {x : Version}
    (hx : x ∈ supportOf parents X) : ∃ u ∈ X, Reaches parents x u :=
  (Finset.mem_filter.mp hx).2

/-- Support is monotone in the version set. -/
theorem supportOf_mono (hlt : ∀ v p, p ∈ parents v → p < v)
    {X Y : Finset Version} (h : X ⊆ Y) :
    supportOf parents X ⊆ supportOf parents Y := by
  intro x hx
  obtain ⟨u, hu, hr⟩ := exists_of_mem_supportOf parents hx
  exact mem_supportOf_of parents hlt (h hu) hr

/-- The maximal-antichain support sits inside the pair's joint support: every
antichain member is an ancestor of a support member. -/
theorem supportOf_maximalCommonAncestorsWithAny_subset (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} :
    supportOf parents (maximalCommonAncestorsWithAny parents S w) ⊆ supportOf parents (S ∪ {w}) := by
  intro x hx
  obtain ⟨m, hm, hr⟩ := exists_of_mem_supportOf parents hx
  obtain ⟨⟨u, huS, hmu⟩, _⟩ := (mem_maximalCommonAncestorsWithAny parents hm).1
  exact mem_supportOf_of parents hlt
    (Finset.mem_union_left _ huS) (hr.trans hmu)

/-- If `w` itself lands in the antichain's support, the antichain is the degenerate
singleton `{w}` (then `w` is below the support, i.e. the pair is comparable). -/
theorem maximalCommonAncestorsWithAny_eq_singleton_of_mem_support
    (hlt : ∀ v p, p ∈ parents v → p < v) {S : Finset Version} {w : Version}
    (hw : w ∈ supportOf parents (maximalCommonAncestorsWithAny parents S w)) :
    maximalCommonAncestorsWithAny parents S w = {w} := by
  obtain ⟨m', hm', hr⟩ := exists_of_mem_supportOf parents hw
  have hm'w : m' = w :=
    Nat.le_antisymm (maximalCommonAncestorsWithAny_le parents hm') (reaches_le hlt hr)
  have hwmem : w ∈ maximalCommonAncestorsWithAny parents S w := hm'w ▸ hm'
  have hwCA : w ∈ CommonAncestorsWithAny parents (↑S) w :=
    (mem_maximalCommonAncestorsWithAny parents hwmem).1
  refine Finset.ext fun x => ?_
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨hxCA, hxmax⟩ := mem_maximalCommonAncestorsWithAny parents hx
    exact (hxmax w hwCA hxCA.2).symm
  · rintro rfl
    exact hwmem

/-- **The measure strictly drops across a nesting level**: with a proper antichain
(two distinct members), the antichain's support is a *strict* subset of the pair's,
`w` is in the latter, never the former. -/
theorem supportOf_maximalCommonAncestorsWithAny_ssubset
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} {m m' : Version}
    (hm : m ∈ maximalCommonAncestorsWithAny parents S w)
    (hm' : m' ∈ maximalCommonAncestorsWithAny parents S w)
    (hne : m ≠ m') :
    supportOf parents (maximalCommonAncestorsWithAny parents S w) ⊂ supportOf parents (S ∪ {w}) := by
  refine Finset.ssubset_iff_of_subset (supportOf_maximalCommonAncestorsWithAny_subset parents hlt) |>.mpr
    ⟨w, mem_supportOf_of parents hlt
      (Finset.mem_union_right _ (Finset.mem_singleton_self w))
      Relation.ReflTransGen.refl, ?_⟩
  intro hwsupp
  have hsing := maximalCommonAncestorsWithAny_eq_singleton_of_mem_support parents hlt hwsupp
  rw [hsing, Finset.mem_singleton] at hm hm'
  exact hne (hm.trans hm'.symm)

open Classical in
/-- **The ascending-rank antichain fold** (the rule's engine). `accS` is the scratch
node's support (the antichain prefix already folded), `acc` its state; each pending
member `m` is merged through the *virtual merge base of the sub-pair* `(accS, m)`, the
recursive occurrence on the sub-pair's own maximal antichain. Termination is
by the joint support measure, lexicographic with the pending length. -/
noncomputable def vfoldAux (hlt : ∀ v p, p ∈ parents v → p < v)
    (accS : Finset Version) (acc : D.State) : List Version → D.State
  | [] => acc
  | m :: ms =>
      vfoldAux hlt (accS ∪ {m})
        (D.merge
          (match _h : (maximalCommonAncestorsWithAny parents accS m).sort (· ≤ ·) with
            | [] => D.init
            | m₁ :: ms₁ => vfoldAux hlt {m₁} (stateD ver m₁) ms₁)
          acc (stateD ver m))
        ms
termination_by pending =>
  ((supportOf parents (accS ∪ pending.toFinset)).card, pending.length)
decreasing_by
  · -- the nested virtual-merge-base call: a proper antichain strictly shrinks the support;
    -- a singleton one keeps it and shrinks the pending list
    have hMeq : (m₁ :: ms₁).toFinset = maximalCommonAncestorsWithAny parents accS m := by
      rw [← _h, Finset.sort_toFinset]
    have hset : ({m₁} ∪ ms₁.toFinset : Finset Version) = maximalCommonAncestorsWithAny parents accS m := by
      rw [← hMeq, List.toFinset_cons, Finset.insert_eq]
    rw [hset]
    have hsub : supportOf parents (maximalCommonAncestorsWithAny parents accS m)
        ⊆ supportOf parents (accS ∪ (m :: ms).toFinset) := by
      refine (supportOf_maximalCommonAncestorsWithAny_subset parents hlt).trans (supportOf_mono parents hlt ?_)
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_union_right _ (by simp [List.toFinset_cons])
    rcases Nat.lt_or_ge (supportOf parents (maximalCommonAncestorsWithAny parents accS m)).card
        (supportOf parents (accS ∪ (m :: ms).toFinset)).card with hcard | hcard
    · exact Prod.Lex.left _ _ hcard
    · have heq : supportOf parents (maximalCommonAncestorsWithAny parents accS m)
          = supportOf parents (accS ∪ (m :: ms).toFinset) :=
        Finset.eq_of_subset_of_card_le hsub hcard
      have hmm : m ∈ supportOf parents (maximalCommonAncestorsWithAny parents accS m) := by
        rw [heq]
        exact mem_supportOf_of parents hlt
          (Finset.mem_union_right _ (by simp [List.toFinset_cons]))
          Relation.ReflTransGen.refl
      have hsing := maximalCommonAncestorsWithAny_eq_singleton_of_mem_support parents hlt hmm
      rw [hsing, Finset.sort_singleton] at _h
      injection _h with h₁ h₂
      subst h₁
      rw [← h₂, heq]
      exact Prod.Lex.right _ (Nat.succ_pos _)
  · -- the tail call: same support, shorter pending list
    have hset : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hset]
    exact Prod.Lex.right _ (Nat.lt_succ_self _)

open Classical in
/-- **The virtual-merge-base state of a support/version pair** (`VirtualMergeBase`):
sort the maximal antichain ascending by rank and fold. An empty antichain returns `σ₀`
(under `StoreInv` its event set, the empty union, is exactly the then-empty
intersection, so this is not a junk case); a singleton returns the registered state
(the existing GCA rule). -/
noncomputable def virtualBaseAux (hlt : ∀ v p, p ∈ parents v → p < v)
    (S : Finset Version) (w : Version) : D.State :=
  match _h : (maximalCommonAncestorsWithAny parents S w).sort (· ≤ ·) with
  | [] => D.init
  | m₁ :: ms₁ => vfoldAux ver parents hlt {m₁} (stateD ver m₁) ms₁

/-- Case equation: empty antichain. -/
theorem virtualBaseAux_of_sort_nil (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version}
    (h : (maximalCommonAncestorsWithAny parents S w).sort (· ≤ ·) = []) :
    virtualBaseAux ver parents hlt S w = D.init := by
  unfold virtualBaseAux
  split
  · rfl
  · rename_i m₁ ms₁ heq
    rw [h] at heq
    cases heq

/-- Case equation: nonempty antichain, the fold from its least member. -/
theorem virtualBaseAux_of_sort_cons (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} {m₁ : Version} {ms₁ : List Version}
    (h : (maximalCommonAncestorsWithAny parents S w).sort (· ≤ ·) = m₁ :: ms₁) :
    virtualBaseAux ver parents hlt S w
      = vfoldAux ver parents hlt {m₁} (stateD ver m₁) ms₁ := by
  unfold virtualBaseAux
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i m₁' ms₁' heq
    rw [h] at heq
    injection heq with h₁ h₂
    rw [h₁, h₂]

/-- Fold equation: empty pending list. -/
theorem vfoldAux_nil (hlt : ∀ v p, p ∈ parents v → p < v)
    (accS : Finset Version) (acc : D.State) :
    vfoldAux ver parents hlt accS acc [] = acc := by
  unfold vfoldAux
  rfl

/-- Fold equation: one step, the inner scratch merge folded back into `virtualBaseAux`. -/
theorem vfoldAux_cons (hlt : ∀ v p, p ∈ parents v → p < v)
    (accS : Finset Version) (acc : D.State) (m : Version) (ms : List Version) :
    vfoldAux ver parents hlt accS acc (m :: ms)
      = vfoldAux ver parents hlt (accS ∪ {m})
          (D.merge (virtualBaseAux ver parents hlt accS m) acc (stateD ver m)) ms := by
  conv_lhs => rw [vfoldAux]
  unfold virtualBaseAux
  rfl

end VirtualState

/-- **The virtual merge base state of a head pair**: recursively merge the
pair's maximal common ancestors, read from the configuration's ranked store.
This is the state the widened merge rule (`StepV.mergeVirtual`) places in the
merge-base slot. -/
noncomputable def virtualMergeBaseState (C : Configuration D) (v₁ v₂ : Version) : D.State :=
  virtualBaseAux C.ver C.parents C.parents_lt {v₁} v₂


/-- The canonical framework resolver used by every verified MRDT. -/
noncomputable def canonicalVirtualMergeBase (D : MRDTSig) : VirtualMergeBaseResolver D where
  state := virtualMergeBaseState

end Sal.MRDTs
