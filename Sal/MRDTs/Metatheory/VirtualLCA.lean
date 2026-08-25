import Sal.MRDTs.Metatheory.StoreInvariant
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold

/-! # Canonical virtual LCA

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
/-- The MCA antichain of support `S` and `w`, as a `Finset` (every common ancestor
reaches `w`, so ranks are bounded by `w`: the `range` bound is intrinsic and needs no
hypothesis). -/
noncomputable def mcaFinset (S : Finset Version) (w : Version) : Finset Version :=
  (Finset.range (w + 1)).filter (fun m => IsMCA parents (↑S) w m)

open Classical in
theorem mcaFinset_isMCA {S : Finset Version} {w m : Version}
    (hm : m ∈ mcaFinset parents S w) : IsMCA parents (↑S) w m :=
  (Finset.mem_filter.mp hm).2

open Classical in
theorem mcaFinset_le {S : Finset Version} {w m : Version}
    (hm : m ∈ mcaFinset parents S w) : m ≤ w :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

open Classical in
/-- Full membership characterization (the rank bound is derivable from `hlt`). -/
theorem mem_mcaFinset (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w m : Version} :
    m ∈ mcaFinset parents S w ↔ IsMCA parents (↑S) w m := by
  refine ⟨mcaFinset_isMCA parents, fun h => Finset.mem_filter.mpr ⟨?_, h⟩⟩
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

/-- The MCA antichain's support sits inside the pair's joint support (every MCA
member is an ancestor of a support member). -/
theorem supportOf_mca_subset (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} :
    supportOf parents (mcaFinset parents S w) ⊆ supportOf parents (S ∪ {w}) := by
  intro x hx
  obtain ⟨m, hm, hr⟩ := exists_of_mem_supportOf parents hx
  obtain ⟨⟨u, huS, hmu⟩, _⟩ := (mcaFinset_isMCA parents hm).1
  exact mem_supportOf_of parents hlt
    (Finset.mem_union_left _ huS) (hr.trans hmu)

/-- If `w` itself lands in the antichain's support, the antichain is the degenerate
singleton `{w}` (then `w` is below the support, i.e. the pair is comparable). -/
theorem mcaFinset_eq_singleton_of_mem_support
    (hlt : ∀ v p, p ∈ parents v → p < v) {S : Finset Version} {w : Version}
    (hw : w ∈ supportOf parents (mcaFinset parents S w)) :
    mcaFinset parents S w = {w} := by
  obtain ⟨m', hm', hr⟩ := exists_of_mem_supportOf parents hw
  have hm'w : m' = w :=
    Nat.le_antisymm (mcaFinset_le parents hm') (reaches_le hlt hr)
  have hwmem : w ∈ mcaFinset parents S w := hm'w ▸ hm'
  have hwCA : w ∈ CommonAnc parents (↑S) w :=
    (mcaFinset_isMCA parents hwmem).1
  refine Finset.ext fun x => ?_
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨hxCA, hxmax⟩ := mcaFinset_isMCA parents hx
    exact (hxmax w hwCA hxCA.2).symm
  · rintro rfl
    exact hwmem

/-- **The measure strictly drops across a nesting level**: with a proper antichain
(two distinct members), the antichain's support is a *strict* subset of the pair's,
`w` is in the latter, never the former. -/
theorem supportOf_mca_ssubset (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} {m m' : Version}
    (hm : m ∈ mcaFinset parents S w) (hm' : m' ∈ mcaFinset parents S w)
    (hne : m ≠ m') :
    supportOf parents (mcaFinset parents S w) ⊂ supportOf parents (S ∪ {w}) := by
  refine Finset.ssubset_iff_of_subset (supportOf_mca_subset parents hlt) |>.mpr
    ⟨w, mem_supportOf_of parents hlt
      (Finset.mem_union_right _ (Finset.mem_singleton_self w))
      Relation.ReflTransGen.refl, ?_⟩
  intro hwsupp
  have hsing := mcaFinset_eq_singleton_of_mem_support parents hlt hwsupp
  rw [hsing, Finset.mem_singleton] at hm hm'
  exact hne (hm.trans hm'.symm)

open Classical in
/-- **The ascending-rank antichain fold** (the rule's engine). `accS` is the scratch
node's support (the antichain prefix already folded), `acc` its state; each pending
member `m` is merged through the *virtual LCA of the sub-pair* `(accS, m)`, the
recursive occurrence on the sub-pair's own MCA antichain. Termination is by the joint
support measure, lexicographic with the pending length. -/
noncomputable def vfoldAux (hlt : ∀ v p, p ∈ parents v → p < v)
    (accS : Finset Version) (acc : D.State) : List Version → D.State
  | [] => acc
  | m :: ms =>
      vfoldAux hlt (accS ∪ {m})
        (D.merge
          (match _h : (mcaFinset parents accS m).sort (· ≤ ·) with
            | [] => D.init
            | m₁ :: ms₁ => vfoldAux hlt {m₁} (stateD ver m₁) ms₁)
          acc (stateD ver m))
        ms
termination_by pending =>
  ((supportOf parents (accS ∪ pending.toFinset)).card, pending.length)
decreasing_by
  · -- the nested virtual-LCA call: a proper antichain strictly shrinks the support;
    -- a singleton one keeps it and shrinks the pending list
    have hMeq : (m₁ :: ms₁).toFinset = mcaFinset parents accS m := by
      rw [← _h, Finset.sort_toFinset]
    have hset : ({m₁} ∪ ms₁.toFinset : Finset Version) = mcaFinset parents accS m := by
      rw [← hMeq, List.toFinset_cons, Finset.insert_eq]
    rw [hset]
    have hsub : supportOf parents (mcaFinset parents accS m)
        ⊆ supportOf parents (accS ∪ (m :: ms).toFinset) := by
      refine (supportOf_mca_subset parents hlt).trans (supportOf_mono parents hlt ?_)
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_union_right _ (by simp [List.toFinset_cons])
    rcases Nat.lt_or_ge (supportOf parents (mcaFinset parents accS m)).card
        (supportOf parents (accS ∪ (m :: ms).toFinset)).card with hcard | hcard
    · exact Prod.Lex.left _ _ hcard
    · have heq : supportOf parents (mcaFinset parents accS m)
          = supportOf parents (accS ∪ (m :: ms).toFinset) :=
        Finset.eq_of_subset_of_card_le hsub hcard
      have hmm : m ∈ supportOf parents (mcaFinset parents accS m) := by
        rw [heq]
        exact mem_supportOf_of parents hlt
          (Finset.mem_union_right _ (by simp [List.toFinset_cons]))
          Relation.ReflTransGen.refl
      have hsing := mcaFinset_eq_singleton_of_mem_support parents hlt hmm
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
/-- **The virtual-LCA state of a support/version pair** (`VirtualLCA`):
sort the MCA antichain ascending by rank and fold. An empty antichain returns `σ₀`
(under `StoreInv` its event set, the empty union, is exactly the then-empty
intersection, so this is not a junk case); a singleton returns the registered state
(the existing LCA rule). -/
noncomputable def vlcaAux (hlt : ∀ v p, p ∈ parents v → p < v)
    (S : Finset Version) (w : Version) : D.State :=
  match _h : (mcaFinset parents S w).sort (· ≤ ·) with
  | [] => D.init
  | m₁ :: ms₁ => vfoldAux ver parents hlt {m₁} (stateD ver m₁) ms₁

/-- Case equation: empty antichain. -/
theorem vlcaAux_of_sort_nil (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version}
    (h : (mcaFinset parents S w).sort (· ≤ ·) = []) :
    vlcaAux ver parents hlt S w = D.init := by
  unfold vlcaAux
  split
  · rfl
  · rename_i m₁ ms₁ heq
    rw [h] at heq
    cases heq

/-- Case equation: nonempty antichain, the fold from its least member. -/
theorem vlcaAux_of_sort_cons (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Finset Version} {w : Version} {m₁ : Version} {ms₁ : List Version}
    (h : (mcaFinset parents S w).sort (· ≤ ·) = m₁ :: ms₁) :
    vlcaAux ver parents hlt S w
      = vfoldAux ver parents hlt {m₁} (stateD ver m₁) ms₁ := by
  unfold vlcaAux
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

/-- Fold equation: one step, the inner scratch merge folded back into `vlcaAux`. -/
theorem vfoldAux_cons (hlt : ∀ v p, p ∈ parents v → p < v)
    (accS : Finset Version) (acc : D.State) (m : Version) (ms : List Version) :
    vfoldAux ver parents hlt accS acc (m :: ms)
      = vfoldAux ver parents hlt (accS ∪ {m})
          (D.merge (vlcaAux ver parents hlt accS m) acc (stateD ver m)) ms := by
  conv_lhs => rw [vfoldAux]
  unfold vlcaAux
  rfl

end VirtualState

/-- **The virtual LCA state of a head pair**: the recursive antichain merge
of `MCA(v₁, v₂)`, read off the configuration's ranked store. This is the state the
widened merge rule (`Step3V.mergeVirtual`) places in the LCA slot. -/
noncomputable def virtualLCAState (C : Configuration D) (v₁ v₂ : Version) : D.State :=
  vlcaAux C.ver C.parents C.parents_lt {v₁} v₂


/-- The canonical framework resolver used by every verified MRDT. -/
noncomputable def canonicalVirtualLCA (D : MRDTSig) : VirtualLCAResolver D where
  state := virtualLCAState

end Sal.MRDTs
