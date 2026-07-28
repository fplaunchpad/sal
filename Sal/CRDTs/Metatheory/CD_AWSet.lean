import Sal.CRDTs.Metatheory.JoinLemma_Of_CD

/-!
# `AWSet` discharges the causal-delta bound

The second instantiation of the CD bundle
(`CoreVCs + LatticeVCsPlus + CDVC`), and the demonstration that the
per-CRDT `CDVC` is *usable*: `AWSet` (the add-wins skeleton with
non-trivial `rc`, state-dependent removes, and the defeater
configurations) satisfies

* `LatticeVCsPlus` (`AWSet_latticeVCsPlus`): unions are ACI and both
  update shapes inflate (an add inserts; a rem moves `added` into
  `dead`), definitional for a real state-based CRDT;
* `CDVC` (`AWSet_cdVC`): for `e = add`, the bound is *context-free*
  set algebra (an add's delta is its own timestamp, already generated
  by `update B e`). For `e = rem` it is exactly the trichotomy,
  one inclusion:

      adds(U∖e) ⊆ killed(U∖e) ∪ adds(↓e∖e)

  Every add `a` of `U∖e` either observed `e`'s issue point
  (`a vis e`, putting `a` in the causal past `↓e∖e`), or, since
  union-maximality of `e` cancels the rc-edge `e → a`, has an
  absorber `z ≠ e` in `U`, i.e. is already dead in `U∖e`.

Consequences: `AWSet_joinLemma_via_cd` and
`AWSet_ra_linearizable_via_cd`, the full metatheorem for `AWSet`
through the CD route. Compared with the direct `JoinPeelVCs`
discharge (`AWSet_joinPeelVCs`, which needs the σ-characterization
*plus* four set-algebra lemmas, the `no_absorber_of_max` argument and
two 30-line peel proofs), the CD discharge consumes the same
σ-characterization but replaces everything after it by the single
trichotomy inclusion `h_key` below.
-/

namespace Sal.Emulation

open Classical

/-! ### The lattice contract -/

theorem AWSet_merge_assoc :
    ∀ a b c : AWSet.State,
      AWSet.merge (AWSet.merge a b) c
        = AWSet.merge a (AWSet.merge b c) := by
  intro a b c
  simp only [AWSet_merge, awMerge]
  exact Prod.ext (Set.union_assoc _ _ _) (Set.union_assoc _ _ _)

/-- Both update shapes inflate w.r.t. the union order. -/
theorem AWSet_update_inflation :
    ∀ (s : AWSet.State) (e : Op AWSet.AppOp),
      AWSet.merge s (AWSet.update s e) = AWSet.update s e := by
  intro s e
  rcases he : e.2.2
  · simp only [AWSet_update, AWSet_merge, awUpdate_add he, awMerge]
    refine Prod.ext ?_ ?_
    · ext t
      simp only [Set.mem_union, Set.mem_insert_iff]
      tauto
    · exact Set.union_self _
  · simp only [AWSet_update, AWSet_merge, awUpdate_rem he, awMerge]
    refine Prod.ext (Set.union_self _) ?_
    ext t
    simp only [Set.mem_union]
    tauto

theorem AWSet_latticeVCsPlus : LatticeVCsPlus AWSet :=
  ⟨AWSet_merge_assoc, AWSet_merge_idem, AWSet_update_inflation⟩

/-! ### The causal-delta bound -/

/-- **`AWSet` discharges (CD).** -/
theorem AWSet_cdVC : CDVC AWSet := by
  intro C U A B e h_tr h_ir h_in h_cl h_e h_max hA hB
  have hAeq := AWSet_canonical_eq hA
  have hBeq := AWSet_canonical_eq hB
  subst hAeq
  subst hBeq
  rcases he_op : e.2.2
  · -- e = add: context-free set algebra.
    simp only [AWSet_update, AWSet_merge, awUpdate_add he_op, awMerge]
    refine Prod.ext ?_ ?_
    · ext t
      simp only [Set.mem_union, Set.mem_insert_iff]
      tauto
    · ext t
      simp only [Set.mem_union]
      tauto
  · -- e = rem: the trichotomy, as one inclusion.
    have h_key : awAdds (U \ {e}) ⊆
        awKilled C (U \ {e}) ∪ awAdds (downset C e \ {e}) := by
      rintro t ⟨a, ⟨haU, hane⟩, hadd, ht⟩
      have h_nc : ¬ AWSet.commutes e a :=
        AWSet_not_comm_rem_add he_op hadd
      have h_noedge := h_max a haU hane
      have h1 : ¬ C.vis e a := fun hv => h_noedge (Or.inl ⟨hv, h_nc⟩)
      have h_rc : AWSet.rc e a = RcRes.Fst_then_snd := by
        simp only [AWSet_rc, awRc_eq, he_op, hadd]
      by_cases h2 : C.vis a e
      · -- a lies in e's causal past.
        exact Or.inr ⟨a, ⟨Or.inr (Relation.TransGen.single
          ⟨h2, fun hc => h_nc (commutes_symm hc)⟩), hane⟩, hadd, ht⟩
      · -- maximality hands a an absorber z ≠ e inside U.
        have h_abs : ∃ z ∈ U, C.vis a z ∧ ¬ AWSet.commutes a z := by
          by_contra h_no
          exact h_noedge (Or.inr ⟨h1, h2, h_rc, h_no⟩)
        obtain ⟨z, hzU, hz_vis, hz_nc⟩ := h_abs
        have hz_rem : z.2.2 = AWOp.rem := by
          rcases hz_op : z.2.2
          · exact absurd (AWSet_comm_add_add hadd hz_op) hz_nc
          · rfl
        have hz_ne : z ≠ e := fun heq => h2 (heq ▸ hz_vis)
        exact Or.inl ⟨a, ⟨haU, hane⟩, hadd, ht, z, ⟨hzU, hz_ne⟩,
          hz_vis, hz_rem⟩
    simp only [AWSet_update, AWSet_merge, awUpdate_rem he_op, awMerge]
    refine Prod.ext ?_ ?_
    · ext t
      simp only [Set.mem_union]
      tauto
    · ext t
      simp only [Set.mem_union]
      constructor
      · rintro ((h | h) | h)
        · rcases h_key h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · exact Or.inl h
        · exact h
      · intro h
        exact Or.inr h

/-! ### Consequences -/

/-- The Join Lemma for `AWSet`, derived through the CD bundle. -/
theorem AWSet_joinLemma_via_cd : JoinLemma AWSet :=
  join_lemma_of_cd AWSet_coreVCs AWSet_latticeVCsPlus AWSet_cdVC

/-- **End-to-end RA-linearizability for `AWSet`** through
`CoreVCs + LatticeVCsPlus + CDVC`. -/
theorem AWSet_ra_linearizable_via_cd
    (C : Configuration AWSet)
    (hReach : (labeledTS AWSet).ReachableFrom (initConfig AWSet) C) :
    IsRALinearizable C :=
  ra_linearizable_of_core_lattice_cd AWSet_coreVCs
    AWSet_latticeVCsPlus AWSet_cdVC C hReach

end Sal.Emulation
