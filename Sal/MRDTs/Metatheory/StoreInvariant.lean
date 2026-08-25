import Sal.MRDTs.Framework.Execution
import Mathlib.Data.Nat.Find

/-! # Version-store invariant and LCA event theorem -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

section
variable {D : MRDTSig}

/-! ## §1. The store invariant bundle -/

/-- Invariants of the raw ranked store (`ver`, `parents`) sufficient for the LCA lemma.
Stated over raw functions (not `Configuration`) so that *maintenance* under a transition
can be proved without constructing a full invariant-laden `Configuration`. -/
structure StoreInv (ver : Version → Option (D.State × Set (Op D.AppOp)))
    (parents : Version → List Version) : Prop where
  /-- Every DAG edge has an allocated source (parent). In particular an unallocated
  version is nobody's parent, so a fresh version has no out-edges. -/
  parents_alloc : ∀ v p, p ∈ parents v → (ver p).isSome
  /-- Event sets grow along DAG edges (Apply adds one event, Merge unions). -/
  events_mono : ∀ v p, p ∈ parents v →
    ∀ {sp Ep sv Ev}, ver p = some (sp, Ep) → ver v = some (sv, Ev) → Ep ⊆ Ev
  /-- **The generator-version invariant** (paper appendix Prop. `lca`): every event `e`
  of every allocated version has an allocated *origin* version `v₀` containing `e` such
  that every version containing `e` is reachable from `v₀`. -/
  origin : ∀ {v s E}, ver v = some (s, E) → ∀ e ∈ E,
    ∃ v₀ s₀ E₀, ver v₀ = some (s₀, E₀) ∧ e ∈ E₀ ∧
      (∀ {w sw Ew}, ver w = some (sw, Ew) → e ∈ Ew → Reaches parents v₀ w)

/-- `events_mono` along reachability: an allocated ancestor's events are contained in
any allocated descendant's. Intermediate versions are allocated via `parents_alloc`. -/
theorem storeInv_events_mono_reaches
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (hInv : StoreInv ver parents) {a b : Version}
    (hr : Reaches parents a b) :
    ∀ {sa Ea sb Eb}, ver a = some (sa, Ea) → ver b = some (sb, Eb) → Ea ⊆ Eb := by
  induction hr with
  | refl =>
    intro sa Ea sb Eb ha hb
    rw [ha, Option.some.injEq, Prod.mk.injEq] at hb
    rw [hb.2]
  | tail _hpre hstep ih =>
    rename_i mid c
    intro sa Ea sc Ec ha hc
    have hmid : (ver mid).isSome := hInv.parents_alloc c mid hstep
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp hmid
    exact (ih ha hm).trans (hInv.events_mono c mid hstep hm hc)

/-! ## §2. The LCA lemma (paper Lemma LCA) -/

/-- **Lemma LCA** (`lin.tex:160`), from the store invariant alone: if `v_⊤` is an LCA of
`v₁, v₂` and all three are allocated, `E(v_⊤) = E(v₁) ∩ E(v₂)`.

⊆ : monotonicity along the two `Reaches` legs. ⊇ : a shared event's origin reaches both
sides, hence, by the LCA's domination clause, reaches `v_⊤`, and monotonicity lands the
event in `E(v_⊤)`. -/
theorem lca_events_of_storeInv
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (hInv : StoreInv ver parents)
    {v₁ v₂ vT : Version} (hLCA : IsLCA parents v₁ v₂ vT)
    {s₁ E₁ s₂ E₂ sT ET}
    (h₁ : ver v₁ = some (s₁, E₁)) (h₂ : ver v₂ = some (s₂, E₂))
    (hT : ver vT = some (sT, ET)) :
    ET = E₁ ∩ E₂ := by
  obtain ⟨hr₁, hr₂, hdom⟩ := hLCA
  ext e
  constructor
  · intro he
    exact ⟨storeInv_events_mono_reaches hInv hr₁ hT h₁ he,
           storeInv_events_mono_reaches hInv hr₂ hT h₂ he⟩
  · rintro ⟨he₁, he₂⟩
    obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin h₁ e he₁
    have hr₀T : Reaches parents v₀ vT :=
      hdom v₀ (hall h₁ he₁) (hall h₂ he₂)
    exact storeInv_events_mono_reaches hInv hr₀T hv₀ hT he₀

/-- The LCA, when it exists, is unique (the paper's claim below Def. LCA): two LCAs
dominate each other, and the rank order `parents_lt` is antisymmetric. -/
theorem isLCA_unique {parents : Version → List Version}
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {v₁ v₂ u w : Version}
    (hu : IsLCA parents v₁ v₂ u) (hw : IsLCA parents v₁ v₂ w) : u = w := by
  obtain ⟨hu₁, hu₂, hu_dom⟩ := hu
  obtain ⟨hw₁, hw₂, hw_dom⟩ := hw
  exact Nat.le_antisymm
    (reaches_le hlt (hw_dom u hu₁ hu₂))
    (reaches_le hlt (hu_dom w hw₁ hw₂))

/-! ## §3. DAG extension: reachability under allocation of a fresh version

The two lemmas that make `origin` maintainable: extending the store with a fresh version
`vm` (unallocated, hence, by `parents_alloc`, with no out-edges in the old graph)
(i) does not change reachability between old allocated versions, and (ii) reachability
*into* `vm` factors through its declared parents. Stated pointwise (`hver_old`,
`hpar_old`, …) to match `Step3`'s field equations without `if`-shuffling. -/

section Extension

variable {ver : Version → Option (D.State × Set (Op D.AppOp))}
  {parents : Version → List Version}
  {vm : Version}
  {parents' : Version → List Version}

/-- New-graph reachability to an old (allocated) target collapses to old reachability. -/
theorem reaches_old_of_new
    (hpar_alloc : ∀ v p, p ∈ parents v → (ver p).isSome)
    (hfresh : ver vm = none)
    (hpar_old : ∀ w, w ≠ vm → parents' w = parents w)
    {a b : Version}
    (hr : Reaches parents' a b) :
    (ver b).isSome → Reaches parents a b := by
  induction hr with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail _hpre hstep ih =>
    rename_i mid c
    intro hc
    have hc_ne : c ≠ vm := by
      intro h; rw [h, hfresh] at hc; simp at hc
    rw [hpar_old c hc_ne] at hstep
    exact Relation.ReflTransGen.tail (ih (hpar_alloc c mid hstep)) hstep

/-- Old reachability to an allocated target survives the extension. -/
theorem reaches_new_of_old
    (hpar_alloc : ∀ v p, p ∈ parents v → (ver p).isSome)
    (hfresh : ver vm = none)
    (hpar_old : ∀ w, w ≠ vm → parents' w = parents w)
    {a b : Version}
    (hr : Reaches parents a b) :
    (ver b).isSome → Reaches parents' a b := by
  induction hr with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail _hpre hstep ih =>
    rename_i mid c
    intro hc
    have hc_ne : c ≠ vm := by
      intro h; rw [h, hfresh] at hc; simp at hc
    refine Relation.ReflTransGen.tail (ih (hpar_alloc c mid hstep)) ?_
    show mid ∈ parents' c
    rw [hpar_old c hc_ne]; exact hstep

/-- Reachability into the fresh version factors through its declared parents. -/
theorem reaches_new_target
    (hpar_alloc : ∀ v p, p ∈ parents v → (ver p).isSome)
    (hfresh : ver vm = none)
    {ps : List Version}
    (hpar_new : parents' vm = ps)
    (hpar_old : ∀ w, w ≠ vm → parents' w = parents w)
    (hps : ∀ p ∈ ps, (ver p).isSome)
    {a : Version}
    (hr : Reaches parents' a vm) :
    a = vm ∨ ∃ p ∈ ps, Reaches parents a p := by
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hstep' : c ∈ parents' vm := hstep
    rw [hpar_new] at hstep'
    exact Or.inr ⟨c, hstep',
      reaches_old_of_new hpar_alloc hfresh hpar_old hpre (hps c hstep')⟩

end Extension

/-! ## §4. `StoreInv` maintenance under the two allocating transitions -/

section Maintenance

variable {ver : Version → Option (D.State × Set (Op D.AppOp))}
  {parents : Version → List Version}
  {ver' : Version → Option (D.State × Set (Op D.AppOp))}
  {parents' : Version → List Version}

/-- **Merge maintains `StoreInv`.** The fresh version `vm` carries `E₁ ∪ E₂` with
parents `[v₁, v₂]`; every event of the union keeps its old origin, whose reachability
extends through the new edges. -/
theorem storeInv_merge_extend
    (hInv : StoreInv ver parents)
    {vm v₁ v₂ : Version} (hfresh : ver vm = none)
    {s₁ : D.State} {E₁ : Set (Op D.AppOp)} {s₂ : D.State} {E₂ : Set (Op D.AppOp)}
    (h₁ : ver v₁ = some (s₁, E₁)) (h₂ : ver v₂ = some (s₂, E₂))
    {sm : D.State}
    (hver_new : ver' vm = some (sm, E₁ ∪ E₂))
    (hver_old : ∀ w, w ≠ vm → ver' w = ver w)
    (hpar_new : parents' vm = [v₁, v₂])
    (hpar_old : ∀ w, w ≠ vm → parents' w = parents w) :
    StoreInv ver' parents' := by
  have hv₁_ne : v₁ ≠ vm := by
    intro h; rw [h, hfresh] at h₁; simp at h₁
  have hv₂_ne : v₂ ≠ vm := by
    intro h; rw [h, hfresh] at h₂; simp at h₂
  refine ⟨?_, ?_, ?_⟩
  · -- parents_alloc
    intro v p hp
    by_cases hv : v = vm
    · subst hv
      rw [hpar_new] at hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · rw [hver_old p hv₁_ne, h₁]; rfl
      · rw [hver_old p hv₂_ne, h₂]; rfl
    · rw [hpar_old v hv] at hp
      have hpalloc := hInv.parents_alloc v p hp
      have hp_ne : p ≠ vm := by
        intro h; rw [h, hfresh] at hpalloc; simp at hpalloc
      rw [hver_old p hp_ne]; exact hpalloc
  · -- events_mono
    intro v p hp sp Ep sv Ev hvp hvv
    by_cases hv : v = vm
    · subst hv
      rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hvv
      rw [hpar_new] at hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · rw [hver_old p hv₁_ne, h₁, Option.some.injEq, Prod.mk.injEq] at hvp
        rw [← hvp.2, ← hvv.2]
        exact Set.subset_union_left
      · rw [hver_old p hv₂_ne, h₂, Option.some.injEq, Prod.mk.injEq] at hvp
        rw [← hvp.2, ← hvv.2]
        exact Set.subset_union_right
    · rw [hpar_old v hv] at hp
      have hpalloc := hInv.parents_alloc v p hp
      have hp_ne : p ≠ vm := by
        intro h; rw [h, hfresh] at hpalloc; simp at hpalloc
      rw [hver_old p hp_ne] at hvp
      rw [hver_old v hv] at hvv
      exact hInv.events_mono v p hp hvp hvv
  · -- origin
    intro v s E hv e he
    -- Lift the old `∀ w` clause to the new store; the only new target is `vm`,
    -- whose events split over `E₁ ∪ E₂`, each side reached via the old origin
    -- path plus the new edge.
    have lift : ∀ (v₀ : Version),
        (∀ {w sw Ew}, ver w = some (sw, Ew) → e ∈ Ew → Reaches parents v₀ w) →
        ∀ {w sw Ew}, ver' w = some (sw, Ew) → e ∈ Ew → Reaches parents' v₀ w := by
      intro v₀ hall w sw Ew hw hew
      by_cases hwm : w = vm
      · rw [hwm] at hw ⊢
        rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hw
        rw [← hw.2] at hew
        rcases hew with hew | hew
        · have hr' : Reaches parents' v₀ v₁ :=
            reaches_new_of_old hInv.parents_alloc hfresh hpar_old
              (hall h₁ hew) (by rw [h₁]; rfl)
          refine Relation.ReflTransGen.tail hr' ?_
          show v₁ ∈ parents' vm
          rw [hpar_new]; simp
        · have hr' : Reaches parents' v₀ v₂ :=
            reaches_new_of_old hInv.parents_alloc hfresh hpar_old
              (hall h₂ hew) (by rw [h₂]; rfl)
          refine Relation.ReflTransGen.tail hr' ?_
          show v₂ ∈ parents' vm
          rw [hpar_new]; simp
      · rw [hver_old w hwm] at hw
        exact reaches_new_of_old hInv.parents_alloc hfresh hpar_old
          (hall hw hew) (by rw [hw]; rfl)
    by_cases hvm : v = vm
    · rw [hvm, hver_new, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.2] at he
      rcases he with he | he
      · obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin h₁ e he
        have hv₀_ne : v₀ ≠ vm := by
          intro h; rw [h, hfresh] at hv₀; simp at hv₀
        exact ⟨v₀, s₀, E₀, by rw [hver_old v₀ hv₀_ne]; exact hv₀, he₀,
          lift v₀ hall⟩
      · obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin h₂ e he
        have hv₀_ne : v₀ ≠ vm := by
          intro h; rw [h, hfresh] at hv₀; simp at hv₀
        exact ⟨v₀, s₀, E₀, by rw [hver_old v₀ hv₀_ne]; exact hv₀, he₀,
          lift v₀ hall⟩
    · rw [hver_old v hvm] at hv
      obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin hv e he
      have hv₀_ne : v₀ ≠ vm := by
        intro h; rw [h, hfresh] at hv₀; simp at hv₀
      exact ⟨v₀, s₀, E₀, by rw [hver_old v₀ hv₀_ne]; exact hv₀, he₀,
        lift v₀ hall⟩

/-- **Apply maintains `StoreInv`.** The fresh version carries `Ep ∪ {e}` with parent
`[vp]`; the fresh event's origin is the fresh version itself (store-wide timestamp
freshness makes it absent from every old version), and old events keep their origins. -/
theorem storeInv_apply_extend
    (hInv : StoreInv ver parents)
    {vnew vp : Version} (hfresh : ver vnew = none)
    {sp : D.State} {Ep : Set (Op D.AppOp)}
    (hp : ver vp = some (sp, Ep))
    {e : Op D.AppOp}
    (he_fresh : ∀ w sw Ew, ver w = some (sw, Ew) → e ∉ Ew)
    {snew : D.State}
    (hver_new : ver' vnew = some (snew, Ep ∪ {e}))
    (hver_old : ∀ w, w ≠ vnew → ver' w = ver w)
    (hpar_new : parents' vnew = [vp])
    (hpar_old : ∀ w, w ≠ vnew → parents' w = parents w) :
    StoreInv ver' parents' := by
  have hvp_ne : vp ≠ vnew := by
    intro h; rw [h, hfresh] at hp; simp at hp
  refine ⟨?_, ?_, ?_⟩
  · -- parents_alloc
    intro v p hpe
    by_cases hv : v = vnew
    · subst hv
      rw [hpar_new, List.mem_singleton] at hpe
      rw [hpe, hver_old vp hvp_ne, hp]; rfl
    · rw [hpar_old v hv] at hpe
      have hpalloc := hInv.parents_alloc v p hpe
      have hp_ne : p ≠ vnew := by
        intro h; rw [h, hfresh] at hpalloc; simp at hpalloc
      rw [hver_old p hp_ne]; exact hpalloc
  · -- events_mono
    intro v p hpe sp' Ep' sv Ev hvp hvv
    by_cases hv : v = vnew
    · subst hv
      rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hvv
      rw [hpar_new, List.mem_singleton] at hpe
      rw [hpe, hver_old vp hvp_ne, hp, Option.some.injEq, Prod.mk.injEq] at hvp
      rw [← hvp.2, ← hvv.2]
      exact Set.subset_union_left
    · rw [hpar_old v hv] at hpe
      have hpalloc := hInv.parents_alloc v p hpe
      have hp_ne : p ≠ vnew := by
        intro h; rw [h, hfresh] at hpalloc; simp at hpalloc
      rw [hver_old p hp_ne] at hvp
      rw [hver_old v hv] at hvv
      exact hInv.events_mono v p hpe hvp hvv
  · -- origin
    intro v s E hv e' he'
    -- Lift of the `∀ w` clause for an *old* event `e' ≠ e` with `e' ∈ Ep` known
    -- whenever it lands in the new version's set.
    have lift : ∀ (v₀ : Version), e' ≠ e →
        (∀ {w sw Ew}, ver w = some (sw, Ew) → e' ∈ Ew → Reaches parents v₀ w) →
        ∀ {w sw Ew}, ver' w = some (sw, Ew) → e' ∈ Ew → Reaches parents' v₀ w := by
      intro v₀ he'_ne hall w sw Ew hw hew
      by_cases hwm : w = vnew
      · rw [hwm] at hw ⊢
        rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hw
        rw [← hw.2] at hew
        have he'p : e' ∈ Ep := by
          rcases hew with h | h
          · exact h
          · exact absurd h he'_ne
        have hr' : Reaches parents' v₀ vp :=
          reaches_new_of_old hInv.parents_alloc hfresh hpar_old
            (hall hp he'p) (by rw [hp]; rfl)
        refine Relation.ReflTransGen.tail hr' ?_
        show vp ∈ parents' vnew
        rw [hpar_new]; simp
      · rw [hver_old w hwm] at hw
        exact reaches_new_of_old hInv.parents_alloc hfresh hpar_old
          (hall hw hew) (by rw [hw]; rfl)
    by_cases hvm : v = vnew
    · rw [hvm, hver_new, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.2] at he'
      rcases he' with he' | he'
      · -- an old event of the parent's set
        have he'_ne : e' ≠ e := by
          intro h; subst h; exact he_fresh vp sp Ep hp he'
        obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin hp e' he'
        have hv₀_ne : v₀ ≠ vnew := by
          intro h; rw [h, hfresh] at hv₀; simp at hv₀
        exact ⟨v₀, s₀, E₀, by rw [hver_old v₀ hv₀_ne]; exact hv₀, he₀,
          lift v₀ he'_ne hall⟩
      · -- the fresh event: its origin is the fresh version itself
        have he'_eq : e' = e := he'
        rw [he'_eq]
        refine ⟨vnew, snew, Ep ∪ {e}, hver_new, Or.inr rfl, ?_⟩
        intro w sw Ew hw hew
        by_cases hwm : w = vnew
        · rw [hwm]
          exact Relation.ReflTransGen.refl
        · rw [hver_old w hwm] at hw
          exact absurd hew (he_fresh w sw Ew hw)
    · -- an old version: its events are old (freshness), keep their origins
      rw [hver_old v hvm] at hv
      have he'_ne : e' ≠ e := by
        intro h; subst h; exact he_fresh v s E hv he'
      obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin hv e' he'
      have hv₀_ne : v₀ ≠ vnew := by
        intro h; rw [h, hfresh] at hv₀; simp at hv₀
      exact ⟨v₀, s₀, E₀, by rw [hver_old v₀ hv₀_ne]; exact hv₀, he₀,
        lift v₀ he'_ne hall⟩

end Maintenance

theorem commonAnc_reaches_mca {parents : Version → List Version}
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Set Version} {w : Version} {x : Version}
    (hx : x ∈ CommonAnc parents S w) :
    ∃ m, IsMCA parents S w m ∧ Reaches parents x m := by
  let P := fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y
  haveI : DecidablePred P := fun _ => Classical.dec _
  have hxw : x ≤ w := reaches_le hlt hx.2
  have hp : P (Nat.findGreatest P w) :=
    Nat.findGreatest_spec (m := x) hxw ⟨hx, Relation.ReflTransGen.refl⟩
  refine ⟨_, ⟨hp.1, ?_⟩, hp.2⟩
  intro y hy hzy
  have hpy : P y := ⟨hy, hp.2.trans hzy⟩
  have hyw : y ≤ w := reaches_le hlt hy.2
  have hymax : y ≤ Nat.findGreatest P w := by
    by_contra hn
    exact Nat.findGreatest_is_greatest (Nat.not_le.mp hn) hyw hpy
  exact Nat.le_antisymm hymax (reaches_le hlt hzy)

theorem reaches_alloc
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (hInv : StoreInv ver parents) {a b : Version}
    (hr : Reaches parents a b) (hb : (ver b).isSome) : (ver a).isSome := by
  induction hr with
  | refl => exact hb
  | tail _ hstep ih => exact ih (hInv.parents_alloc _ _ hstep)

theorem mca_events_cover
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (hInv : StoreInv ver parents)
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Set Version} {w : Version}
    (hS : ∀ u ∈ S, (ver u).isSome)
    {sw : D.State} {Ew : Set (Op D.AppOp)} (hw : ver w = some (sw, Ew))
    (e : Op D.AppOp) :
    (∃ m, IsMCA parents S w m ∧ ∃ sm Em, ver m = some (sm, Em) ∧ e ∈ Em)
      ↔ (∃ u ∈ S, ∃ su Eu, ver u = some (su, Eu) ∧ e ∈ Eu) ∧ e ∈ Ew := by
  constructor
  · rintro ⟨m, ⟨⟨⟨u, huS, hmu⟩, hmw⟩, _⟩, sm, Em, hm, heEm⟩
    obtain ⟨⟨su, Eu⟩, hu⟩ := Option.isSome_iff_exists.mp (hS u huS)
    exact ⟨⟨u, huS, su, Eu, hu,
      storeInv_events_mono_reaches hInv hmu hm hu heEm⟩,
      storeInv_events_mono_reaches hInv hmw hm hw heEm⟩
  · rintro ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩
    obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin hu e heEu
    have hv₀CA : v₀ ∈ CommonAnc parents S w :=
      ⟨⟨u, huS, hall hu heEu⟩, hall hw heEw⟩
    obtain ⟨m, hmMCA, hv₀m⟩ := commonAnc_reaches_mca hlt hv₀CA
    have hm_alloc : (ver m).isSome :=
      reaches_alloc hInv hmMCA.1.2 (by rw [hw]; rfl)
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp hm_alloc
    exact ⟨m, hmMCA, sm, Em, hm,
      storeInv_events_mono_reaches hInv hv₀m hv₀ hm he₀⟩

theorem storeInv_init :
    StoreInv (initConfig D).ver (initConfig D).parents := by
  refine ⟨?_, ?_, ?_⟩
  · simp [initConfig]
  · simp [initConfig]
  · intro v s E hv e he
    by_cases h : v = 0
    · subst v
      simp [initConfig] at hv
      rw [← hv.2] at he
      exact absurd he (Set.notMem_empty e)
    · simp [initConfig, h] at hv

theorem storeInv_step {C C' : Configuration D} {l : Label D}
    (step : Step D C l C') (inv : StoreInv C.ver C.parents) :
    StoreInv C'.ver C'.parents := by
  cases step with
  | createReplica _ _ _ _ _ hver _ hparents => rw [hver, hparents]; exact inv
  | @apply t r o v s ev vnew _ _ _ freshStore freshVersion _ _ _ _ _ hver _ hparents =>
      exact storeInv_apply_extend (e := (t, r, o))
        (snew := D.update s (t, r, o)) inv freshVersion ‹_›
        (fun w sw Ew hw hmem => freshStore w sw Ew hw _ hmem rfl)
        (by rw [hver]; simp) (fun w hw => by rw [hver]; simp [hw])
        (by rw [hparents]; simp) (fun w hw => by rw [hparents]; simp [hw])
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      _ _ hv₁ hv₂ _ _ freshVersion _ _ _ _ _ _ hver _ hparents =>
      exact storeInv_merge_extend (sm := D.merge sT s₁ s₂)
        inv freshVersion hv₁ hv₂
        (by rw [hver]; simp) (fun w hw => by rw [hver]; simp [hw])
        (by rw [hparents]; simp) (fun w hw => by rw [hparents]; simp [hw])
  | query => exact inv

theorem storeInv_stepV {V : VirtualLCAResolver D}
    {C C' : Configuration D} {l : Label D}
    (step : StepV D V C l C') (inv : StoreInv C.ver C.parents) :
    StoreInv C'.ver C'.parents := by
  cases step with
  | base h => exact storeInv_step h inv
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂
      _ _ hv₁ hv₂ freshVersion _ _ _ _ _ _ hver _ hparents =>
      exact storeInv_merge_extend (sm := D.merge (V.state C v₁ v₂) s₁ s₂)
        inv freshVersion hv₁ hv₂
        (by rw [hver]; simp) (fun w hw => by rw [hver]; simp [hw])
        (by rw [hparents]; simp) (fun w hw => by rw [hparents]; simp [hw])

open LabeledTS in
theorem storeInv_reachable {C : Configuration D}
    (reach : (labeledTS D).ReachableFrom (initConfig D) C) :
    StoreInv C.ver C.parents := by
  induction reach with
  | refl => exact storeInv_init
  | tail _ hs ih =>
      obtain ⟨_, step⟩ := hs
      exact storeInv_step step ih

open LabeledTS in
theorem storeInv_reachableV {V : VirtualLCAResolver D} {C : Configuration D}
    (reach : (labeledTSV D V).ReachableFrom (initConfig D) C) :
    StoreInv C.ver C.parents := by
  induction reach with
  | refl => exact storeInv_init
  | tail _ hs ih =>
      obtain ⟨_, step⟩ := hs
      exact storeInv_stepV step ih

end

end Sal.MRDTs
