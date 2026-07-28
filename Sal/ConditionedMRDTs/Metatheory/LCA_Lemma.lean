import Sal.ConditionedMRDTs.Framework.ExecutionModel
-- `Nat.findGreatest` for the maximal-common-ancestor selection (§7).
import Mathlib.Data.Nat.Find
-- `Finset.sort` (the canonical ascending-rank fold order), `Finset.sup` (rank bounds
-- for the finite MCA antichain and the well-founded support measure), §8.
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The LCA Lemma as a store invariant, and the ternary transition system

Two results:

1. **`lca_events_of_storeInv`**: the paper's Lemma LCA (`lin.tex:160`,
   `L(v_⊤) = L(v₁) ∩ L(v₂)`) proved from an explicit invariant bundle `StoreInv` over the
   raw ranked store:
   * `parents_alloc`: DAG edges have allocated sources;
   * `events_mono`: event sets grow along DAG edges;
   * `origin`: every event has a *generator version* (paper appendix Prop. `lca`)
     from which every version containing the event is reachable.
   The ⊆ direction is `events_mono` along `Reaches`; the ⊇ direction sends the shared
   event's origin through the LCA's domination clause. The paper *asserts* generator
   uniqueness ("there will always be a unique generator vertex") and hand-waves the
   descent termination; here the origin is carried as an invariant, so no descent is
   needed at all.

2. **`Step3`**: the ternary labeled transition system over the `Configuration`
   (Apply / Merge / CreateReplica / Query, paper Fig. `sem`), with the Merge rule gated on
   `IsLCA` (the paper's `v_⊤ = LCA(H(r₁), H(r₂))` premise; criss-cross configurations
   therefore disable Merge rather than falsify the lemma: the paper's own potential-LCA
   *recursive merge* refinement is out of scope, as in the paper's main development), plus
   * `storeInv_reachable`: `StoreInv` is a reachability invariant of `Step3`;
   * `merged_store_lca_events` / `applied_store_lca_events`: **maintainability / non-
     vacuity**: the `lca_events` *field* that a `Step3` target `Configuration` must carry
     is derivable for the extended store, so the invariant-laden structure never blocks a
     transition whose premises hold.

The Apply rule's timestamp freshness is **store-wide** (`h_fresh_store`), quantifying over
all versions' event sets, faithful to the paper's `∀ e' ∈ ⋃ range(L)` where `L` is
*version*-indexed. The 2-way Emulation TS's replica-indexed freshness is strictly weaker
and would not maintain `origin` for historical versions.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

section
variable {D : ConditionedMRDTSig}

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

/-! ## §5. The ternary transition system `Step3` (paper Fig. `sem`)

Emulation style: the target `C'` is posited with field equations, so the `Configuration`
invariants are carried by the structure. The **maintainability** of the store-side
invariants, in particular the `lca_events` field, is discharged in §6, so the
invariant-laden structure never blocks a step. -/

/-- Transition labels (paper Fig. `sem`). -/
inductive Label3 (D : ConditionedMRDTSig) where
  | createReplica (r : Replica)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp)
  | merge (r₁ r₂ : Replica)
  | query (r : Replica) (q : D.Query) (v : D.Value)

/-- The ternary step relation. Merge is gated on `IsLCA` (paper's
`v_⊤ = LCA(H(r₁), H(r₂))`) and reads the LCA *state* from the store; criss-cross
configurations (no LCA) disable Merge: the paper's potential-LCA recursive merge is out
of scope. Apply's timestamp freshness is store-wide (see file header). -/
inductive Step3 (D : ConditionedMRDTSig) :
    Configuration D → Label3 D → Configuration D → Prop where
  /-- **CreateReplica**: fresh replica at `σ₀`, head at the initial version `0`. -/
  | createReplica {C : Configuration D} {r : Replica}
      (h_fresh : C.N r = none)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r D.init)
      (hL : C'.L = updateRep C.L r ∅)
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = C.ver)
      (hhead : C'.head = fun r' => if r' = r then some 0 else C.head r')
      (hparents : C'.parents = C.parents) :
      Step3 D C (.createReplica r) C'
  /-- **Apply**: apply `o` at `r`'s head version `v`, allocating a fresh version
  `vnew > v` carrying the updated state and extended event set. -/
  | apply {C : Configuration D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
      (h_head : C.head r = some v)
      (h_ver : C.ver v = some (s, ev))
      (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
      (h_fresh_store : ∀ w sw Ew, C.ver w = some (sw, Ew) →
        ∀ e' ∈ Ew, Op.time e' ≠ t)
      (h_vnew : C.ver vnew = none)
      (h_rank : v < vnew)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r (D.update s (t, r, o)))
      (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
      (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
      (hver : C'.ver = fun w => if w = vnew
        then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
      (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r')
      (hparents : C'.parents = fun w => if w = vnew then [v] else C.parents w) :
      Step3 D C (.apply t r o) C'
  /-- **Merge** (ternary): `r₁` absorbs `r₂` through the LCA version `v_⊤`, allocating
  a fresh version `vm > v₁, v₂` carrying `mergeL (state v_⊤) s₁ s₂` over `E₁ ∪ E₂`. -/
  | merge {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
      {ev₁ ev₂ evT : Set (Op D.AppOp)}
      (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
      (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
      (h_lca : IsLCA C.parents v₁ v₂ vT)
      (h_verT : C.ver vT = some (sT, evT))
      (h_vm : C.ver vm = none)
      (h_rank₁ : v₁ < vm) (h_rank₂ : v₂ < vm)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r₁ (D.mergeL sT s₁ s₂))
      (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = fun w => if w = vm
        then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (hhead : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (hparents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w) :
      Step3 D C (.merge r₁ r₂) C'
  /-- **Query**: observe `r`; configuration unchanged. -/
  | query {C : Configuration D} {r : Replica} {q : D.Query}
      {v : D.Value} {s : D.State}
      (h_s : C.N r = some s)
      (h_val : v = D.query s q) :
      Step3 D C (.query r q v) C

/-- The ternary LTS. -/
def labeledTS3 (D : ConditionedMRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label3 D
  step := Step3 D
  silent := fun _ => False

/-! ## §6. `StoreInv` is a reachability invariant; `lca_events` is maintainable -/

/-- `StoreInv` holds initially: one allocated version (`0`), no edges, no events. -/
theorem storeInv_init (hInit : D.Inv D.init) :
    StoreInv (initConfig D hInit).ver (initConfig D hInit).parents := by
  have hpar : ∀ v, (initConfig D hInit).parents v = [] := fun _ => rfl
  have hver : ∀ v, (initConfig D hInit).ver v
      = if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro v p hp
    rw [hpar] at hp
    exact absurd hp List.not_mem_nil
  · intro v p hp
    rw [hpar] at hp
    exact absurd hp List.not_mem_nil
  · intro v s E hv e he
    rw [hver] at hv
    by_cases h : v = 0
    · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.2] at he
      exact absurd he (Set.notMem_empty e)
    · rw [if_neg h] at hv
      simp at hv

/-- `StoreInv` is preserved by every `Step3` transition. -/
theorem storeInv_step {C C' : Configuration D} {ℓ : Label3 D}
    (hstep : Step3 D C ℓ C')
    (hInv : StoreInv C.ver C.parents) : StoreInv C'.ver C'.parents := by
  cases hstep with
  | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
    rw [hver, hparents]; exact hInv
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      _C' hN hL hvis hver hhead hparents =>
    exact storeInv_apply_extend (e := (t, r, o)) (snew := D.update s (t, r, o))
      hInv h_vnew h_ver
      (fun w sw Ew hw hmem => h_fresh_store w sw Ew hw _ hmem rfl)
      (by rw [hver]; simp)
      (fun w hw => by rw [hver]; simp [hw])
      (by rw [hparents]; simp)
      (fun w hw => by rw [hparents]; simp [hw])
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂
      _C' hN hL hvis hver hhead hparents =>
    exact storeInv_merge_extend (sm := D.mergeL sT s₁ s₂)
      hInv h_vm h_ver₁ h_ver₂
      (by rw [hver]; simp)
      (fun w hw => by rw [hver]; simp [hw])
      (by rw [hparents]; simp)
      (fun w hw => by rw [hparents]; simp [hw])
  | query h_s h_val => exact hInv

open LabeledTS in
/-- **`StoreInv` is a reachability invariant of the ternary system.** -/
theorem storeInv_reachable {C : Configuration D} {hInit : D.Inv D.init}
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    StoreInv C.ver C.parents := by
  induction hReach with
  | refl => exact storeInv_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact storeInv_step hstep ih

/-- **Maintainability of the `lca_events` field under Merge** (non-vacuity of `Step3`):
for a store satisfying `StoreInv`, the merge-extended store satisfies the `lca_events`
shape for *every* LCA triple, so the invariant-laden `Configuration` a `Step3.merge`
must produce is never blocked by its `lca_events` field. (Combined with
`storeInv_reachable`, it is discharged.) -/
theorem merged_store_lca_events
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    {ver' : Version → Option (D.State × Set (Op D.AppOp))}
    {parents' : Version → List Version}
    (hInv : StoreInv ver parents)
    {vm v₁ v₂ : Version} (hfresh : ver vm = none)
    {s₁ : D.State} {E₁ : Set (Op D.AppOp)} {s₂ : D.State} {E₂ : Set (Op D.AppOp)}
    (h₁ : ver v₁ = some (s₁, E₁)) (h₂ : ver v₂ = some (s₂, E₂))
    {sm : D.State}
    (hver_new : ver' vm = some (sm, E₁ ∪ E₂))
    (hver_old : ∀ w, w ≠ vm → ver' w = ver w)
    (hpar_new : parents' vm = [v₁, v₂])
    (hpar_old : ∀ w, w ≠ vm → parents' w = parents w) :
    ∀ {w₁ w₂ wT : Version} {t₁ F₁ t₂ F₂ tT FT},
      IsLCA parents' w₁ w₂ wT →
      ver' w₁ = some (t₁, F₁) → ver' w₂ = some (t₂, F₂) →
      ver' wT = some (tT, FT) →
      FT = F₁ ∩ F₂ :=
  fun hLCA ha hb hc =>
    lca_events_of_storeInv
      (storeInv_merge_extend hInv hfresh h₁ h₂ hver_new hver_old hpar_new hpar_old)
      hLCA ha hb hc

/-- Maintainability of `lca_events` under Apply, same shape. -/
theorem applied_store_lca_events
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    {ver' : Version → Option (D.State × Set (Op D.AppOp))}
    {parents' : Version → List Version}
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
    ∀ {w₁ w₂ wT : Version} {t₁ F₁ t₂ F₂ tT FT},
      IsLCA parents' w₁ w₂ wT →
      ver' w₁ = some (t₁, F₁) → ver' w₂ = some (t₂, F₂) →
      ver' wT = some (tT, FT) →
      FT = F₁ ∩ F₂ :=
  fun hLCA ha hb hc =>
    lca_events_of_storeInv
      (storeInv_apply_extend hInv hfresh hp he_fresh
        hver_new hver_old hpar_new hpar_old)
      hLCA ha hb hc

/-! ## §7. Virtual LCAs: the MCA covering lemma

The MCA covering lemma in set-support form. Under
`StoreInv`, the event sets of the maximal common ancestors of `(S, w)` **cover exactly**
the intersection `(⋃_{u∈S} E(u)) ∩ E(w)`, the event set the Merge rule demands of an
LCA. At a singleton MCA set this degenerates to `lca_events_of_storeInv`
(`mca_events_cover_of_isLCA` below). `origin` is load-bearing: with op-based redelivery
(two incomparable birth sites) the union strictly undershoots the intersection. -/

/-- Reaching an allocated version from anywhere forces allocation: every non-final
node of the path is the source of a DAG edge (`parents_alloc`). -/
theorem reaches_alloc
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (hInv : StoreInv ver parents) {a b : Version}
    (hr : Reaches parents a b) (hb : (ver b).isSome) : (ver a).isSome := by
  induction hr with
  | refl => exact hb
  | tail _hpre hstep ih => exact ih (hInv.parents_alloc _ _ hstep)

/-- Every common ancestor reaches a **maximal** common ancestor: among the members
reachable from `x` (ranks bounded by `w` via `parents_lt`), one of maximal rank is
Reaches-maximal. Pure DAG-order content, no allocation needed. -/
theorem commonAnc_reaches_mca {parents : Version → List Version}
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {S : Set Version} {w : Version} {x : Version}
    (hx : x ∈ CommonAnc parents S w) :
    ∃ m, IsMCA parents S w m ∧ Reaches parents x m := by
  haveI hdec : DecidablePred
      (fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y) :=
    fun _ => Classical.dec _
  have hxw : x ≤ w := reaches_le hlt hx.2
  have hPz : Nat.findGreatest
        (fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y) w
          ∈ CommonAnc parents S w ∧
      Reaches parents x (Nat.findGreatest
        (fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y) w) :=
    Nat.findGreatest_spec
      (P := fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y)
      (m := x) hxw ⟨hx, Relation.ReflTransGen.refl⟩
  refine ⟨_, ⟨hPz.1, ?_⟩, hPz.2⟩
  intro y hy hzy
  have hPy : y ∈ CommonAnc parents S w ∧ Reaches parents x y :=
    ⟨hy, hPz.2.trans hzy⟩
  have hyw : y ≤ w := reaches_le hlt hy.2
  have hyz : y ≤ Nat.findGreatest
      (fun y => y ∈ CommonAnc parents S w ∧ Reaches parents x y) w := by
    by_contra hlt'
    exact Nat.findGreatest_is_greatest (Nat.not_le.mp hlt') hyw hPy
  exact Nat.le_antisymm hyz (reaches_le hlt hzy)

/-- **The covering lemma (set-support form).** Under `StoreInv` (+ the rank order),
an event lies in some MCA's event set **iff** it lies in some support member's and in
`w`'s: `⋃_{m ∈ MCA(S,w)} E(m) = (⋃_{u∈S} E(u)) ∩ E(w)`. Degenerate cases for free: an
empty MCA set forces an empty intersection (the ⊇ direction *constructs* an MCA from a
shared event's origin), and a singleton MCA set recovers Lemma LCA. -/
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
    exact ⟨⟨u, huS, su, Eu, hu, storeInv_events_mono_reaches hInv hmu hm hu heEm⟩,
      storeInv_events_mono_reaches hInv hmw hm hw heEm⟩
  · rintro ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩
    -- the shared event's origin is a common ancestor …
    obtain ⟨v₀, s₀, E₀, hv₀, he₀, hall⟩ := hInv.origin hu e heEu
    have hv₀CA : v₀ ∈ CommonAnc parents S w :=
      ⟨⟨u, huS, hall hu heEu⟩, hall hw heEw⟩
    -- … which reaches a maximal one, where monotonicity lands the event.
    obtain ⟨m, hmMCA, hv₀m⟩ := commonAnc_reaches_mca hlt hv₀CA
    have hm_alloc : (ver m).isSome := reaches_alloc hInv hmMCA.1.2 (by rw [hw]; rfl)
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp hm_alloc
    exact ⟨m, hmMCA, sm, Em, hm,
      storeInv_events_mono_reaches hInv hv₀m hv₀ hm he₀⟩

/-- An LCA is the MCA of the corresponding singleton support (`k = 1` degeneration):
it is a common ancestor dominating every other, and domination plus the rank order
forces maximality. -/
theorem isMCA_singleton_of_isLCA {parents : Version → List Version}
    (hlt : ∀ v p, p ∈ parents v → p < v)
    {v₁ v₂ vT : Version} (hLCA : IsLCA parents v₁ v₂ vT) :
    IsMCA parents {v₁} v₂ vT := by
  obtain ⟨hr₁, hr₂, hdom⟩ := hLCA
  refine ⟨⟨⟨v₁, rfl, hr₁⟩, hr₂⟩, ?_⟩
  rintro x ⟨⟨u, rfl, hxu⟩, hxw⟩ hTx
  exact Nat.le_antisymm (reaches_le hlt (hdom x hxu hxw)) (reaches_le hlt hTx)

/-- Conversely, every MCA of the singleton support is dominated by the LCA, hence
equals it: LCAs are exactly the case `|MCA| = 1`. -/
theorem isMCA_eq_of_isLCA {parents : Version → List Version}
    {v₁ v₂ vT m : Version} (hLCA : IsLCA parents v₁ v₂ vT)
    (hm : IsMCA parents {v₁} v₂ m) : m = vT := by
  obtain ⟨⟨⟨u, huS, hmu⟩, hmw⟩, hmax⟩ := hm
  rcases huS with rfl
  have hTCA : vT ∈ CommonAnc parents {u} v₂ := ⟨⟨u, rfl, hLCA.1⟩, hLCA.2.1⟩
  exact (hmax vT hTCA (hLCA.2.2 m hmu hmw)).symm

/-! ## §8. The virtual-LCA state: the recursive antichain merge

The rule: sort the MCA antichain ascending by
rank (the canonical order, version ids are allocation ranks) and fold, merging each
member against the accumulated scratch node through *their* virtual LCA, recursively.
A scratch node is identified with its **support**, the finite set of antichain members
it joins (`CommonAnc` over a downward-closed support only consults the maximal ones).

Termination is unconditional: a call is measured by the joint real support
`supportOf (S ∪ {w})`; every sub-pair's support lies inside the common-ancestor set,
which `w` never belongs to when the antichain is proper, so the support strictly
shrinks at each nesting level; within a level the pending list shrinks. Only
`parents_lt` (the rank order, threaded as the explicit hypothesis `hlt`) is consumed.

Defined over the **raw store** (`ver`, `parents`) in the style of `StoreInv`, so that
GC pruning (which preserves `parents` and the read entries) commutes with it
definitionally and SPOT stores need no full `Configuration`. -/

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
        (D.mergeL
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
          (D.mergeL (vlcaAux ver parents hlt accS m) acc (stateD ver m)) ms := by
  conv_lhs => rw [vfoldAux]
  unfold vlcaAux
  rfl

end VirtualState

/-- **The virtual LCA state of a head pair**: the recursive antichain merge
of `MCA(v₁, v₂)`, read off the configuration's ranked store. This is the state the
widened merge rule (`Step3V.mergeVirtual`) places in the LCA slot. -/
noncomputable def virtualLCAState (C : Configuration D) (v₁ v₂ : Version) : D.State :=
  vlcaAux C.ver C.parents C.parents_lt {v₁} v₂

/-! ## §9. The widened step relation: `Step3V`

`Step3` plus the virtual-merge rule. Rather than widen `Step3` in place with a
`mergeVirtual` constructor, the widening is a **conservative-extension layer**
(`.base` embeds every `Step3` step), because in-place widening breaks the exhaustive
`Step3` case analyses of the instance-level honesty layers
(`MRDT_Instances/Peritext_Composed/Supplies.lean`, `RGA_Rehoming/RGA_Honest_Residual.lean`,
`RGA_HHext_Discharge.lean`). Every metatheory
result over `Step3` lifts through `.base`; `mergeVirtual` is the one genuinely new case.

`mergeVirtual` allocates **only** the final `vm` (scratch nodes never enter the store);
its LCA slot carries `virtualLCAState C v₁ v₂`. No `IsLCA` gate: with a singleton MCA
antichain the virtual state *is* the registered LCA state, so the rule strictly
generalizes `Step3.merge` (`isMCA_singleton_of_isLCA`). -/

/-- The ternary step relation widened with the virtual-LCA merge. -/
inductive Step3V (D : ConditionedMRDTSig) :
    Configuration D → Label3 D → Configuration D → Prop where
  /-- Every gated step is a widened step. -/
  | base {C : Configuration D} {ℓ : Label3 D} {C' : Configuration D} :
      Step3 D C ℓ C' → Step3V D C ℓ C'
  /-- **Virtual merge**: `r₁` absorbs `r₂` through the *recursive antichain merge* of
  `MCA(v₁, v₂)` in the LCA slot, allocating a fresh `vm > v₁, v₂` carrying
  `mergeL (virtualLCAState C v₁ v₂) s₁ s₂` over `E₁ ∪ E₂`. -/
  | mergeVirtual {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
      {ev₁ ev₂ : Set (Op D.AppOp)}
      (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
      (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
      (h_vm : C.ver vm = none)
      (h_rank₁ : v₁ < vm) (h_rank₂ : v₂ < vm)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r₁ (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂))
      (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = fun w => if w = vm
        then some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (hhead : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (hparents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w) :
      Step3V D C (.merge r₁ r₂) C'

/-- The widened ternary LTS. -/
def labeledTS3V (D : ConditionedMRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label3 D
  step := Step3V D
  silent := fun _ => False

open LabeledTS in
/-- Gated reachability is widened reachability. -/
theorem reachableV_of_reachable {C : Configuration D} {hInit : D.Inv D.init}
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    (labeledTS3V D).ReachableFrom (initConfig D hInit) C := by
  induction hReach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact Relation.ReflTransGen.tail ih ⟨ℓ, Step3V.base hstep⟩

/-- `StoreInv` is preserved by every widened step: the virtual case is
`storeInv_merge_extend` verbatim (the extension lemma never inspected the merged
state, so the virtual LCA slot changes nothing). -/
theorem storeInv_stepV {C C' : Configuration D} {ℓ : Label3 D}
    (hstep : Step3V D C ℓ C')
    (hInv : StoreInv C.ver C.parents) : StoreInv C'.ver C'.parents := by
  cases hstep with
  | base h => exact storeInv_step h hInv
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂
      h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂
      _C' hN hL hvis hver hhead hparents =>
    exact storeInv_merge_extend (sm := D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂)
      hInv h_vm h_ver₁ h_ver₂
      (by rw [hver]; simp)
      (fun w hw => by rw [hver]; simp [hw])
      (by rw [hparents]; simp)
      (fun w hw => by rw [hparents]; simp [hw])

open LabeledTS in
/-- **`StoreInv` is a reachability invariant of the widened system.** -/
theorem storeInv_reachableV {C : Configuration D} {hInit : D.Inv D.init}
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    StoreInv C.ver C.parents := by
  induction hReach with
  | refl => exact storeInv_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact storeInv_stepV hstep ih

end

/-! ## Axiom audit (kernel layer) -/

#print axioms mca_events_cover
#print axioms vfoldAux_cons
#print axioms storeInv_stepV
#print axioms storeInv_reachableV

end Sal.ConditionedMRDTs
