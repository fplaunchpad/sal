import Sal.ConditionedMRDTs.Framework.ExecutionModel

/-!
# The LCA Lemma as a store invariant, and the ternary transition system (mission N1)

Two deliverables (see `MRDT_METATHEORY_DRAFT.md` T1):

1. **`lca_events_of_storeInv`** — the paper's Lemma LCA (`lin.tex:160`,
   `L(v_⊤) = L(v₁) ∩ L(v₂)`) proved from an explicit invariant bundle `StoreInv` over the
   raw ranked store:
   * `parents_alloc` — DAG edges have allocated sources;
   * `events_mono`   — event sets grow along DAG edges;
   * `origin`        — every event has a *generator version* (paper appendix Prop. `lca`)
     from which every version containing the event is reachable.
   The ⊆ direction is `events_mono` along `Reaches`; the ⊇ direction sends the shared
   event's origin through the LCA's domination clause. The paper *asserts* generator
   uniqueness ("there will always be a unique generator vertex") and hand-waves the
   descent termination; here the origin is carried as an invariant, so no descent is
   needed at all.

2. **`Step3`** — the ternary labeled transition system over the Phase-0 `Configuration`
   (Apply / Merge / CreateReplica / Query, paper Fig. `sem`), with the Merge rule gated on
   `IsLCA` (the paper's `v_⊤ = LCA(H(r₁), H(r₂))` premise; criss-cross configurations
   therefore disable Merge rather than falsify the lemma — the paper's own potential-LCA
   *recursive merge* refinement is out of scope, as in the paper's main development), plus
   * `storeInv_reachable` — `StoreInv` is a reachability invariant of `Step3`;
   * `merged_store_lca_events` / `applied_store_lca_events` — **maintainability / non-
     vacuity**: the `lca_events` *field* that a `Step3` target `Configuration` must carry
     is derivable for the extended store, so the invariant-laden structure never blocks a
     transition whose premises hold. (Phase-0 deferred exactly this obligation.)

The Apply rule's timestamp freshness is **store-wide** (`h_fresh_store`), quantifying over
all versions' event sets — faithful to the paper's `∀ e' ∈ ⋃ range(L)` where `L` is
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

/-! ## §2. The LCA lemma (mission N1, paper Lemma LCA) -/

/-- **Lemma LCA** (`lin.tex:160`), from the store invariant alone: if `v_⊤` is an LCA of
`v₁, v₂` and all three are allocated, `E(v_⊤) = E(v₁) ∩ E(v₂)`.

⊆ : monotonicity along the two `Reaches` legs. ⊇ : a shared event's origin reaches both
sides, hence — by the LCA's domination clause — reaches `v_⊤`, and monotonicity lands the
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
`vm` (unallocated, hence — by `parents_alloc` — with no out-edges in the old graph)
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
invariants — in particular the `lca_events` field, whose Phase-0 maintenance was
deferred — is discharged in §6, so the invariant-laden structure never blocks a step. -/

/-- Transition labels (paper Fig. `sem`). -/
inductive Label3 (D : ConditionedMRDTSig) where
  | createReplica (r : Replica)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp)
  | merge (r₁ r₂ : Replica)
  | query (r : Replica) (q : D.Query) (v : D.Value)

/-- The ternary step relation. Merge is gated on `IsLCA` (paper's
`v_⊤ = LCA(H(r₁), H(r₂))`) and reads the LCA *state* from the store; criss-cross
configurations (no LCA) disable Merge — the paper's potential-LCA recursive merge is out
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
shape for *every* LCA triple — so the invariant-laden `Configuration` a `Step3.merge`
must produce is never blocked by its `lca_events` field. (Phase-0 deferred exactly this
maintenance obligation; combined with `storeInv_reachable`, it is discharged.) -/
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

/-- Maintainability of `lca_events` under Apply — same shape. -/
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

end

end Sal.ConditionedMRDTs
