import Sal.ConditionedMRDTs.Metatheory.Product
import Sal.ConditionedMRDTs.Metatheory.GenericSafety

/-!
# The product safety kit — contract and safety lifts for `D₁ ⊗ D₂`

Mechanizes the F5 layer of `Development/COMPOSITION_PENPAPER.md` (obligations
O12–O15 of its §5.5 plan): the `GenericSafety` predicates compose across the
binary product `prodSig D₁ D₂`, so the generic per-version safety metatheorem
`version_inv_on_of_causal_canonical` fires at the product from component
certificates plus the memo's one-sided conditions.

Contents, by memo obligation:

* **O12** — the **pinned-extension lemma** (memo §2.4.2):
  `exists_extension_pinned` / `exists_extension_pinned₂`. For transitive
  irreflexive `vis` on a finite disjoint union `X = X₁ ⊎ X₂` enumerated by
  lists, any `vis`-respecting enumeration `ℓ₁` of the first part extends to a
  `vis`-respecting enumeration `ρ` of the whole with `π₁ ρ = ℓ₁`. Mechanized
  by **insertion induction** (each second-part element is inserted after all
  its `vis`-predecessors — `exists_insert_pinned`), not the memo's
  acyclicity/topological-sort argument; the statement is the memo's.
  Transitivity + irreflexivity are taken globally (every consumer —
  `GoodConfig3` — supplies them globally).
* **O13** — the honesty lifts: `genHonest_prod_iff` (the ∀-enumeration shape
  is componentwise **iff**, given `CrossPastEnumerable` — the ⇐ direction is
  `Product.lean`'s `genHonest_prod`), and `honestAppOn_prod` (the ∃-causal-
  fold shape composes via pinned extension with ONE side pinned; the free
  side's enumeration is arbitrary because `A⊗` on an `inl` event does not
  read `.2`). `CrossPastEnumerable` states the memo's enumerability side
  condition — the opposite-side part of every event's causal past admits an
  enumeration — `CausalPastEnumerable`-style, an explicit hypothesis per the
  repo convention (holds in reachable configurations).
* **O14** — `safetyStepOn_prod` (memo §2.4.3): the fused stability +
  `Inv`-preservation obligation is componentwise. The untouched component is
  definitional (`(upd⊗ σS e).2 = σS.2` at an `inl` step); the stepped
  component's hypotheses project through the raw kit (`projConf₁/₂`,
  `causalFold_proj₁/₂`).
* **O15** — `causalCanonical_prod_of_one_sided` (memo §2.4.4): the sound
  **one-sided** repair. The naive two-sided statement is REFUTED — see the
  theorem's docstring.

The composite product safety metatheorem `prod_version_inv_on_of_one_sided`
is `version_inv_on_of_causal_canonical` at the product with O12–O15 supplying
its hypotheses (memo §2.4.5).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §O12a  Pinned insertion — the generic list machinery

The engine of the memo §2.4.2 lemma, in insertion form: a
transitive-irreflexive-respecting list admits an insertion point for any new
element — after all its `R`-predecessors — and the insertion preserves
`respects`. Iterating over a batch yields the extension; the pinning is that
insertions never disturb the base list's relative order (recorded as
`filterMap`-invariance along any function vanishing on the batch). -/

section PinnedInsertion

variable {α : Type} {R : α → α → Prop}

/-- **One pinned insertion**: an `R`-respecting list `l` splits as `π ++ τ`
such that `π ++ x :: τ` still respects `R` — descend past the head while some
remaining element is an `R`-predecessor of `x`. Transitivity + irreflexivity
enter exactly once: a kept-prefix element `R`-above `x` would chain with the
`R`-predecessor of `x` below it into a violation of `l`'s own order. -/
private theorem exists_insert_pinned
    (htrans : ∀ {a b c : α}, R a b → R b c → R a c)
    (hirrefl : ∀ a : α, ¬ R a a) :
    ∀ (l : List α), respects l R → ∀ x : α,
      ∃ π τ, l = π ++ τ ∧ respects (π ++ x :: τ) R := by
  intro l
  induction l with
  | nil =>
    intro _ x
    refine ⟨[], [], rfl, ?_⟩
    unfold respects
    rw [List.nil_append]
    exact List.Pairwise.cons (fun b hb => absurd hb List.not_mem_nil)
      List.Pairwise.nil
  | cons a l ih =>
    intro hresp x
    have hresp' : (a :: l).Pairwise (fun u v => ¬ R v u) := hresp
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hresp'
    by_cases hex : ∃ y ∈ a :: l, R y x
    · obtain ⟨π, τ, hsplit, hrins⟩ := ih hl x
      subst hsplit
      refine ⟨a :: π, τ, rfl, ?_⟩
      unfold respects
      rw [List.cons_append, List.pairwise_cons]
      refine ⟨?_, hrins⟩
      intro b hb
      rcases List.mem_append.mp hb with hbπ | hbx
      · exact ha b (List.mem_append_left τ hbπ)
      · rcases List.mem_cons.mp hbx with rfl | hbτ
        · -- `b = x`: a prefix element `R`-above `x` contradicts `hex`
          intro hxa
          obtain ⟨y, hy, hyx⟩ := hex
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hirrefl y (htrans hyx hxa)
          · exact ha y hy (htrans hyx hxa)
        · exact ha b (List.mem_append_right π hbτ)
    · refine ⟨[], a :: l, rfl, ?_⟩
      unfold respects
      rw [List.nil_append, List.pairwise_cons]
      exact ⟨fun b hb hbx => hex ⟨b, hb, hbx⟩, hresp⟩

/-- **Iterated pinned insertion**: extend an `R`-respecting base list by any
batch, one insertion at a time. The result is a permutation of the
concatenation, respects `R`, and its `filterMap` along any function vanishing
on the batch equals the base's — the base's relative order is untouched. -/
private theorem exists_extension_of_respects
    (htrans : ∀ {a b c : α}, R a b → R b c → R a c)
    (hirrefl : ∀ a : α, ¬ R a a) :
    ∀ (add base : List α), respects base R →
      ∃ ρ : List α, ρ.Perm (add ++ base) ∧ respects ρ R ∧
        ∀ {β : Type} (f : α → Option β), (∀ x ∈ add, f x = none) →
          ρ.filterMap f = base.filterMap f := by
  intro add
  induction add with
  | nil =>
    intro base hbase
    exact ⟨base, List.Perm.refl base, hbase, fun _ _ => rfl⟩
  | cons x add ih =>
    intro base hbase
    obtain ⟨π, τ, hsplit, hrins⟩ :=
      exists_insert_pinned (R := R) htrans hirrefl base hbase x
    subst hsplit
    obtain ⟨ρ, hperm, hresp, hfm⟩ := ih (π ++ x :: τ) hrins
    refine ⟨ρ, ?_, hresp, ?_⟩
    · exact hperm.trans
        ((List.Perm.append_left add List.perm_middle).trans List.perm_middle)
    · intro β f hf
      rw [hfm f (fun y hy => hf y (List.mem_cons_of_mem x hy))]
      simp only [List.filterMap_append, List.filterMap_cons,
        hf x List.mem_cons_self]

end PinnedInsertion

/-! ## §O12b  The pinned-extension lemma at the disjoint union (memo §2.4.2) -/

section OpPinnedExtension

variable {A₁ A₂ : Type}

/-- `listPermOf` transports backwards along a permutation. -/
theorem listPermOf_of_perm {γ : Type} {l l' : List γ} {X : Set γ}
    (hp : l.Perm l') (h : listPermOf l' X) : listPermOf l X :=
  ⟨hp.nodup_iff.mpr h.1, fun a => hp.mem_iff.trans (h.2 a)⟩

/-- Enumerations of the two parts of `X` glue by concatenation into an
enumeration of `X` (blocks are disjoint injective images; membership by
`op_sum_cases` + the roundtrips). -/
theorem listPermOf_glue {X : Set (Op (A₁ ⊕ A₂))}
    {ℓ₁ : List (Op A₁)} {ℓ₂ : List (Op A₂)}
    (h₁ : listPermOf ℓ₁ (evRes₁ X)) (h₂ : listPermOf ℓ₂ (evRes₂ X)) :
    listPermOf (ℓ₁.map inlOp ++ ℓ₂.map inrOp) X := by
  constructor
  · rw [List.nodup_append]
    refine ⟨h₁.1.map inlOp_injective, h₂.1.map inrOp_injective, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact inlOp_ne_inrOp a b
  · intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (h₁.2 a).mp ha
      · exact (h₂.2 b).mp hb
    · intro hx
      rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (h₁.2 a).mpr hx, rfl⟩
      · exact Or.inr ⟨b, (h₂.2 b).mpr hx, rfl⟩

/-- **The pinned-extension lemma** (memo §2.4.2): for `vis` transitive and
irreflexive on a finite disjoint union `X = X₁ ⊎ X₂` enumerated by lists, any
`vis`-respecting enumeration `ℓ₁` of the first part extends to a
`vis`-respecting enumeration `ρ` of the whole with `π₁ ρ = ℓ₁`.

Mechanized by insertion induction — each second-part element is inserted at
the earliest position after all its `vis`-predecessors — rather than the
memo's acyclicity/topological-sort argument; the statement is the memo's.
(`htrans`/`hirrefl` are taken globally: every consumer — `GoodConfig3` —
supplies them globally.) -/
theorem exists_extension_pinned
    {vis : Op (A₁ ⊕ A₂) → Op (A₁ ⊕ A₂) → Prop}
    (htrans : ∀ {a b c}, vis a b → vis b c → vis a c)
    (hirrefl : ∀ a, ¬ vis a a)
    {X : Set (Op (A₁ ⊕ A₂))} {ℓ₁ : List (Op A₁)} {ℓ₂ : List (Op A₂)}
    (hp₁ : listPermOf ℓ₁ (evRes₁ X))
    (hr₁ : respects ℓ₁ (fun a b => vis (inlOp a) (inlOp b)))
    (hp₂ : listPermOf ℓ₂ (evRes₂ X)) :
    ∃ ρ : List (Op (A₁ ⊕ A₂)),
      listPermOf ρ X ∧ respects ρ vis ∧ projList₁ ρ = ℓ₁ := by
  have hbase : respects (ℓ₁.map inlOp) vis := by
    unfold respects
    rw [List.pairwise_map]
    exact hr₁
  obtain ⟨ρ, hperm, hresp, hfm⟩ := exists_extension_of_respects (R := vis)
    htrans hirrefl (ℓ₂.map inrOp) (ℓ₁.map inlOp) hbase
  refine ⟨ρ, ?_, hresp, ?_⟩
  · exact listPermOf_of_perm (hperm.trans List.perm_append_comm)
      (listPermOf_glue hp₁ hp₂)
  · have hnone : ∀ x ∈ ℓ₂.map inrOp, oplOp (A₁ := A₁) x = none := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      rfl
    show ρ.filterMap oplOp = ℓ₁
    rw [hfm oplOp hnone]
    exact projList₁_map_inlOp ℓ₁

/-- The pinned-extension lemma, second part pinned (`π₂ ρ = ℓ₂`) — the dual
consumed at `inr` events. -/
theorem exists_extension_pinned₂
    {vis : Op (A₁ ⊕ A₂) → Op (A₁ ⊕ A₂) → Prop}
    (htrans : ∀ {a b c}, vis a b → vis b c → vis a c)
    (hirrefl : ∀ a, ¬ vis a a)
    {X : Set (Op (A₁ ⊕ A₂))} {ℓ₁ : List (Op A₁)} {ℓ₂ : List (Op A₂)}
    (hp₂ : listPermOf ℓ₂ (evRes₂ X))
    (hr₂ : respects ℓ₂ (fun a b => vis (inrOp a) (inrOp b)))
    (hp₁ : listPermOf ℓ₁ (evRes₁ X)) :
    ∃ ρ : List (Op (A₁ ⊕ A₂)),
      listPermOf ρ X ∧ respects ρ vis ∧ projList₂ ρ = ℓ₂ := by
  have hbase : respects (ℓ₂.map inrOp) vis := by
    unfold respects
    rw [List.pairwise_map]
    exact hr₂
  obtain ⟨ρ, hperm, hresp, hfm⟩ := exists_extension_of_respects (R := vis)
    htrans hirrefl (ℓ₁.map inlOp) (ℓ₂.map inrOp) hbase
  refine ⟨ρ, ?_, hresp, ?_⟩
  · exact listPermOf_of_perm hperm (listPermOf_glue hp₁ hp₂)
  · have hnone : ∀ x ∈ ℓ₁.map inlOp, oprOp (A₂ := A₂) x = none := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      rfl
    show ρ.filterMap oprOp = ℓ₂
    rw [hfm oprOp hnone]
    exact projList₂_map_inrOp ℓ₂

/-- `Pairwise` over a list transfers back from `Pairwise` over its `π₁`-image:
a pairwise fact about the projected sublist yields, on the full list, the
tagged form guarded by both elements being `inl` (the reverse of the
`respects_projList₁` direction; consumed by O15's `loOn` clause). -/
private theorem pairwise_of_pairwise_projList₁
    {ρ : List (Op (A₁ ⊕ A₂))} {P : Op A₁ → Op A₁ → Prop}
    (h : (projList₁ ρ).Pairwise P) :
    ρ.Pairwise (fun x y => ∀ a b, x = inlOp a → y = inlOp b → P a b) := by
  induction ρ with
  | nil => exact List.Pairwise.nil
  | cons e ρ ih =>
    rcases op_sum_cases e with ⟨a, rfl⟩ | ⟨c, rfl⟩
    · have hcons : projList₁ (A₂ := A₂) (inlOp a :: ρ) = a :: projList₁ ρ := by
        simp only [projList₁, List.filterMap_cons, oplOp_inlOp]
      rw [hcons] at h
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, ih htail⟩
      intro y hy a' b' ha' hb'
      obtain rfl : a = a' := inlOp_injective ha'
      subst hb'
      exact hhead b' (mem_projList₁.mpr hy)
    · have hcons : projList₁ (A₁ := A₁) (inrOp c :: ρ) = projList₁ ρ := by
        simp only [projList₁, List.filterMap_cons, oplOp_inrOp]
      rw [hcons] at h
      refine List.pairwise_cons.mpr ⟨?_, ih h⟩
      intro _ _ a' _ ha' _
      exact absurd ha'.symm (inlOp_ne_inrOp a' c)

end OpPinnedExtension

variable {D₁ D₂ : ConditionedMRDTSig}

/-! ## Projection plumbing: causal pasts and causal folds

The two identities every lift below reads: the component projection of a
product causal past is the projected configuration's causal past
(`evRes₁_past`/`evRes₂_past` — `vis`/`events` of `projConf₁/₂` are
restrictions), and causal folds project (`causalFold_proj₁/₂`, memo §2.1.5 —
a sublist of a vis-respecting list vis-respects, since component `vis` edges
are product `vis` edges). -/

theorem evRes₁_past {C : Configuration (prodSig D₁ D₂)} (a : Op D₁.AppOp) :
    evRes₁ {e' ∈ C.events | C.vis e' (inlOp a)}
      = {e' ∈ (projConf₁ C).events | (projConf₁ C).vis e' a} :=
  Set.ext fun _ => and_congr mem_projConf₁_events.symm Iff.rfl

theorem evRes₂_past {C : Configuration (prodSig D₁ D₂)} (b : Op D₂.AppOp) :
    evRes₂ {e' ∈ C.events | C.vis e' (inrOp b)}
      = {e' ∈ (projConf₂ C).events | (projConf₂ C).vis e' b} :=
  Set.ext fun _ => and_congr mem_projConf₂_events.symm Iff.rfl

/-- Causal folds project onto component 1 (memo §2.1.5): the witness is the
`π₁`-sublist — `listPermOf` restricts, `respects vis` restricts (component
edges are product edges), and the fold is F1. -/
theorem causalFold_proj₁
    {Cb : Sal.Emulation.Configuration (prodSig D₁ D₂).toCRDTSig}
    {S : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {σ : (prodSig D₁ D₂).State}
    (h : CausalFold Cb S σ) :
    CausalFold (projCore₁ Cb) (evRes₁ S) σ.1 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  refine ⟨projList₁ ρ, listPermOf_projList₁ hp, ?_, ?_⟩
  · unfold respects at hr ⊢
    unfold projList₁
    rw [List.pairwise_filterMap]
    refine hr.imp ?_
    intro x y hxy a hxa b hyb
    rw [oplOp_eq_some] at hxa hyb
    subst hxa; subst hyb
    exact fun hv => hxy hv
  · exact congrArg Prod.fst ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)

/-- Causal folds project onto component 2. -/
theorem causalFold_proj₂
    {Cb : Sal.Emulation.Configuration (prodSig D₁ D₂).toCRDTSig}
    {S : Set (Op (D₁.AppOp ⊕ D₂.AppOp))} {σ : (prodSig D₁ D₂).State}
    (h : CausalFold Cb S σ) :
    CausalFold (projCore₂ Cb) (evRes₂ S) σ.2 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  refine ⟨projList₂ ρ, listPermOf_projList₂ hp, ?_, ?_⟩
  · unfold respects at hr ⊢
    unfold projList₂
    rw [List.pairwise_filterMap]
    refine hr.imp ?_
    intro x y hxy a hxa b hyb
    rw [oprOp_eq_some] at hxa hyb
    subst hxa; subst hyb
    exact fun hv => hxy hv
  · exact congrArg Prod.snd ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)

/-! ## §O13  The honesty lifts (memo §2.4.1–§2.4.2) -/

/-- **The enumerability side condition** (memo §2.4.1 (⇒) / §2.4.2): the
opposite-side part of every event's causal past admits an enumeration.
`CausalPastEnumerable`-style: holds in reachable configurations, whose event
sets are finite, but the repo has no generic finiteness result for reachable
configurations' event sets, so it is kept as an explicit hypothesis. -/
def CrossPastEnumerable (C : Configuration (prodSig D₁ D₂)) : Prop :=
  (∀ a : Op D₁.AppOp, inlOp a ∈ C.events →
    ∃ π : List (Op D₂.AppOp),
      listPermOf π (evRes₂ {e' ∈ C.events | C.vis e' (inlOp a)})) ∧
  (∀ b : Op D₂.AppOp, inrOp b ∈ C.events →
    ∃ π : List (Op D₁.AppOp),
      listPermOf π (evRes₁ {e' ∈ C.events | C.vis e' (inrOp b)}))

/-- **`GenHonest` is componentwise, iff** (memo §2.4.1): the (⇐) direction is
free (`genHonest_prod`, `Product.lean`); the (⇒) direction glues each
component enumeration of a past with an arbitrary enumeration of its
opposite-side part — this is where `CrossPastEnumerable` is load-bearing. -/
theorem genHonest_prod_iff
    {P₁ : Op D₁.AppOp → D₁.State → Prop} {P₂ : Op D₂.AppOp → D₂.State → Prop}
    {C : Configuration (prodSig D₁ D₂)}
    (hEnum : CrossPastEnumerable C) :
    GenHonest (prodSig D₁ D₂) (prodPred P₁ P₂) C ↔
      GenHonest D₁ P₁ (projConf₁ C) ∧ GenHonest D₂ P₂ (projConf₂ C) := by
  constructor
  · intro hGen
    constructor
    · intro a ha π₁ hπ₁
      have ha' : inlOp a ∈ C.events := mem_projConf₁_events.mp ha
      obtain ⟨ℓ₂, hℓ₂⟩ := hEnum.1 a ha'
      have hπ₁' : listPermOf π₁
          (evRes₁ {e' ∈ C.events | C.vis e' (inlOp a)}) := by
        rw [evRes₁_past]
        exact hπ₁
      have hP : P₁ a (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init
          (π₁.map inlOp ++ ℓ₂.map inrOp)).1 :=
        hGen (inlOp a) ha' _ (listPermOf_glue hπ₁' hℓ₂)
      rwa [applySeq_prod, projList₁_append, projList₁_map_inlOp,
        projList₁_map_inrOp, List.append_nil] at hP
    · intro b hb π₂ hπ₂
      have hb' : inrOp b ∈ C.events := mem_projConf₂_events.mp hb
      obtain ⟨ℓ₁, hℓ₁⟩ := hEnum.2 b hb'
      have hπ₂' : listPermOf π₂
          (evRes₂ {e' ∈ C.events | C.vis e' (inrOp b)}) := by
        rw [evRes₂_past]
        exact hπ₂
      have hP : P₂ b (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init
          (ℓ₁.map inlOp ++ π₂.map inrOp)).2 :=
        hGen (inrOp b) hb' _ (listPermOf_glue hℓ₁ hπ₂')
      rwa [applySeq_prod, projList₂_append, projList₂_map_inlOp,
        projList₂_map_inrOp, List.nil_append] at hP
  · rintro ⟨hG₁, hG₂⟩
    exact genHonest_prod hG₁ hG₂

/-- **`HonestAppOn` composes** (memo §2.4.2 corollary): component `HonestAppOn`
on both projections + enumerability of the opposite-side parts of causal
pasts + componentwise `A⊗` give `HonestAppOn` of the product. For an `inl`
event, component honesty hands a causal enumeration `ρ¹` of `past₁(e)` whose
fold satisfies `A₁`; pin it and extend over `past⊗(e)` (pinned extension —
only ONE side is pinned: the other side's enumeration is free because
`A⊗ (ι₁ e)` does not read `.2`), and F1 reads the pinned component fold off
the product fold. -/
theorem honestAppOn_prod
    {A₁ : Op D₁.AppOp → D₁.State → Prop} {A₂ : Op D₂.AppOp → D₂.State → Prop}
    {C : Configuration (prodSig D₁ D₂)}
    (hvtr : ∀ {a b c : Op (D₁.AppOp ⊕ D₂.AppOp)},
      C.vis a b → C.vis b c → C.vis a c)
    (hvir : ∀ a : Op (D₁.AppOp ⊕ D₂.AppOp), ¬ C.vis a a)
    (hEnum : CrossPastEnumerable C)
    (h₁ : HonestAppOn D₁ A₁ (projConf₁ C))
    (h₂ : HonestAppOn D₂ A₂ (projConf₂ C)) :
    HonestAppOn (prodSig D₁ D₂) (prodPred A₁ A₂) C := by
  intro e he
  rcases op_sum_cases e with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨σ₁, ⟨ρ₁, hp₁, hr₁, hf₁⟩, hA⟩ := h₁ a (mem_projConf₁_events.mpr he)
    rw [← evRes₁_past] at hp₁
    have hr₁' : respects ρ₁
        (fun x y : Op D₁.AppOp => C.vis (inlOp x) (inlOp y)) := hr₁
    obtain ⟨ℓ₂, hℓ₂⟩ := hEnum.1 a he
    obtain ⟨ρ, hp, hr, hπ⟩ := exists_extension_pinned (vis := C.vis)
      (fun {x y z} h1 h2 => hvtr h1 h2) hvir hp₁ hr₁' hℓ₂
    refine ⟨applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ,
      ⟨ρ, hp, hr, rfl⟩, ?_⟩
    show A₁ a (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ).1
    have hfold : (applySeq (prodSig D₁ D₂).toCRDTSig
        (prodSig D₁ D₂).init ρ).1 = σ₁ := by
      rw [applySeq_prod, hπ]
      exact hf₁
    rw [hfold]
    exact hA
  · obtain ⟨σ₂, ⟨ρ₂, hp₂, hr₂, hf₂⟩, hA⟩ := h₂ b (mem_projConf₂_events.mpr he)
    rw [← evRes₂_past] at hp₂
    have hr₂' : respects ρ₂
        (fun x y : Op D₂.AppOp => C.vis (inrOp x) (inrOp y)) := hr₂
    obtain ⟨ℓ₁, hℓ₁⟩ := hEnum.2 b he
    obtain ⟨ρ, hp, hr, hπ⟩ := exists_extension_pinned₂ (vis := C.vis)
      (fun {x y z} h1 h2 => hvtr h1 h2) hvir hp₂ hr₂' hℓ₁
    refine ⟨applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ,
      ⟨ρ, hp, hr, rfl⟩, ?_⟩
    show A₂ b (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ).2
    have hfold : (applySeq (prodSig D₁ D₂).toCRDTSig
        (prodSig D₁ D₂).init ρ).2 = σ₂ := by
      rw [applySeq_prod, hπ]
      exact hf₂
    rw [hfold]
    exact hA

/-! ## §O14  `SafetyStepOn` is componentwise (memo §2.4.3) -/

/-- The componentwise product invariant `I₁ ×ᵖ I₂` (memo §2.4.3). -/
def prodInv (I₁ : D₁.State → Prop) (I₂ : D₂.State → Prop) :
    (prodSig D₁ D₂).State → Prop :=
  fun s => I₁ s.1 ∧ I₂ s.2

theorem prodInv_iff (I₁ : D₁.State → Prop) (I₂ : D₂.State → Prop)
    (s : (prodSig D₁ D₂).State) :
    prodInv I₁ I₂ s ↔ I₁ s.1 ∧ I₂ s.2 := Iff.rfl

/-- **`SafetyStepOn` composes** (memo §2.4.3): at an `inl` step the untouched
component is definitional (`(upd⊗ σS e).2 = σS.2`, so `I₂` carries over
verbatim) and every stepped-component hypothesis projects — memberships and
closures through the preimage, future-freeness and `past ⊆ S` by
contrapositives through `ι₁`, causal folds by `causalFold_proj₁` with
`(past⊗(ι₁ e))↾₁ = past₁(e)`. The component obligation is applied at
`projConf₁ C` — configuration-level, no reachability (memo §2.1.4). -/
theorem safetyStepOn_prod {I₁ : D₁.State → Prop}
    {A₁ : Op D₁.AppOp → D₁.State → Prop} {I₂ : D₂.State → Prop}
    {A₂ : Op D₂.AppOp → D₂.State → Prop}
    (h₁ : SafetyStepOn D₁ I₁ A₁) (h₂ : SafetyStepOn D₂ I₂ A₂) :
    SafetyStepOn (prodSig D₁ D₂) (prodInv I₁ I₂) (prodPred A₁ A₂) := by
  intro C E S e σS σP hEev hEcl heE hSsub heS hScl hfut hpast hFS hFP hI hA
  rcases op_sum_cases e with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have hFS₁ : CausalFold (Configuration.core (projConf₁ C))
        (evRes₁ S) σS.1 := by
      rw [projConf₁_core]
      exact causalFold_proj₁ hFS
    have hFP₁ : CausalFold (Configuration.core (projConf₁ C))
        {e' ∈ (projConf₁ C).events | (projConf₁ C).vis e' a} σP.1 := by
      rw [projConf₁_core, ← evRes₁_past]
      exact causalFold_proj₁ hFP
    have hstep := h₁ (projConf₁ C) (evRes₁ E) (evRes₁ S) a σS.1 σP.1
      (fun x hx => mem_projConf₁_events.mpr (hEev (inlOp x) hx))
      (fun x y hv hy => hEcl (inlOp x) (inlOp y) hv hy)
      heE (fun x hx => hSsub hx) heS
      (fun x y hv hy => hScl (inlOp x) (inlOp y) hv hy)
      (fun x hx hv => hfut (inlOp x) hx hv)
      (fun x hv => hpast (inlOp x) hv)
      hFS₁ hFP₁ hI.1 hA
    show I₁ ((prodSig D₁ D₂).update σS (inlOp a)).1
        ∧ I₂ ((prodSig D₁ D₂).update σS (inlOp a)).2
    rw [prodSig_update_inl]
    exact ⟨hstep, hI.2⟩
  · have hFS₂ : CausalFold (Configuration.core (projConf₂ C))
        (evRes₂ S) σS.2 := by
      rw [projConf₂_core]
      exact causalFold_proj₂ hFS
    have hFP₂ : CausalFold (Configuration.core (projConf₂ C))
        {e' ∈ (projConf₂ C).events | (projConf₂ C).vis e' b} σP.2 := by
      rw [projConf₂_core, ← evRes₂_past]
      exact causalFold_proj₂ hFP
    have hstep := h₂ (projConf₂ C) (evRes₂ E) (evRes₂ S) b σS.2 σP.2
      (fun x hx => mem_projConf₂_events.mpr (hEev (inrOp x) hx))
      (fun x y hv hy => hEcl (inrOp x) (inrOp y) hv hy)
      heE (fun x hx => hSsub hx) heS
      (fun x y hv hy => hScl (inrOp x) (inrOp y) hv hy)
      (fun x hx hv => hfut (inrOp x) hx hv)
      (fun x hv => hpast (inrOp x) hv)
      hFS₂ hFP₂ hI.2 hA
    show I₁ ((prodSig D₁ D₂).update σS (inrOp b)).1
        ∧ I₂ ((prodSig D₁ D₂).update σS (inrOp b)).2
    rw [prodSig_update_inr]
    exact ⟨hI.1, hstep⟩

/-! ## §O15  `CausalCanonical`, one-sided (memo §2.4.4) -/

/-- **`CausalCanonical` of the product, one-sided pinning** (memo §2.4.4):
`GoodConfig3 C` + `CausalCanonical (projConf₁ C)` + `D₂` all-comm with
`rc₂ ≡ Either` give `CausalCanonical C`. Pin component 1's causal witness and
extend by pinned extension; `loOn⊗` edges are `inl`/`inl` only (mixed dead by
F3, `inr`/`inr` dead by all-comm + `Either`), so the extension respects
`loOn⊗` through the pinned `π₁`-order; the free side's fold agrees with the
projected canonical fold by all-comm permutation-invariance
(`perm_ext_iff_of_nodup` + `applySeq_perm_of_all_comm`), the canonical fold
supplied by `GoodConfig3.canonical` at the product.

**The naive two-sided statement is REFUTED** (memo §2.4.4, execution checked
realizable in §5.3) — do not pose it: with 4 events, `vis|E = {c→a, b→d}`
(`a, b` component 1; `c, d` component 2), the component causal witnesses
`ℓ₁ = [a, b]` and `ℓ₂ = [d, c]` are each legitimate, but a joint extension
needs `a<b`, `d<c`, `c<a`, `b<d` — the cycle `a<b<d<c<a`. No product causal
enumeration extends both; the failure is the two-sided pinning itself. When
both components are rc-nontrivial/order-sensitive, product `CausalCanonical`
inherits the open status of OQ8 — composition is neutral there. -/
theorem causalCanonical_prod_of_one_sided
    {C : Configuration (prodSig D₁ D₂)} (hG : GoodConfig3 C)
    (hCC₁ : CausalCanonical (projConf₁ C))
    (hcomm₂ : ∀ a b : Op D₂.AppOp, D₂.toCRDTSig.commutes a b)
    (hrc₂ : ∀ a b : Op D₂.AppOp, D₂.toCRDTSig.rc a b = RcRes.Either) :
    CausalCanonical C := by
  intro v s E hv
  have hv₁ : (projConf₁ C).ver v = some (s.1, evRes₁ E) := by
    have hdef : (projConf₁ C).ver v
        = (C.ver v).map (fun p => (p.1.1, evRes₁ p.2)) := rfl
    rw [hdef, hv]
    rfl
  obtain ⟨ρ₁, hp₁, hvis₁, hlo₁, hf₁⟩ := hCC₁ v s.1 (evRes₁ E) hv₁
  obtain ⟨ρc, hpc, _hloc, hfc⟩ := hG.canonical v s E hv
  have hvis₁' : respects ρ₁
      (fun x y : Op D₁.AppOp => C.vis (inlOp x) (inlOp y)) := hvis₁
  obtain ⟨ρ, hp, hvisR, hπ₁⟩ := exists_extension_pinned (vis := C.vis)
    (fun {x y z} h1 h2 => hG.vis_trans h1 h2) hG.vis_irrefl
    hp₁ hvis₁' (listPermOf_projList₂ hpc)
  refine ⟨ρ, hp, hvisR, ?_, ?_⟩
  · -- `loOn⊗` respect: `inl`/`inl` via the pinned `π₁`-order and the F3
    -- localization; mixed and `inr`/`inr` edges are dead outright.
    have hloρ : (projList₁ ρ).Pairwise (fun x y =>
        ¬ loOn (Configuration.core (projConf₁ C)) (evRes₁ E) y x) := by
      rw [hπ₁]
      exact hlo₁
    have hpw := pairwise_of_pairwise_projList₁ hloρ
    unfold respects
    refine hpw.imp ?_
    intro x y hxy hlo
    rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases op_sum_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact hxy a b rfl rfl ((loOn_prod_inl_iff b a).mp hlo)
    · exact loOn_prod_cross_rl b a hlo
    · exact loOn_prod_cross_lr b a hlo
    · rcases hlo with ⟨_, hnc⟩ | ⟨_, _, hrcE, _⟩
      · exact hnc (commutes_prod_inr_of (hcomm₂ b a))
      · exact RcRes.noConfusion
          (((prodSig_rc_inr_inr b a).trans (hrc₂ b a)) ▸ hrcE)
  · -- fold: `.1` is the pinned fold; `.2` is a fold of SOME enumeration of
    -- `E↾₂`, equal to the projected canonical fold by all-comm invariance.
    have hfold₂ : applySeq D₂.toCRDTSig D₂.init (projList₂ ρ) = s.2 := by
      have hpermρ : (projList₂ ρ).Perm (projList₂ ρc) := by
        rw [List.perm_ext_iff_of_nodup (nodup_projList₂ hp.1)
          (nodup_projList₂ hpc.1)]
        intro x
        rw [mem_projList₂, mem_projList₂]
        exact (hp.2 (inrOp x)).trans ((hpc.2 (inrOp x)).symm)
      rw [applySeq_perm_of_all_comm hcomm₂ hpermρ D₂.init]
      exact congrArg Prod.snd
        ((applySeq_prod (prodSig D₁ D₂).init ρc).symm.trans hfc)
    calc applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init ρ
        = (applySeq D₁.toCRDTSig D₁.init (projList₁ ρ),
           applySeq D₂.toCRDTSig D₂.init (projList₂ ρ)) :=
          applySeq_prod (prodSig D₁ D₂).init ρ
      _ = (s.1, s.2) := by rw [hπ₁, hf₁, hfold₂]
      _ = s := rfl

/-! ## The composite product safety metatheorem (memo §2.4.5) -/

/-- **Product safety, end to end**: `version_inv_on_of_causal_canonical` at
the product, with O12–O15 supplying its hypotheses — the product invariant
`I₁ ×ᵖ I₂` holds at every version of `C` from the two component certificates
(`SafetyStepOn`, `HonestAppOn` at the projections) plus the one-sided
conditions (component 1 causally canonical at the projection; component 2
all-comm with `rc ≡ Either`) and the enumerability side condition. -/
theorem prod_version_inv_on_of_one_sided
    {I₁ : D₁.State → Prop} {A₁ : Op D₁.AppOp → D₁.State → Prop}
    {I₂ : D₂.State → Prop} {A₂ : Op D₂.AppOp → D₂.State → Prop}
    (hInit₁ : I₁ D₁.init) (hInit₂ : I₂ D₂.init)
    (hStep₁ : SafetyStepOn D₁ I₁ A₁) (hStep₂ : SafetyStepOn D₂ I₂ A₂)
    (hcomm₂ : ∀ a b : Op D₂.AppOp, D₂.toCRDTSig.commutes a b)
    (hrc₂ : ∀ a b : Op D₂.AppOp, D₂.toCRDTSig.rc a b = RcRes.Either)
    {C : Configuration (prodSig D₁ D₂)} (hG : GoodConfig3 C)
    (hCC₁ : CausalCanonical (projConf₁ C))
    (hEnum : CrossPastEnumerable C)
    (hHon₁ : HonestAppOn D₁ A₁ (projConf₁ C))
    (hHon₂ : HonestAppOn D₂ A₂ (projConf₂ C)) :
    ∀ (v : Version) (s : (prodSig D₁ D₂).State)
      (E : Set (Op (D₁.AppOp ⊕ D₂.AppOp))),
      C.ver v = some (s, E) → I₁ s.1 ∧ I₂ s.2 :=
  version_inv_on_of_causal_canonical
    (I := prodInv I₁ I₂) (A := prodPred A₁ A₂)
    ⟨hInit₁, hInit₂⟩
    (safetyStepOn_prod hStep₁ hStep₂)
    hG
    (causalCanonical_prod_of_one_sided hG hCC₁ hcomm₂ hrc₂)
    (honestAppOn_prod hG.vis_trans hG.vis_irrefl hEnum hHon₁ hHon₂)

/-! ## Axiom audit -/

#print axioms exists_extension_pinned
#print axioms genHonest_prod_iff
#print axioms honestAppOn_prod
#print axioms safetyStepOn_prod
#print axioms causalCanonical_prod_of_one_sided
#print axioms prod_version_inv_on_of_one_sided

end Sal.ConditionedMRDTs
