import Sal.ConditionedMRDTs.Metatheory.GenHonest

/-!
# The binary product combinator `D₁ ⊗ D₂`: the raw composition kit

The product of two conditioned MRDT signatures composes at the boundary
`JoinLemma3At`: cross-component pairs commute *by `rfl`* (the (D-cross) fact),
so `loOn` localizes, folds and configurations project field-for-field, and
the glued join witness is a plain concatenation.

Layering: this file imports only `Metatheory.GenHonest` (hence the framework
and the generic metatheory); it imports no instance files. The demo capstone
consuming this kit is `MRDT_Instances/ProductDemo/ProductDemo.lean`.

Contents:

* Event injections/projections (`inlOp`/`inrOp`/`oplOp`/`oprOp`/
  `projList₁`/`projList₂`/`evRes₁`/`evRes₂`) with their roundtrip kit, and
  the combinator `prodSig D₁ D₂ : ConditionedMRDTSig` with its `rfl` simp
  kit (`prodSig_update_inl`, `prodSig_rc_cross`, …). The mixed `rc` is
  `Either`, forced not chosen: cross pairs commute, so any mixed
  `Fst_then_snd` would violate `rc_non_comm_directional`.
* Fold projection `applySeq_prod` and its block corollaries. No commutation
  is used: this identity, not an exchange argument, is where "interleaving
  order between components cannot matter" is discharged once and for all.
* The two definitional kernel facts: (D-cross) `commutes_prod_cross` (cross
  pairs commute by `rfl`) and (D-proj)
  `commutes_prod_inl_iff`/`commutes_prod_inr_iff` (same-side commutation is
  the component's; the forward direction instantiates the untouched
  component at its `init`).
* The binary replica-keyed core projects field-for-field:
  `projCore₁`/`projCore₂`, with `mem_projCore₁_events` etc.
* The ternary ranked-store `Configuration` projects too:
  `projConf₁`/`projConf₂` (every store field restricts; consumed by the
  contract lifts). Reachability does NOT project: the projection of a
  product-reachable configuration is in general unreachable for the
  component's own LTS. That is why everything below consumes
  configuration-level certificates only.
* `loOn` localization: mixed pairs carry no edge in either direction
  (`loOn_prod_cross_lr`/`_rl`, both arms, including the absorber existential),
  same-side edges coincide with the component's
  (`loOn_prod_inl_iff`/`_inr_iff`), and the `respects`/`listPermOf`
  splitting kit.
* `updateVCs_prod`: the guarded update-layer VC bundle composes.
* Canonical states and enumerations project
  (`isCanonicalState_proj₁`/`_proj₂`).
* The closure-free concatenation gluing `canonical_glue`: component canonical
  states at the restricted sets assemble into the product canonical state at
  the mixed set, witness `ι₁ρ¹ ++ ι₂ρ²`, no re-interleaving.
* The join gluings `joinLemma3At_prod` (visNC-closure premises) and
  `joinLemma3FAt_prod` (full-closure premises, over the per-configuration
  `JoinLemma3FAt`), both instances of the one closure-free concatenation
  core; plus the composite convenience theorem
  `prod_ra_linearizable3_of_honest_reach` (contract `prodContract H₁ H₂`,
  component contracts precomposed with the core projections).
* The free direction of the `GenHonest` lift (`genHonest_prod`). The `⇒`
  direction (needs causal-past enumerability), the `HonestApp` lift and its
  pinned-linear-extension lemma, `SafetyStepOn`, and `CausalCanonical` live
  in `Product_Safety.lean`; the ≈-kit lives in `ProductEq.lean`.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## Event injections and projections -/

section OpKit
variable {A₁ A₂ : Type}

/-- Inject a component-1 event into the sum payload, preserving the `(t, r)`
prefix (`ι₁`). -/
def inlOp (e : Op A₁) : Op (A₁ ⊕ A₂) := (e.1, e.2.1, Sum.inl e.2.2)

/-- Inject a component-2 event (`ι₂`). -/
def inrOp (e : Op A₂) : Op (A₁ ⊕ A₂) := (e.1, e.2.1, Sum.inr e.2.2)

/-- Partial projection onto component 1 (`opl`). -/
def oplOp (x : Op (A₁ ⊕ A₂)) : Option (Op A₁) :=
  match x.2.2 with
  | Sum.inl o => some (x.1, x.2.1, o)
  | Sum.inr _ => none

/-- Partial projection onto component 2 (`opr`). -/
def oprOp (x : Op (A₁ ⊕ A₂)) : Option (Op A₂) :=
  match x.2.2 with
  | Sum.inl _ => none
  | Sum.inr o => some (x.1, x.2.1, o)

/-- List projection onto component 1 (`π₁`). -/
def projList₁ (ρ : List (Op (A₁ ⊕ A₂))) : List (Op A₁) := ρ.filterMap oplOp

/-- List projection onto component 2 (`π₂`). -/
def projList₂ (ρ : List (Op (A₁ ⊕ A₂))) : List (Op A₂) := ρ.filterMap oprOp

/-- Event-set restriction to component 1: the `ι₁`-preimage (`↾₁`). -/
def evRes₁ (ev : Set (Op (A₁ ⊕ A₂))) : Set (Op A₁) := {e | inlOp e ∈ ev}

/-- Event-set restriction to component 2 (`↾₂`). -/
def evRes₂ (ev : Set (Op (A₁ ⊕ A₂))) : Set (Op A₂) := {e | inrOp e ∈ ev}

theorem inlOp_injective : Function.Injective (inlOp (A₁ := A₁) (A₂ := A₂)) := by
  intro a b h
  rcases a with ⟨t, r, o⟩
  rcases b with ⟨t', r', o'⟩
  simp only [inlOp, Prod.mk.injEq, Sum.inl.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem inrOp_injective : Function.Injective (inrOp (A₁ := A₁) (A₂ := A₂)) := by
  intro a b h
  rcases a with ⟨t, r, o⟩
  rcases b with ⟨t', r', o'⟩
  simp only [inrOp, Prod.mk.injEq, Sum.inr.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem inlOp_ne_inrOp (a : Op A₁) (b : Op A₂) : inlOp a ≠ inrOp b := by
  intro h
  simp [inlOp, inrOp] at h

/-- Every mixed event is an `inlOp`- or an `inrOp`-image. -/
theorem op_sum_cases (x : Op (A₁ ⊕ A₂)) :
    (∃ a, x = inlOp a) ∨ (∃ b, x = inrOp b) := by
  rcases x with ⟨t, r, o⟩
  cases o with
  | inl o₁ => exact Or.inl ⟨(t, r, o₁), rfl⟩
  | inr o₂ => exact Or.inr ⟨(t, r, o₂), rfl⟩

theorem oplOp_inlOp (a : Op A₁) : oplOp (A₂ := A₂) (inlOp a) = some a := rfl
theorem oplOp_inrOp (b : Op A₂) : oplOp (A₁ := A₁) (inrOp b) = none := rfl
theorem oprOp_inlOp (a : Op A₁) : oprOp (A₂ := A₂) (inlOp a) = none := rfl
theorem oprOp_inrOp (b : Op A₂) : oprOp (A₁ := A₁) (inrOp b) = some b := rfl

/-- `oplOp x = some a ↔ x = inlOp a`: `oplOp` is the partial inverse of
`inlOp`. -/
theorem oplOp_eq_some {x : Op (A₁ ⊕ A₂)} {a : Op A₁} :
    oplOp x = some a ↔ x = inlOp a := by
  rcases x with ⟨t, r, o⟩
  rcases a with ⟨t', r', o'⟩
  cases o with
  | inl o₁ => simp [oplOp, inlOp]
  | inr o₂ => simp [oplOp, inlOp]

theorem oprOp_eq_some {x : Op (A₁ ⊕ A₂)} {b : Op A₂} :
    oprOp x = some b ↔ x = inrOp b := by
  rcases x with ⟨t, r, o⟩
  rcases b with ⟨t', r', o'⟩
  cases o with
  | inl o₁ => simp [oprOp, inrOp]
  | inr o₂ => simp [oprOp, inrOp]

theorem mem_projList₁ {ρ : List (Op (A₁ ⊕ A₂))} {a : Op A₁} :
    a ∈ projList₁ ρ ↔ inlOp a ∈ ρ := by
  simp only [projList₁, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rw [oplOp_eq_some] at hxa
    exact hxa ▸ hx
  · intro h
    exact ⟨inlOp a, h, oplOp_inlOp a⟩

theorem mem_projList₂ {ρ : List (Op (A₁ ⊕ A₂))} {b : Op A₂} :
    b ∈ projList₂ ρ ↔ inrOp b ∈ ρ := by
  simp only [projList₂, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxb⟩
    rw [oprOp_eq_some] at hxb
    exact hxb ▸ hx
  · intro h
    exact ⟨inrOp b, h, oprOp_inrOp b⟩

theorem projList₁_append (ρ σ : List (Op (A₁ ⊕ A₂))) :
    projList₁ (ρ ++ σ) = projList₁ ρ ++ projList₁ σ :=
  List.filterMap_append

theorem projList₂_append (ρ σ : List (Op (A₁ ⊕ A₂))) :
    projList₂ (ρ ++ σ) = projList₂ ρ ++ projList₂ σ :=
  List.filterMap_append

/-- Roundtrip: projecting an injected block recovers it. -/
theorem projList₁_map_inlOp (ρ : List (Op A₁)) :
    projList₁ (A₂ := A₂) (ρ.map inlOp) = ρ := by
  induction ρ with
  | nil => rfl
  | cons a ρ ih =>
    simp only [List.map_cons, projList₁, List.filterMap_cons, oplOp_inlOp]
    exact congrArg (a :: ·) ih

theorem projList₁_map_inrOp (ρ : List (Op A₂)) :
    projList₁ (A₁ := A₁) (ρ.map inrOp) = [] := by
  induction ρ with
  | nil => rfl
  | cons b ρ ih =>
    simp only [List.map_cons, projList₁, List.filterMap_cons, oplOp_inrOp]
    exact ih

theorem projList₂_map_inlOp (ρ : List (Op A₁)) :
    projList₂ (A₂ := A₂) (ρ.map inlOp) = [] := by
  induction ρ with
  | nil => rfl
  | cons a ρ ih =>
    simp only [List.map_cons, projList₂, List.filterMap_cons, oprOp_inlOp]
    exact ih

theorem projList₂_map_inrOp (ρ : List (Op A₂)) :
    projList₂ (A₁ := A₁) (ρ.map inrOp) = ρ := by
  induction ρ with
  | nil => rfl
  | cons b ρ ih =>
    simp only [List.map_cons, projList₂, List.filterMap_cons, oprOp_inrOp]
    exact congrArg (b :: ·) ih

theorem mem_evRes₁ {ev : Set (Op (A₁ ⊕ A₂))} {a : Op A₁} :
    a ∈ evRes₁ ev ↔ inlOp a ∈ ev := Iff.rfl

theorem mem_evRes₂ {ev : Set (Op (A₁ ⊕ A₂))} {b : Op A₂} :
    b ∈ evRes₂ ev ↔ inrOp b ∈ ev := Iff.rfl

/-- Preimages commute with intersection. -/
theorem evRes₁_inter (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₁ (ev₁ ∩ ev₂) = evRes₁ ev₁ ∩ evRes₁ ev₂ := rfl

theorem evRes₂_inter (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₂ (ev₁ ∩ ev₂) = evRes₂ ev₁ ∩ evRes₂ ev₂ := rfl

/-- Preimages commute with union. -/
theorem evRes₁_union (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₁ (ev₁ ∪ ev₂) = evRes₁ ev₁ ∪ evRes₁ ev₂ := rfl

theorem evRes₂_union (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₂ (ev₁ ∪ ev₂) = evRes₂ ev₁ ∪ evRes₂ ev₂ := rfl

theorem evRes₁_empty : evRes₁ (∅ : Set (Op (A₁ ⊕ A₂))) = (∅ : Set (Op A₁)) := rfl

theorem evRes₂_empty : evRes₂ (∅ : Set (Op (A₁ ⊕ A₂))) = (∅ : Set (Op A₂)) := rfl

/-- `projList₁` preserves `Nodup` (filterMap along the partial inverse of an
injection). -/
theorem nodup_projList₁ {ρ : List (Op (A₁ ⊕ A₂))} (h : ρ.Nodup) :
    (projList₁ ρ).Nodup :=
  h.filterMap fun x x' a hx hx' => by
    rw [Option.mem_def, oplOp_eq_some] at hx hx'
    rw [hx, hx']

theorem nodup_projList₂ {ρ : List (Op (A₁ ⊕ A₂))} (h : ρ.Nodup) :
    (projList₂ ρ).Nodup :=
  h.filterMap fun x x' b hx hx' => by
    rw [Option.mem_def, oprOp_eq_some] at hx hx'
    rw [hx, hx']

/-- Enumerations project: `π₁` of an enumeration of `ev` enumerates `ev↾₁`
(with `evRes₁_union` this is the union-splitting of enumerations). -/
theorem listPermOf_projList₁ {ρ : List (Op (A₁ ⊕ A₂))} {ev : Set (Op (A₁ ⊕ A₂))}
    (h : listPermOf ρ ev) : listPermOf (projList₁ ρ) (evRes₁ ev) :=
  ⟨nodup_projList₁ h.1, fun a => (mem_projList₁).trans (h.2 (inlOp a))⟩

theorem listPermOf_projList₂ {ρ : List (Op (A₁ ⊕ A₂))} {ev : Set (Op (A₁ ⊕ A₂))}
    (h : listPermOf ρ ev) : listPermOf (projList₂ ρ) (evRes₂ ev) :=
  ⟨nodup_projList₂ h.1, fun b => (mem_projList₂).trans (h.2 (inrOp b))⟩

end OpKit

/-! ## The combinator `prodSig D₁ D₂` -/

variable (D₁ D₂ : ConditionedMRDTSig)

/-- **The binary heterogeneous product** `D₁ ⊗ D₂`. State is the product, ops
the sum; `update`/`mergeL`/`Inv`/`applicable` componentwise; `rc` per
component on same-side pairs and `Either` on mixed pairs (forced: cross pairs
commute by (D-cross), so any mixed `Fst_then_snd` would violate
`rc_non_comm_directional`). The only law field, `merge_init_slice`, is the
`Prod.ext` of the components'. -/
def prodSig : ConditionedMRDTSig where
  State := D₁.State × D₂.State
  dec_state := inferInstance
  init := (D₁.init, D₂.init)
  AppOp := D₁.AppOp ⊕ D₂.AppOp
  dec_op := inferInstance
  Query := D₁.Query ⊕ D₂.Query
  Value := D₁.Value ⊕ D₂.Value
  update := fun s e =>
    match e.2.2 with
    | Sum.inl o => (D₁.update s.1 (e.1, e.2.1, o), s.2)
    | Sum.inr o => (s.1, D₂.update s.2 (e.1, e.2.1, o))
  merge := fun a b => (D₁.merge a.1 b.1, D₂.merge a.2 b.2)
  query := fun s q =>
    match q with
    | Sum.inl q₁ => Sum.inl (D₁.query s.1 q₁)
    | Sum.inr q₂ => Sum.inr (D₂.query s.2 q₂)
  rc := fun x y =>
    match x.2.2, y.2.2 with
    | Sum.inl o, Sum.inl o' => D₁.rc (x.1, x.2.1, o) (y.1, y.2.1, o')
    | Sum.inr o, Sum.inr o' => D₂.rc (x.1, x.2.1, o) (y.1, y.2.1, o')
    | Sum.inl _, Sum.inr _ => RcRes.Either
    | Sum.inr _, Sum.inl _ => RcRes.Either
  mergeL := fun l a b => (D₁.mergeL l.1 a.1 b.1, D₂.mergeL l.2 a.2 b.2)
  merge_init_slice := fun a b => by
    show (D₁.mergeL D₁.init a.1 b.1, D₂.mergeL D₂.init a.2 b.2)
      = (D₁.merge a.1 b.1, D₂.merge a.2 b.2)
    rw [D₁.merge_init_slice, D₂.merge_init_slice]
  Inv := fun s => D₁.Inv s.1 ∧ D₂.Inv s.2
  applicable := fun e s =>
    match e.2.2 with
    | Sum.inl o => D₁.applicable (e.1, e.2.1, o) s.1
    | Sum.inr o => D₂.applicable (e.1, e.2.1, o) s.2

variable {D₁ D₂}

/-! ### The `rfl` simp kit -/

theorem prodSig_init : (prodSig D₁ D₂).init = (D₁.init, D₂.init) := rfl

theorem prodSig_update_inl (s : (prodSig D₁ D₂).State) (e : Op D₁.AppOp) :
    (prodSig D₁ D₂).update s (inlOp e) = (D₁.update s.1 e, s.2) := rfl

theorem prodSig_update_inr (s : (prodSig D₁ D₂).State) (e : Op D₂.AppOp) :
    (prodSig D₁ D₂).update s (inrOp e) = (s.1, D₂.update s.2 e) := rfl

theorem prodSig_rc_inl_inl (a b : Op D₁.AppOp) :
    (prodSig D₁ D₂).rc (inlOp a) (inlOp b) = D₁.rc a b := rfl

theorem prodSig_rc_inr_inr (a b : Op D₂.AppOp) :
    (prodSig D₁ D₂).rc (inrOp a) (inrOp b) = D₂.rc a b := rfl

theorem prodSig_rc_inl_inr (a : Op D₁.AppOp) (b : Op D₂.AppOp) :
    (prodSig D₁ D₂).rc (inlOp a) (inrOp b) = RcRes.Either := rfl

theorem prodSig_rc_inr_inl (b : Op D₂.AppOp) (a : Op D₁.AppOp) :
    (prodSig D₁ D₂).rc (inrOp b) (inlOp a) = RcRes.Either := rfl

theorem prodSig_mergeL (l a b : (prodSig D₁ D₂).State) :
    (prodSig D₁ D₂).mergeL l a b
      = (D₁.mergeL l.1 a.1 b.1, D₂.mergeL l.2 a.2 b.2) := rfl

theorem prodSig_inv (s : (prodSig D₁ D₂).State) :
    (prodSig D₁ D₂).Inv s ↔ D₁.Inv s.1 ∧ D₂.Inv s.2 := Iff.rfl

theorem prodSig_applicable_inl (e : Op D₁.AppOp) (s : (prodSig D₁ D₂).State) :
    (prodSig D₁ D₂).applicable (inlOp e) s ↔ D₁.applicable e s.1 := Iff.rfl

theorem prodSig_applicable_inr (e : Op D₂.AppOp) (s : (prodSig D₁ D₂).State) :
    (prodSig D₁ D₂).applicable (inrOp e) s ↔ D₂.applicable e s.2 := Iff.rfl

/-- `Inv` of the product holds at the product `init` given the components'. -/
theorem prodSig_inv_init (h₁ : D₁.Inv D₁.init) (h₂ : D₂.Inv D₂.init) :
    (prodSig D₁ D₂).Inv (prodSig D₁ D₂).init := ⟨h₁, h₂⟩

/-! ## The two definitional kernel facts -/

/-- **(D-cross)** Cross-component pairs commute **by `rfl`**: both orders
reduce to the same pair because each update produces an explicit pair
constructor and the other side's update projects off it. This single
definitional fact is what kills mixed `loOn` edges, localizes the absorber
existential, and makes the join witness a plain concatenation. -/
theorem commutes_prod_cross (e : Op D₁.AppOp) (f : Op D₂.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp e) (inrOp f) :=
  fun _ => rfl

/-- (D-cross), other orientation. -/
theorem commutes_prod_cross' (f : Op D₂.AppOp) (e : Op D₁.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp f) (inlOp e) :=
  fun _ => rfl

/-- (D-proj), the cheap direction: component-1 commutation lifts to the
product (the carried component is untouched on both sides). -/
theorem commutes_prod_inl_of {a b : Op D₁.AppOp}
    (h : D₁.toCRDTSig.commutes a b) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp a) (inlOp b) := fun s => by
  show (D₁.update (D₁.update s.1 a) b, s.2) = (D₁.update (D₁.update s.1 b) a, s.2)
  rw [h s.1]

theorem commutes_prod_inr_of {a b : Op D₂.AppOp}
    (h : D₂.toCRDTSig.commutes a b) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp a) (inrOp b) := fun s => by
  show (s.1, D₂.update (D₂.update s.2 a) b) = (s.1, D₂.update (D₂.update s.2 b) a)
  rw [h s.2]

/-- **(D-proj)** Same-side commutation is the component's. The forward
direction instantiates the product hypothesis at `(s₁, D₂.init)`: `S₂` is
inhabited via `init`, so no `Inv` is needed. -/
theorem commutes_prod_inl_iff (a b : Op D₁.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp a) (inlOp b)
      ↔ D₁.toCRDTSig.commutes a b :=
  ⟨fun h s₁ => congrArg Prod.fst (h (s₁, D₂.init)), commutes_prod_inl_of⟩

theorem commutes_prod_inr_iff (a b : Op D₂.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp a) (inrOp b)
      ↔ D₂.toCRDTSig.commutes a b :=
  ⟨fun h s₂ => congrArg Prod.snd (h (D₁.init, s₂)), commutes_prod_inr_of⟩

/-! ## Folds project: `applySeq_prod` -/

/-- The product fold of a mixed list is the pair of component folds of the
filtered sublists, from any start state. **No commutation is used**: this
identity, not an exchange argument, is where "interleaving order between
components cannot matter" is discharged once and for all. -/
theorem applySeq_prod (s : (prodSig D₁ D₂).State)
    (ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))) :
    applySeq (prodSig D₁ D₂).toCRDTSig s ρ
      = (applySeq D₁.toCRDTSig s.1 (projList₁ ρ),
         applySeq D₂.toCRDTSig s.2 (projList₂ ρ)) := by
  induction ρ generalizing s with
  | nil => rfl
  | cons e ρ ih =>
    rcases e with ⟨t, r, o⟩
    cases o with
    | inl o₁ =>
      exact ih ((D₁.update s.1 (t, r, o₁), s.2) : (prodSig D₁ D₂).State)
    | inr o₂ =>
      exact ih ((s.1, D₂.update s.2 (t, r, o₂)) : (prodSig D₁ D₂).State)

/-- A pure component-1 block folds as `(fold₁, id)`. -/
theorem applySeq_prod_inl_block (s : (prodSig D₁ D₂).State)
    (ρ : List (Op D₁.AppOp)) :
    applySeq (prodSig D₁ D₂).toCRDTSig s (ρ.map inlOp)
      = (applySeq D₁.toCRDTSig s.1 ρ, s.2) := by
  rw [applySeq_prod, projList₁_map_inlOp, projList₂_map_inlOp]
  rfl

/-- A pure component-2 block folds as `(id, fold₂)`. -/
theorem applySeq_prod_inr_block (s : (prodSig D₁ D₂).State)
    (ρ : List (Op D₂.AppOp)) :
    applySeq (prodSig D₁ D₂).toCRDTSig s (ρ.map inrOp)
      = (s.1, applySeq D₂.toCRDTSig s.2 ρ) := by
  rw [applySeq_prod, projList₁_map_inrOp, projList₂_map_inrOp]
  rfl

/-! ## The binary replica-keyed core projects -/

/-- Projection of the product's binary core onto component 1: states by
`Prod.fst`, event sets by the `ι₁`-preimage, `vis` by restriction along
`ι₁`. Every structural field restricts, total on configurations, with no
reachability hypothesis. -/
def projCore₁ (C : Sal.Emulation.Configuration (prodSig D₁ D₂).toCRDTSig) :
    Sal.Emulation.Configuration D₁.toCRDTSig where
  N := fun r => (C.N r).map Prod.fst
  L := fun r => (C.L r).map evRes₁
  vis := fun a b => C.vis (inlOp a) (inlOp b)
  dom_eq := fun r => by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal := fun {a b r s₁} h hL hb => by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct := fun {a b r s r' s'} hL ha hL' hb hne => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inlOp_injective h)
  vis_total_same_replica := fun {a b r s r' s'} hL ha hL' hb hne hrep => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inlOp_injective h)) hrep

/-- Projection of the product's binary core onto component 2. -/
def projCore₂ (C : Sal.Emulation.Configuration (prodSig D₁ D₂).toCRDTSig) :
    Sal.Emulation.Configuration D₂.toCRDTSig where
  N := fun r => (C.N r).map Prod.snd
  L := fun r => (C.L r).map evRes₂
  vis := fun a b => C.vis (inrOp a) (inrOp b)
  dom_eq := fun r => by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal := fun {a b r s₂} h hL hb => by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct := fun {a b r s r' s'} hL ha hL' hb hne => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inrOp_injective h)
  vis_total_same_replica := fun {a b r s r' s'} hL ha hL' hb hne hrep => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inrOp_injective h)) hrep

variable {C : Sal.Emulation.Configuration (prodSig D₁ D₂).toCRDTSig}

theorem projCore₁_vis (a b : Op D₁.AppOp) :
    (projCore₁ C).vis a b ↔ C.vis (inlOp a) (inlOp b) := Iff.rfl

theorem projCore₂_vis (a b : Op D₂.AppOp) :
    (projCore₂ C).vis a b ↔ C.vis (inrOp a) (inrOp b) := Iff.rfl

/-- The projected core's event universe is the restriction of the product's:
`(proj₁ C).events = (C.events)↾₁`. -/
theorem mem_projCore₁_events {a : Op D₁.AppOp} :
    a ∈ (projCore₁ C).events ↔ inlOp a ∈ C.events := by
  constructor
  · rintro ⟨r, s₁, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

theorem mem_projCore₂_events {b : Op D₂.AppOp} :
    b ∈ (projCore₂ C).events ↔ inrOp b ∈ C.events := by
  constructor
  · rintro ⟨r, s₂, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

/-! ## `loOn` localization -/

/-- **Mixed pairs carry no `loOn` edge, ever** (`inl → inr` direction). Arm 1
needs `¬commutes`, refuted by (D-cross); arm 2 needs a mixed
`rc = Fst_then_snd`, but mixed `rc` is `Either` by definition. -/
theorem loOn_prod_cross_lr {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a : Op D₁.AppOp) (b : Op D₂.AppOp) :
    ¬ loOn C ev (inlOp a) (inrOp b) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (commutes_prod_cross a b)
  · exact RcRes.noConfusion ((prodSig_rc_inl_inr a b) ▸ hrc)

/-- Mixed pairs carry no `loOn` edge (`inr → inl` direction). -/
theorem loOn_prod_cross_rl {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (b : Op D₂.AppOp) (a : Op D₁.AppOp) :
    ¬ loOn C ev (inrOp b) (inlOp a) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (commutes_prod_cross' b a)
  · exact RcRes.noConfusion ((prodSig_rc_inr_inl b a) ▸ hrc)

/-- **Same-side `loOn` edges coincide with the component's** at the restricted
set. The absorber existential transfers in both directions: a component
absorber lifts (contrapositive of (D-proj)(⇒)), and a product absorber of an
`inl` event must itself be `inl` (if `inr`, (D-cross) refutes its
`¬commutes`), and then projects. -/
theorem loOn_prod_inl_iff {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a b : Op D₁.AppOp) :
    loOn C ev (inlOp a) (inlOp b) ↔ loOn (projCore₁ C) (evRes₁ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc (commutes_prod_inl_of hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inlOp e₃, h₃, hv₃, fun hc => hnc₃ ((commutes_prod_inl_iff b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact habs ⟨c, h₃, hv₃, fun hc => hnc₃ (commutes_prod_inl_of hc)⟩
      · exact hnc₃ (commutes_prod_cross b c)

theorem loOn_prod_inr_iff {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a b : Op D₂.AppOp) :
    loOn C ev (inrOp a) (inrOp b) ↔ loOn (projCore₂ C) (evRes₂ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc (commutes_prod_inr_of hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inrOp e₃, h₃, hv₃, fun hc => hnc₃ ((commutes_prod_inr_iff b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact hnc₃ (commutes_prod_cross' b c)
      · exact habs ⟨c, h₃, hv₃, fun hc => hnc₃ (commutes_prod_inr_of hc)⟩

/-- `respects` projects: the `π₁`-sublist of a product-`loOn`-respecting list
respects the component `loOn` at the restricted set. -/
theorem respects_projList₁ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (h : respects ρ (loOn C ev)) :
    respects (projList₁ ρ) (loOn (projCore₁ C) (evRes₁ ev)) := by
  unfold respects at h ⊢
  unfold projList₁
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oplOp_eq_some] at hxa hyb
  subst hxa; subst hyb
  exact fun hlo => hxy ((loOn_prod_inl_iff b a).mpr hlo)

theorem respects_projList₂ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (h : respects ρ (loOn C ev)) :
    respects (projList₂ ρ) (loOn (projCore₂ C) (evRes₂ ev)) := by
  unfold respects at h ⊢
  unfold projList₂
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oprOp_eq_some] at hxa hyb
  subst hxa; subst hyb
  exact fun hlo => hxy ((loOn_prod_inr_iff b a).mpr hlo)

/-! ## Canonical states project -/

/-- Canonical states project onto component 1: the witness is the
`π₁`-sublist, Nodup/enumeration/`respects`/fold all transferring through the
fold and localization kit. -/
theorem isCanonicalState_proj₁ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {s : (prodSig D₁ D₂).State}
    (h : IsCanonicalState C ev s) :
    IsCanonicalState (projCore₁ C) (evRes₁ ev) s.1 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨projList₁ ρ, listPermOf_projList₁ hp, respects_projList₁ hr,
    congrArg Prod.fst ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)⟩

theorem isCanonicalState_proj₂ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {s : (prodSig D₁ D₂).State}
    (h : IsCanonicalState C ev s) :
    IsCanonicalState (projCore₂ C) (evRes₂ ev) s.2 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨projList₂ ρ, listPermOf_projList₂ hp, respects_projList₂ hr,
    congrArg Prod.snd ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)⟩

/-! ## The concatenation gluing: closure-free core -/

/-- **The glued witness is a plain concatenation** `ι₁ρ¹ ++ ι₂ρ²`: component
canonical states at the restricted sets assemble into the product canonical
state at the mixed set. No re-interleaving, no closure hypothesis of any
kind: cross pairs carry no `loOn` edge in either direction, the blocks are
disjoint images of injections (a), within-block `respects` transfers along
the same-side iff (b), and the fold is `applySeq_prod` plus the roundtrips
(c). -/
theorem canonical_glue {U : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {m₁ : D₁.State} {m₂ : D₂.State}
    (h₁ : IsCanonicalState (projCore₁ C) (evRes₁ U) m₁)
    (h₂ : IsCanonicalState (projCore₂ C) (evRes₂ U) m₂) :
    IsCanonicalState C U ((m₁, m₂) : (prodSig D₁ D₂).State) := by
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  refine ⟨ρ₁.map inlOp ++ ρ₂.map inrOp, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (a) Nodup: injective images, disjoint blocks (payload tags differ)
    rw [List.nodup_append]
    refine ⟨hp₁.1.map inlOp_injective, hp₂.1.map inrOp_injective, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact inlOp_ne_inrOp a b
  · -- (a) membership: each event lands in the matching block (roundtrip)
    intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (hp₁.2 a).mp ha
      · exact (hp₂.2 b).mp hb
    · intro hx
      rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (hp₁.2 a).mpr hx, rfl⟩
      · exact Or.inr ⟨b, (hp₂.2 b).mpr hx, rfl⟩
  · -- (b) respects: within blocks by the same-side iff; cross pairs edge-free
    unfold respects
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hr₁.imp fun {x y} h hlo => h ((loOn_prod_inl_iff y x).mp hlo)
    · rw [List.pairwise_map]
      exact hr₂.imp fun {x y} h hlo => h ((loOn_prod_inr_iff y x).mp hlo)
    · intro x hx y hy
      rw [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      exact loOn_prod_cross_rl b a
  · -- (c) fold: applySeq_prod + roundtrips
    rw [applySeq_prod, projList₁_append, projList₂_append,
      projList₁_map_inlOp, projList₁_map_inrOp,
      projList₂_map_inlOp, projList₂_map_inrOp,
      List.append_nil]
    show (applySeq D₁.toCRDTSig D₁.init ρ₁, applySeq D₂.toCRDTSig D₂.init ρ₂)
      = (m₁, m₂)
    rw [hf₁, hf₂]

/-! ## `updateVCs_prod` -/

/-- The guarded update-layer VC bundle composes. Same-side pairs transfer
componentwise ((D-proj), `rc⊗ = rcᵢ`, `(t,r)`-prefix preserved by the
injections); mixed pairs are vacuous (cross pairs commute, mixed `rc` is
`Either`); a mixed `cond_comm_lift` triple is impossible (its `rc`-edge or
its `¬commutes` premise dies), and the all-one-side case projects with
`applySeq_prod`: the untouched component folds the *same* list on both
sides. -/
theorem updateVCs_prod (hU₁ : UpdateVCs D₁.toCRDTSig)
    (hU₂ : UpdateVCs D₂.toCRDTSig) :
    UpdateVCs (prodSig D₁ D₂).toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · -- rc_non_comm_directional
    intro x y hd hr
    rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases op_sum_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · -- inl / inl
      have hiff := hU₁.rc_non_comm_directional a b hd hr
      constructor
      · intro hnc
        exact hiff.mp fun hc => hnc (commutes_prod_inl_of hc)
      · intro hor hc
        exact (hiff.mpr hor) ((commutes_prod_inl_iff a b).mp hc)
    · -- inl / inr : both sides false
      constructor
      · intro hnc
        exact absurd (commutes_prod_cross a b) hnc
      · rintro (h | h) <;> exact RcRes.noConfusion h
    · -- inr / inl : both sides false
      constructor
      · intro hnc
        exact absurd (commutes_prod_cross' a b) hnc
      · rintro (h | h) <;> exact RcRes.noConfusion h
    · -- inr / inr
      have hiff := hU₂.rc_non_comm_directional a b hd hr
      constructor
      · intro hnc
        exact hiff.mp fun hc => hnc (commutes_prod_inr_of hc)
      · intro hor hc
        exact (hiff.mpr hor) ((commutes_prod_inr_iff a b).mp hc)
  · -- no_rc_chain : a mixed rc-edge is impossible, so the chain is one-sided
    intro x y z hd₁ hd₂ h
    obtain ⟨hxy, hyz⟩ := h
    rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases op_sum_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
      rcases op_sum_cases z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hU₁.no_rc_chain a b c hd₁ hd₂ ⟨hxy, hyz⟩
    · exact RcRes.noConfusion hyz
    · exact RcRes.noConfusion hxy
    · exact RcRes.noConfusion hxy
    · exact RcRes.noConfusion hxy
    · exact RcRes.noConfusion hxy
    · exact RcRes.noConfusion hyz
    · exact hU₂.no_rc_chain a b c hd₁ hd₂ ⟨hxy, hyz⟩
  · -- cond_comm_lift : the rc-edge and the ¬commutes premise force one side
    intro s e e' e'' π hd₁ hd₂ hd₃ hrc hnc
    rcases op_sum_cases e with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases op_sum_cases e' with ⟨b, rfl⟩ | ⟨b, rfl⟩
    case inl.inr => exact absurd hrc (by rw [prodSig_rc_inl_inr]; exact fun h => RcRes.noConfusion h)
    case inr.inl => exact absurd hrc (by rw [prodSig_rc_inr_inl]; exact fun h => RcRes.noConfusion h)
    case inl.inl =>
      rcases op_sum_cases e'' with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · -- all component 1: project with applySeq_prod
        rw [prodSig_update_inl, prodSig_update_inl,
          prodSig_update_inl, prodSig_update_inl,
          applySeq_prod, applySeq_prod]
        show (D₁.update (applySeq D₁.toCRDTSig
              (D₁.update (D₁.update s.1 b) a) (projList₁ π)) c,
            applySeq D₂.toCRDTSig s.2 (projList₂ π))
          = (D₁.update (applySeq D₁.toCRDTSig
              (D₁.update (D₁.update s.1 a) b) (projList₁ π)) c,
            applySeq D₂.toCRDTSig s.2 (projList₂ π))
        exact congrArg (fun x => (x, applySeq D₂.toCRDTSig s.2 (projList₂ π)))
          (hU₁.cond_comm_lift s.1 a b c (projList₁ π) hd₁ hd₂ hd₃ hrc
            fun hcomm => hnc (commutes_prod_inl_of hcomm))
      · -- e'' on the other side: (D-cross) refutes ¬commutes
        exact absurd (commutes_prod_cross b c) hnc
    case inr.inr =>
      rcases op_sum_cases e'' with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact absurd (commutes_prod_cross' b c) hnc
      · rw [prodSig_update_inr, prodSig_update_inr,
          prodSig_update_inr, prodSig_update_inr,
          applySeq_prod, applySeq_prod]
        show (applySeq D₁.toCRDTSig s.1 (projList₁ π),
            D₂.update (applySeq D₂.toCRDTSig
              (D₂.update (D₂.update s.2 b) a) (projList₂ π)) c)
          = (applySeq D₁.toCRDTSig s.1 (projList₁ π),
            D₂.update (applySeq D₂.toCRDTSig
              (D₂.update (D₂.update s.2 a) b) (projList₂ π)) c)
        exact congrArg (fun x => (applySeq D₁.toCRDTSig s.1 (projList₁ π), x))
          (hU₂.cond_comm_lift s.2 a b c (projList₂ π) hd₁ hd₂ hd₃ hrc
            fun hcomm => hnc (commutes_prod_inr_of hcomm))

/-! ## The join gluings -/

/-- **The join gluing**: the product satisfies `JoinLemma3At` at `C` whenever
the components do at the projections. Premise projection: `vis` facts
restrict; visNC-closure projects because every component NC-edge is a product
NC-edge ((D-proj), an *iff* on same-side pairs, so no strength is silently
lost); canonical states project; preimages commute with `∩`/`∪`. The witness
is the concatenation gluing, with no interleaving combinatorics. -/
theorem joinLemma3At_prod
    (h₁ : JoinLemma3At D₁ (projCore₁ C)) (h₂ : JoinLemma3At D₂ (projCore₂ C)) :
    JoinLemma3At (prodSig D₁ D₂) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ hc₁ hc₂
  have hJ₁ := h₁ (evRes₁ ev₁) (evRes₁ ev₂) s₀.1 s₁.1 s₂.1
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inlOp a) hv)
    (fun a ha => mem_projCore₁_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₁_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb =>
      hcl₁ (inlOp a) (inlOp b) hv (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (fun a b hv hnc hb =>
      hcl₂ (inlOp a) (inlOp b) hv (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (isCanonicalState_proj₁ h₀)
    (isCanonicalState_proj₁ hc₁)
    (isCanonicalState_proj₁ hc₂)
  have hJ₂ := h₂ (evRes₂ ev₁) (evRes₂ ev₂) s₀.2 s₁.2 s₂.2
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inrOp a) hv)
    (fun a ha => mem_projCore₂_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₂_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb =>
      hcl₁ (inrOp a) (inrOp b) hv (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (fun a b hv hnc hb =>
      hcl₂ (inrOp a) (inrOp b) hv (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (isCanonicalState_proj₂ h₀)
    (isCanonicalState_proj₂ hc₁)
    (isCanonicalState_proj₂ hc₂)
  exact canonical_glue hJ₁ hJ₂

/-- The ternary Join Lemma under **full causal closure**, at a single
configuration: the per-`C` body of `JoinLemma3F` (`VC_Set.lean:211`),
mirroring `JoinLemma3At`. Components whose Join Lemma is proved under full
closure (as with an Enable-wins flag) supply this to the full-closure gluing
below. -/
def JoinLemma3FAt (D : ConditionedMRDTSig)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

theorem JoinLemma3F.at {D : ConditionedMRDTSig} (h : JoinLemma3F D)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : JoinLemma3FAt D C :=
  fun ev₁ ev₂ s₀ s₁ s₂ htr hir h1 h2 hc1 hc2 =>
    h C ev₁ ev₂ s₀ s₁ s₂ htr hir h1 h2 hc1 hc2

/-- The join gluing, full-closure form: the concatenation core is
closure-free, and full vis-closure projects the same way (dropping the
NC-conjunct: component `vis`-edges are product `vis`-edges outright). -/
theorem joinLemma3FAt_prod
    (h₁ : JoinLemma3FAt D₁ (projCore₁ C)) (h₂ : JoinLemma3FAt D₂ (projCore₂ C)) :
    JoinLemma3FAt (prodSig D₁ D₂) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ hc₁ hc₂
  have hJ₁ := h₁ (evRes₁ ev₁) (evRes₁ ev₂) s₀.1 s₁.1 s₂.1
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inlOp a) hv)
    (fun a ha => mem_projCore₁_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₁_events.mpr (hin₂ _ ha))
    (fun a b hv hb => hcl₁ (inlOp a) (inlOp b) hv hb)
    (fun a b hv hb => hcl₂ (inlOp a) (inlOp b) hv hb)
    (isCanonicalState_proj₁ h₀)
    (isCanonicalState_proj₁ hc₁)
    (isCanonicalState_proj₁ hc₂)
  have hJ₂ := h₂ (evRes₂ ev₁) (evRes₂ ev₂) s₀.2 s₁.2 s₂.2
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inrOp a) hv)
    (fun a ha => mem_projCore₂_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₂_events.mpr (hin₂ _ ha))
    (fun a b hv hb => hcl₁ (inrOp a) (inrOp b) hv hb)
    (fun a b hv hb => hcl₂ (inrOp a) (inrOp b) hv hb)
    (isCanonicalState_proj₂ h₀)
    (isCanonicalState_proj₂ hc₁)
    (isCanonicalState_proj₂ hc₂)
  exact canonical_glue hJ₁ hJ₂

/-! ## The ternary ranked-store `Configuration` projects

Every store field restricts; the projection is total on configurations, with
no reachability hypothesis. What does NOT transfer is reachability itself,
which is precisely why the kit consumes configuration-level certificates
only. -/

/-- Projection of a ternary product configuration onto component 1: the
replica-keyed core as in `projCore₁`, the store by projecting each version's
`(state, event-set)` pair; `head`/`parents` unchanged. -/
def projConf₁ (C : Configuration (prodSig D₁ D₂)) : Configuration D₁ where
  N := fun r => (C.N r).map Prod.fst
  L := fun r => (C.L r).map evRes₁
  vis := fun a b => C.vis (inlOp a) (inlOp b)
  dom_eq := fun r => by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal := fun {a b r s₁} h hL hb => by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct := fun {a b r s r' s'} hL ha hL' hb hne => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inlOp_injective h)
  causal_mono := fun {a b} h => C.causal_mono h
  vis_total_same_replica := fun {a b r s r' s'} hL ha hL' hb hne hrep => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inlOp_injective h)) hrep
  ver := fun v => (C.ver v).map fun p => (p.1.1, evRes₁ p.2)
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by
    rw [C.ver_init]
    rfl
  head_coherent := fun r v hv => by
    obtain ⟨h1, h2⟩ := C.head_coherent r v hv
    constructor
    · rw [← h1]
      cases C.ver v with
      | none => rfl
      | some p => rfl
    · rw [← h2]
      cases C.ver v with
      | none => rfl
      | some p => rfl
  ver_inv := fun v s e hv => by
    obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp hv
    have hInv := C.ver_inv v p.1 p.2 (by rw [hp])
    have hs : p.1.1 = s := congrArg Prod.fst hpe
    rw [← hs]
    exact hInv.1
  lca_events := fun {v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT} hlca hv₁ hv₂ hvT => by
    obtain ⟨p₁, hp₁, hpe₁⟩ := Option.map_eq_some_iff.mp hv₁
    obtain ⟨p₂, hp₂, hpe₂⟩ := Option.map_eq_some_iff.mp hv₂
    obtain ⟨pT, hpT, hpeT⟩ := Option.map_eq_some_iff.mp hvT
    have h := C.lca_events hlca (by rw [hp₁]) (by rw [hp₂]) (by rw [hpT])
    have hT : evRes₁ pT.2 = eT := congrArg Prod.snd hpeT
    have h1 : evRes₁ p₁.2 = e₁ := congrArg Prod.snd hpe₁
    have h2 : evRes₁ p₂.2 = e₂ := congrArg Prod.snd hpe₂
    rw [← hT, ← h1, ← h2, h]
    rfl

/-- Projection of a ternary product configuration onto component 2. -/
def projConf₂ (C : Configuration (prodSig D₁ D₂)) : Configuration D₂ where
  N := fun r => (C.N r).map Prod.snd
  L := fun r => (C.L r).map evRes₂
  vis := fun a b => C.vis (inrOp a) (inrOp b)
  dom_eq := fun r => by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal := fun {a b r s₂} h hL hb => by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct := fun {a b r s r' s'} hL ha hL' hb hne => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inrOp_injective h)
  causal_mono := fun {a b} h => C.causal_mono h
  vis_total_same_replica := fun {a b r s r' s'} hL ha hL' hb hne hrep => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inrOp_injective h)) hrep
  ver := fun v => (C.ver v).map fun p => (p.1.2, evRes₂ p.2)
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by
    rw [C.ver_init]
    rfl
  head_coherent := fun r v hv => by
    obtain ⟨h1, h2⟩ := C.head_coherent r v hv
    constructor
    · rw [← h1]
      cases C.ver v with
      | none => rfl
      | some p => rfl
    · rw [← h2]
      cases C.ver v with
      | none => rfl
      | some p => rfl
  ver_inv := fun v s e hv => by
    obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp hv
    have hInv := C.ver_inv v p.1 p.2 (by rw [hp])
    have hs : p.1.2 = s := congrArg Prod.fst hpe
    rw [← hs]
    exact hInv.2
  lca_events := fun {v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT} hlca hv₁ hv₂ hvT => by
    obtain ⟨p₁, hp₁, hpe₁⟩ := Option.map_eq_some_iff.mp hv₁
    obtain ⟨p₂, hp₂, hpe₂⟩ := Option.map_eq_some_iff.mp hv₂
    obtain ⟨pT, hpT, hpeT⟩ := Option.map_eq_some_iff.mp hvT
    have h := C.lca_events hlca (by rw [hp₁]) (by rw [hp₂]) (by rw [hpT])
    have hT : evRes₂ pT.2 = eT := congrArg Prod.snd hpeT
    have h1 : evRes₂ p₁.2 = e₁ := congrArg Prod.snd hpe₁
    have h2 : evRes₂ p₂.2 = e₂ := congrArg Prod.snd hpe₂
    rw [← hT, ← h1, ← h2, h]
    rfl

section TernaryProj
variable {CT : Configuration (prodSig D₁ D₂)}

/-- The ternary projection commutes with the core projection: taking the
binary core of `projConf₁` is `projCore₁` of the core (definitional: both
sides carry the same `N`/`L`/`vis` data). -/
theorem projConf₁_core :
    Configuration.core (projConf₁ CT) = projCore₁ (Configuration.core CT) := rfl

theorem projConf₂_core :
    Configuration.core (projConf₂ CT) = projCore₂ (Configuration.core CT) := rfl

theorem mem_projConf₁_events {a : Op D₁.AppOp} :
    a ∈ (projConf₁ CT).events ↔ inlOp a ∈ CT.events := by
  constructor
  · rintro ⟨r, s₁, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

theorem mem_projConf₂_events {b : Op D₂.AppOp} :
    b ∈ (projConf₂ CT).events ↔ inrOp b ∈ CT.events := by
  constructor
  · rintro ⟨r, s₂, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

end TernaryProj

/-! ## The `GenHonest` lift, free direction -/

/-- Componentwise honesty predicate on the product: an `inl` event is judged
by `P₁` at the first component of the fold, an `inr` event by `P₂` at the
second (`P⊗`). -/
def prodPred (P₁ : Op D₁.AppOp → D₁.State → Prop)
    (P₂ : Op D₂.AppOp → D₂.State → Prop) :
    Op (D₁.AppOp ⊕ D₂.AppOp) → D₁.State × D₂.State → Prop :=
  fun e s =>
    match e.2.2 with
    | Sum.inl o => P₁ (e.1, e.2.1, o) s.1
    | Sum.inr o => P₂ (e.1, e.2.1, o) s.2

theorem prodPred_inl (P₁ : Op D₁.AppOp → D₁.State → Prop)
    (P₂ : Op D₂.AppOp → D₂.State → Prop) (e : Op D₁.AppOp)
    (s : D₁.State × D₂.State) :
    prodPred P₁ P₂ (inlOp e) s ↔ P₁ e s.1 := Iff.rfl

theorem prodPred_inr (P₁ : Op D₁.AppOp → D₁.State → Prop)
    (P₂ : Op D₂.AppOp → D₂.State → Prop) (e : Op D₂.AppOp)
    (s : D₁.State × D₂.State) :
    prodPred P₁ P₂ (inrOp e) s ↔ P₂ e s.2 := Iff.rfl

/-- **`GenHonest` lifts componentwise** (the free (⇐) direction): if each
component's honesty holds at its projection, the product is honest for the
componentwise predicate. Key identity:
`past₁(e) = (past⊗(ι₁ e))↾₁` (`vis`/`events` of the projection are
restrictions), so `π₁` of a product enumeration of the past enumerates the
component past, and `applySeq_prod` reads the component fold off the product
fold.

(The (⇒) direction needs enumerability of the opposite side's past; it is in
`Product_Safety.lean`.) -/
theorem genHonest_prod {P₁ : Op D₁.AppOp → D₁.State → Prop}
    {P₂ : Op D₂.AppOp → D₂.State → Prop} {C : Configuration (prodSig D₁ D₂)}
    (h₁ : GenHonest D₁ P₁ (projConf₁ C)) (h₂ : GenHonest D₂ P₂ (projConf₂ C)) :
    GenHonest (prodSig D₁ D₂) (prodPred P₁ P₂) C := by
  intro e he π hπ
  rcases op_sum_cases e with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · show P₁ a (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init π).1
    rw [applySeq_prod]
    refine h₁ a (mem_projConf₁_events.mpr he) (projList₁ π) ?_
    have hres : evRes₁ {e' ∈ C.events | C.vis e' (inlOp a)}
        = {e' ∈ (projConf₁ C).events | (projConf₁ C).vis e' a} :=
      Set.ext fun x => and_congr mem_projConf₁_events.symm Iff.rfl
    rw [← hres]
    exact listPermOf_projList₁ hπ
  · show P₂ b (applySeq (prodSig D₁ D₂).toCRDTSig (prodSig D₁ D₂).init π).2
    rw [applySeq_prod]
    refine h₂ b (mem_projConf₂_events.mpr he) (projList₂ π) ?_
    have hres : evRes₂ {e' ∈ C.events | C.vis e' (inrOp b)}
        = {e' ∈ (projConf₂ C).events | (projConf₂ C).vis e' b} :=
      Set.ext fun x => and_congr mem_projConf₂_events.symm Iff.rfl
    rw [← hres]
    exact listPermOf_projList₂ hπ

/-! ## The composite convenience theorem -/

/-- The product contract `H⊗`: component configuration-contracts precomposed
with the core projections. Contracts thread through the gluing untouched:
nothing in the join reads their content. -/
def prodContract (H₁ : Sal.Emulation.Configuration D₁.toCRDTSig → Prop)
    (H₂ : Sal.Emulation.Configuration D₂.toCRDTSig → Prop) :
    Configuration (prodSig D₁ D₂) → Prop :=
  fun C => H₁ (projCore₁ (Configuration.core C)) ∧ H₂ (projCore₂ (Configuration.core C))

/-- **The composite metatheorem**: per-version RA-linearizability of the
product at every `H⊗`-honestly reachable configuration, from the component
joins-under-contracts. This is `ra_linearizable3_of_honest_reach`
instantiated with the join gluing; the component certificates are consumed at
the *projections* of product-reachable cores, which is exactly why they must
be configuration-level (`JoinLemma3At` under a configuration predicate), not
reachability-indexed. -/
theorem prod_ra_linearizable3_of_honest_reach
    {H₁ : Sal.Emulation.Configuration D₁.toCRDTSig → Prop}
    {H₂ : Sal.Emulation.Configuration D₂.toCRDTSig → Prop}
    {hInit : (prodSig D₁ D₂).Inv (prodSig D₁ D₂).init}
    (hJoin₁ : ∀ Cb : Sal.Emulation.Configuration D₁.toCRDTSig,
      H₁ Cb → JoinLemma3At D₁ Cb)
    (hJoin₂ : ∀ Cb : Sal.Emulation.Configuration D₂.toCRDTSig,
      H₂ Cb → JoinLemma3At D₂ Cb)
    {C : Configuration (prodSig D₁ D₂)}
    (hReach : HonestReach (prodSig D₁ D₂) (prodContract H₁ H₂) hInit C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reach
    (fun _C' hH => joinLemma3At_prod (hJoin₁ _ hH.1) (hJoin₂ _ hH.2)) hReach

/-! ## Axiom audit -/

#print axioms canonical_glue
#print axioms joinLemma3At_prod
#print axioms joinLemma3FAt_prod
#print axioms updateVCs_prod
#print axioms genHonest_prod
#print axioms prod_ra_linearizable3_of_honest_reach

end Sal.ConditionedMRDTs
