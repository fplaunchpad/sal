import Sal.MRDTs.Metatheory.Correctness

/-! # Binary products of plain MRDT signatures -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

variable {A₁ A₂ : Type}

def inlOp (e : Op A₁) : Op (A₁ ⊕ A₂) := (e.1, e.2.1, Sum.inl e.2.2)
def inrOp (e : Op A₂) : Op (A₁ ⊕ A₂) := (e.1, e.2.1, Sum.inr e.2.2)

def oplOp (x : Op (A₁ ⊕ A₂)) : Option (Op A₁) :=
  match x.2.2 with
  | .inl a => some (x.1, x.2.1, a)
  | .inr _ => none

def oprOp (x : Op (A₁ ⊕ A₂)) : Option (Op A₂) :=
  match x.2.2 with
  | .inl _ => none
  | .inr b => some (x.1, x.2.1, b)

def projList₁ (ρ : List (Op (A₁ ⊕ A₂))) : List (Op A₁) := ρ.filterMap oplOp
def projList₂ (ρ : List (Op (A₁ ⊕ A₂))) : List (Op A₂) := ρ.filterMap oprOp

def evRes₁ (ev : Set (Op (A₁ ⊕ A₂))) : Set (Op A₁) := {e | inlOp e ∈ ev}
def evRes₂ (ev : Set (Op (A₁ ⊕ A₂))) : Set (Op A₂) := {e | inrOp e ∈ ev}

theorem inlOp_injective : Function.Injective (inlOp (A₁ := A₁) (A₂ := A₂)) := by
  intro a b h
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp only [inlOp, Prod.mk.injEq, Sum.inl.injEq] at h
  simp [h.1, h.2.1, h.2.2]

theorem inrOp_injective : Function.Injective (inrOp (A₁ := A₁) (A₂ := A₂)) := by
  intro a b h
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp only [inrOp, Prod.mk.injEq, Sum.inr.injEq] at h
  simp [h.1, h.2.1, h.2.2]

theorem inlOp_ne_inrOp (a : Op A₁) (b : Op A₂) : inlOp a ≠ inrOp b := by
  intro h
  have h' := congrArg (fun e : Op (A₁ ⊕ A₂) => e.2.2) h
  cases h'

theorem op_sum_cases (x : Op (A₁ ⊕ A₂)) :
    (∃ a : Op A₁, x = inlOp a) ∨ (∃ b : Op A₂, x = inrOp b) := by
  rcases x with ⟨t, r, x | x⟩
  · exact Or.inl ⟨(t, r, x), rfl⟩
  · exact Or.inr ⟨(t, r, x), rfl⟩

@[simp] theorem oplOp_inlOp (a : Op A₁) :
    oplOp (A₂ := A₂) (inlOp a) = some a := by rcases a with ⟨t, r, a⟩; rfl
@[simp] theorem oplOp_inrOp (b : Op A₂) :
    oplOp (A₁ := A₁) (inrOp b) = none := by rcases b with ⟨t, r, b⟩; rfl
@[simp] theorem oprOp_inlOp (a : Op A₁) :
    oprOp (A₂ := A₂) (inlOp a) = none := by rcases a with ⟨t, r, a⟩; rfl
@[simp] theorem oprOp_inrOp (b : Op A₂) :
    oprOp (A₁ := A₁) (inrOp b) = some b := by rcases b with ⟨t, r, b⟩; rfl

theorem oplOp_eq_some {x : Op (A₁ ⊕ A₂)} {a : Op A₁} :
    oplOp x = some a ↔ x = inlOp a := by
  rcases x with ⟨t, r, x | x⟩
  · rcases a with ⟨t', r', a⟩
    simp [oplOp, inlOp]
  · simp [oplOp, inlOp]

theorem oprOp_eq_some {x : Op (A₁ ⊕ A₂)} {b : Op A₂} :
    oprOp x = some b ↔ x = inrOp b := by
  rcases x with ⟨t, r, x | x⟩
  · simp [oprOp, inrOp]
  · rcases b with ⟨t', r', b⟩
    simp [oprOp, inrOp]

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

@[simp] theorem projList₁_append (ρ σ : List (Op (A₁ ⊕ A₂))) :
    projList₁ (ρ ++ σ) = projList₁ ρ ++ projList₁ σ := by
  simp [projList₁]

@[simp] theorem projList₂_append (ρ σ : List (Op (A₁ ⊕ A₂))) :
    projList₂ (ρ ++ σ) = projList₂ ρ ++ projList₂ σ := by
  simp [projList₂]

@[simp] theorem projList₁_map_inlOp (ρ : List (Op A₁)) :
    projList₁ (ρ.map (inlOp (A₂ := A₂))) = ρ := by
  induction ρ <;> simp_all [projList₁]

@[simp] theorem projList₁_map_inrOp (ρ : List (Op A₂)) :
    projList₁ (ρ.map (inrOp (A₁ := A₁))) = [] := by
  induction ρ <;> simp_all [projList₁]

@[simp] theorem projList₂_map_inlOp (ρ : List (Op A₁)) :
    projList₂ (ρ.map (inlOp (A₂ := A₂))) = [] := by
  induction ρ <;> simp_all [projList₂]

@[simp] theorem projList₂_map_inrOp (ρ : List (Op A₂)) :
    projList₂ (ρ.map (inrOp (A₁ := A₁))) = ρ := by
  induction ρ <;> simp_all [projList₂]

@[simp] theorem evRes₁_inter (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₁ (ev₁ ∩ ev₂) = evRes₁ ev₁ ∩ evRes₁ ev₂ := rfl
@[simp] theorem evRes₂_inter (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₂ (ev₁ ∩ ev₂) = evRes₂ ev₁ ∩ evRes₂ ev₂ := rfl
@[simp] theorem evRes₁_union (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₁ (ev₁ ∪ ev₂) = evRes₁ ev₁ ∪ evRes₁ ev₂ := rfl
@[simp] theorem evRes₂_union (ev₁ ev₂ : Set (Op (A₁ ⊕ A₂))) :
    evRes₂ (ev₁ ∪ ev₂) = evRes₂ ev₁ ∪ evRes₂ ev₂ := rfl

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

theorem listPermOf_projList₁ {ρ : List (Op (A₁ ⊕ A₂))}
    {ev : Set (Op (A₁ ⊕ A₂))} (h : listPermOf ρ ev) :
    listPermOf (projList₁ ρ) (evRes₁ ev) := by
  constructor
  · exact nodup_projList₁ h.1
  · intro a
    rw [mem_projList₁]
    exact h.2 (inlOp a)

theorem listPermOf_projList₂ {ρ : List (Op (A₁ ⊕ A₂))}
    {ev : Set (Op (A₁ ⊕ A₂))} (h : listPermOf ρ ev) :
    listPermOf (projList₂ ρ) (evRes₂ ev) := by
  constructor
  · exact nodup_projList₂ h.1
  · intro b
    rw [mem_projList₂]
    exact h.2 (inrOp b)

/-- Component enumerations glue into an exact enumeration of the mixed event
set.  Cross-component timestamps remain distinct because the target set is
enumerated without duplication. -/
theorem listPermOf_glue {ev : Set (Op (A₁ ⊕ A₂))}
    {ρ₁ : List (Op A₁)} {ρ₂ : List (Op A₂)}
    (h₁ : listPermOf ρ₁ (evRes₁ ev))
    (h₂ : listPermOf ρ₂ (evRes₂ ev)) :
    listPermOf (ρ₁.map inlOp ++ ρ₂.map inrOp) ev := by
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

/-- Filtering a mixed history preserves every ordering constraint between
events of its left component. -/
theorem respects_projList₁_of {R : Op (A₁ ⊕ A₂) → Op (A₁ ⊕ A₂) → Prop}
    {R₁ : Op A₁ → Op A₁ → Prop} {ρ : List (Op (A₁ ⊕ A₂))}
    (rel : ∀ a b, R₁ a b → R (inlOp a) (inlOp b))
    (h : respects ρ R) : respects (projList₁ ρ) R₁ := by
  unfold respects at h ⊢
  unfold projList₁
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oplOp_eq_some] at hxa hyb
  subst x
  subst y
  exact fun hba => hxy (rel b a hba)

/-- Filtering a mixed history preserves every ordering constraint between
events of its right component. -/
theorem respects_projList₂_of {R : Op (A₁ ⊕ A₂) → Op (A₁ ⊕ A₂) → Prop}
    {R₂ : Op A₂ → Op A₂ → Prop} {ρ : List (Op (A₁ ⊕ A₂))}
    (rel : ∀ a b, R₂ a b → R (inrOp a) (inrOp b))
    (h : respects ρ R) : respects (projList₂ ρ) R₂ := by
  unfold respects at h ⊢
  unfold projList₂
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oprOp_eq_some] at hxa hyb
  subst x
  subst y
  exact fun hba => hxy (rel b a hba)

variable (D₁ D₂ : MRDTSig)

/-- Componentwise product. Generation and safety policies remain external. -/
def prodSig : MRDTSig where
  State := D₁.State × D₂.State
  dec_state := inferInstance
  init := (D₁.init, D₂.init)
  AppOp := D₁.AppOp ⊕ D₂.AppOp
  dec_op := inferInstance
  Query := D₁.Query ⊕ D₂.Query
  Value := D₁.Value ⊕ D₂.Value
  update s e :=
    match e.2.2 with
    | .inl o => (D₁.update s.1 (e.1, e.2.1, o), s.2)
    | .inr o => (s.1, D₂.update s.2 (e.1, e.2.1, o))
  merge a b := (D₁.merge a.1 b.1, D₂.merge a.2 b.2)
  query s q :=
    match q with
    | .inl q => .inl (D₁.query s.1 q)
    | .inr q => .inr (D₂.query s.2 q)
  mergeL l a b := (D₁.mergeL l.1 a.1 b.1, D₂.mergeL l.2 a.2 b.2)
  merge_init_slice a b := by
    simp only
    rw [D₁.merge_init_slice, D₂.merge_init_slice]

variable {D₁ D₂}

@[simp] theorem prodSig_update_inl (s : (prodSig D₁ D₂).State)
    (e : Op D₁.AppOp) :
    (prodSig D₁ D₂).update s (inlOp e) = (D₁.update s.1 e, s.2) := by
  rcases e with ⟨t, r, e⟩; rfl

@[simp] theorem prodSig_update_inr (s : (prodSig D₁ D₂).State)
    (e : Op D₂.AppOp) :
    (prodSig D₁ D₂).update s (inrOp e) = (s.1, D₂.update s.2 e) := by
  rcases e with ⟨t, r, e⟩; rfl

@[simp] theorem prodSig_mergeL (l a b : (prodSig D₁ D₂).State) :
    (prodSig D₁ D₂).mergeL l a b =
      (D₁.mergeL l.1 a.1 b.1, D₂.mergeL l.2 a.2 b.2) := rfl

theorem commutes_prod_cross (a : Op D₁.AppOp) (b : Op D₂.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp a) (inrOp b) := by
  intro s
  simp

theorem commutes_prod_cross' (b : Op D₂.AppOp) (a : Op D₁.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp b) (inlOp a) := by
  intro s
  simp

theorem commutes_prod_inl_of {a b : Op D₁.AppOp}
    (h : D₁.toCRDTSig.commutes a b) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp a) (inlOp b) := by
  intro s
  exact Prod.ext (h s.1) rfl

theorem commutes_prod_inr_of {a b : Op D₂.AppOp}
    (h : D₂.toCRDTSig.commutes a b) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp a) (inrOp b) := by
  intro s
  exact Prod.ext rfl (h s.2)

theorem commutes_prod_inl_iff (a b : Op D₁.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inlOp a) (inlOp b) ↔
      D₁.toCRDTSig.commutes a b := by
  constructor
  · intro h s
    exact congrArg Prod.fst (h (s, D₂.init))
  · exact commutes_prod_inl_of

theorem commutes_prod_inr_iff (a b : Op D₂.AppOp) :
    (prodSig D₁ D₂).toCRDTSig.commutes (inrOp a) (inrOp b) ↔
      D₂.toCRDTSig.commutes a b := by
  constructor
  · intro h s
    exact congrArg Prod.snd (h (D₁.init, s))
  · exact commutes_prod_inr_of

theorem applySeq_prod (s : (prodSig D₁ D₂).State)
    (ρ : List (Op (D₁.AppOp ⊕ D₂.AppOp))) :
    applySeq (prodSig D₁ D₂).toCRDTSig s ρ =
      (applySeq D₁.toCRDTSig s.1 (projList₁ ρ),
       applySeq D₂.toCRDTSig s.2 (projList₂ ρ)) := by
  induction ρ generalizing s with
  | nil => rfl
  | cons e ρ ih =>
      rcases e with ⟨t, r, e | e⟩
      · exact ih ((D₁.update s.1 (t, r, e), s.2) : (prodSig D₁ D₂).State)
      · exact ih ((s.1, D₂.update s.2 (t, r, e)) : (prodSig D₁ D₂).State)

/-! ## Projection of canonical configurations -/

def projCore₁
    (C : Sal.MRDTs.Foundation.Configuration (prodSig D₁ D₂).toCRDTSig) :
    Sal.MRDTs.Foundation.Configuration D₁.toCRDTSig where
  N r := (C.N r).map Prod.fst
  L r := (C.L r).map evRes₁
  vis a b := C.vis (inlOp a) (inlOp b)
  dom_eq r := by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal h hL hb := by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct hL ha hL' hb hne := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inlOp_injective h)
  vis_total_same_replica hL ha hL' hb hne hrep := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inlOp_injective h)) hrep

def projCore₂
    (C : Sal.MRDTs.Foundation.Configuration (prodSig D₁ D₂).toCRDTSig) :
    Sal.MRDTs.Foundation.Configuration D₂.toCRDTSig where
  N r := (C.N r).map Prod.snd
  L r := (C.L r).map evRes₂
  vis a b := C.vis (inrOp a) (inrOp b)
  dom_eq r := by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal h hL hb := by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct hL ha hL' hb hne := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inrOp_injective h)
  vis_total_same_replica hL ha hL' hb hne hrep := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inrOp_injective h)) hrep

variable {C : Sal.MRDTs.Foundation.Configuration (prodSig D₁ D₂).toCRDTSig}

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

theorem loOn_prod_cross_lr {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a : Op D₁.AppOp) (b : Op D₂.AppOp) :
    ¬ loOn C ev (inlOp a) (inrOp b) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (commutes_prod_cross a b)
  · exact RcRes.noConfusion hrc

theorem loOn_prod_cross_rl {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (b : Op D₂.AppOp) (a : Op D₁.AppOp) :
    ¬ loOn C ev (inrOp b) (inlOp a) := by
  rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
  · exact hnc (commutes_prod_cross' b a)
  · exact RcRes.noConfusion hrc

theorem loOn_prod_inl_iff {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a b : Op D₁.AppOp) :
    loOn C ev (inlOp a) (inlOp b) ↔
      loOn (projCore₁ C) (evRes₁ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc (commutes_prod_inl_of hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inlOp e₃, h₃, hv₃,
        fun hc => hnc₃ ((commutes_prod_inl_iff b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact habs ⟨c, h₃, hv₃, fun hc => hnc₃ (commutes_prod_inl_of hc)⟩
      · exact hnc₃ (commutes_prod_cross b c)

theorem loOn_prod_inr_iff {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    (a b : Op D₂.AppOp) :
    loOn C ev (inrOp a) (inrOp b) ↔
      loOn (projCore₂ C) (evRes₂ ev) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc (commutes_prod_inr_of hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      exact habs ⟨inrOp e₃, h₃, hv₃,
        fun hc => hnc₃ ((commutes_prod_inr_iff b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, h₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact hnc₃ (commutes_prod_cross' b c)
      · exact habs ⟨c, h₃, hv₃, fun hc => hnc₃ (commutes_prod_inr_of hc)⟩

/-- Global arbitration on a product restricts exactly to global arbitration
on its left component. -/
theorem lo_prod_inl_iff (a b : Op D₁.AppOp) :
    Sal.MRDTs.Foundation.lo C (inlOp a) (inlOp b) ↔
      Sal.MRDTs.Foundation.lo (projCore₁ C) a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc (commutes_prod_inl_of hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, hv₃, hnc₃⟩
      exact habs ⟨inlOp e₃, hv₃,
        fun hc => hnc₃ ((commutes_prod_inl_iff b e₃).mp hc)⟩
  · rintro (⟨hv, hnc⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hv, fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)⟩
    · refine Or.inr ⟨hnv, hnv', hrc, ?_⟩
      rintro ⟨e₃, hv₃, hnc₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact habs ⟨c, hv₃, fun hc => hnc₃ (commutes_prod_inl_of hc)⟩
      · exact hnc₃ (commutes_prod_cross b c)

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
  subst x; subst y
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
  subst x; subst y
  exact fun hlo => hxy ((loOn_prod_inr_iff b a).mpr hlo)

theorem isCanonicalState_proj₁ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {s : (prodSig D₁ D₂).State} (h : IsCanonicalState C ev s) :
    IsCanonicalState (projCore₁ C) (evRes₁ ev) s.1 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨projList₁ ρ, listPermOf_projList₁ hp, respects_projList₁ hr,
    congrArg Prod.fst ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)⟩

theorem isCanonicalState_proj₂ {ev : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {s : (prodSig D₁ D₂).State} (h : IsCanonicalState C ev s) :
    IsCanonicalState (projCore₂ C) (evRes₂ ev) s.2 := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨projList₂ ρ, listPermOf_projList₂ hp, respects_projList₂ hr,
    congrArg Prod.snd ((applySeq_prod (prodSig D₁ D₂).init ρ).symm.trans hf)⟩

theorem canonical_glue {U : Set (Op (D₁.AppOp ⊕ D₂.AppOp))}
    {m₁ : D₁.State} {m₂ : D₂.State}
    (h₁ : IsCanonicalState (projCore₁ C) (evRes₁ U) m₁)
    (h₂ : IsCanonicalState (projCore₂ C) (evRes₂ U) m₂) :
    IsCanonicalState C U ((m₁, m₂) : (prodSig D₁ D₂).State) := by
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  refine ⟨ρ₁.map inlOp ++ ρ₂.map inrOp, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp₁.1.map inlOp_injective, hp₂.1.map inrOp_injective, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact inlOp_ne_inrOp a b
  · intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (hp₁.2 a).mp ha
      · exact (hp₂.2 b).mp hb
    · intro hx
      rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (hp₁.2 a).mpr hx, rfl⟩
      · exact Or.inr ⟨b, (hp₂.2 b).mpr hx, rfl⟩
  · unfold respects
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
  · rw [applySeq_prod, projList₁_append, projList₂_append,
      projList₁_map_inlOp, projList₁_map_inrOp,
      projList₂_map_inlOp, projList₂_map_inrOp, List.append_nil]
    show (applySeq D₁.toCRDTSig D₁.init ρ₁,
      applySeq D₂.toCRDTSig D₂.init ρ₂) = (m₁, m₂)
    rw [hf₁, hf₂]

/-- Componentwise Join composes for the plain product signature. -/
theorem joinLemma3At_prod
    (h₁ : JoinLemma3At D₁ (projCore₁ C))
    (h₂ : JoinLemma3At D₂ (projCore₂ C)) :
    JoinLemma3At (prodSig D₁ D₂) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ hc₁ hc₂
  have hJ₁ := h₁ (evRes₁ ev₁) (evRes₁ ev₂) s₀.1 s₁.1 s₂.1
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inlOp a) hv)
    (fun a ha => mem_projCore₁_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₁_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb =>
      hcl₁ (inlOp a) (inlOp b) hv
        (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (fun a b hv hnc hb =>
      hcl₂ (inlOp a) (inlOp b) hv
        (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (isCanonicalState_proj₁ h₀)
    (isCanonicalState_proj₁ hc₁)
    (isCanonicalState_proj₁ hc₂)
  have hJ₂ := h₂ (evRes₂ ev₁) (evRes₂ ev₂) s₀.2 s₁.2 s₂.2
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inrOp a) hv)
    (fun a ha => mem_projCore₂_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projCore₂_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb =>
      hcl₁ (inrOp a) (inrOp b) hv
        (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (fun a b hv hnc hb =>
      hcl₂ (inrOp a) (inrOp b) hv
        (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (isCanonicalState_proj₂ h₀)
    (isCanonicalState_proj₂ hc₁)
    (isCanonicalState_proj₂ hc₂)
  exact canonical_glue hJ₁ hJ₂

/-! ## Projection of operational configurations -/

def projConf₁ (C : Configuration (prodSig D₁ D₂)) : Configuration D₁ where
  N r := (C.N r).map Prod.fst
  L r := (C.L r).map evRes₁
  vis a b := C.vis (inlOp a) (inlOp b)
  dom_eq r := by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal h hL hb := by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct hL ha hL' hb hne := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inlOp_injective h)
  causal_mono h := C.causal_mono h
  vis_total_same_replica hL ha hL' hb hne hrep := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inlOp_injective h)) hrep
  ver v := (C.ver v).map fun p => (p.1.1, evRes₁ p.2)
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by rw [C.ver_init]; rfl
  head_coherent r v hv := by
    obtain ⟨h1, h2⟩ := C.head_coherent r v hv
    constructor
    · rw [← h1]
      cases C.ver v <;> rfl
    · rw [← h2]
      cases C.ver v <;> rfl
  lca_events hlca hv₁ hv₂ hvT := by
    obtain ⟨p₁, hp₁, hpe₁⟩ := Option.map_eq_some_iff.mp hv₁
    obtain ⟨p₂, hp₂, hpe₂⟩ := Option.map_eq_some_iff.mp hv₂
    obtain ⟨pT, hpT, hpeT⟩ := Option.map_eq_some_iff.mp hvT
    have h := C.lca_events hlca (by rw [hp₁]) (by rw [hp₂]) (by rw [hpT])
    have hT : evRes₁ pT.2 = _ := congrArg Prod.snd hpeT
    have h1 : evRes₁ p₁.2 = _ := congrArg Prod.snd hpe₁
    have h2 : evRes₁ p₂.2 = _ := congrArg Prod.snd hpe₂
    simp only at hT h1 h2
    rw [← hT, ← h1, ← h2, h]
    rfl

def projConf₂ (C : Configuration (prodSig D₁ D₂)) : Configuration D₂ where
  N r := (C.N r).map Prod.snd
  L r := (C.L r).map evRes₂
  vis a b := C.vis (inrOp a) (inrOp b)
  dom_eq r := by
    rw [Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact C.dom_eq r
  vis_src h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_tgt h := by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩
  vis_causal h hL hb := by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct hL ha hL' hb hne := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inrOp_injective h)
  causal_mono h := C.causal_mono h
  vis_total_same_replica hL ha hL' hb hne hrep := by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inrOp_injective h)) hrep
  ver v := (C.ver v).map fun p => (p.1.2, evRes₂ p.2)
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by rw [C.ver_init]; rfl
  head_coherent r v hv := by
    obtain ⟨h1, h2⟩ := C.head_coherent r v hv
    constructor
    · rw [← h1]
      cases C.ver v <;> rfl
    · rw [← h2]
      cases C.ver v <;> rfl
  lca_events hlca hv₁ hv₂ hvT := by
    obtain ⟨p₁, hp₁, hpe₁⟩ := Option.map_eq_some_iff.mp hv₁
    obtain ⟨p₂, hp₂, hpe₂⟩ := Option.map_eq_some_iff.mp hv₂
    obtain ⟨pT, hpT, hpeT⟩ := Option.map_eq_some_iff.mp hvT
    have h := C.lca_events hlca (by rw [hp₁]) (by rw [hp₂]) (by rw [hpT])
    have hT : evRes₂ pT.2 = _ := congrArg Prod.snd hpeT
    have h1 : evRes₂ p₁.2 = _ := congrArg Prod.snd hpe₁
    have h2 : evRes₂ p₂.2 = _ := congrArg Prod.snd hpe₂
    simp only at hT h1 h2
    rw [← hT, ← h1, ← h2, h]
    rfl

@[simp] theorem projConf₁_core {CT : Configuration (prodSig D₁ D₂)} :
    Configuration.core (projConf₁ CT) = projCore₁ (Configuration.core CT) := rfl

@[simp] theorem projConf₂_core {CT : Configuration (prodSig D₁ D₂)} :
    Configuration.core (projConf₂ CT) = projCore₂ (Configuration.core CT) := rfl

theorem mem_projConf₁_events {CT : Configuration (prodSig D₁ D₂)}
    {a : Op D₁.AppOp} : a ∈ (projConf₁ CT).events ↔ inlOp a ∈ CT.events := by
  constructor
  · rintro ⟨r, s₁, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₁ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

theorem mem_projConf₂_events {CT : Configuration (prodSig D₁ D₂)}
    {b : Op D₂.AppOp} : b ∈ (projConf₂ CT).events ↔ inrOp b ∈ CT.events := by
  constructor
  · rintro ⟨r, s₂, hL, hs⟩
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact ⟨r, s, hLs, hs⟩
  · rintro ⟨r, s, hL, hs⟩
    exact ⟨r, evRes₂ s, Option.map_eq_some_iff.mpr ⟨s, hL, rfl⟩, hs⟩

/-- The operational invariant of a product configuration projects to its
left component. -/
theorem GoodConfig3.proj₁ {CT : Configuration (prodSig D₁ D₂)}
    (h : GoodConfig3 CT) : GoodConfig3 (projConf₁ CT) where
  canonical := by
    intro v s E hv
    change (CT.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hs : p.1.1 = s := congrArg Prod.fst hpeq
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst s
    subst E
    exact isCanonicalState_proj₁ (h.canonical v p.1 p.2 hp)
  vis_trans := fun hab hbc => h.vis_trans hab hbc
  vis_irrefl := fun a => h.vis_irrefl (inlOp a)
  ver_events_sub := by
    intro v s E hv a ha
    rw [mem_projConf₁_events]
    change (CT.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact h.ver_events_sub v p.1 p.2 hp (inlOp a) ha
  ver_causal := by
    intro v s E hv a b hab hb
    change (CT.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact h.ver_causal v p.1 p.2 hp (inlOp a) (inlOp b) hab hb

/-- The operational invariant of a product configuration projects to its
right component. -/
theorem GoodConfig3.proj₂ {CT : Configuration (prodSig D₁ D₂)}
    (h : GoodConfig3 CT) : GoodConfig3 (projConf₂ CT) where
  canonical := by
    intro v s E hv
    change (CT.ver v).map (fun p => (p.1.2, evRes₂ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hs : p.1.2 = s := congrArg Prod.fst hpeq
    have hE : evRes₂ p.2 = E := congrArg Prod.snd hpeq
    subst s
    subst E
    exact isCanonicalState_proj₂ (h.canonical v p.1 p.2 hp)
  vis_trans := fun hab hbc => h.vis_trans hab hbc
  vis_irrefl := fun a => h.vis_irrefl (inrOp a)
  ver_events_sub := by
    intro v s E hv a ha
    rw [mem_projConf₂_events]
    change (CT.ver v).map (fun p => (p.1.2, evRes₂ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₂ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact h.ver_events_sub v p.1 p.2 hp (inrOp a) ha
  ver_causal := by
    intro v s E hv a b hab hb
    change (CT.ver v).map (fun p => (p.1.2, evRes₂ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₂ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact h.ver_causal v p.1 p.2 hp (inrOp a) (inrOp b) hab hb

#print axioms joinLemma3At_prod

end Sal.MRDTs
