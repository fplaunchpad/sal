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
  rc x y :=
    match x.2.2, y.2.2 with
    | .inl a, .inl b => D₁.rc (x.1, x.2.1, a) (y.1, y.2.1, b)
    | .inr a, .inr b => D₂.rc (x.1, x.2.1, a) (y.1, y.2.1, b)
    | .inl _, .inr _ | .inr _, .inl _ => RcRes.Either
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

end Sal.MRDTs
