import Sal.MRDTs.Paper1.Automation.GenericTaggedPrefixCodes

/-! Compositional decoding laws for finite words. These contracts concern
arbitrary token and symbol types, independently of replicated datatypes. -/
namespace Sal.MRDTs.Paper1.Automation.PrefixCodes
variable {Token Symbol Out Other : Type}

theorem Code.cancel {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) {a b : Token} (ha : valid a) (hb : valid b)
    {u v : List Symbol} (eq : enc a ++ u = enc b ++ v) : a = b ∧ u = v := by
  have same : a = b := by
    by_contra ne
    have pa : enc a <+: enc a ++ u := List.prefix_append _ _
    have pb : enc b <+: enc a ++ u := by rw [eq]; exact List.prefix_append _ _
    rcases Nat.le_total (enc a).length (enc b).length with h | h
    · exact C.prefixFree a b ha hb ne (List.prefix_of_prefix_length_le pa pb h)
    · exact C.prefixFree b a hb ha (Ne.symm ne) (List.prefix_of_prefix_length_le pb pa h)
  subst b
  exact ⟨rfl, List.append_cancel_left eq⟩

def Code.map {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) (f : Symbol → Out) (inj : Function.Injective f) :
    Code valid (fun a => (enc a).map f) where
  nonempty := by intro a ha; simpa using C.nonempty a ha
  prefixFree := by
    intro a b ha hb ne pref
    exact C.prefixFree a b ha hb ne (map_prefix_reflect f inj pref)

def Code.fixedWidth (valid : Token → Prop) (enc : Token → List Symbol) (width : Nat)
    (positive : 0 < width) (length : ∀ a, valid a → (enc a).length = width)
    (inj : ∀ a b, valid a → valid b → enc a = enc b → a = b) : Code valid enc where
  nonempty := by intro a ha empty; have := length a ha; simp [empty] at this; omega
  prefixFree := by
    intro a b ha hb ne pref
    exact ne (inj a b ha hb (pref.eq_of_length ((length a ha).trans (length b hb).symm)))

theorem encode_append (enc : Token → List Symbol) (xs ys : List Token) :
    encode enc (xs ++ ys) = encode enc xs ++ encode enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih, List.append_assoc]

/-- Prefix reflection needs complete, nonempty codewords in both token lists;
the unmatched suffix may end at any symbol boundary. -/
theorem Code.encode_prefix_reflect {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) : ∀ (xs ys : List Token),
    (∀ x ∈ xs, valid x) → (∀ y ∈ ys, valid y) →
    encode enc xs <+: encode enc ys → xs <+: ys
  | [], _, _, _, _ => List.nil_prefix
  | x :: xs, [], hx, _, h => by
    have empty : enc x = [] := by
      have := h.length_le
      simp [encode] at this
      exact this.1
    exact (C.nonempty x (hx x List.mem_cons_self) empty).elim
  | x :: xs, y :: ys, hx, hy, h => by
    obtain ⟨tail, eq⟩ := h
    simp only [encode, List.append_assoc] at eq
    obtain ⟨same, rest⟩ := C.cancel (hx x List.mem_cons_self) (hy y List.mem_cons_self) eq
    subst y
    exact List.cons_prefix_cons.mpr ⟨rfl,
      C.encode_prefix_reflect xs ys
        (fun t ht => hx t (List.mem_cons_of_mem _ ht))
        (fun t ht => hy t (List.mem_cons_of_mem _ ht)) ⟨tail, rest⟩⟩

/-- A prefix-free language stays prefix-free under a prefix-free symbol code. -/
def Code.words {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) (wordValid : List Token → Prop)
    (symbols : ∀ xs, wordValid xs → ∀ x ∈ xs, valid x)
    (nonempty : ∀ xs, wordValid xs → xs ≠ [])
    (free : ∀ xs ys, wordValid xs → wordValid ys → xs ≠ ys → ¬ xs <+: ys) :
    Code wordValid (encode enc) where
  nonempty := by
    intro xs hx eq
    have pref : xs <+: [] := C.encode_prefix_reflect xs [] (symbols xs hx) (by simp)
      (by simpa [eq, encode])
    exact nonempty xs hx (List.prefix_nil.mp pref)
  prefixFree := by
    intro xs ys hx hy ne pref
    exact free xs ys hx hy ne (C.encode_prefix_reflect xs ys (symbols xs hx) (symbols ys hy) pref)

def Code.product {va : Token → Prop} {ea : Token → List Symbol}
    {vb : Other → Prop} {eb : Other → List Symbol}
    (A : Code va ea) (B : Code vb eb) :
    Code (fun p : Token × Other => va p.1 ∧ vb p.2) (fun p => ea p.1 ++ eb p.2) where
  nonempty := by
    intro p hp empty
    have parts : ea p.1 = [] ∧ eb p.2 = [] := by simpa using empty
    exact A.nonempty p.1 hp.1 parts.1
  prefixFree := by
    rintro ⟨a,b⟩ ⟨c,d⟩ ha hb ne ⟨rest, eq⟩
    simp only [List.append_assoc] at eq
    obtain ⟨same, tail⟩ := A.cancel ha.1 hb.1 eq
    change a = c at same
    subst c
    have equal : b = d := by
      by_contra different
      exact B.prefixFree b d ha.2 hb.2 different ⟨rest, tail⟩
    exact ne (by rw [equal])

/-- Predicate lifting through concatenated codewords. -/
theorem encode_all (enc : Token → List Symbol) (P : Symbol → Prop)
    (xs : List Token) (words : ∀ x ∈ xs, ∀ s ∈ enc x, P s) :
    ∀ s ∈ encode enc xs, P s := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact words x List.mem_cons_self s hs
    · exact ih (fun t ht => words t (List.mem_cons_of_mem _ ht)) s hs

def Code.relabel {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) (f : Other → Token) (newValid : Other → Prop)
    (preserves : ∀ a, newValid a → valid (f a))
    (inj : ∀ a b, newValid a → newValid b → f a = f b → a = b) :
    Code newValid (fun a => enc (f a)) where
  nonempty := fun a ha => C.nonempty (f a) (preserves a ha)
  prefixFree := by
    intro a b ha hb ne pref
    exact C.prefixFree (f a) (f b) (preserves a ha) (preserves b hb)
      (fun eq => ne (inj a b ha hb eq)) pref

/-- Disjoint output alphabets distinguish the branches before decoding any
tokens. Each branch may itself be a product or variable-length word code. -/
def Code.sum {va : Token → Prop} {ea : Token → List Symbol}
    {vb : Other → Prop} {eb : Other → List Symbol}
    (A : Code va ea) (B : Code vb eb)
    (separate : ∀ a b, va a → vb b → ∀ x ∈ ea a, ∀ y ∈ eb b, x ≠ y) :
    Code (Sum.elim va vb) (Sum.elim ea eb) where
  nonempty := by intro e he; cases e with
    | inl a => exact A.nonempty a he
    | inr b => exact B.nonempty b he
  prefixFree := by
    intro e f he hf ne pref
    have cross : ∀ a b, va a → vb b → ¬ ea a <+: eb b ∧ ¬ eb b <+: ea a := by
      intro a b ha hb
      cases hx : ea a with
      | nil => exact (A.nonempty a ha hx).elim
      | cons x xs =>
        cases hy : eb b with
        | nil => exact (B.nonempty b hb hy).elim
        | cons y ys =>
          have hne := separate a b ha hb x (by rw [hx]; exact List.mem_cons_self)
            y (by rw [hy]; exact List.mem_cons_self)
          constructor
          · intro h; exact hne (List.cons_prefix_cons.mp h).1
          · intro h; exact hne (List.cons_prefix_cons.mp h).1.symm
    cases e with
    | inl a => cases f with
      | inl b => exact A.prefixFree a b he hf (fun eq => ne (by rw [eq])) pref
      | inr b => exact (cross a b he hf).1 pref
    | inr a => cases f with
      | inl b => exact (cross b a hf he).2 pref
      | inr b => exact B.prefixFree a b he hf (fun eq => ne (by rw [eq])) pref

end Sal.MRDTs.Paper1.Automation.PrefixCodes
