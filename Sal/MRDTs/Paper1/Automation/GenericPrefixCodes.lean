import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex

namespace Sal.MRDTs.Paper1.Automation.PrefixCodes
variable {Token Symbol : Type}

/-- The decoding contract is independent of the alphabet and of how tokens
are issued. Nonempty words exclude the empty-token ambiguity. -/
structure Code (valid : Token → Prop) (enc : Token → List Symbol) : Prop where
  nonempty : ∀ t, valid t → enc t ≠ []
  prefixFree : ∀ a b, valid a → valid b → a ≠ b → ¬ enc a <+: enc b

/-- A prefix-free code has no empty word when every valid token has a
competing valid token. This separates the generic decoding law from the
application's choice of token domain. -/
theorem nonempty_of_prefixFree (valid : Token → Prop) (enc : Token → List Symbol)
    (prefixFree : ∀ a b, valid a → valid b → a ≠ b → ¬ enc a <+: enc b)
    (competitor : ∀ a, valid a → ∃ b, valid b ∧ a ≠ b) :
    ∀ a, valid a → enc a ≠ [] := by
  intro a ha empty
  obtain ⟨b, hb, ne⟩ := competitor a ha
  apply prefixFree a b ha hb ne
  rw [empty]
  exact List.nil_prefix

def encode (enc : Token → List Symbol) : List Token → List Symbol
  | [] => []
  | t :: ts => enc t ++ encode enc ts

theorem encode_eq (enc : Token → List Symbol) (f : List Token → List Symbol)
    (nil : f [] = []) (cons : ∀ t ts, f (t :: ts) = enc t ++ f ts)
    (ts : List Token) : f ts = encode enc ts := by
  induction ts with
  | nil => exact nil
  | cons t ts ih => rw [cons, encode, ih]

theorem encode_injective {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) : ∀ (xs ys : List Token),
    (∀ t ∈ xs, valid t) → (∀ t ∈ ys, valid t) →
    encode enc xs = encode enc ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hy, eq => by
    have empty : enc y = [] := by
      cases he : enc y with
      | nil => rfl
      | cons s ss => simp [encode, he] at eq
    exact False.elim (C.nonempty y (hy y List.mem_cons_self) empty)
  | x :: xs, [], hx, _, eq => by
    have empty : enc x = [] := by
      cases he : enc x with
      | nil => rfl
      | cons s ss => simp [encode, he] at eq
    exact False.elim (C.nonempty x (hx x List.mem_cons_self) empty)
  | x :: xs, y :: ys, hx, hy, eq => by
    simp only [encode] at eq
    have heads : x = y := by
      by_contra ne
      have px : enc x <+: enc x ++ encode enc xs := List.prefix_append _ _
      have py : enc y <+: enc x ++ encode enc xs := by rw [eq]; exact List.prefix_append _ _
      rcases Nat.le_total (enc x).length (enc y).length with le | le
      · exact C.prefixFree x y (hx x List.mem_cons_self) (hy y List.mem_cons_self) ne
          (List.prefix_of_prefix_length_le px py le)
      · exact C.prefixFree y x (hy y List.mem_cons_self) (hx x List.mem_cons_self) (Ne.symm ne)
          (List.prefix_of_prefix_length_le py px le)
    subst y
    have tails := List.append_cancel_left eq
    rw [encode_injective C xs ys
      (fun t ht => hx t (List.mem_cons_of_mem _ ht))
      (fun t ht => hy t (List.mem_cons_of_mem _ ht)) tails]

/-- Adding a fixed terminator preserves injectivity of a symbol map. Its
freshness is needed for prefix reflection, but equality only needs cancellation. -/
theorem map_suffix_injective (f : Token → Symbol) (injective : Function.Injective f)
    (suffix : List Symbol) : Function.Injective (fun xs : List Token => xs.map f ++ suffix) := by
  intro xs ys eq
  apply List.map_injective_iff.mpr injective
  exact List.append_inj_left' eq (by simp)

/-- Unary delimiter encoding works over every alphabet. -/
def delimiter (symbol stop : Symbol) (n : Nat) : List Symbol :=
  List.replicate n symbol ++ [stop]

theorem delimiter_mono (R : Symbol → Symbol → Prop) (symbol stop : Symbol)
    (ordered : R stop symbol) {d e : Nat} (h : d < e) :
    List.Lex R (delimiter symbol stop d) (delimiter symbol stop e) := by
  induction d generalizing e with
  | zero =>
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos h).symm⟩
    simpa [delimiter, List.replicate_succ] using List.Lex.rel ordered
  | succ d ih =>
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 :=
      ⟨e - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)).symm⟩
    simpa [delimiter, List.replicate_succ] using List.Lex.cons (ih (Nat.lt_of_succ_lt_succ h))

theorem delimiter_prefixFree (symbol stop : Symbol) (distinct : symbol ≠ stop)
    {d e : Nat} (ne : d ≠ e) : ¬ delimiter symbol stop d <+: delimiter symbol stop e := by
  induction d generalizing e with
  | zero =>
    cases e with
    | zero => exact False.elim (ne rfl)
    | succ e =>
      intro h
      change stop :: [] <+: symbol :: (List.replicate e symbol ++ [stop]) at h
      exact distinct (List.cons_prefix_cons.mp h).1.symm
  | succ d ih =>
    cases e with
    | zero =>
      intro h
      change symbol :: (List.replicate d symbol ++ [stop]) <+: stop :: [] at h
      exact distinct (List.cons_prefix_cons.mp h).1
    | succ e =>
      intro h
      change symbol :: (List.replicate d symbol ++ [stop]) <+: symbol :: (List.replicate e symbol ++ [stop]) at h
      have tails := (List.cons_prefix_cons.mp h).2
      exact ih (fun eq => ne (by rw [eq])) tails

end Sal.MRDTs.Paper1.Automation.PrefixCodes
