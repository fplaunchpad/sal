import Sal.MRDTs.Paper1.Automation.GenericSortedLists
import Mathlib.Data.List.Lex
import Mathlib.Tactic

/-! Derive strict ordering laws from the recursive equations of a
lexicographic comparator, independently of records and their payloads. -/
namespace Sal.MRDTs.Paper1.Automation.OrderedLists

variable {A R : Type} [LinearOrder A]

theorem comparator_lex (cmp : List A → List A → Bool)
    (nil : cmp [] [] = false)
    (left : ∀ a as, cmp [] (a :: as) = true)
    (right : ∀ a as, cmp (a :: as) [] = false)
    (cons : ∀ a as b bs, cmp (a :: as) (b :: bs) =
      if a < b then true else if b < a then false else cmp as bs) :
    ∀ xs ys, cmp xs ys = true ↔ List.Lex (· < ·) xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys; cases ys with
    | nil => simp [nil]
    | cons a as => simp [left, List.Lex.nil]
  | cons a as ih =>
    intro ys; cases ys with
    | nil => simp [right]
    | cons b bs =>
      rw [cons]
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h, List.Lex.rel h]
      · simp [ih, List.lex_cons_iff]
      · simp only [not_lt_of_gt h, ↓reduceIte, h, Bool.false_eq_true, false_iff]
        intro lex
        cases lex with
        | rel hab => exact (not_lt_of_gt h) hab
        | cons _ => exact (lt_irrefl _) h

/-- Once the comparator equations hold, every key projection receives the
four laws required by canonical sorted insertion and merge. -/
def orderOfComparator (cmp : List A → List A → Bool)
    (nil : cmp [] [] = false)
    (left : ∀ a as, cmp [] (a :: as) = true)
    (right : ∀ a as, cmp (a :: as) [] = false)
    (cons : ∀ a as b bs, cmp (a :: as) (b :: bs) =
      if a < b then true else if b < a then false else cmp as bs)
    (key : R → List A) : Order key (fun a b => cmp (key a) (key b)) where
  trans := by
    intro a b c hab hbc
    apply (comparator_lex cmp nil left right cons _ _).mpr
    exact List.lex_trans (fun h₁ h₂ => lt_trans h₁ h₂)
      ((comparator_lex cmp nil left right cons _ _).mp hab)
      ((comparator_lex cmp nil left right cons _ _).mp hbc)
  irrefl := by
    intro a
    apply Bool.eq_false_iff.mpr
    intro h
    exact List.lex_irrefl (fun x => lt_irrefl x) _
      ((comparator_lex cmp nil left right cons _ _).mp h)
  asymm := by
    intro a b hab
    apply Bool.eq_false_iff.mpr
    intro hba
    exact asymm ((comparator_lex cmp nil left right cons _ _).mp hab)
      ((comparator_lex cmp nil left right cons _ _).mp hba)
  total := by
    intro a b hne
    rcases trichotomous_of (List.Lex (· < · : A → A → Prop)) (key a) (key b) with h | h | h
    · exact Or.inl ((comparator_lex cmp nil left right cons _ _).mpr h)
    · exact (hne h).elim
    · exact Or.inr ((comparator_lex cmp nil left right cons _ _).mpr h)

end Sal.MRDTs.Paper1.Automation.OrderedLists
