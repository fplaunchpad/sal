import Sal.MRDTs.Paper1.Automation.GenericPrefixCodes
import Mathlib.Tactic
namespace Sal.MRDTs.Paper1.Automation.PrefixCodes
variable {Token Symbol Tag Out : Type}
theorem map_prefix_reflect (f : Symbol → Out) (hf : Function.Injective f) :
    ∀ {a b : List Symbol}, a.map f <+: b.map f → a <+: b
  | [], _, _ => List.nil_prefix
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    obtain ⟨head, tail⟩ := List.cons_prefix_cons.mp h
    exact List.cons_prefix_cons.mpr ⟨hf head, map_prefix_reflect f hf tail⟩
/-- Disjoint injective symbol alphabets tag a prefix-free code without adding
any separator or changing the concatenation protocol. -/
def Code.tagged {valid : Token → Prop} {enc : Token → List Symbol}
    (C : Code valid enc) (symbol : Tag → Symbol → Out)
    (within : ∀ t, Function.Injective (symbol t))
    (across : ∀ t u, t ≠ u → ∀ a b, symbol t a ≠ symbol u b) :
    Code (fun e : Tag × Token => valid e.2)
      (fun e => (enc e.2).map (symbol e.1)) where
  nonempty := by intro e he; simpa using C.nonempty e.2 he
  prefixFree := by
    rintro ⟨t,a⟩ ⟨u,b⟩ ha hb ne pref
    by_cases same : t = u
    · subst u
      exact C.prefixFree a b ha hb (fun eq => ne (by rw [eq]))
        (map_prefix_reflect (symbol t) (within t) pref)
    · obtain ⟨x,xs,hx⟩ : ∃ x xs, enc a = x :: xs := by
        cases h : enc a with
        | nil => exact (C.nonempty a ha h).elim
        | cons x xs => exact ⟨x,xs,rfl⟩
      obtain ⟨y,ys,hy⟩ : ∃ y ys, enc b = y :: ys := by
        cases h : enc b with
        | nil => exact (C.nonempty b hb h).elim
        | cons y ys => exact ⟨y,ys,rfl⟩
      rw [hx,hy] at pref
      exact across t u same x y (List.cons_prefix_cons.mp pref).1
end Sal.MRDTs.Paper1.Automation.PrefixCodes
