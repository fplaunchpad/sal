import Sal.MRDTs.Paper1.Automation.GenericPrefixCodes
import Mathlib.Tactic

namespace Sal.MRDTs.Paper1.Automation.PrefixCodes
variable {Symbol : Type}

/-- A reserved singleton, or a nonempty marker-terminated word with a
marker-free body. Alphabet restrictions are independent of prefix decoding. -/
def TerminatedTag (sentinel marker : Symbol) (allowed : Symbol → Prop)
    (word : List Symbol) : Prop :=
  word = [sentinel] ∨ ∃ h body, word = (h :: body) ++ [marker] ∧
    h ≠ sentinel ∧ h ≠ marker ∧ allowed h ∧
    ∀ s ∈ body, s ≠ marker ∧ allowed s

theorem TerminatedTag.nonempty {sentinel marker : Symbol} {allowed : Symbol → Prop}
    {word : List Symbol} (valid : TerminatedTag sentinel marker allowed word) : word ≠ [] := by
  rcases valid with rfl | ⟨h, body, rfl, _⟩ <;> simp

theorem TerminatedTag.allSymbols {sentinel marker : Symbol} {allowed : Symbol → Prop}
    (sentinelAllowed : allowed sentinel) (markerAllowed : allowed marker)
    {word : List Symbol} (valid : TerminatedTag sentinel marker allowed word) :
    ∀ s ∈ word, allowed s := by
  rcases valid with rfl | ⟨h, body, rfl, _, _, head, tail⟩
  · simpa using sentinelAllowed
  · intro s hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | hs) | rfl
    · exact head
    · exact (tail s hs).2
    · exact markerAllowed

/-- A terminator absent from the body makes complete words prefix-free. -/
theorem marker_terminated_prefixFree (marker : Symbol) : ∀ {u v : List Symbol},
    (∀ s ∈ v, s ≠ marker) → u ≠ v → ¬ ((u ++ [marker]) <+: (v ++ [marker]))
  | [], [], _, ne, _ => ne rfl
  | [], y :: ys, valid, _, pref => by
      rw [List.nil_append, List.cons_append, List.cons_prefix_cons] at pref
      exact valid y List.mem_cons_self pref.1.symm
  | x :: xs, [], _, _, pref => by
      rw [List.cons_append, List.nil_append, List.cons_prefix_cons] at pref
      obtain ⟨rfl, tail⟩ := pref
      simp at tail
  | x :: xs, y :: ys, valid, ne, pref => by
      rw [List.cons_append, List.cons_append, List.cons_prefix_cons] at pref
      obtain ⟨rfl, tail⟩ := pref
      exact marker_terminated_prefixFree marker
        (fun s hs => valid s (List.mem_cons_of_mem _ hs))
        (fun eq => ne (by rw [eq])) tail

theorem TerminatedTag.prefixFree {sentinel marker : Symbol} {allowed : Symbol → Prop}
    {a b : List Symbol} (ha : TerminatedTag sentinel marker allowed a)
    (hb : TerminatedTag sentinel marker allowed b) (ne : a ≠ b) : ¬ a <+: b := by
  rcases ha with rfl | ⟨x, xs, rfl, xsentinel, _, _, _⟩
  · rcases hb with rfl | ⟨y, ys, rfl, ysentinel, _, _, _⟩
    · exact (ne rfl).elim
    · intro pref
      rw [List.cons_append, List.cons_prefix_cons] at pref
      exact ysentinel pref.1.symm
  · rcases hb with rfl | ⟨y, ys, rfl, _, ymarker, _, tail⟩
    · intro pref
      have := pref.length_le
      simp at this
    · exact marker_terminated_prefixFree marker
        (by
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ymarker
          · exact (tail s hs).1)
        (by simpa using ne)

def TerminatedTag.code (sentinel marker : Symbol) (allowed : Symbol → Prop) :
    Code (TerminatedTag sentinel marker allowed) id where
  nonempty := fun _ valid => valid.nonempty
  prefixFree := fun _ _ ha hb ne => ha.prefixFree hb ne

end Sal.MRDTs.Paper1.Automation.PrefixCodes
