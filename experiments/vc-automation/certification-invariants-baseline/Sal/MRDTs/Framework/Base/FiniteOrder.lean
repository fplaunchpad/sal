import Sal.MRDTs.Framework.Base.Replay
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Finite topological enumeration, independent of datatypes and execution. -/

namespace Sal.MRDTs
open Foundation Classical

/-- A nonempty list ordered by a transitive irreflexive relation has an
`R`-minimal element (no element of the list is `R`-below it). -/
private theorem exists_rel_min {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) :
    ∀ (l : List α), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, ¬ R x m := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hirrefl _
      · exact absurd hx List.not_mem_nil
    · obtain ⟨m, hm, hmin⟩ := ih hl
      by_cases ham : R a m
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro x hx hxa
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hirrefl _ hxa
        · exact hmin x hx (htrans hxa ham)
      · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
        intro x hx hxm
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ham hxm
        · exact hmin x hx hxm

/-- Any finite list reorders into an `R`-respecting one (`R` transitive,
irreflexive): peel a minimal element, recurse on the rest. -/
private theorem exists_respecting_perm_aux {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n →
      ∃ l', l.Perm l' ∧ respects l' R := by
  classical
  intro n
  induction n with
  | zero =>
    intro l hl
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hnil
    exact ⟨[], List.Perm.refl _, List.Pairwise.nil⟩
  | succ n ihn =>
    intro l hl
    by_cases hnil : l = []
    · subst hnil
      exact ⟨[], List.Perm.refl _, List.Pairwise.nil⟩
    · obtain ⟨m, hm_mem, hm_min⟩ :=
        exists_rel_min (R := R) (fun hab hbc => htrans hab hbc) hirrefl l hnil
      have hperm : l.Perm (m :: l.erase m) := List.perm_cons_erase hm_mem
      have hlen : (l.erase m).length ≤ n := by
        have herase := List.length_erase_of_mem hm_mem
        have hpos : l.length ≠ 0 :=
          fun h => hnil (List.eq_nil_of_length_eq_zero h)
        omega
      obtain ⟨l'', hp'', hr''⟩ := ihn (l.erase m) hlen
      refine ⟨m :: l'', hperm.trans (hp''.cons m), ?_⟩
      unfold respects
      rw [List.pairwise_cons]
      refine ⟨?_, hr''⟩
      intro y hy
      exact hm_min y (List.mem_of_mem_erase (hp''.mem_iff.mpr hy))

/-- Reordering wrapper: every finite list has an `R`-respecting
permutation. -/
theorem exists_respecting_perm {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) (l : List α) :
    ∃ l', l.Perm l' ∧ respects l' R :=
  exists_respecting_perm_aux (R := R) (fun hab hbc => htrans hab hbc) hirrefl
    l.length l (Nat.le_refl _)

end Sal.MRDTs
