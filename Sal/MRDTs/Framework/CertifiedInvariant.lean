import Sal.MRDTs.Framework.SequentialInduction
import Mathlib.Data.Finset.Image

/-! Structural closure rules for certified event carriers. The caller supplies
the semantic consequence of its issuer; subset and insertion transport are
independent of the operation language. No invariant is assumed at a smaller
origin merely because it holds at the merged prefix. -/
namespace Sal.MRDTs.Foundation

variable {E K : Type} [DecidableEq E] [DecidableEq K]

omit [DecidableEq E] in
theorem witness_mono {s t : Finset E} {R : E → Prop}
    (subset : s ⊆ t) (witness : ∃ e ∈ s, R e) : ∃ e ∈ t, R e := by
  obtain ⟨e, member, fact⟩ := witness
  exact ⟨e, subset member, fact⟩

theorem all_insert (P : Finset E → E → Prop)
    (mono : ∀ {s t}, s ⊆ t → ∀ {e}, P s e → P t e)
    {events : Finset E} {e : E}
    (old : ∀ p ∈ events, P events p) (new : P events e) :
    ∀ p ∈ insert e events, P (insert e events) p := by
  intro p member
  rcases Finset.mem_insert.mp member with rfl | member
  · exact mono (Finset.subset_insert p events) new
  · exact mono (Finset.subset_insert e events) (old p member)

theorem all_insert_of_origin (P : Finset E → E → Prop)
    (mono : ∀ {s t}, s ⊆ t → ∀ {e}, P s e → P t e)
    {events origin : Finset E} {e : E}
    (old : ∀ p ∈ events, P events p) (subset : origin ⊆ events)
    (new : (∀ p ∈ origin, P events p) → P events e) :
    ∀ p ∈ insert e events, P (insert e events) p :=
  all_insert P mono old (new (fun p member => old p (subset member)))

/-- Fresh keys preserve injectivity, independently of the meaning of a key. -/
theorem key_unique_insert (key : E → K) {events : Finset E} {e : E}
    (unique : ∀ a ∈ events, ∀ b ∈ events, key a = key b → a = b)
    (fresh : key e ∉ events.image key) :
    ∀ a ∈ insert e events, ∀ b ∈ insert e events, key a = key b → a = b := by
  intro a ha b hb same
  simp only [Finset.mem_insert] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · exact hb.symm
    · exact False.elim (fresh (Finset.mem_image.mpr ⟨b, hb, same.symm⟩))
  · rcases hb with hb | hb
    · subst b
      exact False.elim (fresh (Finset.mem_image.mpr ⟨a, ha, same⟩))
    · exact unique a ha b hb same

end Sal.MRDTs.Foundation
