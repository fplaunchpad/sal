import Sal.MRDTs.Paper1.SequentialSimulation

/-! A finite description of a tagged set implementation. The description gives
record operations, independently of the abstract machine. Projection equations
and sequential simulation are consequences, rather than supplied bridge VCs. -/
namespace Sal.MRDTs.Paper1.Automation
open Foundation

inductive SetAction (R A : Type) where
  | add (record : R) (keep : R → Bool)
  | remove (element : A)

namespace SetAction
variable {R A : Type} [DecidableEq R] [DecidableEq A]

def records (key : R → A) (s : Finset R) : SetAction R A → Finset R
  | .add r keep => insert r (s.filter (fun p => keep p = true))
  | .remove x => s.filter (fun r => key r ≠ x)

def elements (key : R → A) (s : Finset A) : SetAction R A → Finset A
  | .add r _ => insert (key r) s
  | .remove x => s.erase x

/-- Overwriting tags for the added element is harmless: the new tag supplies
that element's witness. Tags for every other element must survive. -/
def Valid (key : R → A) : SetAction R A → Prop
  | .add r keep => ∀ p, key p ≠ key r → keep p = true
  | .remove _ => True

theorem image_records (key : R → A) (s : Finset R) (a : SetAction R A)
    (h : a.Valid key) : (a.records key s).image key = a.elements key (s.image key) := by
  cases a with
  | add r keep =>
    ext x
    simp only [records, elements, Finset.image_insert, Finset.mem_insert,
      Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (hx | ⟨p, ⟨hp, _⟩, he⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨p, hp, he⟩
    · rintro (hx | ⟨p, hp, he⟩)
      · exact Or.inl hx
      · by_cases hx : x = key r
        · exact Or.inl hx
        · exact Or.inr ⟨p, ⟨hp, h p (by simpa [he] using hx)⟩, he⟩
  | remove y =>
    ext x
    simp only [records, elements, Finset.mem_image, Finset.mem_filter,
      Finset.mem_erase]
    constructor
    · rintro ⟨p, ⟨hp, hn⟩, he⟩
      exact ⟨by simpa [he] using hn, p, hp, he⟩
    · rintro ⟨hn, p, hp, he⟩
      exact ⟨p, ⟨hp, by simpa [he] using hn⟩, he⟩
end SetAction

/-- The finite data are a record key and one action per concrete event. The
only semantic obligations describe the raw update equations and independent
model actions; neither a projection-step theorem nor history soundness is an
input. -/
structure FiniteSetDescription (R A E : Type) [DecidableEq R] [DecidableEq A]
    (update : Finset R → E → Finset R) (abstractUpdate : Finset A → E → Finset A) where
  key : R → A
  action : E → SetAction R A
  valid : ∀ e, (action e).Valid key
  concrete : ∀ s e, update s e = (action e).records key s
  abstract : ∀ s e, abstractUpdate s e = (action e).elements key s

namespace FiniteSetDescription
variable {R A E : Type} [DecidableEq R] [DecidableEq A]
variable {update : Finset R → E → Finset R} {abstractUpdate : Finset A → E → Finset A}

theorem project_update (H : FiniteSetDescription R A E update abstractUpdate)
    (s : Finset R) (e : E) :
    (update s e).image H.key = abstractUpdate (s.image H.key) e := by
  rw [H.concrete, H.abstract]
  exact SetAction.image_records H.key s (H.action e) (H.valid e)

/-- Every abstract set has a record representative if each element has a tag. -/
theorem representative (H : FiniteSetDescription R A E update abstractUpdate)
    (tag : A → R) (htag : ∀ x, H.key (tag x) = x) (s : Finset A) :
    (s.image tag).image H.key = s := by
  simp [Finset.image_image, Function.comp_def, htag]

end FiniteSetDescription
end Sal.MRDTs.Paper1.Automation

/-- Derive the finite-description laws by exhausting the supplied event's
application constructors and reducing the annotated raw definitions. This
frontend has no access to projection-step or history-bridge lemmas. -/
macro "derive_finite_set_law" "[" defs:ident,* "]" : tactic => `(tactic| (
  first
  | (intro s e; rcases e with ⟨t, r, op⟩; cases op <;>
      first
      | (simp [$[$defs:ident],*, Sal.MRDTs.Paper1.Automation.SetAction.records,
          Sal.MRDTs.Paper1.Automation.SetAction.elements,
          Sal.MRDTs.Foundation.Op.op, Sal.MRDTs.Foundation.Op.time]; done)
      | (ext p; simp [$[$defs:ident],*, Sal.MRDTs.Paper1.Automation.SetAction.records,
          Sal.MRDTs.Paper1.Automation.SetAction.elements,
          Sal.MRDTs.Foundation.Op.op, Sal.MRDTs.Foundation.Op.time]; grind))
  | (intro e; rcases e with ⟨t, r, op⟩; cases op <;>
      simp [$[$defs:ident],*, Sal.MRDTs.Paper1.Automation.SetAction.Valid,
        Sal.MRDTs.Foundation.Op.op, Sal.MRDTs.Foundation.Op.time] <;> grind)))
