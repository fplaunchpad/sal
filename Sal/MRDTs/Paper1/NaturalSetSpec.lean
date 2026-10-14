import Sal.MRDTs.Paper1.HistorySpec
import Mathlib.Data.Finset.Basic

/-! One independent ordinary-set ADT for the ordinary and efficient OR-set
implementations. Public operation alphabets use explicit adapters; tags,
replicas, and merge state do not occur in this abstract machine. -/
namespace Sal.MRDTs.Paper1.NaturalSetSpec

inductive Action (α : Type) where
  | add (element : α)
  | remove (element : α)
  deriving DecidableEq

variable {α U : Type} [DecidableEq α]

def step (s : Finset α) : Action α → Finset α
  | .add x => insert x s
  | .remove x => s.erase x

@[simp] theorem step_add (s : Finset α) (x : α) : step s (.add x) = insert x s := rfl
@[simp] theorem step_remove (s : Finset α) (x : α) : step s (.remove x) = s.erase x := rfl

/-- The decoder exposes only the ordinary add/remove request. -/
def model (decode : U → Action α) : DeterministicSpec U α Bool where
  State := Finset α
  initial := ∅
  update s u := step s (decode u)
  query s x := decide (x ∈ s)

@[simp] theorem model_initial (decode : U → Action α) :
    (model decode).initial = (∅ : Finset α) := rfl

@[simp] theorem model_update (decode : U → Action α) (s : Finset α) (u : U) :
    (model decode).update s u = step s (decode u) := rfl

@[simp] theorem model_query (decode : U → Action α) (s : Finset α) (x : α) :
    (model decode).query s x = decide (x ∈ s) := rfl

end Sal.MRDTs.Paper1.NaturalSetSpec
