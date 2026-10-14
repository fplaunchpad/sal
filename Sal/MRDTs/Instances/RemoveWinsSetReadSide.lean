import Sal.MRDTs.Paper1.RemoveWinsSetEvent

namespace Sal.MRDTs.Instances.RemoveWinsSet
open Foundation
variable {α : Type} [DecidableEq α] [Fintype α]

theorem query_of_equal {s t : State α} (equal : s = t) (x : α) : query s x = query t x :=
  equal ▸ rfl

theorem query_false_of_tag (s : State α) (x : α) (ts : Timestamp)
    (present : (x,ts) ∈ s) : query s x = false := by
  have hx : x ∈ s.image Prod.fst := Finset.mem_image.mpr ⟨(x,ts),present,rfl⟩
  simp [query,view,hx]

theorem add_present (s : State α) (ts r : Nat) (x : α) :
    query (step s (ts,r,.add x)) x = true := by
  simp [query,Paper1.RemoveWinsSet.view_step,Paper1.RemoveWinsSet.decode,Op.op]

theorem remove_absent (s : State α) (ts r : Nat) (x : α) :
    query (step s (ts,r,.remove x)) x = false := by
  apply query_false_of_tag _ x ts
  simp [step]

/-- A concurrent Rem introduces a fresh tag surviving the Add branch. -/
theorem remove_wins_concurrent (s : State α) (ta ra tr rr : Nat) (x : α)
    (fresh : (x,tr) ∉ s) :
    query (merge s (step s (ta,ra,.add x)) (step s (tr,rr,.remove x))) x = false := by
  apply query_false_of_tag _ x tr
  simp [merge,step,fresh]

theorem remove_then_add (s : State α) (tr rr ta ra : Nat) (x : α) :
    query (step (step s (tr,rr,.remove x)) (ta,ra,.add x)) x = true :=
  add_present _ ta ra x

end Sal.MRDTs.Instances.RemoveWinsSet
