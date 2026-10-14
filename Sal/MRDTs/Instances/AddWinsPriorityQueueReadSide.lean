import Sal.MRDTs.Paper1.AddWinsPriorityQueueSpec

/-! Observable Add-wins, observed removal, retained acquired priority and
signed increment laws. No claim that removal resets acquired priority. -/
namespace Sal.MRDTs.Instances.AddWinsPriorityQueue
open Foundation
variable {α : Type} [DecidableEq α]

theorem query_congr {s t : State α} (h : s = t) (x : α) : query s x = query t x := by rw [h]

theorem observed_remove_absent (s : State α) (t r : Nat) (x : α) :
    query (step s (t,r,.remove x)) x = none := by
  rw [query,Paper1.AddWinsPriorityQueue.winner_remove,if_pos rfl]
  rfl

theorem remove_retains_acquired (s : State α) (t r : Nat) (x y : α) :
    acquired (step s (t,r,.remove y)) x = acquired s x := rfl

theorem acquired_fresh_increment (s : State α) (t r : Nat) (x : α) (n : Int)
    (fresh : (x,t,n) ∉ s.2) :
    acquired (step s (t,r,.inc x n)) x = n + acquired s x := by
  simp only [acquired,step,Finset.filter_insert,ite_true]
  rw [Finset.sum_insert]
  exact fun h => fresh (Finset.mem_filter.mp h).1

theorem priority_fresh_increment (s : State α) (t r : Nat) (x : α) (n : Int)
    (fresh : (x,t,n) ∉ s.2) :
    query (step s (t,r,.inc x n)) x = (query s x).map (fun v => v + n) := by
  have amount := acquired_fresh_increment s t r x n fresh
  have same : winner (step s (t,r,.inc x n)) x = winner s x := rfl
  unfold query
  rw [same,amount]
  rw [Option.map_map]
  congr 1
  funext p
  simp [Int.add_assoc,Int.add_comm]

theorem query_present (s : State α) (x : α) (t v : Nat) (member : (x,t,v) ∈ s.1) :
    query s x ≠ none := by
  have present : toLex (t,v) ∈ (s.1.filter (fun p => p.1 = x)).image (fun p => toLex p.2) :=
    Finset.mem_image.mpr ⟨(x,t,v),Finset.mem_filter.mpr ⟨member,rfl⟩,rfl⟩
  obtain ⟨best,hbest⟩ := Finset.max_of_mem present
  have bestWinner : winner s x = (best : WithBot (Lex (Timestamp × Nat))) := hbest
  rw [query,bestWinner]
  change some _ ≠ none
  simp

theorem add_present (s : State α) (t r : Nat) (x : α) (v : Nat) :
    query (step s (t,r,.add x v)) x ≠ none := by
  apply query_present _ x t v
  simp [step]

/-- Different replicas may issue the divergent Remove and Add branches. A
fresh Add survives the ancestor-sensitive merge even when the other branch
removed every observed Add of this element. -/
theorem concurrent_add_wins (base : State α) (ta tr ra rr : Nat) (x : α) (v : Nat)
    (fresh : (x,ta,v) ∉ base.1) :
    query (merge base (step base (tr,rr,.remove x)) (step base (ta,ra,.add x v))) x ≠ none := by
  apply query_present _ x ta v
  simp [merge,step,fresh]

#print axioms priority_fresh_increment
#print axioms concurrent_add_wins
end Sal.MRDTs.Instances.AddWinsPriorityQueue
