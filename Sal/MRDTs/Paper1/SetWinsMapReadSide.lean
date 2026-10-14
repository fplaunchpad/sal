import Sal.MRDTs.Paper1.SetWinsMapEvent

namespace Sal.MRDTs.Paper1.SetWinsMap
open Foundation Instances.SetWinsMap

@[simp] theorem mem_lookup (s : State) (k v : Nat) :
    v ∈ lookup s k ↔ ∃ t, (t,(k,v)) ∈ s := by
  simp only [lookup,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨t,j,w⟩,⟨hp,key⟩,val⟩
    simp only at key val
    subst j; subst w
    exact ⟨t,hp⟩
  · rintro ⟨t,hp⟩
    exact ⟨(t,(k,v)),⟨hp,rfl⟩,rfl⟩

theorem set_accumulates (s : State) (t r k v : Nat) :
    lookup (update s (t,r,.set k v)) k = insert v (lookup s k) := by
  ext w
  simp only [mem_lookup,source_set,Finset.mem_insert,Prod.mk.injEq]
  grind

theorem delete_clears (s : State) (t r k : Nat) :
    lookup (update s (t,r,.del k)) k = ∅ := by
  ext v
  simp only [mem_lookup,source_del,Finset.mem_filter,ne_eq,not_true_eq_false,
    and_false,exists_false,Finset.notMem_empty]

theorem concurrent_set_wins (l : State) (td rd ts rs k v : Nat)
    (fresh : (ts,(k,v)) ∉ l) :
    v ∈ lookup (merge l (update l (td,rd,.del k)) (update l (ts,rs,.set k v))) k := by
  rw [mem_lookup]
  refine ⟨ts,?_⟩
  simp [merge,update,Op.op,Op.time,fresh]

#print axioms set_accumulates
#print axioms delete_clears
#print axioms concurrent_set_wins
end Sal.MRDTs.Paper1.SetWinsMap
