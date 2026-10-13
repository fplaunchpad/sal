import Sal.MRDTs.Paper1.AnchoredQueue

namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA

theorem fifoFold_snoc (es : List Event) (e : Event) :
    fifoFold (es ++ [e]) = fifoStep (fifoFold es) e := by
  simp [fifoFold,List.foldl_append]

/-- The independent FIFO's live identities come from previously allocated
births, including after idempotent removals. No implementation state is used. -/
theorem fifoFold_ids_subset (es : List Event) :
    ∀ target ∈ (fifoFold es).map Prod.fst, target ∈ eInsIds es := by
  induction es using List.reverseRecOn with
  | nil => simp [fifoFold]
  | append_singleton es e ih =>
      rw [fifoFold_snoc,eInsIds_append]
      rcases e with ⟨time,rep,op⟩
      cases op with
      | ins value pref anchor =>
          intro target mem
          simp only [fifoStep,Op.op,Op.time,List.map_append,List.map_cons,List.map_nil,
            List.mem_append,List.mem_singleton] at mem
          rcases mem with old | rfl
          · exact List.mem_append_left _ (ih target old)
          · apply List.mem_append_right
            simp [eInsIds,eIsIns]
      | del target =>
          intro x mem
          obtain ⟨record,hm,he⟩ := List.mem_map.mp mem
          have old := List.mem_of_mem_filter hm
          exact List.mem_append_left _ (ih x (List.mem_map.mpr ⟨record,old,he⟩))

/-- Allocation freshness over the birth history suffices for live-state
freshness; a discarded element cannot make its identity available again. -/
theorem fifo_fresh_of_birth_fresh {es : List Event} {time : Nat}
    (fresh : time ∉ eInsIds es) : time ∉ (fifoFold es).map Prod.fst :=
  fun mem => fresh (fifoFold_ids_subset es time mem)

#print axioms fifoFold_ids_subset
end Sal.MRDTs.Paper1.AnchoredQueue
