import Sal.MRDTs.Instances.NotionCoreMachine

/-! Connect the combined interpreter's actual checked insertion loop to the
raw parent-table append used by the graph and traversal proofs. The conditions
concern ID uniqueness and parent rank, never the desired traversal or view. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineRows
open NotionRunAllocation (Id)
open NotionCoreParentMap (Row Table)
open NotionCoreMachine

theorem lookup_absent (rows : Table) (id : Id)
    (absent : id ∉ rows.map (fun row => row.item.id)) :
    NotionCoreParentMap.lookup rows id = none := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have different : row.item.id ≠ id := by
      intro same
      exact absent (List.mem_cons.mpr (Or.inl same.symm))
    have tail : id ∉ rest.map (fun row => row.item.id) :=
      fun member => absent (List.mem_cons_of_mem _ member)
    simpa [NotionCoreParentMap.lookup, different] using ih tail

/-- The real duplicate/self-origin checks accept a fresh non-self row and
append it, rather than requiring the caller to assume that update equation. -/
theorem integrate_fresh (rows : Table) (row : Row)
    (fresh : row.item.id ∉ rows.map (fun row => row.item.id))
    (parent : row.origin ≠ .item row.item.id) :
    integrate rows row = some (rows ++ [row]) := by
  simp [integrate, lookup_absent rows row.item.id fresh, parent]

theorem integrateRows_fresh (rows fresh : Table)
    (unique : NotionCoreParentMap.Unique fresh)
    (apart : List.Disjoint (rows.map (fun row => row.item.id)) (fresh.map (fun row => row.item.id)))
    (parents : ∀ row ∈ fresh, row.origin ≠ .item row.item.id) :
    integrateRows rows fresh = some (rows ++ fresh) := by
  induction fresh generalizing rows with
  | nil => simp [integrateRows]
  | cons row rest ih =>
    have freshId : row.item.id ∉ rows.map (fun row => row.item.id) := by
      intro member
      exact List.disjoint_left.mp apart member (by simp)
    have restUnique := (List.nodup_cons.mp unique).2
    have restApart : List.Disjoint ((rows ++ [row]).map (fun row => row.item.id))
        (rest.map (fun row => row.item.id)) := by
      apply List.disjoint_left.mpr
      intro id old new
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at old
      rcases old with old | rfl
      · exact List.disjoint_left.mp apart old (List.mem_cons_of_mem _ new)
      · exact (List.nodup_cons.mp unique).1 new
    rw [integrateRows, integrate_fresh rows row freshId (parents row (by simp))]
    simpa [List.append_assoc] using ih (rows ++ [row]) restUnique restApart
      (fun value member => parents value (List.mem_cons_of_mem _ member))

/-- Increasing parent counters derive all self-origin checks. The graph
theorems obtain this rank from typed issuance, including internal run links. -/
theorem integrateRows_increasing (rows fresh : Table)
    (unique : NotionCoreParentMap.Unique fresh)
    (apart : List.Disjoint (rows.map (fun row => row.item.id)) (fresh.map (fun row => row.item.id)))
    (rank : NotionCoreParentMap.Increasing fresh) :
    integrateRows rows fresh = some (rows ++ fresh) := by
  apply integrateRows_fresh rows fresh unique apart
  intro row member equal
  have smaller := rank row member
  simp [equal, NotionCoreParentMap.originCounter] at smaller

#print axioms integrateRows_increasing
end Sal.MRDTs.Instances.NotionCoreMachineRows
