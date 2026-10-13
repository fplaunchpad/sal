import Sal.MRDTs.Paper1.Automation.GenericOrderedRecords
import Sal.MRDTs.Paper1.Automation.OrderedRecordAutomation

/-! Data-only descriptions for immutable ordered records. The ten finite laws
remain kernel checked fields of the existing `Kit`; descriptions carry no proof
or completed correctness theorem. -/
namespace Sal.MRDTs.Paper1.Automation.OrderedRecords
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
structure Description (D : MRDTSig) (Record : Type) where
  carrier : D.State → Finset Record
  id : Record → Nat
  Key : Type
  key : Record → Key
  insertion : Op D.AppOp → Bool
  written : Op D.AppOp → Record
  target : Op D.AppOp → Nat → Prop
  ordered : D.State → Prop

/-- Freshness excludes the idempotence guard, independently of the operation
constructors or the payload stored in an immutable record. -/
theorem fresh_ids {R : Type} (id : R → Nat) (s : List R) (n : Nat)
    (fresh : ∀ p ∈ s, id p ≠ n) : n ∉ s.map id := by
  intro member
  obtain ⟨p, hp, equal⟩ := List.mem_map.mp member
  exact fresh p hp equal

end Sal.MRDTs.Paper1.Automation.OrderedRecords

/-- Assemble the unchanged Type-valued kit from a proof-free description.
`laws` is a shared finite-law solver, never a datatype theorem bundle. -/
macro "derive_ordered_kit " description:term " using " laws:tacticSeq : tactic => `(tactic| (
  refine {
    carrier := ($description).carrier
    id := ($description).id
    Key := ($description).Key
    key := ($description).key
    insertion := ($description).insertion
    written := ($description).written
    target := ($description).target
    ordered := ($description).ordered
    init_carrier := ?init_carrier
    init_ordered := ?init_ordered
    written_id := ?written_id
    update_provenance := ?update_provenance
    update_mem := ?update_mem
    update_ordered := ?update_ordered
    birth_not_killed := ?birth_not_killed
    merge_mem := ?merge_mem
    merge_ordered := ?merge_ordered
    ext := ?ext }
  ($laws)))

/-- Shared finite-law derivation. Operation constructors are discovered by
case analysis; the only annotations are implementation definitions to reduce. -/
macro "ordered_kit_laws" " unfolding " "[" defs:ident,* "]" : tactic => `(tactic| (
  case init_carrier => simp [$[$defs:ident],*]
  case init_ordered => simp [$[$defs:ident],*]
  case written_id =>
    intro e; rcases e with ⟨t, r, op⟩; cases op <;> simp [$[$defs:ident],*]
  case update_provenance =>
    intro s e p hp
    rcases e with ⟨t, r, op⟩
    cases op <;> simp only [$[$defs:ident],*, List.mem_toFinset] at hp ⊢
    all_goals try split at hp
    all_goals simp_all [$[$defs:ident],*]
    all_goals (simp only [ordered_generic_simps, List.mem_filter, decide_eq_true_eq] at *; grind)
  case update_mem =>
    intro s e fresh p
    simp only [$[$defs:ident],*, List.mem_toFinset] at fresh
    have absent := Sal.MRDTs.Paper1.Automation.OrderedRecords.fresh_ids _ s e.1 fresh
    rcases e with ⟨t, r, op⟩
    cases op <;> simp [$[$defs:ident],*, absent, List.mem_toFinset]
    all_goals (simp only [ordered_generic_simps, List.mem_filter, decide_eq_true_eq] at *; grind)
  case update_ordered =>
    intro s e hs keys
    rcases e with ⟨t, r, op⟩
    cases op <;> simp only [$[$defs:ident],*, List.mem_toFinset] at hs keys ⊢
    all_goals try split
    all_goals ordered_generic
  case birth_not_killed =>
    intro e ins
    rcases e with ⟨t, r, op⟩
    cases op <;> simp_all [$[$defs:ident],*]
  case merge_mem =>
    intro l a b al bl ab ba p
    simp only [$[$defs:ident],*, List.mem_toFinset, Sal.MRDTs.Paper1.Automation.Certified.cell] at al bl ab ba ⊢
    simp only [ordered_algorithm_simps]
    rw [Sal.MRDTs.Paper1.Automation.OrderedLists.survivor_mem _ _ l a b al bl ab ba p]
    tauto
  case merge_ordered =>
    intro l a b ha hb coherent
    simp only [$[$defs:ident],*, List.mem_toFinset] at ha hb coherent ⊢
    ordered_generic
  case ext =>
    intro s t hs ht same
    simp only [$[$defs:ident],*] at hs ht ⊢
    ordered_generic))

/-- Standard description-driven interface: definitions, never law scripts. -/
macro "derive_ordered_kit " description:term " unfolding " "[" defs:ident,* "]" : tactic =>
  `(tactic| derive_ordered_kit $description using
    ordered_kit_laws unfolding [$defs,*])
