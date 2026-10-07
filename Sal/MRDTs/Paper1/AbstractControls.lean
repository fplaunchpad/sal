import Sal.MRDTs.Paper1.AbstractORSet

/-! PASS+FAIL controls for the abstraction-first formalism. A legitimate
add/remove history has multiple abstract-canonical representatives, but their
tags cannot all be used interchangeably as merge inputs for that history. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractControls
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open AbstractMRDT
open Classical

abbrev add : Event Nat := (1,0,.add 7)
abbrev remove : Event Nat := (3,1,.remove 7)
abbrev left : Set (Event Nat) := {add}
abbrev right : Set (Event Nat) := {add,remove}
abbrev old : State Nat := {(0,1,7)}
abbrev fresh : State Nat := {(0,2,7)}

def context : ReplayContext (D Nat).toUpdateSig where
  L _ := some right
  vis a b := a = add ∧ b = remove
  timestamps_distinct := by
    intro a b r s r' s' hs ha hs' hb ne
    cases Option.some.inj hs
    cases Option.some.inj hs'
    change a = add ∨ a = remove at ha
    change b = add ∨ b = remove at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [add,remove]
  vis_total_same_replica := by
    intro a b r s r' s' hs ha hs' hb ne same
    cases Option.some.inj hs
    cases Option.some.inj hs'
    change a = add ∨ a = remove at ha
    change b = add ∨ b = remove at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [add,remove]

theorem old_canonical : Canonical (AbstractSpec.model (α := Nat))
    (EventSpec.conflict Nat) context left old := by
  apply (canonical_iff AbstractSpec.laws context left old).mpr
  refine ⟨[add],by simp [listPermOf],by simp [respects],?_⟩
  simp [AbstractSpec.model,Model.ofQuery,QuerySpec.abstraction,applySeq,D,
    Instances.EfficientORSet.update,elements,add]

theorem fresh_canonical : Canonical (AbstractSpec.model (α := Nat))
    (EventSpec.conflict Nat) context left fresh := by
  apply (canonical_iff AbstractSpec.laws context left fresh).mpr
  refine ⟨[add],by simp [listPermOf],by simp [respects],?_⟩
  simp [AbstractSpec.model,Model.ofQuery,QuerySpec.abstraction,applySeq,D,
    Instances.EfficientORSet.update,elements,add]

theorem removed_canonical : Canonical (AbstractSpec.model (α := Nat))
    (EventSpec.conflict Nat) context right (∅ : State Nat) := by
  apply (canonical_iff AbstractSpec.laws context right (∅ : State Nat)).mpr
  refine ⟨[add,remove],by simp [listPermOf],?_,?_⟩
  · simp [respects,AbstractMRDT.order,context,add,remove]
  · simp [AbstractSpec.model,Model.ofQuery,QuerySpec.abstraction,applySeq,D,
      Instances.EfficientORSet.update,elements,add,remove]

theorem merge_wrong : ¬ Canonical (AbstractSpec.model (α := Nat))
    (EventSpec.conflict Nat) context right (merge old fresh ∅) := by
  intro h
  have same := canonical_equivalent AbstractSpec.laws context right
    (fun e he => ⟨0,right,rfl,he⟩) h removed_canonical
  have read := equivalent_query same (7 : Nat)
  change decide (7 ∈ elements (merge old fresh ∅)) = decide (7 ∈ elements (∅ : State Nat)) at read
  simp [merge,elements] at read

theorem merge_control :
    Canonical (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) context left old ∧
    Canonical (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) context left fresh ∧
    Canonical (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) context right (∅ : State Nat) ∧
    ¬ Canonical (AbstractSpec.model (α := Nat)) (EventSpec.conflict Nat) context right
      (merge old fresh ∅) :=
  ⟨old_canonical,fresh_canonical,removed_canonical,merge_wrong⟩

/-- Even with supported, causally closed event sets, abstract canonicality
alone is insufficient as the metadata representation contract for Join. -/
theorem canonical_only_join_fails :
    ¬ RepresentationJoin (fun C E s => Canonical (AbstractSpec.model (α := Nat))
      (EventSpec.conflict Nat) C E s) := by
  intro join
  apply merge_wrong
  have result := join context left right old fresh (∅ : State Nat)
    (by intro a b c h k; simp [context] at h k; grind)
    (by intro e; simp [context]; grind)
    (fun e he => ⟨0,right,rfl,Or.inl he⟩)
    (fun e he => ⟨0,right,rfl,he⟩)
    (by intro e f h hf; simp [context] at h; simp_all)
    (by intro e f h hf; simp [context] at h; simp_all)
    (by simpa using old_canonical) fresh_canonical removed_canonical
  convert result using 1
  ext e
  simp [left,right]
  tauto

end Sal.MRDTs.Paper1.EfficientORSet.AbstractControls
