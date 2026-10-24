import Sal.MRDTs.Instances.NotionCoreRichSequentialDocument
import Sal.MRDTs.Instances.NotionCoreRichSequentialInputs
import Sal.MRDTs.Instances.NotionCoreFormattingPlanner

/-!
Actual source before-item/END anchors and independent physical-cell indices.

The repaired planner uses these endpoint forms only. Source extraction keeps
markers and tombstones, so an invisible endpoint continues to have the same
identity and coordinate. No displayed-position or exact-coverage premise is
used to define this relation.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichCoordinates
open NotionCoreFormattingSource (Positioned Anchor anchorPosition walk)
open NotionCoreOriginTree (Forest preorder Item)
open NotionRunAllocation (Id)

private theorem numbered_lookup (positions : List Positioned) (offset : Nat) (id : Id)
    (numbered : positions.map Positioned.entry = List.range' offset positions.length) :
    ((positions.find? (fun p => p.item.id == id)).map Positioned.entry) =
      (positions.findIdx? (fun p => p.item.id == id)).map (fun index => offset + index) := by
  induction positions generalizing offset with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] at numbered
    obtain ⟨entry,tail⟩ := numbered
    by_cases hit : p.item.id == id
    · simp [List.find?_cons,List.findIdx?_cons,hit,entry]
    · simp only [List.find?_cons,hit,Bool.false_eq_true,↓reduceIte,List.findIdx?_cons]
      rw [ih (offset + 1) tail]
      simp [hit,Option.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem anchor_before_findIdx (forest : Forest) (id : Id) :
    anchorPosition forest ⟨.item id,.before⟩ =
      ((preorder forest).findIdx? (fun item => item.id == id)) := by
  have lengths : (walk 0 forest).length = (preorder forest).length := by
    simpa using congrArg List.length (NotionCoreFormattingSource.walk_items 0 forest)
  have numbered : (walk 0 forest).map Positioned.entry =
      List.range' 0 (walk 0 forest).length := by
    rw [NotionCoreFormattingSource.walk_entries,lengths]
  have lookup := numbered_lookup (walk 0 forest) 0 id numbered
  have lookup' : ((walk 0 forest).find? (fun p => p.item.id == id)).map Positioned.entry =
      (walk 0 forest).findIdx? (fun p => p.item.id == id) := by simpa using lookup
  change ((walk 0 forest).find? (fun p => p.item.id == id)).map Positioned.entry = _
  rw [lookup']
  rw [← NotionCoreFormattingSource.walk_items 0 forest]
  simp [Function.comp_def]

def physicalSlots (inst : Nat) (forest : Forest) : List NotionCoreSpec.Slot :=
  ((preorder forest).map (NotionCorePhysicalReplay.atom inst)).map NotionCoreSource.Atom.slot

theorem physicalSlots_addresses (inst : Nat) (forest : Forest) :
    (physicalSlots inst forest).map NotionCoreSpec.Slot.address =
      (preorder forest).map (fun item => NotionCorePhysicalReplay.address inst item.id) := by
  simp only [physicalSlots,List.map_map]
  apply List.map_congr_left
  intro item member
  cases kind : item.kind <;> simp [NotionCorePhysicalReplay.atom,NotionCoreSource.Atom.slot,kind]

/-- Semantic stable IDs locate the same physical entry as the actual source
anchor. The encoding is injective, not assumed to preserve timestamp order. -/
theorem endpoint_before (inst : Nat) (forest : Forest) (id : Id)
    (bold gapBold : Nat → Bool) :
    NotionCoreRichSequential.endpointPosition inst
      ⟨physicalSlots inst forest,bold,gapBold⟩
      (.before (NotionCorePhysicalReplay.markerKey id)) =
      anchorPosition forest ⟨.item id,.before⟩ := by
  rw [NotionCoreRichSequential.endpointPosition,physicalSlots_addresses,anchor_before_findIdx]
  simp only [List.findIdx?_map]
  congr 1
  funext item
  have equal : NotionCorePhysicalReplay.address inst item.id =
      (inst,NotionCoreSpec.LocalId.event (NotionCorePhysicalReplay.markerKey id)) ↔ item.id = id := by
    change NotionCorePhysicalReplay.address inst item.id = NotionCorePhysicalReplay.address inst id ↔ _
    exact (NotionCorePhysicalReplay.address_injective inst).eq_iff
  exact Bool.eq_iff_iff.mpr (by simpa only [Function.comp_def,beq_iff_eq] using equal)

theorem endpoint_finish (inst : Nat) (forest : Forest) (bold gapBold : Nat → Bool) :
    NotionCoreRichSequential.endpointPosition inst
      ⟨physicalSlots inst forest,bold,gapBold⟩ .finish =
      anchorPosition forest ⟨.finish,.before⟩ := by
  simp [NotionCoreRichSequential.endpointPosition,anchorPosition,physicalSlots]

theorem translated_endpoint (inst : Nat) (forest : Forest) (bold gapBold : Nat → Bool)
    (source : Anchor) (target : NotionCoreRichSequential.Endpoint)
    (translated : NotionCoreRichSequentialInputs.endpoint source = some target) :
    NotionCoreRichSequential.endpointPosition inst ⟨physicalSlots inst forest,bold,gapBold⟩ target =
      anchorPosition forest source := by
  cases source with
  | mk source side =>
    cases source with
    | start => cases side <;> cases translated
    | finish =>
      cases side with
      | before => cases Option.some.inj translated; exact endpoint_finish inst forest bold gapBold
      | after => cases translated
    | item id =>
      cases side with
      | before => cases Option.some.inj translated; exact endpoint_before inst forest id bold gapBold
      | after => cases translated

/-- Supported source regions and direct-state regions resolve the same
coordinates, including failure at an unavailable physical endpoint. -/
theorem translated_region (forest : Forest) (bold gapBold : Nat → Bool)
    (source : NotionCoreRichPayload.Part) (target : NotionCoreRichSequential.Region)
    (translated : NotionCoreRichSequentialInputs.region source = some target) :
    target.instanceId = source.instanceId ∧
      NotionCoreRichSequential.resolveRegion ⟨physicalSlots source.instanceId forest,bold,gapBold⟩ target =
        (do pure ⟨← anchorPosition forest source.lower,← anchorPosition forest source.upper⟩) := by
  unfold NotionCoreRichSequentialInputs.region at translated
  obtain ⟨lower,lowerTranslated,afterLower⟩ := Option.bind_eq_some_iff.mp translated
  obtain ⟨upper,upperTranslated,afterUpper⟩ := Option.bind_eq_some_iff.mp afterLower
  cases Option.some.inj afterUpper
  refine ⟨rfl,?_⟩
  simp only [NotionCoreRichSequential.resolveRegion]
  rw [translated_endpoint source.instanceId forest bold gapBold source.lower lower lowerTranslated,
    translated_endpoint source.instanceId forest bold gapBold source.upper upper upperTranslated]

/-- A fresh physical run cannot change which old item is found. Its index
changes by exactly the independent insertion embedding, including gap zero. -/
theorem findIdx_splice {α : Type} (old fresh : List α) (predicate : α → Bool) (gap : Nat)
    (absent : ∀ item ∈ fresh, predicate item = false) :
    ((old.take gap ++ fresh ++ old.drop gap).findIdx? predicate) =
      (old.findIdx? predicate).map (NotionCoreRichSequential.shift gap fresh.length) := by
  have noFresh : fresh.findIdx? predicate = none := List.findIdx?_eq_none_iff.mpr absent
  induction gap generalizing old with
  | zero =>
    cases found : old.findIdx? predicate <;>
      simp [NotionCoreRichSequential.shift,noFresh,found]
  | succ gap ih =>
    cases old with
    | nil => simp [noFresh]
    | cons item rest =>
      by_cases hit : predicate item = true
      · simp [List.take_succ_cons,List.drop_succ_cons,List.findIdx?_cons,hit,
          NotionCoreRichSequential.shift]
      · simp only [List.take_succ_cons,List.drop_succ_cons,List.cons_append,
          List.findIdx?_cons,hit,↓reduceIte]
        rw [ih rest]
        simp only [Option.map_map,Bool.false_eq_true,↓reduceIte]
        congr 1
        funext index
        simp only [Function.comp_def,NotionCoreRichSequential.shift]
        split <;> split <;> omega

def originGap (forest : Forest) (origin : Id) : Nat :=
  ((preorder forest).map Item.id).idxOf origin + 1

/-- The actual fresh child insertion determines its physical gap by searching
the origin, rather than taking a surrounding list equation as a premise. -/
theorem inserted_preorder (forest next : Forest) (origin : Id) (first : Item) (rest : List Item)
    (ready : NotionCoreOriginTree.DominatesForest origin first.id forest)
    (present : origin ∈ (preorder forest).map Item.id)
    (inserted : NotionCoreOriginTree.insert (.item origin)
      (NotionCoreOriginTree.runTree first rest) forest = some next) :
    preorder next = (preorder forest).take (originGap forest origin) ++ (first :: rest) ++
      (preorder forest).drop (originGap forest origin) := by
  have physical := NotionCoreOriginTree.insert_run_indices origin first rest forest ready present
  rw [inserted] at physical
  exact Option.some.inj physical

theorem physical_inserted (inst : Nat) (forest next : Forest) (origin : Id)
    (first : Item) (rest : List Item)
    (ready : NotionCoreOriginTree.DominatesForest origin first.id forest)
    (present : origin ∈ (preorder forest).map Item.id)
    (inserted : NotionCoreOriginTree.insert (.item origin)
      (NotionCoreOriginTree.runTree first rest) forest = some next) :
    physicalSlots inst next =
      (physicalSlots inst forest).take (originGap forest origin) ++
        ((first :: rest).map (NotionCorePhysicalReplay.atom inst)).map NotionCoreSource.Atom.slot ++
        (physicalSlots inst forest).drop (originGap forest origin) := by
  simp only [physicalSlots,inserted_preorder forest next origin first rest ready present inserted,
    List.map_append,List.map_take,List.map_drop]

/-- Every old before-item endpoint moves by the same embedding as the
independent direct-state insertion. Freshness excludes an ID alias in the run. -/
theorem before_anchor_inserted (forest next : Forest) (origin endpoint : Id)
    (first : Item) (rest : List Item)
    (ready : NotionCoreOriginTree.DominatesForest origin first.id forest)
    (present : origin ∈ (preorder forest).map Item.id)
    (fresh : ∀ item ∈ first :: rest, item.id ≠ endpoint)
    (inserted : NotionCoreOriginTree.insert (.item origin)
      (NotionCoreOriginTree.runTree first rest) forest = some next) :
    anchorPosition next ⟨.item endpoint,.before⟩ =
      (anchorPosition forest ⟨.item endpoint,.before⟩).map
        (NotionCoreRichSequential.shift (originGap forest origin) (rest.length + 1)) := by
  rw [anchor_before_findIdx,anchor_before_findIdx,
    inserted_preorder forest next origin first rest ready present inserted]
  simpa only [List.length_cons] using
    findIdx_splice (preorder forest) (first :: rest) (fun item => item.id == endpoint)
      (originGap forest origin) (fun item member => by simpa using fresh item member)

theorem finish_anchor_inserted (forest next : Forest) (origin : Id)
    (first : Item) (rest : List Item)
    (ready : NotionCoreOriginTree.DominatesForest origin first.id forest)
    (present : origin ∈ (preorder forest).map Item.id)
    (inserted : NotionCoreOriginTree.insert (.item origin)
      (NotionCoreOriginTree.runTree first rest) forest = some next) :
    anchorPosition next ⟨.finish,.before⟩ =
      (anchorPosition forest ⟨.finish,.before⟩).map
        (NotionCoreRichSequential.shift (originGap forest origin) (rest.length + 1)) := by
  have gapBound : originGap forest origin ≤ (preorder forest).length := by
    have found := List.idxOf_lt_length_of_mem present
    simp only [List.length_map] at found
    unfold originGap
    omega
  simp only [anchorPosition,Option.map_some,NotionCoreRichSequential.shift,gapBound,↓reduceIte]
  rw [inserted_preorder forest next origin first rest ready present inserted]
  simp only [List.length_append,List.length_take,List.length_cons,List.length_drop]
  congr 1
  omega

#print axioms endpoint_before
#print axioms before_anchor_inserted
#print axioms finish_anchor_inserted

end Sal.MRDTs.Instances.NotionCoreRichCoordinates
