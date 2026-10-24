import Sal.MRDTs.Instances.NotionCoreRichSequentialAtomicBridge
import Sal.MRDTs.Instances.NotionCoreRichCoordinates
import Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
import Sal.MRDTs.Instances.NotionCoreMachineDocument

/-! A structural global simulation relation. The independent state stores only
current text/cell/gap data; its implementation-dependent materialization here
is a proof abstraction, not its transition function or history language. -/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
open NotionCoreSpec
open NotionCoreFormattingSource (Positioned)
open NotionCoreOriginTree (Forest preorder)

/-- The registered physical instance domain is retained explicitly. -/
def Registered (actual : NotionCoreAtomicFormattingMachine.State) (inst : Nat) : Prop :=
  ∃ entry ∈ actual.core.instances, entry.1 = inst

structure Related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) : Prop where
  document : ∃ source, NotionCoreMachineDocument.materializeDocument actual.core = some source ∧
    abstract.document = NotionCoreSourceDocument.project source
  registered : ∀ inst, (∃ text, abstract.texts inst = some text) ↔ Registered actual inst
  physical : ∀ inst text, abstract.texts inst = some text →
    text.items = NotionCoreRichCoordinates.physicalSlots inst (NotionCoreAtomicFormattingMachine.instanceForest actual inst)
  unique : ∀ inst, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest actual inst)
  marks : ∀ inst text, abstract.texts inst = some text →
    AtomicBridge.MarksRelated (NotionCoreAtomicFormattingMachine.instanceForest actual) actual.batches inst text

/-- Materialization computes current observations once. Subsequent abstract
updates use independent direct painting/insertion, never this abstraction. -/
def modelText (actual : NotionCoreAtomicFormattingMachine.State) (inst : Nat) : Text :=
  ⟨NotionCoreRichCoordinates.physicalSlots inst (NotionCoreAtomicFormattingMachine.instanceForest actual inst),
    NotionCoreAtomicFormatting.resolveAt (NotionCoreAtomicFormattingMachine.instanceForest actual) actual.batches inst,
    NotionCoreAtomicFormatting.resolveGapAt (NotionCoreAtomicFormattingMachine.instanceForest actual) actual.batches inst⟩

def materialize (actual : NotionCoreAtomicFormattingMachine.State) : Option State :=
  (NotionCoreMachineDocument.materializeDocument actual.core).map fun source =>
    ⟨NotionCoreSourceDocument.project source,fun inst =>
      if actual.core.instances.any (fun entry => entry.1 == inst) then some (modelText actual inst) else none⟩

theorem materialize_related (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (hmat : materialize actual = some abstract)
    (unique : ∀ inst, NotionCoreFormattingPlanner.UniqueIds (NotionCoreAtomicFormattingMachine.instanceForest actual inst)) :
    Related actual abstract := by
  cases hdoc : NotionCoreMachineDocument.materializeDocument actual.core with
  | none => simp [materialize,hdoc] at hmat
  | some source =>
    simp only [materialize,hdoc,Option.map_some,Option.some.injEq] at hmat
    subst abstract
    constructor
    · exact ⟨source,hdoc,rfl⟩
    · intro inst
      by_cases hreg : actual.core.instances.any (fun entry => entry.1 == inst) = true
      · constructor
        · intro _
          exact List.any_eq_true.mp hreg |>.imp (fun entry h => ⟨h.1,by simpa using h.2⟩)
        · intro _
          exact ⟨modelText actual inst,by simp [hreg]⟩
      · constructor
        · rintro ⟨text,ht⟩
          simp only [hreg] at ht
          contradiction
        · intro hr
          have hb : actual.core.instances.any (fun entry => entry.1 == inst) = true :=
            List.any_eq_true.mpr (by simpa only [beq_iff_eq] using hr)
          exact False.elim (hreg hb)
    · intro inst text ht
      dsimp only at ht
      split at ht
      · cases Option.some.inj ht
        rfl
      · contradiction
    · exact unique
    · intro inst text ht
      dsimp only at ht
      split at ht
      · cases Option.some.inj ht
        exact ⟨fun _ => rfl,fun _ => rfl⟩
      · contradiction

theorem related_initial : Related ({} : NotionCoreAtomicFormattingMachine.State) ({} : State) := by
  apply materialize_related
  · rfl
  · intro inst
    change ([] : List NotionRunAllocation.Id).Nodup
    exact List.nodup_nil

/-- A physical live item is looked up at its actual numbered walk coordinate
on both sides. No final read equality is assumed by the relation. -/
theorem readAt_positioned {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (inst : Nat) (text : Text)
    (ht : abstract.texts inst = some text) (position : Positioned)
    (hp : position ∈ NotionCoreFormattingSource.walk 0 (NotionCoreAtomicFormattingMachine.instanceForest actual inst))
    (value : Nat) (hlive : position.item.kind = .text value false) :
    readAt abstract (NotionCorePhysicalReplay.address inst position.item.id) =
      some (NotionCoreAtomicFormattingMachine.boldAt actual (NotionCorePhysicalReplay.address inst position.item.id)) := by
  have htext : text = ⟨NotionCoreRichCoordinates.physicalSlots inst
      (NotionCoreAtomicFormattingMachine.instanceForest actual inst),text.bold,text.gapBold⟩ :=
    Text.ext (related.physical inst text ht) rfl rfl
  have hend : endpointPosition inst text (.before (NotionCorePhysicalReplay.markerKey position.item.id)) = some position.entry := by
    conv_lhs => rw [htext]
    rw [NotionCoreRichCoordinates.endpoint_before]
    exact NotionCoreFormattingPlanner.anchor_before_entry _ (related.unique inst) position hp
  have hbold := (related.marks inst text ht).1 position.entry
  have hsource := NotionCoreAtomicFormattingMachine.boldAt_positioned actual inst
    (related.unique inst) position hp value hlive
  have hlookup : (text.items.map Slot.address).findIdx? (fun a =>
      a == NotionCorePhysicalReplay.address inst position.item.id) = some position.entry := hend
  unfold readAt
  rw [show (NotionCorePhysicalReplay.address inst position.item.id).1 = inst from rfl,ht]
  simp only [Bind.bind,Option.bind]
  rw [hlookup]
  simp only [Pure.pure]
  rw [hbold,hsource]

end Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
