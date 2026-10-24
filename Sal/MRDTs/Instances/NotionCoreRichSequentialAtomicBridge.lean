import Sal.MRDTs.Instances.NotionCoreRichSequentialDocument
import Sal.MRDTs.Instances.NotionCoreAtomicFormatting

/-! Simulation lemmas between direct character/gap painting and the repaired
anchored-annotation renderer. The independent state contains no annotation log.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.AtomicBridge
open NotionCoreOriginTree (Forest)

/-- Scalar intervals are a transient interpretation of current stable anchors,
not retained state or an alternative sequential replay specification. -/
def segmentRange (forests : Nat → Forest) (inst : Nat) (segment : NotionCoreAtomicFormatting.Segment) : Option Range :=
  if segment.instanceId = inst then
    match NotionCoreFormattingSource.anchorPosition (forests inst) segment.lower,
        NotionCoreFormattingSource.anchorPosition (forests inst) segment.upper with
    | some lo,some hi => some ⟨lo,hi⟩
    | _,_ => none
  else none

def rangesFor (forests : Nat → Forest) (inst : Nat) (segments : List NotionCoreAtomicFormatting.Segment) : List Range :=
  segments.filterMap (segmentRange forests inst)

theorem segment_coverage (forests : Nat → Forest) (inst : Nat)
    (segment : NotionCoreAtomicFormatting.Segment) (index : Nat) :
    (segmentRange forests inst segment).any (fun r => r.contains index) =
      NotionCoreAtomicFormatting.segmentCovers forests segment inst index := by
  by_cases h : segment.instanceId = inst
  · have hb : (segment.instanceId == inst) = true := beq_iff_eq.mpr h
    simp only [segmentRange,if_pos h,NotionCoreAtomicFormatting.segmentCovers,hb,Bool.true_and,
      NotionCoreFormattingSource.covers,NotionCoreAtomicFormatting.Segment.operation]
    cases NotionCoreFormattingSource.anchorPosition (forests inst) segment.lower <;>
      cases NotionCoreFormattingSource.anchorPosition (forests inst) segment.upper <;> rfl
  · have hb : (segment.instanceId == inst) = false := by simp only [beq_eq_false_iff_ne]; exact h
    simp only [segmentRange,if_neg h,NotionCoreAtomicFormatting.segmentCovers,hb,Bool.false_and,Option.any_none]

theorem segment_gap_coverage (forests : Nat → Forest) (inst : Nat)
    (segment : NotionCoreAtomicFormatting.Segment) (gap : Nat) :
    (segmentRange forests inst segment).any (fun r => r.gapContains gap) =
      NotionCoreAtomicFormatting.segmentGapCovers forests segment inst gap := by
  by_cases h : segment.instanceId = inst
  · have hb : (segment.instanceId == inst) = true := beq_iff_eq.mpr h
    simp only [segmentRange,if_pos h,NotionCoreAtomicFormatting.segmentGapCovers,hb,Bool.true_and]
    cases NotionCoreFormattingSource.anchorPosition (forests inst) segment.lower <;>
      cases NotionCoreFormattingSource.anchorPosition (forests inst) segment.upper <;> rfl
  · have hb : (segment.instanceId == inst) = false := by simp only [beq_eq_false_iff_ne]; exact h
    simp only [segmentRange,if_neg h,NotionCoreAtomicFormatting.segmentGapCovers,hb,Bool.false_and,Option.any_none]

theorem ranges_coverage (forests : Nat → Forest) (inst : Nat) (segments : List NotionCoreAtomicFormatting.Segment) (index : Nat) :
    covered (rangesFor forests inst segments) index =
      segments.any (fun segment => NotionCoreAtomicFormatting.segmentCovers forests segment inst index) := by
  simp only [covered,rangesFor,List.any_filterMap]
  apply congrArg (fun f => segments.any f)
  funext segment
  exact segment_coverage forests inst segment index

theorem ranges_gap_coverage (forests : Nat → Forest) (inst : Nat) (segments : List NotionCoreAtomicFormatting.Segment) (gap : Nat) :
    gapCovered (rangesFor forests inst segments) gap =
      segments.any (fun segment => NotionCoreAtomicFormatting.segmentGapCovers forests segment inst gap) := by
  simp only [gapCovered,rangesFor,List.any_filterMap]
  apply congrArg (fun f => segments.any f)
  funext segment
  exact segment_gap_coverage forests inst segment gap

/-- Both current characters and insertion gaps are related. A character-only
relation cannot justify inheritance of identities that do not yet exist. -/
def MarksRelated (forests : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch) (inst : Nat) (text : Text) : Prop :=
  (∀ index, text.bold index = NotionCoreAtomicFormatting.resolveAt forests batches inst index) ∧
  (∀ gap, text.gapBold gap = NotionCoreAtomicFormatting.resolveGapAt forests batches inst gap)

theorem paint_refines_latest (forests : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (latest : NotionCoreAtomicFormatting.Batch) (inst : Nat) (text : Text)
    (related : MarksRelated forests batches inst text)
    (fresh : ∀ old ∈ batches, NotionRunAllocation.Before old.priority latest.priority) :
    MarksRelated forests (batches ++ [latest]) inst
      (paint text (rangesFor forests inst latest.segments) latest.value) := by
  constructor
  · intro index
    simp only [paint,ranges_coverage,NotionCoreAtomicFormatting.resolve_latest_at forests batches latest fresh,
      NotionCoreAtomicFormatting.covers,related.1 index]
  · intro gap
    simp only [paint,ranges_gap_coverage,NotionCoreAtomicFormatting.resolve_latest_gap forests batches latest fresh,
      NotionCoreAtomicFormatting.gapCovers,related.2 gap]

private theorem ordered_congr (batches : List NotionCoreAtomicFormatting.Batch)
    (f g : NotionCoreAtomicFormatting.Batch → Bool) (initial : Bool)
    (h : ∀ batch ∈ batches, f batch = g batch) :
    NotionCoreAtomicFormatting.applyOrdered f batches initial =
      NotionCoreAtomicFormatting.applyOrdered g batches initial := by
  induction batches generalizing initial with
  | nil => rfl
  | cons batch rest ih =>
    have hfirst := h batch (by simp)
    have hrest : ∀ batch ∈ rest, f batch = g batch := fun batch hb => h batch (by simp [hb])
    simpa only [NotionCoreAtomicFormatting.applyOrdered,List.foldl_cons,hfirst] using ih _ hrest

private theorem resolve_congr (batches : List NotionCoreAtomicFormatting.Batch)
    (f g : NotionCoreAtomicFormatting.Batch → Bool)
    (h : ∀ batch ∈ batches, f batch = g batch) :
    NotionCoreAtomicFormatting.resolveWith f batches = NotionCoreAtomicFormatting.resolveWith g batches := by
  apply ordered_congr
  intro batch hb
  exact h batch ((NotionCoreAtomicFormatting.sort_perm batches).mem_iff.mp hb)

/-- Only endpoint coordinates are transported. This is not an assumed rich
query equation; the renderer simulation below follows from the gap algebra. -/
def CoordinatesShift (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap width : Nat) : Prop :=
  ∀ batch ∈ batches, rangesFor new inst batch.segments =
    (rangesFor old inst batch.segments).map (Range.shift gap width)

theorem segmentRange_shift (old new : Nat → Forest) (inst gap width : Nat)
    (segment : NotionCoreAtomicFormatting.Segment)
    (h : segment.instanceId = inst →
      NotionCoreFormattingSource.anchorPosition (new inst) segment.lower =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.lower).map (shift gap width) ∧
      NotionCoreFormattingSource.anchorPosition (new inst) segment.upper =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.upper).map (shift gap width)) :
    segmentRange new inst segment = (segmentRange old inst segment).map (Range.shift gap width) := by
  by_cases hi : segment.instanceId = inst
  · obtain ⟨hlo,hhi⟩ := h hi
    simp only [segmentRange,if_pos hi,hlo,hhi]
    cases NotionCoreFormattingSource.anchorPosition (old inst) segment.lower <;>
      cases NotionCoreFormattingSource.anchorPosition (old inst) segment.upper <;> rfl
  · simp only [segmentRange,if_neg hi,Option.map_none]

theorem rangesFor_shift (old new : Nat → Forest) (inst gap width : Nat)
    (segments : List NotionCoreAtomicFormatting.Segment)
    (h : ∀ segment ∈ segments, segment.instanceId = inst →
      NotionCoreFormattingSource.anchorPosition (new inst) segment.lower =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.lower).map (shift gap width) ∧
      NotionCoreFormattingSource.anchorPosition (new inst) segment.upper =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.upper).map (shift gap width)) :
    rangesFor new inst segments = (rangesFor old inst segments).map (Range.shift gap width) := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
    have hfirst := segmentRange_shift old new inst gap width segment (h segment (by simp))
    have hrest : ∀ segment ∈ rest, segment.instanceId = inst →
      NotionCoreFormattingSource.anchorPosition (new inst) segment.lower =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.lower).map (shift gap width) ∧
      NotionCoreFormattingSource.anchorPosition (new inst) segment.upper =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.upper).map (shift gap width) :=
      fun segment hs => h segment (by simp [hs])
    have ihtail := ih hrest
    simp only [rangesFor] at ihtail
    simp only [rangesFor,List.filterMap_cons,hfirst]
    cases segmentRange old inst segment <;> simp only [Option.map_none,Option.map_some,List.map_cons,ihtail]

theorem coordinatesShift_of_endpoints (old new : Nat → Forest)
    (batches : List NotionCoreAtomicFormatting.Batch) (inst gap width : Nat)
    (h : ∀ batch ∈ batches, ∀ segment ∈ batch.segments, segment.instanceId = inst →
      NotionCoreFormattingSource.anchorPosition (new inst) segment.lower =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.lower).map (shift gap width) ∧
      NotionCoreFormattingSource.anchorPosition (new inst) segment.upper =
        (NotionCoreFormattingSource.anchorPosition (old inst) segment.upper).map (shift gap width)) :
    CoordinatesShift old new batches inst gap width := by
  intro batch hb
  exact rangesFor_shift old new inst gap width batch.segments (h batch hb)

theorem resolve_old_character (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap width index : Nat) (h : CoordinatesShift old new batches inst gap width) :
    NotionCoreAtomicFormatting.resolveAt new batches inst (shift gap width index) =
      NotionCoreAtomicFormatting.resolveAt old batches inst index := by
  apply resolve_congr
  intro batch hb
  change batch.segments.any _ = batch.segments.any _
  rw [← ranges_coverage,← ranges_coverage,h batch hb,covered_old]

theorem resolve_new_character (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap width offset : Nat) (hoffset : offset < width)
    (h : CoordinatesShift old new batches inst gap width) :
    NotionCoreAtomicFormatting.resolveAt new batches inst (gap+offset) =
      NotionCoreAtomicFormatting.resolveGapAt old batches inst gap := by
  apply resolve_congr
  intro batch hb
  change batch.segments.any _ = batch.segments.any _
  rw [← ranges_coverage,← ranges_gap_coverage,h batch hb,covered_new _ _ _ _ hoffset]

theorem resolve_old_gap (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap width index : Nat) (h : CoordinatesShift old new batches inst gap width) :
    NotionCoreAtomicFormatting.resolveGapAt new batches inst (shift gap width index) =
      NotionCoreAtomicFormatting.resolveGapAt old batches inst index := by
  apply resolve_congr
  intro batch hb
  change batch.segments.any _ = batch.segments.any _
  rw [← ranges_gap_coverage,← ranges_gap_coverage,h batch hb,gapCovered_old]

theorem resolve_new_gap (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap width offset : Nat) (hoffset : offset ≤ width)
    (h : CoordinatesShift old new batches inst gap width) :
    NotionCoreAtomicFormatting.resolveGapAt new batches inst (gap+offset) =
      NotionCoreAtomicFormatting.resolveGapAt old batches inst gap := by
  apply resolve_congr
  intro batch hb
  change batch.segments.any _ = batch.segments.any _
  rw [← ranges_gap_coverage,← ranges_gap_coverage,h batch hb,gapCovered_new _ _ _ _ hoffset]

/-- A physical insertion preserves the direct-state/renderer relation, including
future insertion gaps. The structural source endpoint embedding is its only
new premise; no resulting character or gap query equality is supplied. -/
theorem insert_refines (old new : Nat → Forest) (batches : List NotionCoreAtomicFormatting.Batch)
    (inst gap : Nat) (fresh : List NotionCoreSpec.Slot) (text : Text)
    (related : MarksRelated old batches inst text)
    (coordinates : CoordinatesShift old new batches inst gap fresh.length) :
    MarksRelated new batches inst (insertAt text gap fresh) := by
  have hold : ∀ index, (insertAt text gap fresh).bold (shift gap fresh.length index) =
      NotionCoreAtomicFormatting.resolveAt new batches inst (shift gap fresh.length index) := by
    intro index
    rw [insert_old_bold,related.1 index,resolve_old_character old new batches _ _ _ _ coordinates]
  have hnew : ∀ offset, offset < fresh.length → (insertAt text gap fresh).bold (gap+offset) =
      NotionCoreAtomicFormatting.resolveAt new batches inst (gap+offset) := by
    intro offset ho
    rw [insert_new_bold _ _ _ _ ho,related.2 gap,
      resolve_new_character old new batches _ _ _ _ ho coordinates]
  have holdgap : ∀ index, (insertAt text gap fresh).gapBold (shift gap fresh.length index) =
      NotionCoreAtomicFormatting.resolveGapAt new batches inst (shift gap fresh.length index) := by
    intro index
    rw [insert_old_gapBold,related.2 index,resolve_old_gap old new batches _ _ _ _ coordinates]
  have hnewgap : ∀ offset, offset ≤ fresh.length → (insertAt text gap fresh).gapBold (gap+offset) =
      NotionCoreAtomicFormatting.resolveGapAt new batches inst (gap+offset) := by
    intro offset ho
    rw [insert_new_gapBold _ _ _ _ ho,related.2 gap,
      resolve_new_gap old new batches _ _ _ _ ho coordinates]
  constructor
  · intro i
    by_cases hleft : i < gap
    · have hs : shift gap fresh.length i = i := by simp [shift,Nat.not_le.mpr hleft]
      simpa only [hs] using hold i
    · by_cases hinside : i < gap+fresh.length
      · have hi : gap+(i-gap)=i := by omega
        simpa only [hi] using hnew (i-gap) (by omega)
      · have hi : shift gap fresh.length (i-fresh.length)=i := by unfold shift; split <;> omega
        simpa only [hi] using hold (i-fresh.length)
  · intro i
    by_cases hleft : i < gap
    · have hs : shift gap fresh.length i = i := by simp [shift,Nat.not_le.mpr hleft]
      simpa only [hs] using holdgap i
    · by_cases hinside : i ≤ gap+fresh.length
      · have hi : gap+(i-gap)=i := by omega
        simpa only [hi] using hnewgap (i-gap) (by omega)
      · have hi : shift gap fresh.length (i-fresh.length)=i := by unfold shift; split <;> omega
        simpa only [hi] using holdgap (i-fresh.length)

#print axioms paint_refines_latest
#print axioms insert_refines

end Sal.MRDTs.Instances.NotionCoreRichSequential.AtomicBridge
