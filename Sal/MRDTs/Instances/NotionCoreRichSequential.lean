import Sal.MRDTs.Instances.NotionCoreSpec
import Mathlib.Order.Monotone.Basic

/-! Direct sequential rich text. The state stores current character and gap
marks, not annotations, priorities, transactions or a replay of operations.
A gap before a retained item remains observable after that item is tombstoned.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential
open NotionCoreSpec

structure Range where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def Range.contains (range : Range) (index : Nat) : Bool :=
  decide (range.lower ≤ index ∧ index < range.upper)

/-- Sticky insertion gaps exclude the left endpoint and include the right. -/
def Range.gapContains (range : Range) (gap : Nat) : Bool :=
  decide (range.lower < gap ∧ gap ≤ range.upper)

structure Text where
  items : List Slot
  bold : Nat → Bool
  gapBold : Nat → Bool

theorem Text.ext {a b : Text} (hi : a.items = b.items)
    (hb : a.bold = b.bold) (hg : a.gapBold = b.gapBold) : a = b := by
  cases a; cases b
  cases hi; cases hb; cases hg
  rfl

def Text.plain (items : List Slot) : Text := ⟨items,fun _ => false,fun _ => false⟩

def covered (ranges : List Range) (index : Nat) : Bool := ranges.any (fun r => r.contains index)
def gapCovered (ranges : List Range) (gap : Nat) : Bool := ranges.any (fun r => r.gapContains gap)

/-- One issued Boolean paints the complete interval union atomically. -/
def paint (text : Text) (ranges : List Range) (value : Bool) : Text :=
  {text with
    bold := fun i => if covered ranges i then value else text.bold i
    gapBold := fun g => if gapCovered ranges g then value else text.gapBold g}

/-- Fresh cells inherit the existing insertion gap; the original gap expands
into width+1 gaps with that same value. Command legality checks the gap bound. -/
def insertAt (text : Text) (gap : Nat) (fresh : List Slot) : Text :=
  { items := text.items.take gap ++ fresh ++ text.items.drop gap
    bold := fun i => if i < gap then text.bold i
      else if i < gap + fresh.length then text.gapBold gap else text.bold (i - fresh.length)
    gapBold := fun g => if g < gap then text.gapBold g
      else if g ≤ gap + fresh.length then text.gapBold gap else text.gapBold (g - fresh.length) }

/-- Every retained old item and before-item endpoint moves by this embedding.
END moves by the same rule for a valid insertion gap. -/
def shift (gap width position : Nat) : Nat := if gap ≤ position then position + width else position

def Range.shift (gap width : Nat) (range : Range) : Range :=
  ⟨NotionCoreRichSequential.shift gap width range.lower,
    NotionCoreRichSequential.shift gap width range.upper⟩

theorem shift_strictMono (gap width : Nat) : StrictMono (shift gap width) := by
  intro a b hab
  unfold shift
  split <;> split <;> omega

theorem range_old_membership (gap width : Nat) (range : Range) (index : Nat) :
    (range.shift gap width).contains (shift gap width index) = range.contains index := by
  have h := shift_strictMono gap width
  simp only [Range.shift,Range.contains,h.le_iff_le,h.lt_iff_lt]

theorem range_old_gap_membership (gap width : Nat) (range : Range) (index : Nat) :
    (range.shift gap width).gapContains (shift gap width index) = range.gapContains index := by
  have h := shift_strictMono gap width
  simp only [Range.shift,Range.gapContains,h.le_iff_le,h.lt_iff_lt]

theorem range_new_membership (gap width : Nat) (range : Range) (offset : Nat)
    (h : offset < width) :
    (range.shift gap width).contains (gap + offset) = range.gapContains gap := by
  simp only [Range.shift,Range.contains,Range.gapContains]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold shift
  split <;> split <;> omega

theorem range_new_gap_membership (gap width : Nat) (range : Range) (offset : Nat)
    (h : offset ≤ width) :
    (range.shift gap width).gapContains (gap + offset) = range.gapContains gap := by
  simp only [Range.shift,Range.gapContains]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold shift
  split <;> split <;> omega

theorem covered_old (ranges : List Range) (gap width index : Nat) :
    covered (ranges.map (Range.shift gap width)) (shift gap width index) = covered ranges index := by
  simp only [covered,List.any_map,Function.comp_def,range_old_membership]

theorem gapCovered_old (ranges : List Range) (gap width index : Nat) :
    gapCovered (ranges.map (Range.shift gap width)) (shift gap width index) = gapCovered ranges index := by
  simp only [gapCovered,List.any_map,Function.comp_def,range_old_gap_membership]

theorem covered_new (ranges : List Range) (gap width offset : Nat) (h : offset < width) :
    covered (ranges.map (Range.shift gap width)) (gap + offset) = gapCovered ranges gap := by
  simp only [covered,gapCovered,List.any_map,Function.comp_def,range_new_membership gap width _ offset h]

theorem gapCovered_new (ranges : List Range) (gap width offset : Nat) (h : offset ≤ width) :
    gapCovered (ranges.map (Range.shift gap width)) (gap + offset) = gapCovered ranges gap := by
  simp only [gapCovered,List.any_map,Function.comp_def,range_new_gap_membership gap width _ offset h]

/-- Painting anchored ranges before insertion gives exactly the same direct
state as inserting first and painting the shifted ranges. This includes the
new character marks and all duplicated sticky gap marks. -/
theorem paint_insert_commute (text : Text) (ranges : List Range) (value : Bool)
    (gap : Nat) (fresh : List Slot) :
    insertAt (paint text ranges value) gap fresh =
      paint (insertAt text gap fresh) (ranges.map (Range.shift gap fresh.length)) value := by
  apply Text.ext
  · rfl
  · funext i
    by_cases hleft : i < gap
    · have hs : shift gap fresh.length i = i := by simp [shift,Nat.not_le.mpr hleft]
      have hc := covered_old ranges gap fresh.length i
      rw [hs] at hc
      simp only [insertAt,paint,hleft,hc,↓reduceIte]
    · by_cases hnew : i < gap + fresh.length
      · have hi : i = gap + (i - gap) := by omega
        have hc := covered_new ranges gap fresh.length (i-gap) (by omega)
        rw [← hi] at hc
        simp only [insertAt,paint,hleft,hnew,hc,↓reduceIte]
      · have hs : shift gap fresh.length (i-fresh.length) = i := by
          unfold shift
          split <;> omega
        have hc := covered_old ranges gap fresh.length (i-fresh.length)
        rw [hs] at hc
        simp only [insertAt,paint,hleft,hnew,hc,↓reduceIte]
  · funext i
    by_cases hleft : i < gap
    · have hs : shift gap fresh.length i = i := by simp [shift,Nat.not_le.mpr hleft]
      have hc := gapCovered_old ranges gap fresh.length i
      rw [hs] at hc
      simp only [insertAt,paint,hleft,hc,↓reduceIte]
    · by_cases hnew : i ≤ gap + fresh.length
      · have hi : i = gap + (i - gap) := by omega
        have hc := gapCovered_new ranges gap fresh.length (i-gap) (by omega)
        rw [← hi] at hc
        simp only [insertAt,paint,hleft,hnew,hc,↓reduceIte]
      · have hs : shift gap fresh.length (i-fresh.length) = i := by
          unfold shift
          split <;> omega
        have hc := gapCovered_old ranges gap fresh.length (i-fresh.length)
        rw [hs] at hc
        simp only [insertAt,paint,hleft,hnew,hc,↓reduceIte]

def erase (text : Text) (targets : List Address) : Text :=
  {text with items := text.items.map (eraseSlot targets)}

@[simp] theorem erase_bold (text : Text) (targets : List Address) :
    (erase text targets).bold = text.bold := rfl
@[simp] theorem erase_gapBold (text : Text) (targets : List Address) :
    (erase text targets).gapBold = text.gapBold := rfl

theorem paint_erase_commute (text : Text) (ranges : List Range) (value : Bool)
    (targets : List Address) :
    erase (paint text ranges value) targets = paint (erase text targets) ranges value := rfl

theorem insert_new_bold (text : Text) (gap : Nat) (fresh : List Slot) (offset : Nat)
    (hoffset : offset < fresh.length) :
    (insertAt text gap fresh).bold (gap+offset) = text.gapBold gap := by
  simp only [insertAt]
  split <;> (first | omega | (split <;> (first | rfl | omega)))

theorem insert_new_gapBold (text : Text) (gap : Nat) (fresh : List Slot) (offset : Nat)
    (hoffset : offset ≤ fresh.length) :
    (insertAt text gap fresh).gapBold (gap+offset) = text.gapBold gap := by
  simp only [insertAt]
  split <;> (first | omega | (split <;> (first | rfl | omega)))

theorem insert_old_bold (text : Text) (gap : Nat) (fresh : List Slot) (index : Nat) :
    (insertAt text gap fresh).bold (shift gap fresh.length index) = text.bold index := by
  by_cases h : gap ≤ index
  · have hs : shift gap fresh.length index = index+fresh.length := by simp [shift,h]
    have hleft : ¬ index+fresh.length < gap := by omega
    have hnew : ¬ index+fresh.length < gap+fresh.length := by omega
    simp only [insertAt,hs,if_neg hleft,if_neg hnew,Nat.add_sub_cancel]
  · have hs : shift gap fresh.length index = index := by simp [shift,h]
    have hleft : index < gap := by omega
    simp only [insertAt,hs,if_pos hleft]

theorem insert_old_gapBold (text : Text) (gap : Nat) (fresh : List Slot) (index : Nat) :
    (insertAt text gap fresh).gapBold (shift gap fresh.length index) = text.gapBold index := by
  by_cases h : gap ≤ index
  · have hs : shift gap fresh.length index = index+fresh.length := by simp [shift,h]
    have hleft : ¬ index+fresh.length < gap := by omega
    by_cases heq : index = gap
    · subst index
      simp only [insertAt,hs,if_neg hleft,le_refl,↓reduceIte]
    · have hnew : ¬ index+fresh.length ≤ gap+fresh.length := by omega
      simp only [insertAt,hs,if_neg hleft,if_neg hnew,Nat.add_sub_cancel]
  · have hs : shift gap fresh.length index = index := by simp [shift,h]
    have hleft : index < gap := by omega
    simp only [insertAt,hs,if_pos hleft]

#print axioms paint_insert_commute
#print axioms paint_erase_commute

end Sal.MRDTs.Instances.NotionCoreRichSequential
