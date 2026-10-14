import Mathlib.Data.List.Basic

/-! A restricted executable counterpart of the demo's annotation interval rule.
This models one text instance, no hidden characters, no prior annotations,
and one same-instance displayed selection segment. It does not formalize
JavaScript or prove source correspondence. The selection and instance orders
come from separately reproduced reachable split/merge traces.
-/
namespace Sal.MRDTs.Instances.NotionFormattingCounterexample

/-- The ordinary exact-selection specification: format the selected semantic
characters, wherever their block is currently displayed. -/
def ordinaryTargets (displayedSelection : List Nat) : List Nat := displayedSelection

/-- Counterpart of `contiguousSegments` + `annotationAnchors` in the
restricted fixture. One displayed same-instance segment becomes the interval
from before its first character to after its last character, measured in the
instance order. `idxOf last + 1` expresses before the next visible character,
or END. Projecting the full RGA traversal onto text characters removes the
split markers. With no deleted text in these fixtures, the projected order is
the visible instance order used here. Presence and uniqueness hold on literals. -/
def intervalTargets (instanceOrder displayedSelection : List Nat) : List Nat :=
  match displayedSelection with
  | [] => []
  | first :: rest =>
      let last := rest.getLast?.getD first
      let lo := instanceOrder.idxOf first
      let hi := instanceOrder.idxOf last + 1
      (instanceOrder.drop lo).take (hi - lo)

/-- PASS+FAIL: ordinary formatting of the displayed `cb` block selects c,b.
It cannot be explained as selecting no character. Expected values are derived
from the ordinary editing request, independently of `intervalTargets`. -/
theorem ordinary_reordered_selection :
    ordinaryTargets [2, 1] = [2, 1] ∧ ordinaryTargets [2, 1] ≠ [] := by decide

/-- The source-rule counterpart instead chooses an empty interval: before c
and after b denote the same boundary in the underlying abc instance. -/
theorem reordered_selection_empty_interval :
    intervalTargets [0, 1, 2] [2, 1] = [] ∧
    intervalTargets [0, 1, 2] [2, 1] ≠ ordinaryTargets [2, 1] := by decide

/-- Minimized two-character counterpart: concurrent splits at 0 and 1,
followed by merging a into b, produce displayed ba from instance ab.
Selecting ba maps before b to after a, the same underlying boundary. -/
theorem two_character_reversal :
    ordinaryTargets [1, 0] = [1, 0] ∧
    intervalTargets [0, 1] [1, 0] = [] ∧
    intervalTargets [0, 1] [1, 0] ≠ ordinaryTargets [1, 0] := by decide

/-- A second distinguishing case: selecting the displayed ac block spans b in
instance order, although b is displayed in another block. -/
theorem noncontiguous_selection_overformats :
    intervalTargets [0, 1, 2] [0, 2] = [0, 1, 2] ∧
    intervalTargets [0, 1, 2] [0, 2] ≠ ordinaryTargets [0, 2] := by decide

/-- Nearby positive control: the same interval rule formats an ordinary
contiguous same-instance selection correctly and does not always return empty. -/
theorem contiguous_selection_control :
    intervalTargets [0, 1, 2] [1, 2] = ordinaryTargets [1, 2] ∧
    intervalTargets [0, 1, 2] [1, 2] ≠ [] := by decide

#print axioms reordered_selection_empty_interval
#print axioms noncontiguous_selection_overformats
end Sal.MRDTs.Instances.NotionFormattingCounterexample
