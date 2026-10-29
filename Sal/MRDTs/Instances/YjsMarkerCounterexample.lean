import Mathlib.Data.List.Basic

/-! A restricted executable counterpart of one measured Yjs rich-text execution.

Research question: is Yjs's marker-based formatting of `Y.Text` RA-linearizable
against the ordinary sequential specification of formatting, where a format
request sets one attribute on the characters its range contains?

Source: Yjs 13.6.31, measured in `experiments/yjs-oracle/results/facts.json`,
fact d (concurrent bold `[0,2)` and unbold `[1,3)` over `a b* c`). The item
lists below are the measured item lists, restricted to the `bold` key.

Yjs renders formatting from marker items interleaved with characters. A
left-to-right walk keeps the current value of `bold`; a live marker sets it
(`some true`) or clears it (`none`); a character takes the current value;
deleted markers are skipped. Formatting a range deletes live markers of the
same key inside the range, inserts an opening marker before the range only
when the current value differs, and inserts a closing marker after the range
only when the walk did not meet an opening marker of equal value inside it.

This module is a semantic counterpart of the measured execution: it fixes the
three item lists and the rendering walk, and compares the merged rendering with
the two sequential outcomes. It does not model Yjs's integration algorithm or
prove source correspondence.
-/
namespace Sal.MRDTs.Instances.YjsMarkerCounterexample

/-- An item identifier: client and clock. -/
abbrev ItemId := Nat × Nat

/-- A `Y.Text` item restricted to the `bold` key: a character, or a format
marker whose value is `some true` (bold) or `none` (clear). -/
inductive Entry where
  | char (ch : Char) (id : ItemId)
  | marker (value : Option Bool) (id : ItemId) (deleted : Bool)
  deriving DecidableEq

/-- The rendering walk, starting from a current value. -/
def renderFrom : Option Bool → List Entry → List (Char × Bool)
  | _, [] => []
  | cur, .char ch _ :: rest => (ch, cur == some true) :: renderFrom cur rest
  | cur, .marker _ _ true :: rest => renderFrom cur rest
  | _, .marker v _ false :: rest => renderFrom v rest

/-- Yjs's rendering of an item list: each character with its `bold` value. -/
def render (items : List Entry) : List (Char × Bool) := renderFrom none items

/-! ## Sequential specification -/

/-- The specification state: each character with its `bold` mark. Without
insertions, identity-bounded intervals coincide with index ranges. -/
abbrev Spec := List (Char × Bool)

/-- Set the mark of every character whose index lies in `[lo, hi)` to `b`. -/
def setRange (b : Bool) (lo hi : Nat) (s : Spec) : Spec :=
  s.mapIdx fun i p => if lo ≤ i ∧ i < hi then (p.1, b) else p

def boldRange (lo hi : Nat) (s : Spec) : Spec := setRange true lo hi s
def unboldRange (lo hi : Nat) (s : Spec) : Spec := setRange false lo hi s

/-- `a b* c`. -/
def initialSpec : Spec := [('a', false), ('b', true), ('c', false)]

/-! ## The measured item lists -/

/-- Client 1's document: `a`, bold (1:3), `b`, clear (1:4), `c`. -/
def initial : List Entry :=
  [.char 'a' (1, 0), .marker (some true) (1, 3) false, .char 'b' (1, 1),
   .marker none (1, 4) false, .char 'c' (1, 2)]

/-- Replica 10 after bolding `[0,2)`: opening marker 10:0 before `a`, 1:3
deleted (equal opening value met inside the range), no closing marker. -/
def local10 : List Entry :=
  [.marker (some true) (10, 0) false, .char 'a' (1, 0),
   .marker (some true) (1, 3) true, .char 'b' (1, 1),
   .marker none (1, 4) false, .char 'c' (1, 2)]

/-- Replica 11 after unbolding `[1,3)`: no opening marker (plain before `b`),
1:3 and 1:4 deleted. -/
def local11 : List Entry :=
  [.char 'a' (1, 0), .marker (some true) (1, 3) true, .char 'b' (1, 1),
   .marker none (1, 4) true, .char 'c' (1, 2)]

/-- Both replicas after exchange: 10:0 inserted, 1:3 and 1:4 deleted. -/
def merged : List Entry :=
  [.marker (some true) (10, 0) false, .char 'a' (1, 0),
   .marker (some true) (1, 3) true, .char 'b' (1, 1),
   .marker none (1, 4) true, .char 'c' (1, 2)]

/-! ## SPOTs -/

/-- PASS+FAIL: the initial list renders `a b* c`, not all plain. -/
theorem initial_render :
    render initial = initialSpec ∧
    render initial ≠ [('a', false), ('b', false), ('c', false)] := by decide

/-- PASS+FAIL: each local effect agrees with the specification applied to the
initial state, and neither request is a no-op. -/
theorem local_effects :
    render local10 = [('a', true), ('b', true), ('c', false)] ∧
    boldRange 0 2 initialSpec = [('a', true), ('b', true), ('c', false)] ∧
    render local11 = [('a', false), ('b', false), ('c', false)] ∧
    unboldRange 1 3 initialSpec = [('a', false), ('b', false), ('c', false)] ∧
    render local10 ≠ initialSpec ∧ render local11 ≠ initialSpec := by decide

/-- The merged list renders all three characters bold. It is neither replica's
local rendering. -/
theorem merged_render :
    render merged = [('a', true), ('b', true), ('c', true)] ∧
    render merged ≠ render local10 ∧ render merged ≠ render local11 := by decide

/-- The two sequential outcomes: bold then unbold, and unbold then bold. -/
theorem sequential_outcomes :
    unboldRange 1 3 (boldRange 0 2 initialSpec) =
      [('a', true), ('b', false), ('c', false)] ∧
    boldRange 0 2 (unboldRange 1 3 initialSpec) =
      [('a', true), ('b', true), ('c', false)] ∧
    unboldRange 1 3 (boldRange 0 2 initialSpec) ≠
      boldRange 0 2 (unboldRange 1 3 initialSpec) := by decide

/-- No linear extension of the two concurrent requests explains the merged
rendering, so the execution is not RA-linearizable against the sequential
specification. -/
theorem merged_not_sequential :
    render merged ≠ unboldRange 1 3 (boldRange 0 2 initialSpec) ∧
    render merged ≠ boldRange 0 2 (unboldRange 1 3 initialSpec) := by decide

/-- `c` (index 2) lies in neither bold range, yet ends bold: it was plain
initially, and the only request whose range contains it unbolds. -/
theorem c_bold_outside_ranges :
    ¬ (0 ≤ 2 ∧ 2 < 2) ∧
    (render merged)[2]? = some ('c', true) ∧
    initialSpec[2]? = some ('c', false) := by decide

/-- Control: had replica 10 emitted its own closing marker 10:1 after `b`, the
merged rendering would be the unbold-then-bold outcome. The missing closer is
the cause. -/
def mergedWithCloser : List Entry :=
  [.marker (some true) (10, 0) false, .char 'a' (1, 0),
   .marker (some true) (1, 3) true, .char 'b' (1, 1),
   .marker none (10, 1) false,
   .marker none (1, 4) true, .char 'c' (1, 2)]

theorem closer_control :
    render mergedWithCloser = [('a', true), ('b', true), ('c', false)] ∧
    render mergedWithCloser = boldRange 0 2 (unboldRange 1 3 initialSpec) ∧
    render mergedWithCloser ≠ render merged := by decide

/-- Control: with 1:4 live (replica 11's deletion of it absent), the rendering
is again the unbold-then-bold outcome, so the bold leak into `c` needs that
deletion. -/
def mergedCloserLive : List Entry :=
  [.marker (some true) (10, 0) false, .char 'a' (1, 0),
   .marker (some true) (1, 3) true, .char 'b' (1, 1),
   .marker none (1, 4) false, .char 'c' (1, 2)]

theorem live_closer_control :
    render mergedCloserLive = [('a', true), ('b', true), ('c', false)] ∧
    render mergedCloserLive ≠ render merged := by decide

#print axioms merged_not_sequential
#print axioms closer_control
#print axioms live_closer_control
end Sal.MRDTs.Instances.YjsMarkerCounterexample
