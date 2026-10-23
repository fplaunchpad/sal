import Sal.MRDTs.Instances.NotionCoreFormattingSource
import Sal.MRDTs.Instances.NotionFormattingCounterexample

/-! Hand-derived controls for the source formatting rule. These typed
fixtures exercise physical origins and anchor coordinates; the JavaScript
oracle separately establishes reachable displayed selections. `decide` checks
the literal results in Lean's kernel and does not execute an external oracle.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingSourceSPOT
open NotionCoreFormattingSource
open NotionCoreOriginTree (Item Tree Forest)

def a : Item := NotionCoreOriginTree.literal 1 97
def b : Item := NotionCoreOriginTree.literal 2 98
def c : Item := NotionCoreOriginTree.literal 3 99
def splitA : Item := ⟨⟨10, [66]⟩, .split⟩
def splitB : Item := ⟨⟨11, [66]⟩, .split⟩

def abc : Forest := .cons (NotionCoreOriginTree.runTree a [b, c]) .nil
def ab : Forest := .cons (NotionCoreOriginTree.runTree a [b]) .nil

/-- Physical abc with markers before b and c. Split nodes are siblings of
the old following item, as with actual descending-ID RGA insertion. -/
def splitABC : Forest := .cons (.node a
  (.cons (.node splitA .nil)
    (.cons (.node b (.cons (.node splitB .nil) (.cons (.node c .nil) .nil))) .nil))) .nil

def before (item : Item) : Anchor := ⟨.item item.id, .before⟩
def after (item : Item) : Anchor := ⟨.item item.id, .after⟩
def finish : Anchor := ⟨.finish, .before⟩
def mark (counter : Nat) (lo hi : Anchor) (value : Bool) : MarkOp :=
  ⟨⟨counter, [65]⟩, lo, hi, value⟩

def selected (item : Item) (bold : Bool := false) (inst : Nat := 0) : Character :=
  ⟨inst, item, bold⟩

def operationsFor (inst : Nat) (operations : List (Nat × MarkOp)) : List MarkOp :=
  operations.filterMap fun (name, operation) => if name = inst then some operation else none

def toggleOps (forest : Forest) (selection : List Character) : List MarkOp :=
  operationsFor 0 (toggleBold (fun _ => forest) [65] 20 selection)

def values (forest : Forest) (operations : List MarkOp) : List Bool :=
  (resolveRichText forest operations).map Formatted.bold

def boldIds (forest : Forest) (operations : List MarkOp) : List Nat :=
  (resolveRichText forest operations).filterMap fun formatted =>
    if formatted.bold then some formatted.item.id.counter else none

/-- PASS+FAIL: after(a) is after its entire subtree. END and START ignore
the side. Unknown item anchors stay unresolved rather than becoming START. -/
theorem subtree_anchor_control :
    anchorPosition abc (before a) = some 0 ∧
    anchorPosition abc (after a) = some 3 ∧
    anchorPosition abc (after a) ≠ some 1 ∧
    anchorPosition abc ⟨.start, .after⟩ = some 0 ∧
    anchorPosition abc ⟨.finish, .after⟩ = some 3 ∧
    anchorPosition abc (before (NotionCoreOriginTree.literal 99 120)) = none := by
  decide +kernel

/-- PASS+FAIL: explicit anchor has priority over affinity. When neither is
present, JavaScript's before comparison is false and chooses after. -/
theorem anchor_field_precedence_control :
    normalizeSide (some .before) (some .after) = .before ∧
    normalizeSide none (some .before) = .before ∧
    normalizeSide none none = .after ∧
    normalizeSide none none ≠ .before := by decide +kernel

/-- PASS+FAIL, reduced N002: selecting displayed ba collapses to
before(b) ... before(successor(a)=b). The two positions are equal, rather
than numerically reversed. The full source trace establishes displayed ba. -/
theorem N002_reversed_display_collapse :
    (toggleOps ab [selected b, selected a]).map (fun op =>
      (anchorPosition ab op.start, anchorPosition ab op.finish)) = [(some 1, some 1)] ∧
    values ab (toggleOps ab [selected b, selected a]) = [false, false] ∧
    boldIds ab (toggleOps ab [selected b, selected a]) ≠ [2, 1] ∧
    values ab (toggleOps ab [selected b, selected a]) ≠ [true, true] := by
  decide +kernel

def sourceA : Item := ⟨⟨2,[83]⟩, .text 97 false⟩
def sourceB : Item := ⟨⟨3,[83]⟩, .text 98 false⟩
def sourceC : Item := ⟨⟨4,[83]⟩, .text 99 false⟩
def sourceSplit (counter : Nat) (session : Nat) : Item := ⟨⟨counter,[session]⟩,.split⟩

def fullN002 : Forest :=
  .cons (.node (sourceSplit 4 65) .nil)
    (.cons (.node sourceA (.cons (.node (sourceSplit 4 66) .nil)
      (.cons (.node sourceB .nil) .nil))) .nil)

/-- PASS+FAIL: exact typed per-instance N002 source fixture from the offline
design oracle, including S:2/S:3 text IDs and A:4/B:4 markers. Its displayed
ba selection yields the original A:6 annotation before(S:3)..before(S:3).
This is a literal source-instance fixture, not a proved whole-document trace. -/
theorem N002_full_source_fixture :
    let operations := operationsFor 0
      (toggleBold (fun _ => fullN002) [65] 6 [selected sourceB, selected sourceA])
    (walk 0 fullN002).map (fun p => (p.item.id.counter, p.entry, p.exit)) =
      [(4,0,1),(2,1,4),(4,2,3),(3,3,4)] ∧
    operations = [⟨⟨6,[65]⟩, before sourceB, before sourceB, true⟩] ∧
    operations.map (fun op => (anchorPosition fullN002 op.start, anchorPosition fullN002 op.finish)) =
      [(some 3,some 3)] ∧
    values fullN002 operations = [false,false] ∧
    values fullN002 operations ≠ [true,true] := by decide +kernel

/-- PASS+FAIL, N003 projection: displayed ac belongs to one instance, but
its instance interval spans the separately displayed b. Markers contribute
physical indices and are projected out of rich text. -/
theorem N003_noncontiguous_spillover :
    (NotionCoreOriginTree.preorder splitABC).map (fun item => item.id.counter) = [1,10,2,11,3] ∧
    (toggleOps splitABC [selected a, selected c]).map (fun op =>
      (anchorPosition splitABC op.start, anchorPosition splitABC op.finish)) = [(some 0, some 5)] ∧
    boldIds splitABC (toggleOps splitABC [selected a, selected c]) = [1,2,3] ∧
    boldIds splitABC (toggleOps splitABC [selected a, selected c]) ≠ [1,3] := by
  decide +kernel

def fullN003 : Forest := .cons (.node sourceA
  (.cons (.node (sourceSplit 5 65) .nil)
    (.cons (.node sourceB (.cons (.node (sourceSplit 5 66) .nil)
      (.cons (.node sourceC .nil) .nil))) .nil))) .nil

/-- PASS+FAIL: exact typed per-instance N003 design-oracle fixture. The
single A:7 operation reaches the unselected S:3 at physical position 2. -/
theorem N003_full_source_fixture :
    let operations := operationsFor 0
      (toggleBold (fun _ => fullN003) [65] 7 [selected sourceA, selected sourceC])
    (walk 0 fullN003).map (fun p => (p.item.id.counter, p.entry, p.exit)) =
      [(2,0,5),(5,1,2),(3,2,5),(5,3,4),(4,4,5)] ∧
    operations = [⟨⟨7,[65]⟩, before sourceA, finish, true⟩] ∧
    values fullN003 operations = [true,true,true] ∧
    values fullN003 operations ≠ [true,false,true] := by decide +kernel

/-- PASS+FAIL: the original rule works for an ordinary contiguous displayed
selection; the negative excludes an always-empty interpretation. -/
theorem contiguous_selection_control :
    boldIds abc (toggleOps abc [selected b, selected c]) = [2,3] ∧
    boldIds abc (toggleOps abc [selected b, selected c]) ≠ [] := by
  decide +kernel

/-- PASS+FAIL: actual reversed numeric boundaries and missing endpoints
produce no effect. Equal-boundary N002 is covered separately above. -/
theorem reversed_and_missing_noop_control :
    values abc [mark 20 (before c) (before a) true] = [false,false,false] ∧
    values abc [mark 20 (before c) (before a) true] ≠ [true,true,true] ∧
    values abc [mark 20 (before (NotionCoreOriginTree.literal 99 120)) finish true] =
      [false,false,false] := by
  decide +kernel

/-- PASS+FAIL: overlapping add/remove/add resolve per character by the last
covering Lamport ID, independent of the input operation order. a is covered
only by the first add, b by the remove, and c by the final add. -/
theorem overlapping_add_remove_control :
    let addAB := mark 20 (before a) (before c) true
    let removeBC := mark 21 (before b) finish false
    let addC := mark 22 (before c) finish true
    values abc [addC, addAB, removeBC] = [true,false,true] ∧
    values abc [removeBC, addC, addAB] = [true,false,true] ∧
    values abc [addC, addAB, removeBC] ≠ [true,true,true] ∧
    values abc [addC, addAB, removeBC] ≠ [false,false,true] := by
  decide +kernel

/-- PASS+FAIL: counter ties use UTF-16 session order. A later removal
overwrites an earlier add, even if the add comes last in the input list. -/
theorem session_tiebreak_control :
    let addA := mark 20 (before a) (before b) true
    let removeA : MarkOp := ⟨⟨20,[66]⟩, before a, before b, false⟩
    values abc [removeA, addA] = [false,false,false] ∧
    values abc [removeA, addA] ≠ [true,false,false] := by
  decide +kernel

/-- PASS+FAIL: the verdict is computed over the entire selection before
segmentation. Every segment removes only when every selected character was
bold; mixed bold states make every emitted segment an add. -/
theorem atomic_toggle_segments_control :
    (toggleBold (fun _ => abc) [65] 20
      [selected a true 0, selected b true 1, selected c true 0]).map
      (fun pair => (pair.1, pair.2.id.counter, pair.2.value)) =
        [(0,20,false),(1,21,false),(0,22,false)] ∧
    (toggleBold (fun _ => abc) [65] 20
      [selected a true 0, selected b false 1, selected c true 0]).map
      (fun pair => pair.2.value) = [true,true,true] ∧
    (toggleBold (fun _ => abc) [65] 20
      [selected a true 0, selected b false 1, selected c true 0]).map
      (fun pair => pair.2.value) ≠ [false,true,false] ∧
    toggleBold (fun _ => abc) [65] 20 [] = [] := by
  decide +kernel

/-- PASS+FAIL: one multi-segment atomic add may include overlapping intervals
in the same instance. Existing removals at lower Lamport IDs do not suppress
that later assignment. The intermediate other-instance segment stays separate. -/
theorem atomic_overlap_control :
    let operations := toggleOps abc
      [selected a, selected c, selected a false 1, selected b]
    operations.length = 2 ∧
    values abc (mark 19 ⟨.start,.before⟩ finish false :: operations) = [true,true,true] ∧
    values abc (mark 19 ⟨.start,.before⟩ finish false :: operations) ≠ [true,false,true] := by
  decide +kernel

def hidden : Forest := .cons (NotionCoreOriginTree.runTree a
  [NotionCoreOriginTree.literal 2 98 true, splitA, c]) .nil

/-- PASS+FAIL: source annotation endpoints skip hidden characters/markers
when finding the next visible item, but physical containment retains both.
An add of visible a stops before c, excluding that visible successor. -/
theorem hidden_marker_control :
    nextVisible hidden a.id = some c ∧
    (annotationAnchors hidden a a).2 = before c ∧
    values hidden (toggleOps hidden [selected a]) = [true,false] ∧
    values hidden (toggleOps hidden [selected a]) ≠ [true,true] ∧
    covers hidden ((toggleOps hidden [selected a])[0]?.getD (mark 0 finish finish false)) 1 = true ∧
    covers hidden ((toggleOps hidden [selected a])[0]?.getD (mark 0 finish finish false)) 2 = true := by
  decide +kernel

def insertedX : Item := NotionCoreOriginTree.literal 30 120
def afterInsert : Forest := .cons (.node a (.cons (.node insertedX .nil)
  (.cons (NotionCoreOriginTree.runTree b [c]) .nil))) .nil

/-- PASS+FAIL: existing source anchors are resolved again after insertion.
Insertion immediately before the old end successor inherits an add ending
there; insertion before the start item does not. No exact-ID repair is used. -/
theorem endpoint_inheritance_control :
    values afterInsert [mark 20 (before a) (before b) true] = [true,true,false,false] ∧
    values afterInsert [mark 20 (before a) (before b) true] ≠ [true,false,false,false] ∧
    values afterInsert [mark 20 (before b) finish true] = [false,false,true,true] ∧
    values afterInsert [mark 20 (before b) finish true] ≠ [false,true,true,true] := by decide +kernel

#print axioms N002_reversed_display_collapse
#print axioms N003_noncontiguous_spillover
#print axioms N002_full_source_fixture
#print axioms N003_full_source_fixture
#print axioms overlapping_add_remove_control
end Sal.MRDTs.Instances.NotionCoreFormattingSourceSPOT
