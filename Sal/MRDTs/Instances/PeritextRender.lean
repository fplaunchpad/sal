import Sal.MRDTs.Instances.EmbedRGA

/-!
# Peritext: the DOCUMENT-ORDER mark read model, and the leak the tree-ancestry
read hides

Companion design + validation: `whiteboard/peritext-read-model-note.md` (§8 gives
the exact theorem statements) and the executable reference
`whiteboard/litmus/peritext_read_model.py` (passes end to end).

A `mark_*_no_leak` theorem asserting formatting never leaks under deletion is
false for the `Peritext_Composed/` frozen-path read (`Peritext_Composed/MarkIntent.lean`
states the honest containment bound `mark_*_within_recorded_ancestry` in its
place). The cause: the frozen-path `resolve` climbs TREE ancestry, and a tree
ancestor sits EARLIER in reading order than its descendants, so a dead
boundary anchor migrates BACKWARD in the document and formats text that was
never in the span.

This file builds the paper-faithful alternative, a DOCUMENT-ORDER read model,
directly on the embed-RGA reading order, validates it on the Litt et al.
examples (§7), exhibits the retracted leak concretely against it as a labelled
control (§8), and records the atomicity price the tombstone-free substrate
charges (§9, the trilemma horn made honest).

## The model

Characters live in embed-RGA reading order (the state's own sorted order; the
embed capstone gives the live read = birth order minus survivors).  A **mark**
is a separate immutable record `(mid, mtype, value, op, start_id, end_id,
startSide, endSide)`, it is NOT an in-sequence boundary node (contrast the
FUSED design of `PeritextEmbed.lean`).  The document-order resolver rehomes a
DEAD boundary anchor to the nearest SURVIVING neighbour in READING order on the
gravity side (NOT by climbing tree ancestry), so a single-replica rehome can
only shrink or hold a span, never migrate it backward.

**Growth is END-side only** (the one design decision to carry in, validated):
an end with `endSide = after` grows right over the newer-than-mark run; an end
with `endSide = before` does not; a start is stable (a `before` start does NOT
grow left, else it over-grabs unrelated newer siblings and diverges from the
paper).  This keeps the read equal to naive marked-text semantics absent
deletion.  "Newer than the mark" = character id `> mid` (the RGA opId tiebreak).
-/

namespace Sal.MRDTs.Instances.PeritextRender

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode unaryCode)
open Sal.MRDTs.Instances.EmbedRGA

/-! ## §1  The mark record and the document -/

/-- Mark types, WITHOUT their per-mark value (a link url / colour lives in the
`value` field): last-writer-wins is per `(character, mtype)`, so the type key
must not carry the value. -/
inductive MType
  | bold | italic | underline | strike | link | comment | color | heading
  deriving DecidableEq, Repr

/-- Boundary gravity: `before` (the boundary sits at the anchor's left edge),
`after` (the anchor's right edge). -/
inductive Side
  | before | after
  deriving DecidableEq, Repr

/-- A mark op: `add` formats, `remove` (removeMark) does not; resolved
last-writer-wins by `mid` per `(character, mtype)`. -/
inductive MarkOp
  | add | remove
  deriving DecidableEq, Repr

/-- A mark: immutable data carried by the mark op.  `mid` is the mark's creation
opId (same Lamport space as character ids).  `start_path`/`end_path` are the
frozen recorded ancestry snapshots used ONLY by the tree-ancestry control (§4);
the document-order resolver ignores them. -/
structure MarkD where
  mid : ℕ
  mtype : MType
  op : MarkOp := MarkOp.add
  value : ℕ := 0
  start_id : ℕ
  end_id : ℕ
  startSide : Side := Side.before
  endSide : Side := Side.after
  start_path : List ℕ := []
  end_path : List ℕ := []

/-- The document: an embed-RGA "birth" state (`shadow`, all inserts, payload =
codepoint) plus a set of logically `deleted` ids.  Mirrors the Python `Doc`:
the live read is the birth order minus survivors (the embed capstone's P3), and
the birth order is exactly what a dead boundary needs to rehome and (for the
control) to climb. -/
structure DocD where
  shadow : EState ℕ
  deleted : List ℕ := []

namespace DocD

/-- The birth order: every insert, in embed reading order. -/
def birthIds (d : DocD) : List ℕ := d.shadow.map Prod.fst

/-- Live?, a birth id that has not been deleted. -/
def isLive (d : DocD) (c : ℕ) : Bool := d.birthIds.contains c && !d.deleted.contains c

/-- The live reading order: birth order minus deleted. -/
def liveIds (d : DocD) : List ℕ := d.birthIds.filter (fun c => !d.deleted.contains c)

/-- The codepoint of a birth id (0 if absent). -/
def cp (d : DocD) (c : ℕ) : ℕ := ((d.shadow.find? (fun r => r.1 == c)).map (fun r => r.2.1)).getD 0

end DocD

/-! ## §2  List helpers (nearest-survivor scan, newer-run skip) -/

/-- Index of `a` in `l` (`l.length` if absent). -/
def idxOf (l : List ℕ) (a : ℕ) : ℕ := l.findIdx (fun c => c == a)

/-- Nearest live id strictly RIGHT of birth position `i` (scanning into higher
positions), or `none`. -/
def scanRight (bd del : List ℕ) (i : ℕ) : Option ℕ :=
  (bd.drop (i + 1)).find? (fun c => !del.contains c)

/-- Nearest live id strictly LEFT of birth position `i`, or `none`. -/
def scanLeft (bd del : List ℕ) (i : ℕ) : Option ℕ :=
  (bd.take i).reverse.find? (fun c => !del.contains c)

/-- Count of contiguous live ids `> mid` starting at live position `j` (the
"newer-than-mark run" the end-side growth extends over). -/
def skipRight (live : List ℕ) (mid j : ℕ) : ℕ :=
  ((live.drop j).takeWhile (fun c => decide (mid < c))).length

/-- Count of contiguous live ids `> mid` immediately LEFT of live position `i`. -/
def skipLeft (live : List ℕ) (mid i : ℕ) : ℕ :=
  ((live.take i).reverse.takeWhile (fun c => decide (mid < c))).length

/-! ## §3  The document-order resolver (paper-faithful)

Both boundaries resolve to a position in the CURRENT live reading order.  A dead
anchor rehomes to the nearest SURVIVING neighbour on the gravity side.  The
coverage of a mark is the half-open live-index interval `[startIncl, endExcl)`. -/

/-- The first covered live index (`none` = the span collapsed to empty).  A
`before` start is stable (no left growth); an `after` start skips the
newer-than-mark run to its right. -/
def startIncl (d : DocD) (m : MarkD) : Option ℕ :=
  let bd := d.birthIds
  let live := d.liveIds
  let resolved : Option ℕ :=
    if d.isLive m.start_id then some m.start_id
    else match m.startSide with
      | Side.before => scanRight bd d.deleted (idxOf bd m.start_id)
      | Side.after  => scanLeft bd d.deleted (idxOf bd m.start_id)
  match resolved, m.startSide with
  | none, Side.before => none        -- no survivor to the right: collapse
  | none, Side.after  => some 0      -- no survivor to the left: document start
  | some a, Side.before => some (idxOf live a)
  | some a, Side.after  =>
      let i := idxOf live a
      some ((i + 1) + skipRight live m.mid (i + 1))

/-- The exclusive upper live index of the covered interval (`none` = collapse).
An `after` end GROWS right over the newer-than-mark run (the end-side growth
decision); a `before` end steps back left over that run. -/
def endExcl (d : DocD) (m : MarkD) : Option ℕ :=
  let bd := d.birthIds
  let live := d.liveIds
  let n := live.length
  let resolved : Option ℕ :=
    if d.isLive m.end_id then some m.end_id
    else match m.endSide with
      | Side.after  => scanLeft bd d.deleted (idxOf bd m.end_id)
      | Side.before => scanRight bd d.deleted (idxOf bd m.end_id)
  match resolved, m.endSide with
  | none, Side.after  => none        -- no survivor to the left: collapse
  | none, Side.before => some n      -- no survivor to the right: document end
  | some a, Side.after  =>
      let i := idxOf live a
      some ((i + 1) + skipRight live m.mid (i + 1))
  | some a, Side.before =>
      let i := idxOf live a
      some (i - skipLeft live m.mid i)

/-- Does mark `m` cover live position `k` in the document-order read? -/
def markCoversPos (d : DocD) (m : MarkD) (k : ℕ) : Bool :=
  match startIncl d m with
  | none => false
  | some f => match endExcl d m with
    | none => false
    | some e => decide (f ≤ k ∧ k < e)

/-- The covered live ids of a single mark, the interval slice. -/
def coveredDoc (d : DocD) (m : MarkD) : List ℕ :=
  match startIncl d m, endExcl d m with
  | some f, some e => (d.liveIds.drop f).take (e - f)
  | _, _ => []

/-! ## §4  The tree-ancestry resolver (the RETRACTED control)

Each boundary climbs its FROZEN recorded ancestor path to the nearest live
ancestor; a tree ancestor is EARLIER in reading order, so a dead anchor drags
the boundary BACKWARD.  Coverage is the plain inclusive interval between the two
resolved anchors (side bits ignored: the frozen-path design had no gravity). -/

/-- Climb a frozen path to its first live member, else the root `0`. -/
def treeResolve (d : DocD) : List ℕ → ℕ
  | [] => 0
  | c :: rest => if c = 0 then 0 else if d.isLive c then c else treeResolve d rest

/-- Does mark `m` cover live position `k` under the tree-ancestry read? -/
def treeCoversPos (d : DocD) (m : MarkD) (k : ℕ) : Bool :=
  let live := d.liveIds
  let n := live.length
  let rs := treeResolve d m.start_path
  let re := treeResolve d m.end_path
  let first := if rs = 0 then 0 else idxOf live rs
  let last := if re = 0 then n - 1 else idxOf live re
  decide (n ≠ 0 ∧ first ≤ k ∧ k ≤ last)

/-! ## §5  The render (per-character last-writer-wins over covering marks) -/

/-- The covering mark with the higher `mid` wins (strict, so ties keep the
earlier, matching the Python `mid > cur`). -/
def winner : Option MarkD → MarkD → Option MarkD
  | none, m => some m
  | some a, m => if a.mid < m.mid then some m else some a

/-- The winning mark of type `mt` covering live position `k` (under a coverage
policy `cover`), if any. -/
def bestCover (cover : MarkD → ℕ → Bool) (marks : List MarkD) (mt : MType) (k : ℕ) :
    Option MarkD :=
  (marks.filter (fun m => decide (m.mtype = mt) && cover m k)).foldl winner none

/-- Is a character at live position `k` formatted with type `mt`?  The winning
covering mark must be an `add`. -/
def fmtAt (cover : MarkD → ℕ → Bool) (marks : List MarkD) (mt : MType) (k : ℕ) : Bool :=
  match bestCover cover marks mt k with
  | some m => decide (m.op = MarkOp.add)
  | none => false

/-- The flag render `(codepoint, isFormatted)` in reading order, under a
coverage policy. -/
def renderFlagWith (d : DocD) (cover : MarkD → ℕ → Bool) (marks : List MarkD) (mt : MType) :
    List (ℕ × Bool) :=
  d.liveIds.mapIdx (fun k c => (d.cp c, fmtAt cover marks mt k))

/-- The id-tagged flag render `(id, codepoint, isFormatted)`, the
theorem-bearing form (ids let "minus the deleted entry" be exact). -/
def renderFlagIdsWith (d : DocD) (cover : MarkD → ℕ → Bool) (marks : List MarkD) (mt : MType) :
    List (ℕ × ℕ × Bool) :=
  d.liveIds.mapIdx (fun k c => (c, d.cp c, fmtAt cover marks mt k))

/-- **The document-order rich-text read** (flag view). -/
def renderMarksDoc (d : DocD) (marks : List MarkD) (mt : MType) : List (ℕ × Bool) :=
  renderFlagWith d (markCoversPos d) marks mt

/-- The document-order read, id-tagged. -/
def renderMarksDocIds (d : DocD) (marks : List MarkD) (mt : MType) : List (ℕ × ℕ × Bool) :=
  renderFlagIdsWith d (markCoversPos d) marks mt

/-- **The tree-ancestry read** (the retracted control), flag view. -/
def renderMarksTree (d : DocD) (marks : List MarkD) (mt : MType) : List (ℕ × Bool) :=
  renderFlagWith d (treeCoversPos d) marks mt

/-- A two-type view `(codepoint, isBold, isItalic)` for the overlap example. -/
def renderPairDoc (d : DocD) (marks : List MarkD) : List (ℕ × Bool × Bool) :=
  d.liveIds.mapIdx (fun k c =>
    (d.cp c, fmtAt (markCoversPos d) marks MType.bold k,
             fmtAt (markCoversPos d) marks MType.italic k))

/-! ## §6  The document builder (auto-prefixed embed fold)

`buildShadow` folds `(id, codepoint, anchor)` records through the embed
`eUpdate`, computing each insert's coordinate prefix as its anchor's stored
coordinate, so the reading order is exactly the embed-RGA reading order. -/

def buildShadow (Γ : OrderedPrefixCode) : List (ℕ × ℕ × ℕ) → EState ℕ
  | recs => recs.foldl (fun s t =>
      let a := t.2.2
      let π := if a = 0 then ([] : List Bool)
               else ((s.find? (fun r => r.1 == a)).map (fun r => r.2.2)).getD []
      eUpdate Γ s (t.1, 0, EOp.ins t.2.1 π a)) []

/-! ## §7  The Litt et al. examples: concrete SPOTs (PASS shaped)

Each expected value is hand-derived from the note §6/§8 and asserted by
`native_decide` over a concrete config.  Codepoints are ASCII
(`a`=97, `b`=98, `c`=99, `d`=100, `x`=120, `z`=122, `W`=87, `A`=65, `B`=66,
`C`=67, `D`=68).  The reading orders come from the embed fold (verified). -/

namespace SPOT

/-- Ex 1 (§3.1): insertion WITHIN a bold span is formatted.  `a, c` bold, `b`
typed between them → `b` is bold.  Reading order `[a, b, c]`. -/
def dEx1 : DocD := { shadow := buildShadow unaryCode [(1, 97, 0), (2, 99, 1), (4, 98, 1)] }
def mEx1 : MarkD := { mid := 3, mtype := MType.bold, start_id := 1, end_id := 2 }

theorem ex1_doc :
    renderMarksDoc dEx1 [mEx1] MType.bold = [(97, true), (98, true), (99, true)] := by
  native_decide

/-- The degenerate reading (inserted `b` stays plain) is refuted. -/
theorem ex1_doc_not_plain_b :
    renderMarksDoc dEx1 [mEx1] MType.bold ≠ [(97, true), (98, false), (99, true)] := by
  native_decide

/-- Ex 2 (§3.2): overlapping `bold[a,c]` and `italic[b,d]`; the overlap carries
both.  `(codepoint, isBold, isItalic)`. -/
def dEx2 : DocD := { shadow := buildShadow unaryCode [(1, 97, 0), (2, 98, 1), (3, 99, 2), (4, 100, 3)] }
def bdEx2 : MarkD := { mid := 10, mtype := MType.bold, start_id := 1, end_id := 3 }
def itEx2 : MarkD := { mid := 11, mtype := MType.italic, start_id := 2, end_id := 4 }

theorem ex2_doc :
    renderPairDoc dEx2 [bdEx2, itEx2]
      = [(97, true, false), (98, true, true), (99, true, true), (100, false, true)] := by
  native_decide

/-- The degenerate reading (the overlap `b, c` carries only bold, not italic
too) is refuted, different-type marks genuinely coexist. -/
theorem ex2_doc_overlap_carries_both :
    renderPairDoc dEx2 [bdEx2, itEx2]
      ≠ [(97, true, false), (98, true, false), (99, true, false), (100, false, true)] := by
  native_decide

/-- Ex 3: mark a span, delete the WHOLE span, reinsert text.  Document-order:
the span collapses (both boundaries find no survivor), so the fresh `d` is
plain.  Reading order after reinsert is `[d, a, b, c]` (`d` a newer root
sibling), live = `[d]`. -/
def dEx3 : DocD :=
  { shadow := buildShadow unaryCode [(1, 97, 0), (2, 98, 1), (3, 99, 2), (4, 100, 0)],
    deleted := [1, 2, 3] }
def mEx3 : MarkD :=
  { mid := 10, mtype := MType.bold, start_id := 1, end_id := 3,
    start_path := [1, 0], end_path := [3, 2, 1, 0] }

theorem ex3_doc : renderMarksDoc dEx3 [mEx3] MType.bold = [(100, false)] := by native_decide

/-- The LEAK COMPANION: the tree-ancestry control climbs both boundaries to the
dead root, so the span becomes the whole document and the brand-new `d` renders
bold.  This is the tree-ancestry read formatting fresh text. -/
theorem ex3_tree : renderMarksTree dEx3 [mEx3] MType.bold = [(100, true)] := by native_decide

theorem ex3_doc_ne_tree :
    renderMarksDoc dEx3 [mEx3] MType.bold ≠ renderMarksTree dEx3 [mEx3] MType.bold := by
  native_decide

/-- Ex 5 (§3.2.1): concurrent add vs removeMark, resolved LWW by `mid`. -/
def dEx5 : DocD := { shadow := buildShadow unaryCode [(1, 97, 0), (2, 98, 1)] }
def add10 : MarkD := { mid := 10, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }
def rem20 : MarkD := { mid := 20, mtype := MType.bold, op := MarkOp.remove, start_id := 1, end_id := 2 }
def add20 : MarkD := { mid := 20, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }
def rem10 : MarkD := { mid := 10, mtype := MType.bold, op := MarkOp.remove, start_id := 1, end_id := 2 }

theorem ex5_doc_remove_wins :
    renderMarksDoc dEx5 [add10, rem20] MType.bold = [(97, false), (98, false)] := by native_decide
theorem ex5_doc_add_wins :
    renderMarksDoc dEx5 [add20, rem10] MType.bold = [(97, true), (98, true)] := by native_decide
/-- LWW genuinely discriminates: swapping which of add/remove has the higher
`mid` flips the verdict (it is not a constant read). -/
theorem ex5_doc_lww_discriminates :
    renderMarksDoc dEx5 [add10, rem20] MType.bold ≠ renderMarksDoc dEx5 [add20, rem10] MType.bold := by
  native_decide

/-- Ex 7 (§3.3): typing at the end of a bold span extends it (`endSide=after`).
`x` typed after `b`, newer than the mark → grabbed.  Reading order `[a, b, x]`. -/
def dEx7 : DocD := { shadow := buildShadow unaryCode [(1, 97, 0), (2, 98, 1), (4, 120, 2)] }
def mEx7 : MarkD := { mid := 3, mtype := MType.bold, start_id := 1, end_id := 2 }
def mEx7old : MarkD := { mid := 9, mtype := MType.bold, start_id := 1, end_id := 2 }

theorem ex7_doc :
    renderMarksDoc dEx7 [mEx7] MType.bold = [(97, true), (98, true), (120, true)] := by native_decide
/-- The older-than-mark concurrent insert (`x` id 4 < mark 9) is NOT grabbed. -/
theorem ex7_doc_older_not_grabbed :
    renderMarksDoc dEx7 [mEx7old] MType.bold = [(97, true), (98, true), (120, false)] := by
  native_decide
/-- The gravity is directed: the SAME insertion is grabbed by a mark older than
it and not by one newer than it, the read is not constantly expanding. -/
theorem ex7_doc_gravity_discriminates :
    renderMarksDoc dEx7 [mEx7] MType.bold ≠ renderMarksDoc dEx7 [mEx7old] MType.bold := by
  native_decide

/-- Ex 8 (§3.3): the directed gravity contrast.  Same document `[a, b, x, z]`
and typed `x`: a link (`endSide=before`) does NOT expand over `x`, while bold
(`endSide=after`) on the same insertion DOES.  Reading order `[a, b, x, z]`. -/
def dEx8 : DocD := { shadow := buildShadow unaryCode [(1, 97, 0), (2, 98, 1), (3, 122, 2), (5, 120, 2)] }
def lnEx8 : MarkD :=
  { mid := 4, mtype := MType.link, value := 1, start_id := 1, end_id := 3,
    startSide := Side.before, endSide := Side.before }
def bdEx8 : MarkD :=
  { mid := 4, mtype := MType.bold, start_id := 1, end_id := 2,
    startSide := Side.before, endSide := Side.after }

theorem ex8_doc_link_no_expand :
    renderMarksDoc dEx8 [lnEx8] MType.link
      = [(97, true), (98, true), (120, false), (122, false)] := by native_decide
theorem ex8_doc_bold_expands :
    renderMarksDoc dEx8 [bdEx8] MType.bold
      = [(97, true), (98, true), (120, true), (122, false)] := by native_decide
/-- The end-side contrast, pinned: the two reads of the same insertion differ on
`x`. -/
theorem ex8_link_ne_bold :
    renderMarksDoc dEx8 [lnEx8] MType.link ≠ renderMarksDoc dEx8 [bdEx8] MType.bold := by
  native_decide

end SPOT

/-! ## §8  The no-leak claim, made concrete and refuted

Chain `W, A, B, C` (reading order = id order), `bold[A, B]` with
`startSide=before, endSide=after`, delete the start anchor `A`.  Document-order
rehomes the start to the nearest surviving neighbour to the right (`B`), so
`bold = {B}` and `W` stays plain.  Tree-ancestry climbs `A`'s path to its parent
`W` (earlier in reading order), so `bold = {W, B}`, `W`, never in the span, is
formatted.  This is the `mark_*_no_leak` error, concretely. -/

namespace LEAK

def dLeak : DocD :=
  { shadow := buildShadow unaryCode [(1, 87, 0), (2, 65, 1), (3, 66, 2), (4, 67, 3)],
    deleted := [2] }
def mLeak : MarkD :=
  { mid := 100, mtype := MType.bold, start_id := 2, end_id := 3,
    startSide := Side.before, endSide := Side.after,
    start_path := [2, 1, 0], end_path := [3, 2, 1, 0] }

/-- **`leak_doc_shrinks` (concrete).**  Document-order does not format `W`; the
frozen-path read does, the two reads differ on `W`. -/
theorem leak_doc_shrinks_doc :
    renderMarksDoc dLeak [mLeak] MType.bold = [(87, false), (66, true), (67, false)] := by
  native_decide
theorem leak_doc_shrinks_tree :
    renderMarksTree dLeak [mLeak] MType.bold = [(87, true), (66, true), (67, false)] := by
  native_decide
theorem leak_doc_shrinks :
    renderMarksDoc dLeak [mLeak] MType.bold ≠ renderMarksTree dLeak [mLeak] MType.bold := by
  native_decide

end LEAK

/-! ## §9  The general no-backward-leak positive, and the tree refutation -/

/-- A mark's document-order coverage never dips below its rehomed start
position: if the covered interval starts at live index `f`, no position `k < f`
is covered.  The document-order analogue of the frozen-path collapse point. -/
theorem markCoversPos_before (d : DocD) (m : MarkD) (f k : ℕ)
    (hf : startIncl d m = some f) (hk : k < f) : markCoversPos d m k = false := by
  simp only [markCoversPos, hf]
  cases endExcl d m with
  | none => rfl
  | some e =>
    have hnk : ¬ f ≤ k := Nat.not_le.mpr hk
    simp only [decide_eq_false_iff_not, not_and]
    exact fun h => absurd h hnk

/-- **`doc_no_backward_leak` (general).**  Every character positioned strictly
before a mark's rehomed start (live index `< f`) carries no activation of that
mark, in reading order, the paper-faithful guarantee that replaces
`mark_*_no_leak`, refuted above.  Shaped like `render_span_before`
(`Peritext_Rehoming/Peritext_Read.lean`), with the boundary a rehomed live
position rather than a boundary node. -/
theorem doc_no_backward_leak (d : DocD) (m : MarkD) (mt : MType) (f k : ℕ)
    (hf : startIncl d m = some f) (hk : k < f) :
    fmtAt (markCoversPos d) [m] mt k = false := by
  have hc : markCoversPos d m k = false := markCoversPos_before d m f k hf hk
  have hb : bestCover (markCoversPos d) [m] mt k = none := by
    unfold bestCover
    simp [hc]
  unfold fmtAt
  rw [hb]

/-- **`tree_backward_leak_refutes_noleak` (general negative).**  There is a
reachable state and a mark whose frozen-path (tree-ancestry) coverage formats a
character the document-order read does not, a character positioned before the
mark's surviving span.  So a `mark_*_no_leak` claim for the frozen-path read is
refuted (the `leak_doc_shrinks` witness, lifted to the resolver level). -/
theorem tree_backward_leak_refutes_noleak :
    ∃ (d : DocD) (m : MarkD) (k : ℕ),
      markCoversPos d m k = false ∧ treeCoversPos d m k = true :=
  ⟨LEAK.dLeak, LEAK.mLeak, 0, by native_decide, by native_decide⟩

/-! ## §10  The atomicity cost, stated honestly (the trilemma horn)

`bold[A, B]` with `endSide=after`; `C` (older than the mark) sits after `B` and
blocks the growth run; `D` (newer, child of `C`) is plain.  Deleting the plain
separating `C` makes `D` contiguous with `B`, and the `endSide=after` growth run
reaches it, so `D` is re-formatted, the delete touched neither `D` nor any
boundary.  This is the document-order analogue of
`fused_delete_reformats_survivor`, the tombstone-free substrate's declared
trilemma horn (a membership re-span, NOT a backward leak). -/

namespace TRILEMMA

def dBefore : DocD := { shadow := buildShadow unaryCode [(1, 65, 0), (2, 66, 1), (3, 67, 2), (5, 68, 3)] }
def dAfter : DocD := { dBefore with deleted := [3] }
def mBold : MarkD :=
  { mid := 4, mtype := MType.bold, start_id := 1, end_id := 2,
    startSide := Side.before, endSide := Side.after }

/-- Before the delete: `A, B` bold, `C, D` plain (`C` blocks the run). -/
theorem respan_before :
    renderMarksDocIds dBefore [mBold] MType.bold
      = [(1, 65, true), (2, 66, true), (3, 67, false), (5, 68, false)] := by native_decide
/-- After deleting `C`: `D` is re-formatted bold. -/
theorem respan_after :
    renderMarksDocIds dAfter [mBold] MType.bold
      = [(1, 65, true), (2, 66, true), (5, 68, true)] := by native_decide

/-- **`doc_delete_can_respan` (concrete).**  The post-delete render is NOT the
pre-delete render with the deleted character `C` removed: the untouched survivor
`D` changed formatting.  The trilemma horn, made explicit rather than hidden. -/
theorem doc_delete_can_respan :
    renderMarksDocIds dAfter [mBold] MType.bold
      ≠ (renderMarksDocIds dBefore [mBold] MType.bold).filter (fun e => decide (e.1 ≠ 3)) := by
  native_decide

end TRILEMMA

/-! ## §11  Convergence: the read is a set-function of the marks

`renderMarksDoc` uses the mark list only through the per-`(char, mtype)` LWW
`bestCover`, which is invariant under permutation of the marks with distinct
`mid`s (marks form a set; removeMark is LWW; character order converges by the
embed capstone `embed_ra_linearizable3`).  Watched concretely: permuting the
two overlapping marks of Ex 2 leaves the render unchanged (PASS), and it is not
vacuous, a render that ignored one of the two marks would differ (FAIL pin). -/

namespace CONVERGE

open SPOT (dEx2 bdEx2 itEx2)

/-- PASS: permuting the mark list leaves the render unchanged (the read is a
function of the mark SET). -/
theorem renderMarksDoc_convergent_bold :
    renderMarksDoc dEx2 [bdEx2, itEx2] MType.bold
      = renderMarksDoc dEx2 [itEx2, bdEx2] MType.bold := by native_decide
theorem renderMarksDoc_convergent_italic :
    renderMarksDoc dEx2 [bdEx2, itEx2] MType.italic
      = renderMarksDoc dEx2 [itEx2, bdEx2] MType.italic := by native_decide
theorem renderMarksDoc_convergent_pair :
    renderPairDoc dEx2 [bdEx2, itEx2] = renderPairDoc dEx2 [itEx2, bdEx2] := by native_decide

/-- FAIL pin: convergence is not vacuous, dropping a mark changes the render, so
the agreement above is genuine mark content, not an empty read. -/
theorem convergent_not_vacuous :
    renderPairDoc dEx2 [bdEx2, itEx2] ≠ renderPairDoc dEx2 [bdEx2] := by native_decide

end CONVERGE

/-! ## §12  Axiom audit -/

#print axioms doc_no_backward_leak
#print axioms tree_backward_leak_refutes_noleak
#print axioms SPOT.ex1_doc
#print axioms SPOT.ex2_doc
#print axioms SPOT.ex3_doc
#print axioms SPOT.ex3_tree
#print axioms SPOT.ex5_doc_remove_wins
#print axioms SPOT.ex5_doc_add_wins
#print axioms SPOT.ex7_doc
#print axioms SPOT.ex8_doc_link_no_expand
#print axioms SPOT.ex8_doc_bold_expands
#print axioms LEAK.leak_doc_shrinks
#print axioms TRILEMMA.doc_delete_can_respan

end Sal.MRDTs.Instances.PeritextRender
