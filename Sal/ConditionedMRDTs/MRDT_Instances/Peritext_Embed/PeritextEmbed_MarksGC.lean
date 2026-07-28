import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_MarkIntent
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MultiEpoch

/-!
# Marks-layer GC for Peritext over the embed compaction stack

Design + Python validation: `whiteboard/marks-gc-note.md` (H-A, retention
roots, 2000/2000 trials) and `whiteboard/litmus/marks_gc_check.py`.  This file
mechanizes the surviving attack's obligations O1–O3 (§8 of the note); O4 (the
A3 guarded pair-drop) is `PeritextEmbed_MarksGC_A3.lean`.  O5 (the settled-cut
protocol half) is the already-tracked residue of the re-coding cluster
(`EmbedRGA_Recoding.lean` §6, `EmbedRGA_CompatChain.lean` `(⋆)`) and is NOT
taken on here.

* **O1** (`KeepSpec` / `keepSPM`): the retention-roots relabeling is a
  `StablePrefixMap` whose `Rest` is the KEPT coordinate set, live ∪
  mark-boundary anchors ∪ declared in-flight anchors.  H2 on kept pairs is the
  `ord` field (`keepSPM_A1` is the note's A1); H1 is derived
  (`keepSPM_injOn_kept`); H3 (`ext`) covers both fresh beyond-cut mints and
  declared stragglers, a straggler's mint lands in a FROZEN sibling group
  (deltas kept verbatim), which is exactly the text layer's skipped-groups
  side condition (`skipAt`, `EmbedRGA_CompactEliasDelta.lean`).  FAIL
  companion `freeze_guard_violation`: renumbering a group that receives an
  in-flight delta flips an order (deltas 2 < 5-in-flight < 9 renumber to 1, 2
  and the frozen 5 jumps the ex-9).

* **O2** (`find?_filter_keep`, `scanRight_filter`, `scanLeft_filter`): a pure
  list fact, no datatype content, removing non-surviving, non-anchor elements
  from a sequence does not change the first survivor on either side of a
  retained element.  Formalized over `List.filter`, both scan directions.

* **O3** (`marksGC_render_congr`, the capstone): `renderMarksDoc` is a
  function of the live id sequence, the boundary-anchor positions relative to
  it, and the id order; the resolver never reads a coordinate.  O1 transports
  the order facts (T1 `eRecode_applySeq` re-sorts the compacted records into
  the SAME sequence), the embed cluster transports the live sequence, ids are
  untouched, so the compacted subject's render EQUALS the uncompacted twin's
  for every beyond-cut continuation whose mints satisfy H3 and whose
  stragglers are declared.  Multi-epoch: `marksGC_render_congr_twoEpoch`
  composes keep-set maps through the existing `StablePrefixMap.comp` /
  `CompatOn` route.

The document model is `MarkDoc.DocD` (`PeritextEmbed_MarkIntent.lean`): an
insert-only embed shadow + a logical deleted list; the marks continuation is
insert-only at the shadow (a text delete appends to `deleted` and never
touches a record), though the fold lemmas below are stated for arbitrary op
lists.  One model note, pinned in the D6 SPOT: for an anchor with NO record
this file's resolver scans from `idxOf = length` (finding the last/first
survivor), where the Python harness degrades to a collapse sentinel, a
different degenerate value, but D6 still FLIPS the read either way, which is
the only load-bearing fact (the refusal's justification).  The positive
obligations never touch that branch: retained anchors always have records.
-/

namespace Sal.ConditionedMRDTs.PeritextEmbed.MarksGC

open Sal.Emulation
open Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc
open Sal.EmbedRGA (OrderedPrefixCode keyLt key unaryCode keyLt_trans)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §0  Pure list helpers -/

/-- **The O2 kernel.**  Filtering away elements that all fail the survivor
test never changes `find?` for that test: every dropped element is a
non-survivor, so the scan skips it anyway. -/
theorem find?_filter_keep {β : Type} (p surv : β → Bool) :
    ∀ (l : List β), (∀ x ∈ l, surv x = true → p x = true) →
      (l.filter p).find? surv = l.find? surv
  | [], _ => rfl
  | x :: xs, h => by
      by_cases hs : surv x = true
      · have hp : p x = true := h x List.mem_cons_self hs
        rw [List.filter_cons_of_pos hp, List.find?_cons_of_pos hs,
          List.find?_cons_of_pos hs]
      · by_cases hp : p x = true
        · rw [List.filter_cons_of_pos hp, List.find?_cons_of_neg hs,
            List.find?_cons_of_neg hs]
          exact find?_filter_keep p surv xs
            (fun y hy => h y (List.mem_cons_of_mem _ hy))
        · rw [List.filter_cons_of_neg hp, List.find?_cons_of_neg hs]
          exact find?_filter_keep p surv xs
            (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- `find?` congruence on members. -/
theorem find?_congr_mem {β : Type} (p q : β → Bool) :
    ∀ (l : List β), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
      have hx := h x List.mem_cons_self
      by_cases hp : p x = true
      · rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos (hx ▸ hp)]
      · rw [List.find?_cons_of_neg hp, List.find?_cons_of_neg (hx ▸ hp)]
        exact find?_congr_mem p q xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- `takeWhile` congruence on members. -/
theorem takeWhile_congr_mem {β : Type} (p q : β → Bool) :
    ∀ (l : List β), (∀ x ∈ l, p x = q x) → l.takeWhile p = l.takeWhile q
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.takeWhile_cons, List.takeWhile_cons, h x List.mem_cons_self,
        takeWhile_congr_mem p q xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `mapIdx` congruence on (index, member) pairs. -/
theorem mapIdx_congr_mem {β γ : Type} :
    ∀ (l : List β) (f g : ℕ → β → γ),
      (∀ i a, a ∈ l → f i a = g i a) → l.mapIdx f = l.mapIdx g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
      rw [List.mapIdx_cons, List.mapIdx_cons, h 0 a List.mem_cons_self,
        mapIdx_congr_mem l _ _ (fun i b hb => h (i + 1) b (List.mem_cons_of_mem _ hb))]

/-- Two filters fuse to their conjunction. -/
theorem filter_and {β : Type} (p q : β → Bool) :
    ∀ (l : List β), (l.filter p).filter q = l.filter (fun a => p a && q a)
  | [] => rfl
  | x :: xs => by
      by_cases hp : p x = true <;> by_cases hq : q x = true <;>
        simp [hp, hq, filter_and p q xs]

/-- `map Prod.fst` commutes with an id-level filter. -/
theorem map_fst_filter {β γ : Type} (kp : β → Bool) :
    ∀ (s : List (β × γ)), (s.filter (fun r => kp r.1)).map Prod.fst
      = (s.map Prod.fst).filter kp
  | [] => rfl
  | x :: xs => by
      by_cases h : kp x.1 = true <;>
        simp [h, map_fst_filter kp xs]

/-- In a `Nodup` split `l₁ ++ a :: l₂`, the pivot is not on the left. -/
theorem nodup_split_not_left {β : Type} {l₁ l₂ : List β} {a : β}
    (h : (l₁ ++ a :: l₂).Nodup) : a ∉ l₁ := by
  intro hin
  induction l₁ with
  | nil => cases hin
  | cons x xs ih =>
      rw [List.cons_append, List.nodup_cons] at h
      rcases List.mem_cons.mp hin with rfl | hin'
      · exact h.1 (List.mem_append_right _ List.mem_cons_self)
      · exact ih h.2 hin'

/-- `idxOf` at the pivot of a split (pivot absent on the left). -/
theorem idxOf_append_cons (l₁ l₂ : List ℕ) (a : ℕ) (ha : a ∉ l₁) :
    idxOf (l₁ ++ a :: l₂) a = l₁.length := by
  induction l₁ with
  | nil => simp [idxOf, List.findIdx_cons]
  | cons x xs ih =>
      have hxa : (x == a) = false := by
        have hne : x ≠ a := fun h => ha (h ▸ List.mem_cons_self)
        simp [hne]
      rw [List.cons_append]
      show (x :: (xs ++ a :: l₂)).findIdx (fun c => c == a) = xs.length + 1
      rw [List.findIdx_cons, hxa]
      simp only [cond_false]
      have ih' : (xs ++ a :: l₂).findIdx (fun c => c == a) = xs.length :=
        ih (fun h => ha (List.mem_cons_of_mem _ h))
      exact congrArg (· + 1) ih'

/-- `idxOf` of an absent element is the length. -/
theorem idxOf_absent (l : List ℕ) (a : ℕ) (ha : a ∉ l) : idxOf l a = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hxa : (x == a) = false := by
        have hne : x ≠ a := fun h => ha (h ▸ List.mem_cons_self)
        simp [hne]
      show (x :: xs).findIdx (fun c => c == a) = xs.length + 1
      rw [List.findIdx_cons, hxa]
      simp only [cond_false]
      exact congrArg (· + 1) (ih (fun h => ha (List.mem_cons_of_mem _ h)))

/-- Dropping the prefix-plus-pivot of a split. -/
theorem drop_append_cons_succ {β : Type} (l t : List β) (a : β) :
    (l ++ a :: t).drop (l.length + 1) = t := by
  have h : l ++ a :: t = (l ++ [a]) ++ t := by simp
  have hlen : (l ++ [a]).length = l.length + 1 := by simp
  rw [h, ← hlen, List.drop_left]

/-! ## §1  O1: the keep-set stable-prefix map

The retention-roots keep-set has three legs: the live records, the boundary
anchors of present (and declared in-flight) mark records, dead anchors
included, that is the whole point, and the anchors of declared in-flight text
ops.  `keepSPM` packages a relabeling whose `Rest` IS that keep-set as a
`StablePrefixMap` (not a parallel notion): H2 on kept pairs is the `ord`
obligation, H3 is `ext` (fresh mints, plus declared stragglers whose frozen
groups keep deltas verbatim), and H1 is inherited from the bundle
(`StablePrefixMap.injOn`). -/

/-- The keep-set, leg by leg (coordinates of the kept records). -/
structure KeepSpec where
  live : List Bool → Prop
  markAnchor : List Bool → Prop
  inflight : List Bool → Prop

/-- Kept = live ∪ mark-boundary anchors ∪ declared in-flight anchors. -/
def KeepSpec.kept (K : KeepSpec) (c : List Bool) : Prop :=
  K.live c ∨ K.markAnchor c ∨ K.inflight c

/-- **O1.**  A keep-set relabeling with order preservation on kept pairs (H2)
and the extension law on declared mints (H3) IS a `StablePrefixMap` whose
domain is the kept coordinate set.  The in-flight freeze guard lives inside
`hext`: a declared straggler's `(π, d)` is a `Mint`, so `f (π ++ enc d) =
f π ++ enc d` forces the straggler's sibling group to keep its deltas
verbatim, the text layer's skipped-groups side condition. -/
def keepSPM (Γ : OrderedPrefixCode) (K : KeepSpec)
    (f : List Bool → List Bool) (Mint : List Bool → ℕ → Prop)
    (hext : ∀ {π : List Bool} {d : ℕ}, Mint π d →
      f (π ++ Γ.enc d) = f π ++ Γ.enc d)
    (hord : ∀ {c c' : List Bool},
      (K.kept c ∨ ∃ π d, Mint π d ∧ c = π ++ Γ.enc d) →
      (K.kept c' ∨ ∃ π d, Mint π d ∧ c' = π ++ Γ.enc d) →
      keyLt (key (f c)) (key (f c')) = keyLt (key c) (key c')) :
    StablePrefixMap Γ where
  f := f
  Rest := K.kept
  MintAt := Mint
  ext := hext
  ord := hord

section KeepSPM

variable {Γ : OrderedPrefixCode} {K : KeepSpec}
  {f : List Bool → List Bool} {Mint : List Bool → ℕ → Prop}
  {hext : ∀ {π : List Bool} {d : ℕ}, Mint π d → f (π ++ Γ.enc d) = f π ++ Γ.enc d}
  {hord : ∀ {c c' : List Bool},
    (K.kept c ∨ ∃ π d, Mint π d ∧ c = π ++ Γ.enc d) →
    (K.kept c' ∨ ∃ π d, Mint π d ∧ c' = π ++ Γ.enc d) →
    keyLt (key (f c)) (key (f c')) = keyLt (key c) (key c')}

/-- A live coordinate is in the map's domain. -/
theorem keepSPM_dom_live {c : List Bool} (h : K.live c) :
    (keepSPM Γ K f Mint hext hord).Dom c := Or.inl (Or.inl h)

/-- A retained mark-boundary anchor, dead or alive, is in the map's domain:
its order against every other kept record is H2-protected. -/
theorem keepSPM_dom_markAnchor {c : List Bool} (h : K.markAnchor c) :
    (keepSPM Γ K f Mint hext hord).Dom c := Or.inl (Or.inr (Or.inl h))

/-- A declared in-flight anchor is in the map's domain. -/
theorem keepSPM_dom_inflight {c : List Bool} (h : K.inflight c) :
    (keepSPM Γ K f Mint hext hord).Dom c := Or.inl (Or.inr (Or.inr h))

include hext hord in
/-- **A1** (note §8): the relabeling preserves the display comparator on the
whole kept set, retained-dead included, H2 restricted to record-bearing
nodes. -/
theorem keepSPM_A1 {c c' : List Bool} (h : K.kept c) (h' : K.kept c') :
    keyLt (key (f c)) (key (f c')) = keyLt (key c) (key c') :=
  (keepSPM Γ K f Mint hext hord).ord' (Or.inl h) (Or.inl h')

include hext hord in
/-- **H1 is derived, not assumed**: the keep-set relabeling is injective on
kept coordinates (via the bundle's `injOn`). -/
theorem keepSPM_injOn_kept {c c' : List Bool} (h : K.kept c) (h' : K.kept c')
    (heq : f c = f c') : c = c' :=
  (keepSPM Γ K f Mint hext hord).injOn (Or.inl h) (Or.inl h') heq

end KeepSPM

/-! ## §2  O2: scan factorization (the A2 lemma), pure lists

The resolver's dead-anchor rehoming is a nearest-survivor scan from the
anchor's birth position.  Dropping settled-dead non-anchor records is a
`filter`; these two lemmas say the scan result is unchanged on either side of
a retained element, because every dropped element is a non-survivor.  No
datatype content: `MarkDoc.scanRight/scanLeft` over an arbitrary split. -/

/-- **O2, right scan.**  In `l₁ ++ a :: l₂` with the retained element `a`
kept by the filter and every survivor of `l₂` kept, the first survivor
strictly right of `a` is the same in the filtered and the full sequence. -/
theorem scanRight_filter (l₁ l₂ : List ℕ) (a : ℕ) (del : List ℕ) (p : ℕ → Bool)
    (hpa : p a = true) (ha : a ∉ l₁)
    (hkeep : ∀ x ∈ l₂, (!del.contains x) = true → p x = true) :
    scanRight ((l₁ ++ a :: l₂).filter p) del (idxOf ((l₁ ++ a :: l₂).filter p) a)
      = scanRight (l₁ ++ a :: l₂) del (idxOf (l₁ ++ a :: l₂) a) := by
  have hsplit : (l₁ ++ a :: l₂).filter p = l₁.filter p ++ a :: l₂.filter p := by
    rw [List.filter_append, List.filter_cons_of_pos hpa]
  have haF : a ∉ l₁.filter p := fun h => ha (List.mem_of_mem_filter h)
  rw [hsplit, idxOf_append_cons _ _ _ haF, idxOf_append_cons _ _ _ ha]
  show ((l₁.filter p ++ a :: l₂.filter p).drop ((l₁.filter p).length + 1)).find? _
      = ((l₁ ++ a :: l₂).drop (l₁.length + 1)).find? _
  rw [drop_append_cons_succ, drop_append_cons_succ]
  exact find?_filter_keep p _ l₂ hkeep

/-- **O2, left scan.**  Mirror statement: the first survivor strictly left of
the retained element is unchanged. -/
theorem scanLeft_filter (l₁ l₂ : List ℕ) (a : ℕ) (del : List ℕ) (p : ℕ → Bool)
    (hpa : p a = true) (ha : a ∉ l₁)
    (hkeep : ∀ x ∈ l₁, (!del.contains x) = true → p x = true) :
    scanLeft ((l₁ ++ a :: l₂).filter p) del (idxOf ((l₁ ++ a :: l₂).filter p) a)
      = scanLeft (l₁ ++ a :: l₂) del (idxOf (l₁ ++ a :: l₂) a) := by
  have hsplit : (l₁ ++ a :: l₂).filter p = l₁.filter p ++ a :: l₂.filter p := by
    rw [List.filter_append, List.filter_cons_of_pos hpa]
  have haF : a ∉ l₁.filter p := fun h => ha (List.mem_of_mem_filter h)
  rw [hsplit, idxOf_append_cons _ _ _ haF, idxOf_append_cons _ _ _ ha]
  show (((l₁.filter p ++ a :: l₂.filter p).take (l₁.filter p).length).reverse).find? _
      = (((l₁ ++ a :: l₂).take l₁.length).reverse).find? _
  rw [List.take_left, List.take_left, ← List.filter_reverse]
  exact find?_filter_keep p _ l₁.reverse
    (fun x hx => hkeep x (List.mem_reverse.mp hx))

/-! ## §3  The resolver factored, and render congruence

`renderMarksDoc` never reads a coordinate: it is a function of the birth id
sequence, the deleted list (membership on birth ids only), and the codepoint
map.  We factor each boundary resolution into a scan half (`startResolved` /
`endResolved`, functions of birth order + deleted) and an arithmetic half
(`startFinish` / `endFinish`, functions of the LIVE sequence only), then prove
the two congruences O3 consumes: the id-level drop (`renderMarksDoc_dropDoc`,
A2 through O2) and coordinate invisibility (`renderMarksDoc_remap`). -/

/-- The scan half of `startIncl`: resolve the start anchor to a live id. -/
def startResolved (d : DocD) (m : MarkD) : Option ℕ :=
  if d.isLive m.start_id then some m.start_id
  else match m.startSide with
    | Side.before => scanRight d.birthIds d.deleted (idxOf d.birthIds m.start_id)
    | Side.after  => scanLeft d.birthIds d.deleted (idxOf d.birthIds m.start_id)

/-- The arithmetic half of `startIncl`: a function of the live sequence. -/
def startFinish (live : List ℕ) (m : MarkD) : Option ℕ → Option ℕ
  | none => match m.startSide with
    | Side.before => none
    | Side.after  => some 0
  | some a => match m.startSide with
    | Side.before => some (idxOf live a)
    | Side.after  => some ((idxOf live a + 1) + skipRight live m.mid (idxOf live a + 1))

/-- The scan half of `endExcl`. -/
def endResolved (d : DocD) (m : MarkD) : Option ℕ :=
  if d.isLive m.end_id then some m.end_id
  else match m.endSide with
    | Side.after  => scanLeft d.birthIds d.deleted (idxOf d.birthIds m.end_id)
    | Side.before => scanRight d.birthIds d.deleted (idxOf d.birthIds m.end_id)

/-- The arithmetic half of `endExcl`. -/
def endFinish (live : List ℕ) (m : MarkD) : Option ℕ → Option ℕ
  | none => match m.endSide with
    | Side.after  => none
    | Side.before => some live.length
  | some a => match m.endSide with
    | Side.after  => some ((idxOf live a + 1) + skipRight live m.mid (idxOf live a + 1))
    | Side.before => some (idxOf live a - skipLeft live m.mid (idxOf live a))

theorem startIncl_factor (d : DocD) (m : MarkD) :
    startIncl d m = startFinish d.liveIds m (startResolved d m) := by
  cases hL : d.isLive m.start_id <;> cases hS : m.startSide <;>
    simp only [startIncl, startResolved, startFinish, hL, hS, Bool.false_eq_true,
      if_false, if_true] <;>
    first
    | rfl
    | (cases hscan : scanRight d.birthIds d.deleted (idxOf d.birthIds m.start_id) <;> rfl)
    | (cases hscan : scanLeft d.birthIds d.deleted (idxOf d.birthIds m.start_id) <;> rfl)

theorem endExcl_factor (d : DocD) (m : MarkD) :
    endExcl d m = endFinish d.liveIds m (endResolved d m) := by
  cases hL : d.isLive m.end_id <;> cases hS : m.endSide <;>
    simp only [endExcl, endResolved, endFinish, hL, hS, Bool.false_eq_true,
      if_false, if_true] <;>
    first
    | rfl
    | (cases hscan : scanRight d.birthIds d.deleted (idxOf d.birthIds m.end_id) <;> rfl)
    | (cases hscan : scanLeft d.birthIds d.deleted (idxOf d.birthIds m.end_id) <;> rfl)

/-! ### General congruence: the render sees only (birth ids, deleted, cps) -/

theorem liveIds_congr {d d' : DocD} (hb : d.birthIds = d'.birthIds)
    (hdel : d.deleted = d'.deleted) : d.liveIds = d'.liveIds := by
  unfold DocD.liveIds
  rw [hb, hdel]

theorem isLive_congr {d d' : DocD} (hb : d.birthIds = d'.birthIds)
    (hdel : d.deleted = d'.deleted) (c : ℕ) : d.isLive c = d'.isLive c := by
  unfold DocD.isLive
  rw [hb, hdel]

theorem startIncl_congr {d d' : DocD} (m : MarkD) (hb : d.birthIds = d'.birthIds)
    (hdel : d.deleted = d'.deleted) : startIncl d m = startIncl d' m := by
  have hres : startResolved d m = startResolved d' m := by
    unfold startResolved
    rw [isLive_congr hb hdel, hb, hdel]
  rw [startIncl_factor, startIncl_factor, liveIds_congr hb hdel, hres]

theorem endExcl_congr {d d' : DocD} (m : MarkD) (hb : d.birthIds = d'.birthIds)
    (hdel : d.deleted = d'.deleted) : endExcl d m = endExcl d' m := by
  have hres : endResolved d m = endResolved d' m := by
    unfold endResolved
    rw [isLive_congr hb hdel, hb, hdel]
  rw [endExcl_factor, endExcl_factor, liveIds_congr hb hdel, hres]

theorem markCoversPos_congr {d d' : DocD} (m : MarkD) (k : ℕ)
    (hb : d.birthIds = d'.birthIds) (hdel : d.deleted = d'.deleted) :
    markCoversPos d m k = markCoversPos d' m k := by
  unfold markCoversPos
  rw [startIncl_congr m hb hdel, endExcl_congr m hb hdel]

/-- **Render congruence**: two documents with the same birth id sequence, the
same deleted list, and the same codepoints on live ids render identically,
coordinates are invisible to the mark read. -/
theorem renderMarksDoc_congr {d d' : DocD} (marks : List MarkD) (mt : MType)
    (hb : d.birthIds = d'.birthIds) (hdel : d.deleted = d'.deleted)
    (hcp : ∀ c ∈ d'.liveIds, d.cp c = d'.cp c) :
    renderMarksDoc d marks mt = renderMarksDoc d' marks mt := by
  unfold renderMarksDoc renderFlagWith
  rw [liveIds_congr hb hdel]
  refine mapIdx_congr_mem _ _ _ (fun k c hc => ?_)
  rw [hcp c hc]
  have hfmt : fmtAt (markCoversPos d) marks mt k
      = fmtAt (markCoversPos d') marks mt k := by
    unfold fmtAt bestCover
    rw [List.filter_congr (fun o _ => by rw [markCoversPos_congr o k hb hdel])]
  rw [hfmt]

/-! ### The id-level drop (retention roots): O2 through the resolver -/

/-- Drop the records whose id fails `kp`; the deleted list is untouched
(restricting it is `renderMarksDoc_deleted_congr` below). -/
def dropDoc (d : DocD) (kp : ℕ → Bool) : DocD :=
  { shadow := d.shadow.filter (fun r => kp r.1), deleted := d.deleted }

theorem birthIds_dropDoc (d : DocD) (kp : ℕ → Bool) :
    (dropDoc d kp).birthIds = d.birthIds.filter kp :=
  map_fst_filter kp d.shadow

/-- Survivors are kept (contrapositive of "only the dead are dropped"). -/
theorem surv_keep {d : DocD} {kp : ℕ → Bool}
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true) :
    ∀ c ∈ d.birthIds, (!d.deleted.contains c) = true → kp c = true := by
  intro c hc hs
  cases hk : kp c with
  | true => rfl
  | false =>
      rw [hdead c hc hk] at hs
      cases hs

theorem liveIds_dropDoc (d : DocD) (kp : ℕ → Bool)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true) :
    (dropDoc d kp).liveIds = d.liveIds := by
  show (dropDoc d kp).birthIds.filter (fun c => !(dropDoc d kp).deleted.contains c)
      = d.birthIds.filter (fun c => !d.deleted.contains c)
  rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc,
    filter_and]
  refine List.filter_congr (fun c hc => ?_)
  cases hs : (!d.deleted.contains c) with
  | true => rw [surv_keep hdead c hc hs, Bool.true_and]
  | false => rw [Bool.and_false]

theorem isLive_dropDoc (d : DocD) (kp : ℕ → Bool)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true) :
    ∀ c, (dropDoc d kp).isLive c = d.isLive c := by
  intro c
  show ((dropDoc d kp).birthIds.contains c && !(dropDoc d kp).deleted.contains c)
      = (d.birthIds.contains c && !d.deleted.contains c)
  rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc]
  by_cases hmem : c ∈ d.birthIds
  · by_cases hkp : kp c = true
    · have h1 : c ∈ d.birthIds.filter kp := List.mem_filter.mpr ⟨hmem, hkp⟩
      simp [List.contains_eq_mem, hmem, h1]
    · have hkpf : kp c = false := by
        cases h : kp c with
        | true => exact absurd h hkp
        | false => rfl
      have h1 : c ∉ d.birthIds.filter kp := fun h => by
        have := (List.mem_filter.mp h).2
        rw [hkpf] at this
        cases this
      have hdel : c ∈ d.deleted := by
        have := hdead c hmem hkpf
        simpa [List.contains_eq_mem] using this
      simp [List.contains_eq_mem, hmem, h1, hdel]
  · have h1 : c ∉ d.birthIds.filter kp := fun h => hmem (List.mem_of_mem_filter h)
    simp [List.contains_eq_mem, hmem, h1]

theorem cp_dropDoc (d : DocD) (kp : ℕ → Bool) {c : ℕ} (hc : kp c = true) :
    (dropDoc d kp).cp c = d.cp c := by
  show (((d.shadow.filter (fun r => kp r.1)).find? (fun r => r.1 == c)).map
      (fun r => r.2.1)).getD 0
    = ((d.shadow.find? (fun r => r.1 == c)).map (fun r => r.2.1)).getD 0
  rw [find?_filter_keep (fun r => kp r.1) (fun r => r.1 == c) d.shadow
    (fun r _ hr => by
      have hrc : r.1 = c := by simpa using hr
      show kp r.1 = true
      rw [hrc]
      exact hc)]

/-- The right scan from a kept (or absent) anchor is drop-invisible, O2
lifted to the document's birth order. -/
theorem scanRight_dropDoc (d : DocD) (kp : ℕ → Bool) (a : ℕ)
    (hnd : d.birthIds.Nodup) (hkpa : kp a = true)
    (hsurv : ∀ c ∈ d.birthIds, (!d.deleted.contains c) = true → kp c = true) :
    scanRight (d.birthIds.filter kp) d.deleted (idxOf (d.birthIds.filter kp) a)
      = scanRight d.birthIds d.deleted (idxOf d.birthIds a) := by
  by_cases hmem : a ∈ d.birthIds
  · obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem
    rw [hsplit] at hnd ⊢
    have ha : a ∉ l₁ := nodup_split_not_left hnd
    refine scanRight_filter l₁ l₂ a d.deleted kp hkpa ha (fun x hx h => ?_)
    exact hsurv x (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)) h
  · have hmemF : a ∉ d.birthIds.filter kp := fun h => hmem (List.mem_of_mem_filter h)
    rw [idxOf_absent _ _ hmem, idxOf_absent _ _ hmemF]
    show ((d.birthIds.filter kp).drop ((d.birthIds.filter kp).length + 1)).find? _
        = (d.birthIds.drop (d.birthIds.length + 1)).find? _
    rw [List.drop_eq_nil_of_le (Nat.le_succ _), List.drop_eq_nil_of_le (Nat.le_succ _)]

/-- The left scan from a kept (or absent) anchor is drop-invisible. -/
theorem scanLeft_dropDoc (d : DocD) (kp : ℕ → Bool) (a : ℕ)
    (hnd : d.birthIds.Nodup) (hkpa : kp a = true)
    (hsurv : ∀ c ∈ d.birthIds, (!d.deleted.contains c) = true → kp c = true) :
    scanLeft (d.birthIds.filter kp) d.deleted (idxOf (d.birthIds.filter kp) a)
      = scanLeft d.birthIds d.deleted (idxOf d.birthIds a) := by
  by_cases hmem : a ∈ d.birthIds
  · obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem
    rw [hsplit] at hnd ⊢
    have ha : a ∉ l₁ := nodup_split_not_left hnd
    refine scanLeft_filter l₁ l₂ a d.deleted kp hkpa ha (fun x hx h => ?_)
    exact hsurv x (by rw [hsplit]; exact List.mem_append_left _ hx) h
  · have hmemF : a ∉ d.birthIds.filter kp := fun h => hmem (List.mem_of_mem_filter h)
    rw [idxOf_absent _ _ hmem, idxOf_absent _ _ hmemF]
    show (((d.birthIds.filter kp).take (d.birthIds.filter kp).length).reverse).find? _
        = ((d.birthIds.take d.birthIds.length).reverse).find? _
    rw [List.take_length, List.take_length, ← List.filter_reverse]
    exact find?_filter_keep kp _ d.birthIds.reverse
      (fun x hx => hsurv x (List.mem_reverse.mp hx))

theorem startResolved_dropDoc (d : DocD) (kp : ℕ → Bool) (m : MarkD)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hkps : kp m.start_id = true) :
    startResolved (dropDoc d kp) m = startResolved d m := by
  unfold startResolved
  rw [isLive_dropDoc d kp hdead m.start_id]
  cases m.startSide with
  | before =>
      rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc,
        scanRight_dropDoc d kp m.start_id hnd hkps (surv_keep hdead)]
  | after =>
      rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc,
        scanLeft_dropDoc d kp m.start_id hnd hkps (surv_keep hdead)]

theorem endResolved_dropDoc (d : DocD) (kp : ℕ → Bool) (m : MarkD)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hkpe : kp m.end_id = true) :
    endResolved (dropDoc d kp) m = endResolved d m := by
  unfold endResolved
  rw [isLive_dropDoc d kp hdead m.end_id]
  cases m.endSide with
  | after =>
      rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc,
        scanLeft_dropDoc d kp m.end_id hnd hkpe (surv_keep hdead)]
  | before =>
      rw [show (dropDoc d kp).deleted = d.deleted from rfl, birthIds_dropDoc,
        scanRight_dropDoc d kp m.end_id hnd hkpe (surv_keep hdead)]

theorem startIncl_dropDoc (d : DocD) (kp : ℕ → Bool) (m : MarkD)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hkps : kp m.start_id = true) :
    startIncl (dropDoc d kp) m = startIncl d m := by
  rw [startIncl_factor, startIncl_factor, liveIds_dropDoc d kp hdead,
    startResolved_dropDoc d kp m hnd hdead hkps]

theorem endExcl_dropDoc (d : DocD) (kp : ℕ → Bool) (m : MarkD)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hkpe : kp m.end_id = true) :
    endExcl (dropDoc d kp) m = endExcl d m := by
  rw [endExcl_factor, endExcl_factor, liveIds_dropDoc d kp hdead,
    endResolved_dropDoc d kp m hnd hdead hkpe]

theorem markCoversPos_dropDoc (d : DocD) (kp : ℕ → Bool) (m : MarkD) (k : ℕ)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hkps : kp m.start_id = true) (hkpe : kp m.end_id = true) :
    markCoversPos (dropDoc d kp) m k = markCoversPos d m k := by
  unfold markCoversPos
  rw [startIncl_dropDoc d kp m hnd hdead hkps, endExcl_dropDoc d kp m hnd hdead hkpe]

/-- **A2, at the render** (the drop half of O3): dropping settled-dead
records that are not boundary anchors of any present mark is invisible to
`renderMarksDoc`.  The two hypotheses are exactly the retention-roots
keep-set: only dead ids may be dropped, and every mark boundary is kept. -/
theorem renderMarksDoc_dropDoc (d : DocD) (kp : ℕ → Bool)
    (marks : List MarkD) (mt : MType)
    (hnd : d.birthIds.Nodup)
    (hdead : ∀ c ∈ d.birthIds, kp c = false → d.deleted.contains c = true)
    (hanchor : ∀ m ∈ marks, kp m.start_id = true ∧ kp m.end_id = true) :
    renderMarksDoc (dropDoc d kp) marks mt = renderMarksDoc d marks mt := by
  unfold renderMarksDoc renderFlagWith
  rw [liveIds_dropDoc d kp hdead]
  refine mapIdx_congr_mem _ _ _ (fun k c hc => ?_)
  have hkpc : kp c = true := by
    have hc' := List.mem_filter.mp hc
    exact surv_keep hdead c hc'.1 hc'.2
  rw [cp_dropDoc d kp hkpc]
  have hfmt : fmtAt (markCoversPos (dropDoc d kp)) marks mt k
      = fmtAt (markCoversPos d) marks mt k := by
    unfold fmtAt bestCover
    rw [List.filter_congr (fun o ho => by
      rw [markCoversPos_dropDoc d kp o k hnd hdead (hanchor o ho).1 (hanchor o ho).2])]
  rw [hfmt]

/-! ### Coordinate invisibility: the re-map never touches the render -/

theorem birthIds_remap (f : List Bool → List Bool) (s : EState ℕ) (del : List ℕ) :
    (DocD.mk (eRemapSt f s) del).birthIds = (DocD.mk s del).birthIds := by
  show (eRemapSt f s).map Prod.fst = s.map Prod.fst
  unfold eRemapSt
  rw [List.map_map]
  exact List.map_congr_left (fun r _ => rfl)

theorem cp_remap (f : List Bool → List Bool) (s : EState ℕ) (del : List ℕ) (c : ℕ) :
    (DocD.mk (eRemapSt f s) del).cp c = (DocD.mk s del).cp c := by
  show (((eRemapSt f s).find? (fun r => r.1 == c)).map (fun r => r.2.1)).getD 0
      = ((s.find? (fun r => r.1 == c)).map (fun r => r.2.1)).getD 0
  unfold eRemapSt
  rw [List.find?_map]
  have hcomp : ((fun (r : ERec ℕ) => r.1 == c) ∘ eRemapRec f)
      = (fun (r : ERec ℕ) => r.1 == c) := rfl
  rw [hcomp]
  cases hfind : s.find? (fun r => r.1 == c) with
  | none => rfl
  | some r => rfl

/-- **The re-map is invisible to the mark render**: same ids, same elements,
same list order, same deleted list, only coordinates change, and the
resolver never reads one. -/
theorem renderMarksDoc_remap (f : List Bool → List Bool) (s : EState ℕ)
    (del : List ℕ) (marks : List MarkD) (mt : MType) :
    renderMarksDoc (DocD.mk (eRemapSt f s) del) marks mt
      = renderMarksDoc (DocD.mk s del) marks mt :=
  renderMarksDoc_congr marks mt (birthIds_remap f s del) rfl
    (fun c _ => cp_remap f s del c)

/-- Restricting the deleted list to ids that still have records (the
`apply_compaction` restriction) is render-invisible: the resolver consults
`deleted` only on birth ids. -/
theorem renderMarksDoc_deleted_congr (d : DocD) (del' : List ℕ)
    (marks : List MarkD) (mt : MType)
    (h : ∀ c ∈ d.birthIds, del'.contains c = d.deleted.contains c) :
    renderMarksDoc { d with deleted := del' } marks mt
      = renderMarksDoc d marks mt := by
  have hb : (DocD.mk d.shadow del').birthIds = d.birthIds := rfl
  have hlive : (DocD.mk d.shadow del').liveIds = d.liveIds := by
    show d.birthIds.filter (fun c => !del'.contains c)
        = d.birthIds.filter (fun c => !d.deleted.contains c)
    exact List.filter_congr (fun c hc => by rw [h c hc])
  have hisLive : ∀ c, (DocD.mk d.shadow del').isLive c = d.isLive c := by
    intro c
    show (d.birthIds.contains c && !del'.contains c)
        = (d.birthIds.contains c && !d.deleted.contains c)
    by_cases hmem : c ∈ d.birthIds
    · rw [h c hmem]
    · have : d.birthIds.contains c = false := by
        simp [List.contains_eq_mem, hmem]
      rw [this, Bool.false_and, Bool.false_and]
  have hscanR : ∀ i, scanRight d.birthIds del' i = scanRight d.birthIds d.deleted i := by
    intro i
    exact find?_congr_mem _ _ _ (fun x hx => by
      rw [h x (List.mem_of_mem_drop hx)])
  have hscanL : ∀ i, scanLeft d.birthIds del' i = scanLeft d.birthIds d.deleted i := by
    intro i
    refine find?_congr_mem _ _ _ (fun x hx => ?_)
    have hx' : x ∈ d.birthIds :=
      (List.take_sublist _ _).subset (List.mem_reverse.mp hx)
    rw [h x hx']
  have hsi : ∀ m : MarkD, startIncl (DocD.mk d.shadow del') m = startIncl d m := by
    intro m
    rw [startIncl_factor, startIncl_factor, hlive]
    have : startResolved (DocD.mk d.shadow del') m = startResolved d m := by
      unfold startResolved
      rw [hisLive m.start_id]
      cases m.startSide with
      | before => exact congrArg _ (hscanR _)
      | after => exact congrArg _ (hscanL _)
    rw [this]
  have hei : ∀ m : MarkD, endExcl (DocD.mk d.shadow del') m = endExcl d m := by
    intro m
    rw [endExcl_factor, endExcl_factor, hlive]
    have : endResolved (DocD.mk d.shadow del') m = endResolved d m := by
      unfold endResolved
      rw [hisLive m.end_id]
      cases m.endSide with
      | after => exact congrArg _ (hscanL _)
      | before => exact congrArg _ (hscanR _)
    rw [this]
  unfold renderMarksDoc renderFlagWith
  rw [show ({ d with deleted := del' } : DocD) = DocD.mk d.shadow del' from rfl, hlive]
  refine mapIdx_congr_mem _ _ _ (fun k c _ => ?_)
  have hcp : (DocD.mk d.shadow del').cp c = d.cp c := rfl
  rw [hcp]
  have hcov : ∀ (o : MarkD), markCoversPos (DocD.mk d.shadow del') o k
      = markCoversPos d o k := by
    intro o
    unfold markCoversPos
    rw [hsi o, hei o]
  have hfmt : fmtAt (markCoversPos (DocD.mk d.shadow del')) marks mt k
      = fmtAt (markCoversPos d) marks mt k := by
    unfold fmtAt bestCover
    rw [List.filter_congr (fun o _ => by rw [hcov o])]
  rw [hfmt]

/-! ## §4  The continuation commutes with the drop (embed layer)

The subject folds the (translated) continuation over the KEPT records; the
twin folds it over everything.  Since an op carries its own anchor prefix,
the only interaction is the sorted-insert position, and on a sorted state,
inserting into a filtered list is the filter of the insert.  `ContOK` is the
continuation discipline (fresh Lamport ids, distinct mint keys) that any
honest beyond-cut continuation satisfies. -/

/-- Continuation discipline over a cut state: fresh ids, distinct insert ids,
mint keys fresh against the state and pairwise. -/
structure ContOK (Γ : OrderedPrefixCode) (s : EState α) (τ : List (Op (EOp α))) :
    Prop where
  freshId : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
    o.2.2 = EOp.ins e π a → o.1 ∉ eIds s
  nodupIns : (eInsIds τ).Nodup
  freshKeySt : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ),
    o.2.2 = EOp.ins e π a → ∀ x ∈ s, key x.2.2 ≠ key (π ++ Γ.enc (o.1 - a))
  freshKeyPair : ∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a →
    ∀ o' ∈ τ, o'.1 ≠ o.1 → ∀ (e' : α) (π' : List Bool) (a' : ℕ),
      o'.2.2 = EOp.ins e' π' a' → key (π' ++ Γ.enc (o'.1 - a')) ≠ key (π ++ Γ.enc (o.1 - a))

theorem eInsIds_cons_ins {o : Op (EOp α)} {τ : List (Op (EOp α))}
    (h : eIsIns o = true) : eInsIds (o :: τ) = o.1 :: eInsIds τ := by
  simp [eInsIds, h]

theorem eInsIds_cons_del {o : Op (EOp α)} {τ : List (Op (EOp α))}
    (h : eIsIns o = false) : eInsIds (o :: τ) = eInsIds τ := by
  simp [eInsIds, h]

theorem eIsIns_of_ins {o : Op (EOp α)} {e : α} {π : List Bool} {a : ℕ}
    (h : o.2.2 = EOp.ins e π a) : eIsIns o = true := by
  unfold eIsIns
  rw [h]

/-- One update preserves the continuation discipline for the remaining ops. -/
theorem ContOK.step {Γ : OrderedPrefixCode} {s : EState α} {o : Op (EOp α)}
    {τ : List (Op (EOp α))} (h : ContOK Γ s (o :: τ)) :
    ContOK Γ (eUpdate Γ s o) τ := by
  obtain ⟨t, rr, op⟩ := o
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o' ho' e π a hins hmem
    cases op with
    | del x =>
        rw [mem_eIds_update_del] at hmem
        exact h.freshId o' (List.mem_cons_of_mem _ ho') e π a hins hmem.1
    | ins e0 π0 a0 =>
        simp only [eUpdate] at hmem
        by_cases hg : t ∈ eIds s
        · rw [if_pos hg] at hmem
          exact h.freshId o' (List.mem_cons_of_mem _ ho') e π a hins hmem
        · rw [if_neg hg] at hmem
          rw [mem_eIds_eInsert] at hmem
          rcases hmem with hmem | hmem
          · exact h.freshId o' (List.mem_cons_of_mem _ ho') e π a hins hmem
          · have h1 : o'.1 ∈ eInsIds τ :=
              mem_eInsIds.mpr ⟨o', ho', eIsIns_of_ins hins, rfl⟩
            have h2 : eInsIds ((t, rr, EOp.ins e0 π0 a0) :: τ) = t :: eInsIds τ :=
              eInsIds_cons_ins rfl
            have h3 := h.nodupIns
            rw [h2, List.nodup_cons] at h3
            rw [hmem] at h1
            exact h3.1 h1
  · cases hop : eIsIns (t, rr, op) with
    | true =>
        have := h.nodupIns
        rw [eInsIds_cons_ins hop, List.nodup_cons] at this
        exact this.2
    | false =>
        have := h.nodupIns
        rw [eInsIds_cons_del hop] at this
        exact this
  · intro o' ho' e π a hins x hx
    cases op with
    | del y =>
        exact h.freshKeySt o' (List.mem_cons_of_mem _ ho') e π a hins x
          (List.mem_of_mem_filter hx)
    | ins e0 π0 a0 =>
        simp only [eUpdate] at hx
        by_cases hg : t ∈ eIds s
        · rw [if_pos hg] at hx
          exact h.freshKeySt o' (List.mem_cons_of_mem _ ho') e π a hins x hx
        · rw [if_neg hg] at hx
          rcases mem_eInsert.mp hx with hx' | hx'
          · exact h.freshKeySt o' (List.mem_cons_of_mem _ ho') e π a hins x hx'
          · -- x is the head op's own record: pairwise mint-key freshness
            have hne : t ≠ o'.1 := by
              intro hEq
              have h1 : o'.1 ∈ eInsIds τ :=
                mem_eInsIds.mpr ⟨o', ho', eIsIns_of_ins hins, rfl⟩
              have h3 := h.nodupIns
              rw [eInsIds_cons_ins rfl, List.nodup_cons] at h3
              rw [← hEq] at h1
              exact h3.1 h1
            have := h.freshKeyPair o' (List.mem_cons_of_mem _ ho') e π a hins
              (t, rr, EOp.ins e0 π0 a0) List.mem_cons_self (fun hEq => hne hEq) e0 π0 a0 rfl
            rw [hx']
            exact this
  · intro o' ho' e π a hins o'' ho'' hne e' π' a' hins'
    exact h.freshKeyPair o' (List.mem_cons_of_mem _ ho') e π a hins
      o'' (List.mem_cons_of_mem _ ho'') hne e' π' a' hins'

/-- Sortedness through one update, with the freshness stated only for
inserts (a delete never needs it). -/
theorem eUpdate_sorted_ins {Γ : OrderedPrefixCode} {s : EState α} {o : Op (EOp α)}
    (hs : ESorted s)
    (hne : ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a →
      ∀ x ∈ s, key x.2.2 ≠ key (π ++ Γ.enc (o.1 - a))) :
    ESorted (eUpdate Γ s o) := by
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | del x => exact List.Pairwise.filter _ hs
  | ins e π a =>
      simp only [eUpdate]
      by_cases hmem : t ∈ eIds s
      · rw [if_pos hmem]
        exact hs
      · rw [if_neg hmem]
        exact eInsert_sorted hs (fun x hx => hne e π a rfl x hx)

/-- Sortedness through a whole disciplined continuation. -/
theorem applySeq_sorted {Γ : OrderedPrefixCode} :
    ∀ (τ : List (Op (EOp α))) (s : EState α), ESorted s → ContOK Γ s τ →
      ESorted (show EState α from applySeq (E Γ α).toCRDTSig s τ)
  | [], _, hs, _ => hs
  | o :: τ', s, hs, hok => by
      show ESorted (show EState α from applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ')
      exact applySeq_sorted τ' (eUpdate Γ s o)
        (eUpdate_sorted_ins hs (fun e π a hins x hx =>
          hok.freshKeySt o List.mem_cons_self e π a hins x hx))
        hok.step

/-- Id-nodup through `eInsert` (fresh newcomer). -/
theorem eIds_eInsert_nodup {r : ERec α} : ∀ {s : EState α},
    (eIds s).Nodup → r.1 ∉ eIds s → (eIds (eInsert r s)).Nodup
  | [], _, _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | x :: xs, hnd, hfresh => by
      have hnd' := hnd
      rw [show eIds (x :: xs) = x.1 :: eIds xs from rfl, List.nodup_cons] at hnd'
      by_cases hc : keyLt (key x.2.2) (key r.2.2) = true
      · rw [show eInsert r (x :: xs) = r :: x :: xs from by
          simp only [eInsert]; rw [if_pos hc]]
        exact List.nodup_cons.mpr ⟨hfresh, hnd⟩
      · rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
          simp only [eInsert]; rw [if_neg hc]]
        rw [show eIds (x :: eInsert r xs) = x.1 :: eIds (eInsert r xs) from rfl,
          List.nodup_cons]
        refine ⟨?_, eIds_eInsert_nodup hnd'.2 (fun h =>
          hfresh (List.mem_cons_of_mem _ h))⟩
        intro hmem
        rcases mem_eIds_eInsert.mp hmem with h | h
        · exact hnd'.1 h
        · exact hfresh (h ▸ List.mem_cons_self)

/-- Id-nodup through one update, no side condition at all. -/
theorem eIds_eUpdate_nodup {Γ : OrderedPrefixCode} {s : EState α} {o : Op (EOp α)}
    (h : (eIds s).Nodup) : (eIds (eUpdate Γ s o)).Nodup := by
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | del x =>
      show ((s.filter (fun r => decide (r.1 ≠ x))).map Prod.fst).Nodup
      exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h
  | ins e π a =>
      simp only [eUpdate]
      by_cases hmem : t ∈ eIds s
      · rw [if_pos hmem]
        exact h
      · rw [if_neg hmem]
        exact eIds_eInsert_nodup h hmem

/-- Id-nodup through a whole continuation. -/
theorem applySeq_ids_nodup {Γ : OrderedPrefixCode} :
    ∀ (τ : List (Op (EOp α))) (s : EState α), (eIds s).Nodup →
      (eIds (show EState α from applySeq (E Γ α).toCRDTSig s τ)).Nodup
  | [], _, h => h
  | o :: τ', s, h => by
      show (eIds (show EState α from applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ')).Nodup
      exact applySeq_ids_nodup τ' (eUpdate Γ s o) (eIds_eUpdate_nodup h)

/-- Record provenance from an arbitrary start state: everything in the fold
is a start record or carries the id of some insert of the continuation. -/
theorem applySeq_rec_sub {Γ : OrderedPrefixCode} :
    ∀ (τ : List (Op (EOp α))) (s : EState α),
    ∀ x ∈ (show EState α from applySeq (E Γ α).toCRDTSig s τ),
      x ∈ s ∨ ∃ o ∈ τ, eIsIns o = true ∧ x.1 = o.1
  | [], _, x, hx => Or.inl hx
  | o :: τ', s, x, hx => by
      have hx' : x ∈ (show EState α from applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ') := hx
      rcases applySeq_rec_sub τ' (eUpdate Γ s o) x hx' with h | ⟨o', ho', hi, hid⟩
      · obtain ⟨t, rr, op⟩ := o
        cases op with
        | del y => exact Or.inl (List.mem_of_mem_filter h)
        | ins e π a =>
            simp only [eUpdate] at h
            by_cases hg : t ∈ eIds s
            · rw [if_pos hg] at h
              exact Or.inl h
            · rw [if_neg hg] at h
              rcases mem_eInsert.mp h with h' | h'
              · exact Or.inl h'
              · exact Or.inr ⟨(t, rr, EOp.ins e π a), List.mem_cons_self,
                  rfl, by rw [h']⟩
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', hi, hid⟩

/-- If every standing record sits strictly below the newcomer, the sorted
insert is a plain cons. -/
theorem eInsert_below {r : ERec α} : ∀ {s : EState α},
    (∀ x ∈ s, keyLt (key x.2.2) (key r.2.2) = true) → eInsert r s = r :: s
  | [], _ => rfl
  | x :: xs, h => by
      simp only [eInsert]
      rw [if_pos (h x List.mem_cons_self)]

/-- **Sorted insertion commutes with an id-level filter** (kept newcomer):
on a sorted state, `eInsert` into the filtered list is the filter of the
insert.  The transitivity step is where sortedness is load-bearing. -/
theorem eInsert_filter (q : ERec α → Bool) (r : ERec α) (hqr : q r = true) :
    ∀ (s : EState α), ESorted s →
      eInsert r (s.filter q) = (eInsert r s).filter q
  | [], _ => by simp [eInsert, hqr]
  | x :: xs, hs => by
      have hxs : ESorted xs := (List.pairwise_cons.mp hs).2
      have hbelow := (List.pairwise_cons.mp hs).1
      by_cases hc : keyLt (key x.2.2) (key r.2.2) = true
      · by_cases hqx : q x = true
        · rw [List.filter_cons_of_pos hqx]
          rw [show eInsert r (x :: xs.filter q) = r :: x :: xs.filter q from by
            simp only [eInsert]; rw [if_pos hc]]
          rw [show eInsert r (x :: xs) = r :: x :: xs from by
            simp only [eInsert]; rw [if_pos hc]]
          rw [List.filter_cons_of_pos hqr, List.filter_cons_of_pos hqx]
        · rw [List.filter_cons_of_neg hqx]
          rw [show eInsert r (x :: xs) = r :: x :: xs from by
            simp only [eInsert]; rw [if_pos hc]]
          rw [List.filter_cons_of_pos hqr, List.filter_cons_of_neg hqx]
          exact eInsert_below (fun y hy =>
            keyLt_trans (hbelow y (List.mem_of_mem_filter hy)) hc)
      · by_cases hqx : q x = true
        · rw [List.filter_cons_of_pos hqx]
          rw [show eInsert r (x :: xs.filter q) = x :: eInsert r (xs.filter q) from by
            simp only [eInsert]; rw [if_neg hc]]
          rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
            simp only [eInsert]; rw [if_neg hc]]
          rw [List.filter_cons_of_pos hqx, eInsert_filter q r hqr xs hxs]
        · rw [List.filter_cons_of_neg hqx]
          rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
            simp only [eInsert]; rw [if_neg hc]]
          rw [List.filter_cons_of_neg hqx]
          exact eInsert_filter q r hqr xs hxs

/-- One update commutes with the id-level keep filter (fresh op, kept mint). -/
theorem eUpdate_filter {Γ : OrderedPrefixCode} (kp : ℕ → Bool)
    (s : EState α) (o : Op (EOp α)) (hsort : ESorted s)
    (hfresh : ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a → o.1 ∉ eIds s)
    (hkp : ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a → kp o.1 = true) :
    eUpdate Γ (s.filter (fun r => kp r.1)) o
      = (eUpdate Γ s o).filter (fun r => kp r.1) := by
  obtain ⟨t, rr, op⟩ := o
  cases op with
  | del x =>
      show (s.filter (fun r => kp r.1)).filter (fun r => decide (r.1 ≠ x))
          = (s.filter (fun r => decide (r.1 ≠ x))).filter (fun r => kp r.1)
      rw [filter_and, filter_and]
      exact List.filter_congr (fun r _ => Bool.and_comm _ _)
  | ins e π a =>
      have hni : t ∉ eIds s := hfresh e π a rfl
      have hniF : t ∉ eIds (s.filter (fun r => kp r.1)) := fun h => by
        rcases List.mem_map.mp h with ⟨r, hr, hrt⟩
        exact hni (List.mem_map.mpr ⟨r, List.mem_of_mem_filter hr, hrt⟩)
      simp only [eUpdate]
      rw [if_neg hniF, if_neg hni]
      exact eInsert_filter (fun r => kp r.1) _ (hkp e π a rfl) s hsort

/-- **The continuation commutes with the drop**: folding a disciplined
continuation whose mints are all kept over the filtered state is the filter
of the twin fold.  This is the "subject birth order = twin birth order
filtered to the subject's records" fact the harness checks structurally. -/
theorem applySeq_filter {Γ : OrderedPrefixCode} (kp : ℕ → Bool) :
    ∀ (τ : List (Op (EOp α))) (s : EState α), ESorted s → ContOK Γ s τ →
    (∀ o ∈ τ, ∀ (e : α) (π : List Bool) (a : ℕ), o.2.2 = EOp.ins e π a → kp o.1 = true) →
    applySeq (E Γ α).toCRDTSig (s.filter (fun r => kp r.1)) τ
      = (show EState α from applySeq (E Γ α).toCRDTSig s τ).filter (fun r => kp r.1)
  | [], _, _, _, _ => rfl
  | o :: τ', s, hsort, hok, hkp => by
      show applySeq (E Γ α).toCRDTSig (eUpdate Γ (s.filter (fun r => kp r.1)) o) τ'
          = (show EState α from
              applySeq (E Γ α).toCRDTSig (eUpdate Γ s o) τ').filter (fun r => kp r.1)
      rw [eUpdate_filter kp s o hsort
        (fun e π a h => hok.freshId o List.mem_cons_self e π a h)
        (fun e π a h => hkp o List.mem_cons_self e π a h)]
      exact applySeq_filter kp τ' (eUpdate Γ s o)
        (eUpdate_sorted_ins hsort (fun e π a hins x hx =>
          hok.freshKeySt o List.mem_cons_self e π a hins x hx))
        hok.step
        (fun o' ho' e π a h => hkp o' (List.mem_cons_of_mem _ ho') e π a h)

/-- The re-map commutes with an id-level filter (ids untouched). -/
theorem eRemapSt_filter (f : List Bool → List Bool) (kp : ℕ → Bool) :
    ∀ (s : EState α), (eRemapSt f s).filter (fun r => kp r.1)
      = eRemapSt f (s.filter (fun r => kp r.1))
  | [] => rfl
  | x :: xs => by
      by_cases h : kp x.1 = true
      · rw [show eRemapSt f (x :: xs) = eRemapRec f x :: eRemapSt f xs from rfl]
        rw [show (eRemapRec f x :: eRemapSt f xs).filter (fun r => kp r.1)
            = eRemapRec f x :: (eRemapSt f xs).filter (fun r => kp r.1) from
          List.filter_cons_of_pos h]
        rw [show (x :: xs).filter (fun r => kp r.1) = x :: xs.filter (fun r => kp r.1) from
          List.filter_cons_of_pos h]
        rw [show eRemapSt f (x :: xs.filter (fun r => kp r.1))
            = eRemapRec f x :: eRemapSt f (xs.filter (fun r => kp r.1)) from rfl]
        rw [eRemapSt_filter f kp xs]
      · rw [show eRemapSt f (x :: xs) = eRemapRec f x :: eRemapSt f xs from rfl]
        rw [show (eRemapRec f x :: eRemapSt f xs).filter (fun r => kp r.1)
            = (eRemapSt f xs).filter (fun r => kp r.1) from
          List.filter_cons_of_neg h]
        rw [show (x :: xs).filter (fun r => kp r.1) = xs.filter (fun r => kp r.1) from
          List.filter_cons_of_neg h]
        exact eRemapSt_filter f kp xs

/-! ## §5  O3: the render-congruence capstone

Hypothesis roles:
* `F` with `hdom`/`hmint`: the O1 keep-set stable-prefix map, its domain the
  kept records, its `MintAt` the beyond-cut mints AND declared stragglers
  (whose frozen groups are what makes `ext` dischargeable);
* `kp` with `hdead`: only settled-dead ids are dropped;
* `hanchor`: every present mark's boundaries are kept, the retention roots;
* `hok`: Lamport discipline of the continuation (fresh ids, fresh mint keys);
* the conclusion: the compacted subject renders EQUAL to the never-compacted
  twin, for the whole continuation, every mark, every type. -/

/-- **O3, single epoch (the capstone).**  Retention-roots compaction is
invisible to `renderMarksDoc`: drop the settled-dead non-anchor records,
re-code the kept coordinates by any keep-set stable-prefix map, translate the
continuation's carried prefixes, and every beyond-cut render equals the
uncompacted twin's. -/
theorem marksGC_render_congr {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (s : EState ℕ) (τ : List (Op (EOp ℕ))) (kp : ℕ → Bool)
    (del : List ℕ) (marks : List MarkD) (mt : MType)
    (hsort : ESorted s) (hnd : (eIds s).Nodup)
    (hok : ContOK Γ s τ)
    (hkp : ∀ o ∈ τ, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → kp o.1 = true)
    (hdom : ∀ x ∈ s.filter (fun r => kp r.1), F.Dom x.2.2)
    (hmint : ∀ o ∈ τ, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F.MintAt π (o.1 - a))
    (hdead : ∀ r ∈ s, kp r.1 = false → del.contains r.1 = true)
    (hanchor : ∀ m ∈ marks, kp m.start_id = true ∧ kp m.end_id = true) :
    renderMarksDoc
      (DocD.mk (applySeq (E Γ ℕ).toCRDTSig
        (eRemapSt F.f (s.filter (fun r => kp r.1))) (τ.map (eRemapOp F.f))) del)
      marks mt
    = renderMarksDoc (DocD.mk (applySeq (E Γ ℕ).toCRDTSig s τ) del) marks mt := by
  -- T1: the embed cluster transports the compacted fold
  rw [eRecode_applySeq F τ (s.filter (fun r => kp r.1)) hdom hmint]
  -- coordinates are invisible to the render
  rw [renderMarksDoc_remap F.f _ del marks mt]
  -- the continuation commutes with the drop
  rw [applySeq_filter kp τ s hsort hok hkp]
  -- and the drop is invisible to the resolver (O2 + retention roots)
  have hgoal := renderMarksDoc_dropDoc
    (DocD.mk (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ) del) kp marks mt
    (applySeq_ids_nodup τ s hnd)
    (fun c hc hkpc => by
      -- a dropped final id is a start record's id (mints are kept), hence dead
      rcases List.mem_map.mp hc with ⟨x, hx, hxc⟩
      rcases applySeq_rec_sub τ s x hx with hxs | ⟨o, ho, hins, hid⟩
      · rw [← hxc]
        refine hdead x hxs ?_
        rw [hxc]
        exact hkpc
      · exfalso
        obtain ⟨t, rr, op⟩ := o
        cases op with
        | del y => exact Bool.noConfusion hins
        | ins e π a =>
            have := hkp _ ho e π a rfl
            rw [← hxc, hid] at hkpc
            rw [hkpc] at this
            exact Bool.noConfusion this)
    hanchor
  exact hgoal

/-- **O3, two epochs.**  Compact at a settled cut (`kp₁`, `F₁`), continue
(`τ₁`, settling), compact again (`kp₂`, `F₂`, on the already re-coded
records), continue (`τ₂`, lagging, translated through the composite): the
final render equals the never-compacted twin's.  The composite is the
`StablePrefixMap.comp` of `EmbedRGA_MultiEpoch.lean`, carried at its own
SURVIVING domain (`Rest'`, `MintAt'`): a retention root freed between the
epochs, e.g. by an A3 pair-drop, is exactly the rank-reclaim shape
`naive_composition_collides` pins, and restricting the composite's domain to
the survivors is the fix that file already provides.  n-epoch towers follow
by the same route through `chainSPM`/`CompatOn` (`CompatChain` when nothing
is reclaimed). -/
theorem marksGC_render_congr_twoEpoch {Γ : OrderedPrefixCode}
    (F₁ F₂ : StablePrefixMap Γ)
    (Rest' : List Bool → Prop) (MintAt' : List Bool → ℕ → Prop)
    (hC : CompatOn F₁ F₂ Rest' MintAt')
    (s : EState ℕ) (τ₁ τ₂ : List (Op (EOp ℕ))) (kp₁ kp₂ : ℕ → Bool)
    (del : List ℕ) (marks : List MarkD) (mt : MType)
    (hsort : ESorted s) (hnd : (eIds s).Nodup)
    (hok₁ : ContOK Γ s τ₁)
    (hkp₁ : ∀ o ∈ τ₁, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → kp₁ o.1 = true)
    (hdom₁ : ∀ x ∈ s.filter (fun r => kp₁ r.1), F₁.Dom x.2.2)
    (hmint₁ : ∀ o ∈ τ₁, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → F₁.MintAt π (o.1 - a))
    (hok₂ : ContOK Γ (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁) τ₂)
    (hkp₂ : ∀ o ∈ τ₂, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → (kp₁ o.1 && kp₂ o.1) = true)
    (hdomG : ∀ x ∈ (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁).filter
        (fun r => kp₁ r.1 && kp₂ r.1),
      (F₁.comp F₂ Rest' MintAt' hC).Dom x.2.2)
    (hmintG : ∀ o ∈ τ₂, ∀ (e : ℕ) (π : List Bool) (a : ℕ),
      o.2.2 = EOp.ins e π a → (F₁.comp F₂ Rest' MintAt' hC).MintAt π (o.1 - a))
    (hdead : ∀ r ∈ (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁),
      (kp₁ r.1 && kp₂ r.1) = false → del.contains r.1 = true)
    (hanchor : ∀ m ∈ marks, (kp₁ m.start_id && kp₂ m.start_id) = true ∧
      (kp₁ m.end_id && kp₂ m.end_id) = true) :
    renderMarksDoc
      (DocD.mk (applySeq (E Γ ℕ).toCRDTSig
        (eRemapSt F₂.f
          ((show EState ℕ from applySeq (E Γ ℕ).toCRDTSig
            (eRemapSt F₁.f (s.filter (fun r => kp₁ r.1)))
            (τ₁.map (eRemapOp F₁.f))).filter (fun r => kp₂ r.1)))
        (τ₂.map (eRemapOp (F₁.comp F₂ Rest' MintAt' hC).f))) del)
      marks mt
    = renderMarksDoc
        (DocD.mk (applySeq (E Γ ℕ).toCRDTSig
          (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁) τ₂) del)
        marks mt := by
  have hstage1 :
      ((show EState ℕ from applySeq (E Γ ℕ).toCRDTSig
        (eRemapSt F₁.f (s.filter (fun r => kp₁ r.1)))
        (τ₁.map (eRemapOp F₁.f))).filter (fun r => kp₂ r.1))
      = eRemapSt F₁.f ((show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁).filter
          (fun r => kp₁ r.1 && kp₂ r.1)) := by
    rw [eRecode_applySeq F₁ τ₁ (s.filter (fun r => kp₁ r.1)) hdom₁ hmint₁]
    rw [applySeq_filter kp₁ τ₁ s hsort hok₁ hkp₁]
    rw [eRemapSt_filter F₁.f kp₂]
    rw [filter_and]
  rw [hstage1]
  rw [show eRemapSt F₂.f (eRemapSt F₁.f
      ((show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁).filter
        (fun r => kp₁ r.1 && kp₂ r.1)))
    = eRemapSt (F₁.comp F₂ Rest' MintAt' hC).f
      ((show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁).filter
        (fun r => kp₁ r.1 && kp₂ r.1)) from by
    rw [StablePrefixMap.comp_f, eRemapSt_comp]]
  exact marksGC_render_congr (F₁.comp F₂ Rest' MintAt' hC)
    (show EState ℕ from applySeq (E Γ ℕ).toCRDTSig s τ₁) τ₂
    (fun c => kp₁ c && kp₂ c) del marks mt
    (applySeq_sorted τ₁ s hsort hok₁)
    (applySeq_ids_nodup τ₁ s hnd)
    hok₂ hkp₂ hdomG hmintG hdead hanchor

/-! ## §6  SPOTs: hand-derived, PASS + FAIL shaped

Geometry D1 of the note (§5.1), unary code, hand-worked in the docstrings;
expected values from the note's tables, never `#eval`'d from the model. -/

namespace SPOT

/-! ### O1: a directed keep-set map (D1(b) geometry)

Cut state: `R` = id 7 (root, delta 7, live), `M` = id 6 (root, delta 6, DEAD,
no mark touches it → dropped), `L` = id 2 (root, delta 2, live), `d` = id 3
(child of `L`, delta 1, DEAD, the mark's end anchor → RETAINED).  Declared
straggler: id 4 anchored at `L` (delta 2) → `L`'s child group is FROZEN
(deltas 1, 2 verbatim); the root group renumbers kept deltas 2, 7 to
ordinals 1, 2.  Beyond-cut mint: id 10 at the root (fresh delta 10 dominates
both ordinals). -/

def gcMk (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1
  else if c = unaryCode.enc 7 then unaryCode.enc 2
  else if c = unaryCode.enc 2 ++ unaryCode.enc 1 then unaryCode.enc 1 ++ unaryCode.enc 1
  else if c = unaryCode.enc 2 ++ unaryCode.enc 2 then unaryCode.enc 1 ++ unaryCode.enc 2
  else c

def keepK : KeepSpec :=
  ⟨fun c => c = unaryCode.enc 2 ∨ c = unaryCode.enc 7,
   fun c => c = unaryCode.enc 2 ++ unaryCode.enc 1,
   fun c => c = unaryCode.enc 2⟩

def mintK : List Bool → ℕ → Prop := fun π d =>
  (π = unaryCode.enc 2 ∧ d = 2) ∨ (π = [] ∧ d = 10)

/-- **O1 inhabited**: the retention-roots relabeling of the D1(b) cut is a
`StablePrefixMap` via the `keepSPM` constructor, H3 covers the frozen
straggler mint and the fresh root mint, H2 discharges on all kept/mint
pairs by computation. -/
def keepFmk : StablePrefixMap unaryCode :=
  keepSPM unaryCode keepK gcMk mintK
    (by
      rintro π d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide)
    (by
      intro c c' h h'
      simp only [KeepSpec.kept, keepK, mintK] at h h'
      rcases h with ((rfl | rfl) | rfl | rfl) |
        ⟨π, d, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩ <;>
      rcases h' with ((rfl | rfl) | rfl | rfl) |
        ⟨π', d', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩ <;> decide)

/-- **A1, concretely**: the retained DEAD anchor `d` keeps its display order
against the live `R` under the relabeling, and the map is not the identity
(the compaction is real). -/
theorem keepFmk_A1_dead_live :
    keyLt (key (gcMk (unaryCode.enc 2 ++ unaryCode.enc 1))) (key (gcMk (unaryCode.enc 7)))
      = keyLt (key (unaryCode.enc 2 ++ unaryCode.enc 1)) (key (unaryCode.enc 7))
    ∧ gcMk (unaryCode.enc 7) ≠ unaryCode.enc 7 := by decide

/-- **FAIL (the freeze guard is load-bearing).**  Renumbering a sibling
group that receives a declared in-flight delta flips an order: kept deltas
2 < 9 renumber to 1, 2 while the in-flight 5 arrives verbatim, the
straggler jumps the ex-9 (note §3's freeze example; `keepSPM`'s `hord`
cannot be discharged for this map on a domain containing the mint). -/
def badRenumber (c : List Bool) : List Bool :=
  if c = unaryCode.enc 2 then unaryCode.enc 1
  else if c = unaryCode.enc 9 then unaryCode.enc 2
  else c

theorem freeze_guard_violation :
    keyLt (key (unaryCode.enc 5)) (key (unaryCode.enc 9)) = true ∧
    keyLt (key (badRenumber (unaryCode.enc 5))) (key (badRenumber (unaryCode.enc 9)))
      = false := by decide

/-! ### O2: the scan factorization, concretely -/

/-- PASS: dropping the dead non-anchor 9 leaves the first survivor right of
the retained 5 unchanged (`some 7` both sides). -/
theorem o2_scan_pass :
    scanRight ([4, 5, 9, 7].filter (fun c => c != 9)) [9, 5]
        (idxOf ([4, 5, 9, 7].filter (fun c => c != 9)) 5) = some 7 ∧
    scanRight [4, 5, 9, 7] [9, 5] (idxOf [4, 5, 9, 7] 5) = some 7 := by decide

/-- FAIL: dropping a SURVIVOR (violating O2's hypothesis) changes the scan
(`none` vs `some 7`), the non-surviving side condition is load-bearing. -/
theorem o2_scan_fail_survivor :
    scanRight ([4, 5, 9, 7].filter (fun c => c != 7)) [9, 5]
        (idxOf ([4, 5, 9, 7].filter (fun c => c != 7)) 5) = none ∧
    (none : Option ℕ) ≠ some 7 := by decide

/-- FAIL: dropping the retained element ITSELF (the anchor) breaks the scan
(`none` vs `some 7`), the keep-the-anchor side condition is load-bearing;
this is D6's flip at list level. -/
theorem o2_scan_fail_anchor :
    scanRight ([4, 5, 9, 7].filter (fun c => c != 5)) [9, 5]
        (idxOf ([4, 5, 9, 7].filter (fun c => c != 5)) 5) = none ∧
    (none : Option ℕ) ≠ some 7 := by decide

/-! ### O3 on D1(b): end-inner, straggler variant: through the capstone

Twin (hand, note §5.1 worked sample): final birth order `n̂ R M L n d` with
ids `[10, 7, 6, 2, 4, 3]` (root deltas 10 > 7 > 6 > 2 newest first, then
`L`'s children 4-then-3), live `[10, 7, 2, 4]`, cps `[105, 82, 76, 110]`.
The mark (mid 5, start `L` before, end `d` after): the dead end anchor `d`
scans left past nothing to the straggler `n` (id 4, live), the span is
`{L, n}`, the straggler sits INSIDE the span because its id 4 is below the
mark's mid 5 (no growth-skip).  Render: `[(105, F), (82, F), (76, T),
(110, T)]`.  Subject: `M` dropped, `d` retained dead, coordinates re-coded
by `keepFmk`, straggler + fresh mint folded through the translated ops. -/

def sD1 : EState ℕ :=
  buildShadow unaryCode [(7, 82, 0), (2, 76, 0), (6, 77, 0), (3, 100, 2)]

theorem sD1_eq : sD1 = [(7, 82, unaryCode.enc 7), (6, 77, unaryCode.enc 6),
    (2, 76, unaryCode.enc 2), (3, 100, unaryCode.enc 2 ++ unaryCode.enc 1)] := by
  native_decide

def τD1 : List (Op (EOp ℕ)) :=
  [(4, 0, EOp.ins 110 (unaryCode.enc 2) 2), (10, 0, EOp.ins 105 [] 0)]

def kpD1 : ℕ → Bool := fun c => c != 6

def delD1 : List ℕ := [3, 6]

def mD1b : MarkD :=
  { mid := 5, mtype := MType.bold, start_id := 2, end_id := 3,
    startSide := Side.before, endSide := Side.after }

def dTwinD1 : DocD :=
  { shadow := applySeq (E unaryCode).toCRDTSig sD1 τD1, deleted := delD1 }

def dSubjD1 : DocD :=
  { shadow := applySeq (E unaryCode).toCRDTSig
      (eRemapSt keepFmk.f (sD1.filter (fun r => kpD1 r.1)))
      (τD1.map (eRemapOp keepFmk.f)),
    deleted := delD1 }

/-- PASS: both renders equal the hand value, the straggler is bold (id 4 <
mid 5, inside the span), the fresh root mint is plain. -/
theorem d1b_renders :
    renderMarksDoc dTwinD1 [mD1b] MType.bold
      = [(105, false), (82, false), (76, true), (110, true)] ∧
    renderMarksDoc dSubjD1 [mD1b] MType.bold
      = [(105, false), (82, false), (76, true), (110, true)] := by native_decide

/-- PASS (structure): the subject's birth order is the twin's filtered to
the kept ids (interior dead `M` dropped, dead ANCHOR `d` retained) while
the coordinates genuinely moved (the compaction is not the identity). -/
theorem d1b_structure :
    dSubjD1.birthIds = dTwinD1.birthIds.filter kpD1 ∧
    (6 ∉ dSubjD1.birthIds) ∧ (6 ∈ dTwinD1.birthIds) ∧ (3 ∈ dSubjD1.birthIds) ∧
    dSubjD1.shadow ≠ dTwinD1.shadow.filter (fun r => kpD1 r.1) := by native_decide

/-- **PASS, fired through the capstone**: `marksGC_render_congr` discharges
on the concrete instance, every hypothesis (sortedness, Lamport freshness,
keep-set domain, mints-at-hand, dead-only drop, anchors kept) is checked,
nothing is recomputed. -/
theorem d1b_via_theorem :
    renderMarksDoc dSubjD1 [mD1b] MType.bold
      = renderMarksDoc dTwinD1 [mD1b] MType.bold := by
  refine marksGC_render_congr keepFmk sD1 τD1 kpD1 delD1 [mD1b] MType.bold
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold ESorted
    native_decide
  · native_decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro o ho e π a hins
      simp only [τD1, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> native_decide
    · native_decide
    · intro o ho e π a hins x hx
      simp only [τD1, List.mem_cons, List.not_mem_nil, or_false] at ho
      rw [sD1_eq] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases ho with rfl | rfl <;>
        (injection hins with h1 h2 h3; subst h1; subst h2; subst h3) <;>
        rcases hx with rfl | rfl | rfl | rfl <;> native_decide
    · intro o ho e π a hins o' ho' hne e' π' a' hins'
      simp only [τD1, List.mem_cons, List.not_mem_nil, or_false] at ho ho'
      rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl
      · exact absurd rfl hne
      · injection hins with h1 h2 h3
        subst h1; subst h2; subst h3
        injection hins' with g1 g2 g3
        subst g1; subst g2; subst g3
        native_decide
      · injection hins with h1 h2 h3
        subst h1; subst h2; subst h3
        injection hins' with g1 g2 g3
        subst g1; subst g2; subst g3
        native_decide
      · exact absurd rfl hne
  · intro o ho e π a hins
    simp only [τD1, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> native_decide
  · intro x hx
    have hfilt : sD1.filter (fun r => kpD1 r.1)
        = [(7, 82, unaryCode.enc 7), (2, 76, unaryCode.enc 2),
           (3, 100, unaryCode.enc 2 ++ unaryCode.enc 1)] := by native_decide
    rw [hfilt] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inl rfl))
  · intro o ho e π a hins
    simp only [τD1, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;>
      (injection hins with h1 h2 h3; subst h1; subst h2; subst h3)
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨rfl, by decide⟩
  · intro r hr hkpr
    rw [sD1_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> revert hkpr <;> native_decide
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact ⟨by native_decide, by native_decide⟩

/-! ### O3 on D2: interior drop + respan across the cut (A2 witnessed)

`A` = 1 (root), `B` = 4 (child of `A`, delta 3, dead, NOT an anchor), `C` = 9
(child of `B`, delta 5, live), mark `[A..C]` mid 10, cut, beyond-cut `n` = 20
under `A` (delta 19, newer than the mark).  Twin (hand): birth `A n B C`,
live `A n C`, span `[A..C]` covers all three, the fresh insert WITHIN the
span is formatted.  Subject: `B` dropped (its chain level survives inside
`C`'s re-coded coordinate `enc 1 ++ enc 1 ++ enc 1`), renders identical. -/

def gcD2 (c : List Bool) : List Bool :=
  if c = unaryCode.enc 1 ++ unaryCode.enc 3 ++ unaryCode.enc 5 then
    unaryCode.enc 1 ++ unaryCode.enc 1 ++ unaryCode.enc 1
  else c

def keepKD2 : KeepSpec :=
  ⟨fun c => c = unaryCode.enc 1 ∨ c = unaryCode.enc 1 ++ unaryCode.enc 3 ++ unaryCode.enc 5,
   fun _ => False, fun _ => False⟩

def FD2 : StablePrefixMap unaryCode :=
  keepSPM unaryCode keepKD2 gcD2 (fun π d => π = unaryCode.enc 1 ∧ d = 19)
    (by rintro π d ⟨rfl, rfl⟩; decide)
    (by
      intro c c' h h'
      simp only [KeepSpec.kept, keepKD2, or_false] at h h'
      rcases h with (rfl | rfl) | ⟨π, d, ⟨rfl, rfl⟩, rfl⟩ <;>
        rcases h' with (rfl | rfl) | ⟨π', d', ⟨rfl, rfl⟩, rfl⟩ <;> decide)

def sD2 : EState ℕ := buildShadow unaryCode [(1, 65, 0), (4, 66, 1), (9, 67, 4)]
def τD2 : List (Op (EOp ℕ)) := [(20, 0, EOp.ins 110 (unaryCode.enc 1) 1)]
def kpD2 : ℕ → Bool := fun c => c != 4
def mD2 : MarkD := { mid := 10, mtype := MType.bold, start_id := 1, end_id := 9 }

def dTwinD2 : DocD :=
  { shadow := applySeq (E unaryCode).toCRDTSig sD2 τD2, deleted := [4] }

def dSubjD2 : DocD :=
  { shadow := applySeq (E unaryCode).toCRDTSig
      (eRemapSt FD2.f (sD2.filter (fun r => kpD2 r.1)))
      (τD2.map (eRemapOp FD2.f)),
    deleted := [4] }

/-- PASS: the fresh insert within the span is bold on BOTH sides; the
interior dead record is genuinely gone from the subject (A2 witnessed) and
its chain level survives inside `C`'s re-coded coordinate. -/
theorem d2_renders :
    renderMarksDoc dTwinD2 [mD2] MType.bold = [(65, true), (110, true), (67, true)] ∧
    renderMarksDoc dSubjD2 [mD2] MType.bold = [(65, true), (110, true), (67, true)] ∧
    (4 ∉ dSubjD2.birthIds) ∧ (4 ∈ dTwinD2.birthIds) := by native_decide

/-- PASS (compression): the subject's coordinates are strictly lighter than
the twin's on the kept records, the drop is not a no-op re-coding. -/
theorem d2_compresses :
    ((dSubjD2.shadow.map (fun r => r.2.2.length)).sum
      < (dTwinD2.shadow.map (fun r => r.2.2.length)).sum) := by native_decide

/-! ### D3: two boundaries in one dead run: the order is observable

`A`=1, `x`=2 (child of `A`), `y`=3 (child of `x`), `B`=4 (child of `y`);
bold m1 `[A..x]` mid 10, italic m2 `[A..y]` mid 11; delete `x, y` (one dead
run); straggler `g`=5 (child of `x`) delivered late.  Twin (hand): birth
`A x g y B`, live `A g B`; m1's dead end `x` rehomes left to `A` (covered
`{A}`), m2's dead end `y` rehomes left to `g` (covered `{A, g}`): `g`
carries italic and not bold, the two boundaries' relative order INSIDE the
dead run decides `g`'s formatting.  H-A retains both records, order intact
(the keep-set keeps every boundary anchor; A1 transports the order). -/

def dTwinD3 : DocD :=
  { shadow := buildShadow unaryCode
      [(1, 65, 0), (2, 120, 1), (3, 121, 2), (4, 66, 3), (5, 103, 2)],
    deleted := [2, 3] }

def m1D3 : MarkD := { mid := 10, mtype := MType.bold, start_id := 1, end_id := 2 }
def m2D3 : MarkD := { mid := 11, mtype := MType.italic, start_id := 1, end_id := 3 }

/-- H-B's cut-time rewrite of m2's dead end to the run's left survivor `A`
(side kept), the labelled control. -/
def m2D3_HB : MarkD := { mid := 11, mtype := MType.italic, start_id := 1, end_id := 1 }

theorem d3_twin :
    renderMarksDoc dTwinD3 [m1D3, m2D3] MType.bold
      = [(65, true), (103, false), (66, false)] ∧
    renderMarksDoc dTwinD3 [m1D3, m2D3] MType.italic
      = [(65, true), (103, true), (66, false)] := by native_decide

/-- **FAIL (H-B, the labelled control)**: rewriting m2's dead end to `A` at
the cut erases the boundary order inside the dead run, `g` LOSES italic.
The retention-roots keep-set exists precisely to keep this read. -/
theorem d3_HB_erases_order :
    renderMarksDoc dTwinD3 [m1D3, m2D3_HB] MType.italic
      = [(65, true), (103, false), (66, false)] ∧
    renderMarksDoc dTwinD3 [m1D3, m2D3_HB] MType.italic
      ≠ renderMarksDoc dTwinD3 [m1D3, m2D3] MType.italic := by native_decide

/-! ### D6: the no-retention flip (why the runtime refuses)

D1 geometry, no continuation: `R`=1, `L`=2 (root, newer, reads first),
`d`=3 (child of `L`, dead), mark start `L` before / end `d` after, mid 5.
Twin (hand): the dead end rehomes left from `d` to `L`: covered `{L}`.
NONE-compaction drops `d`'s record.  In THIS file's resolver the recordless
anchor resolves at `idxOf = length`, so the end scan walks from the list end
and lands on `R`: covered `{L, R}`, a DIFFERENT degenerate value than the
Python harness's collapse sentinel (covered `{}`), but a FLIP either way,
which is the load-bearing fact.  Companion: with LIVE anchors the same
compaction reads twin-identical, the refusal is precisely about dead mark
anchors. -/

def dTwinD6 : DocD :=
  { shadow := buildShadow unaryCode [(1, 82, 0), (2, 76, 0), (3, 100, 2)],
    deleted := [3] }

def dNoneD6 : DocD :=
  { shadow := (buildShadow unaryCode [(1, 82, 0), (2, 76, 0), (3, 100, 2)]).filter
      (fun r => r.1 != 3),
    deleted := [3] }

def mD6 : MarkD :=
  { mid := 5, mtype := MType.bold, start_id := 2, end_id := 3,
    startSide := Side.before, endSide := Side.after }

/-- The live-anchor companion mark `[L..R]`. -/
def mD6live : MarkD :=
  { mid := 5, mtype := MType.bold, start_id := 2, end_id := 1,
    startSide := Side.before, endSide := Side.after }

/-- **FAIL (D6, the required negative)**: dropping the dead mark anchor
WITHOUT retention flips the read (`{L}` bold becomes `{L, R}` bold); the
live-anchor companion is twin-identical under the same drop. -/
theorem d6_no_retention_flip :
    renderMarksDoc dTwinD6 [mD6] MType.bold = [(76, true), (82, false)] ∧
    renderMarksDoc dNoneD6 [mD6] MType.bold = [(76, true), (82, true)] ∧
    renderMarksDoc dNoneD6 [mD6] MType.bold
      ≠ renderMarksDoc dTwinD6 [mD6] MType.bold ∧
    renderMarksDoc dNoneD6 [mD6live] MType.bold
      = renderMarksDoc dTwinD6 [mD6live] MType.bold := by native_decide

end SPOT

/-! ## §7  Axiom audit -/

#print axioms keepSPM_A1
#print axioms keepSPM_injOn_kept
#print axioms scanRight_filter
#print axioms scanLeft_filter
#print axioms renderMarksDoc_congr
#print axioms renderMarksDoc_dropDoc
#print axioms renderMarksDoc_remap
#print axioms renderMarksDoc_deleted_congr
#print axioms applySeq_filter
#print axioms marksGC_render_congr
#print axioms marksGC_render_congr_twoEpoch
#print axioms SPOT.keepFmk
#print axioms SPOT.freeze_guard_violation
#print axioms SPOT.d1b_renders
#print axioms SPOT.d1b_via_theorem
#print axioms SPOT.d2_renders
#print axioms SPOT.d3_HB_erases_order
#print axioms SPOT.d6_no_retention_flip

end Sal.ConditionedMRDTs.PeritextEmbed.MarksGC
