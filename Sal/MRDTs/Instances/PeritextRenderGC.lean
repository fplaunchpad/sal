import Sal.MRDTs.Instances.PeritextRender


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

namespace Sal.MRDTs.Instances.PeritextRender.GC

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.EmbedRGA
open Sal.MRDTs.Instances.PeritextRender
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

/-! ## Scan factorization for state collection

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


#print axioms renderMarksDoc_dropDoc

end Sal.MRDTs.Instances.PeritextRender.GC
