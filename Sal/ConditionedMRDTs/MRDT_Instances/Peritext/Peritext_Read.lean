import Sal.ConditionedMRDTs.MRDT_Instances.Peritext.Peritext
import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_MRDT

open Classical

set_option maxHeartbeats 1000000

/-!
# Peritext (FUSED) — the read model and the GENUINE positional intent theorem

The Phase-1 capstone (`Peritext.lean`) certifies state convergence up to `≈`.
It says nothing about the sequence a user reads.  This file:

1. **Read model.**  Generalises the tombstone-free RGA document read
   (`RGA_Tombstone_Free_ReadSide.lean`) to `α := PeritextElt` and interprets
   boundary nodes: `renderRichText` is the reading-order depth-first traversal,
   maintaining an open-`markId → Mark` set.  A `bound … isStart:=true` opens its
   `markId`, the matching `false` closes it; character nodes emit `(codepoint,
   currentFormatting)`; boundary nodes are invisible.  Pairing is explicit, by
   `markId`.

2. **Structural guarantees** (generalise the ReadSide ones): the read shows exactly
   the live nodes (`document_sound` + `mem_document_iff`), and delete removes exactly
   its target (`del_not_in_document`, `del_document_mem`).  Read convergence lifts
   (`document_convergent`, `renderRichText_convergent`).

3. **The genuine intent theorem — the whole point.**  `render_id_active_iff_between`
   (with the region lemmas `render_span_before / _inside / _after`) is an
   INDEPENDENT positional guarantee: a character carries mark-instance `id` **iff**
   it lies, *in reading order*, strictly between `id`'s start-boundary node and its
   end-boundary node.  The right-hand side is a decomposition of the reading-order
   element list, computed differently from the open-set fold — so this is a
   correctness theorem (the fold computes betweenness), **not** a restatement of the
   read (contrast the `oq:linspec` self-referential-spec trap).

   In particular `mark_no_backward_leak`: a character positioned *before* a mark's
   start boundary is never formatted by that mark.  This is precisely the guarantee
   the frozen-path product design **fails** — there, deleting a mark's anchor makes
   the boundary climb tree-ancestry and migrate backward, leaking formatting to
   earlier text (`Peritext_Composed/MarkIntent.lean`, the retracted `mark_*_no_leak`).  Here
   boundaries are live RGA nodes, so a character's formatting is decided by its
   reading-order position, and no boundary migration occurs.

## Honest scope of the guarantee (do not overclaim)

The positional theorem holds **at every fixed reachable state** (it is a static
property of the read).  It forbids the boundary-migration backward leak *by
construction*.  The residual is **not** a formatting leak but the RGA's own
read-*order* cost: `del_can_reorder_survivors`
(`RGA_Tombstone_Free_SPOT.lean`) shows that deleting an *interior* node re-sorts its
surviving children among its siblings by timestamp, which can change the reading
order — and therefore which characters sit between two boundaries.  So under
interior deletion the *span can change membership*, but always by a bounded local
re-sort of the physical sequence, never by a boundary jumping backward to unrelated
earlier text.  The fused corner trades atomicity (the third horn of the trilemma)
for live positioning; that residual is inherited from the RGA and is exactly
`del_can_reorder_survivors`, demonstrated concretely below — the wins
(`fused_no_leak_spot`, `fused_delete_interior_no_leak` vs. the product
retraction) AND the loss (`fused_delete_reformats_survivor`: deleting a plain
character moves an untouched survivor across a mark boundary, re-formatting
it — the do-level sequential-spec failure, machine-checked).
-/

namespace Sal.ConditionedMRDTs.Peritext.Read

/-- The read state: the tombstone-free RGA at the rich-text payload. -/
abbrev St := concrete_st PeritextElt

/-! ## §1  The document-order traversal (generalised from the ReadSide)

Identical to `RGA_Tombstone_Free_ReadSide.lean` but at `α := PeritextElt`; the
traversal only ever inspects `contains`/`anc`, which are payload-agnostic. -/

/-- Id-monotone anchors: every live record's anchor is strictly older. -/
def mono (s : St) : Prop := ∀ t, contains s t = true → anc s t < t

/-- The live children of `p` among the candidate ids, in `ids` order. -/
def children (s : St) (ids : List ℕ) (p : ℕ) : List ℕ :=
  ids.filter (fun c => contains s c && anc s c == p)

/-- Fueled depth-first traversal. -/
def docAux (s : St) (ids : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, p => (children s ids p).flatMap (fun c => c :: docAux s ids fuel c)

def fuelOf (ids : List ℕ) : ℕ := ids.foldr max 0 + 1

/-- **The document read**: node ids in reading order — depth-first from the root
sentinel `0`, siblings in `ids` order (descending = newest first). -/
def document (s : St) (ids : List ℕ) : List ℕ :=
  docAux s ids (fuelOf ids) 0

theorem docAux_zero (s : St) (ids : List ℕ) (p : ℕ) : docAux s ids 0 p = [] := rfl

theorem docAux_succ (s : St) (ids : List ℕ) (f p : ℕ) :
    docAux s ids (f + 1) p
      = (children s ids p).flatMap (fun c => c :: docAux s ids f c) := rfl

theorem mem_children (s : St) (ids : List ℕ) (p c : ℕ) :
    c ∈ children s ids p ↔ (c ∈ ids ∧ contains s c = true ∧ anc s c = p) := by
  simp [children, List.mem_filter]

/-! ### List plumbing -/

theorem flatMap_congr {β γ : Type} {l : List β} {f g : β → List γ}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]

theorem le_foldr_max (ids : List ℕ) : ∀ c ∈ ids, c ≤ ids.foldr max 0 := by
  induction ids with
  | nil => intro c h; cases h
  | cons d ds ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih c h) (le_max_right _ _)

/-! ## §2  Soundness: the read shows only live nodes -/

theorem docAux_mem_sound (s : St) (ids : List ℕ) :
    ∀ f p c, c ∈ docAux s ids f p → contains s c = true ∧ c ∈ ids := by
  intro f
  induction f with
  | zero => intro p c h; rw [docAux_zero] at h; cases h
  | succ f ih =>
    intro p c h
    rw [docAux_succ] at h
    rcases List.mem_flatMap.mp h with ⟨d, hd, hc⟩
    obtain ⟨hdi, hdc, _⟩ := (mem_children s ids p d).mp hd
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hdc, hdi⟩
    · exact ih d c hc'

/-- **Soundness**: everything the read emits is a live identity from `ids`.  The
tombstone-free "no ghosts" headline; no hypotheses. -/
theorem document_sound (s : St) (ids : List ℕ) (c : ℕ)
    (h : c ∈ document s ids) : contains s c = true ∧ c ∈ ids :=
  docAux_mem_sound s ids _ 0 c h

/-- **Delete erases its target from the read** — immediate from soundness. -/
theorem del_not_in_document (s : St) (t r x : ℕ) (pre ids : List ℕ) :
    x ∉ document (do_ s (t, r, app_op_t.Del pre x)) ids := by
  intro h
  have hc := (document_sound _ _ _ h).1
  rw [contains_doDel] at hc
  simp at hc

/-! ## §3  Completeness: the read shows exactly the live set (`wf` + `mono`) -/

theorem children_nil_of_ge (s : St) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) (p : ℕ) (hp : B ≤ p) :
    children s ids p = [] := by
  cases h : children s ids p with
  | nil => rfl
  | cons c cs =>
    exfalso
    have hc : c ∈ children s ids p := h ▸ List.mem_cons_self ..
    obtain ⟨hci, hcc, hca⟩ := (mem_children s ids p c).mp hc
    have h1 : p < c := hca ▸ hmono c hcc
    have h2 : c ≤ B := hB c hci
    omega

theorem mem_docAux_of_child (s : St) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) (f p c : ℕ) (hf : B < f + p)
    (hc : c ∈ children s ids p) : c ∈ docAux s ids f p := by
  cases f with
  | zero =>
    exfalso
    have hp : B ≤ p := by omega
    rw [children_nil_of_ge s ids hmono B hB p hp] at hc
    cases hc
  | succ f =>
    rw [docAux_succ]
    exact List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self ..⟩

theorem docAux_nest (s : St) (ids : List ℕ) (hmono : mono s)
    (B : ℕ) (hB : ∀ c ∈ ids, c ≤ B) :
    ∀ f q p c, B < f + q → p ∈ docAux s ids f q → c ∈ children s ids p →
      c ∈ docAux s ids f q := by
  intro f
  induction f with
  | zero => intro q p c _ hp _; rw [docAux_zero] at hp; cases hp
  | succ f ih =>
    intro q p c hfq hp hc
    rw [docAux_succ] at hp ⊢
    rcases List.mem_flatMap.mp hp with ⟨d, hd, hpd⟩
    obtain ⟨hdi, hdc, hda⟩ := (mem_children s ids q d).mp hd
    have hqd : q < d := hda ▸ hmono d hdc
    have hfd : B < f + d := by omega
    refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
    rcases List.mem_cons.mp hpd with hpd' | hpd'
    · have hcd : c ∈ children s ids d := hpd' ▸ hc
      have : c ∈ docAux s ids f d := mem_docAux_of_child s ids hmono B hB f d c hfd hcd
      exact List.mem_cons.mpr (Or.inr this)
    · have : c ∈ docAux s ids f d := ih d p c hfd hpd' hc
      exact List.mem_cons.mpr (Or.inr this)

theorem mem_document_of_live (s : St) (ids : List ℕ)
    (hmono : mono s) (hwf : wf s)
    (hids : ∀ t, contains s t = true → t ∈ ids) :
    ∀ c, contains s c = true → c ∈ document s ids := by
  have hB : ∀ c ∈ ids, c ≤ ids.foldr max 0 := le_foldr_max ids
  set B := ids.foldr max 0 with hBdef
  have hfuel : fuelOf ids = B + 1 := rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcid : c ∈ ids := hids c hc
    have hchild : c ∈ children s ids (anc s c) :=
      (mem_children s ids (anc s c) c).mpr ⟨hcid, hc, rfl⟩
    unfold document
    rcases hwf c hc with h0 | hplive
    · rw [h0] at hchild
      exact mem_docAux_of_child s ids hmono B hB (fuelOf ids) 0 c (by omega) hchild
    · have hplt : anc s c < c := hmono c hc
      have hpdoc : anc s c ∈ docAux s ids (fuelOf ids) 0 := ih (anc s c) hplt hplive
      exact docAux_nest s ids hmono B hB (fuelOf ids) 0 (anc s c) c (by omega)
        hpdoc hchild

/-- **The read is exactly the live set** on `wf`+`mono` states with a covering
candidate list — no tombstone read, no live element hidden. -/
theorem mem_document_iff (s : St) (ids : List ℕ)
    (hmono : mono s) (hwf : wf s)
    (hids : ∀ t, contains s t = true → t ∈ ids) (c : ℕ) :
    c ∈ document s ids ↔ contains s c = true :=
  ⟨fun h => (document_sound s ids c h).1, mem_document_of_live s ids hmono hwf hids c⟩

/-- **Delete removes exactly its target from the read's membership.** -/
theorem del_document_mem (s : St) (t r x : ℕ) (pre ids : List ℕ)
    (hmono : mono (do_ s (t, r, .Del pre x)))
    (hwf : wf (do_ s (t, r, .Del pre x)))
    (hids : ∀ k, contains (do_ s (t, r, .Del pre x)) k = true → k ∈ ids)
    (c : ℕ) :
    c ∈ document (do_ s (t, r, .Del pre x)) ids
      ↔ (c ∈ ids ∧ contains s c = true ∧ c ≠ x) := by
  rw [mem_document_iff _ ids hmono hwf hids c, contains_doDel]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hids c (by rw [contains_doDel, h1, Bool.true_and]; exact bne_iff_ne.mpr h2), h1, h2⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩

/-! ## §4  Convergence at the read -/

theorem children_congr_of_eq {s₁ s₂ : St} (h : eq s₁ s₂)
    (ids : List ℕ) (p : ℕ) : children s₁ ids p = children s₂ ids p := by
  unfold children
  apply List.filter_congr
  intro c _
  obtain ⟨hc, hs⟩ := h c
  by_cases h1 : contains s₁ c = true
  · have h2 : contains s₂ c = true := hc ▸ h1
    have hanc : anc s₁ c = anc s₂ c := congrArg Prod.snd (hs h1)
    simp only [h1, h2, hanc]
  · simp only [Bool.not_eq_true] at h1
    have h2 : contains s₂ c = false := hc ▸ h1
    simp only [h1, h2, Bool.false_and]

theorem docAux_congr_of_eq {s₁ s₂ : St} (h : eq s₁ s₂)
    (ids : List ℕ) : ∀ f p, docAux s₁ ids f p = docAux s₂ ids f p := by
  intro f
  induction f with
  | zero => intro p; rfl
  | succ f ih =>
    intro p
    rw [docAux_succ, docAux_succ, children_congr_of_eq h ids p]
    apply flatMap_congr
    intro c _
    show c :: docAux s₁ ids f c = c :: docAux s₂ ids f c
    rw [ih c]

/-- **Convergence at the read** (identities): `≈`-converged states read the same
node sequence. -/
theorem document_convergent {s₁ s₂ : St} (h : eq s₁ s₂)
    (ids : List ℕ) : document s₁ ids = document s₂ ids :=
  docAux_congr_of_eq h ids (fuelOf ids) 0

/-! ## §5  The rich-text render (open-`markId` set fold)

`renderRichText` walks the reading-order element sequence, maintaining the open
`(markId, Mark)` pairs.  A start boundary opens its pair, a close removes it by
`markId`; characters emit their codepoint tagged with the current formatting;
boundary nodes are invisible.  Everything below the RGA layer is a **pure** fold on
`List PeritextElt` — this is what makes the positional theorem a genuine, independent
statement rather than a restatement of the traversal. -/

/-- Open marks carried by the fold: `(markId, Mark)` pairs, most-recent first. -/
abbrev OpenSet := List (ℕ × Mark)

/-- A rendered character: its codepoint and the open-mark set active at it. -/
abbrev Rendered := ℕ × OpenSet

/-- The open set after processing a reading-order element list. -/
def openAfter : List PeritextElt → OpenSet → OpenSet
  | [], acc => acc
  | PeritextElt.char _ :: rest, acc => openAfter rest acc
  | PeritextElt.bound id mk true :: rest, acc => openAfter rest ((id, mk) :: acc)
  | PeritextElt.bound id _mk false :: rest, acc =>
      openAfter rest (acc.filter (fun p => p.1 != id))

@[simp] theorem openAfter_nil (acc : OpenSet) : openAfter [] acc = acc := rfl
@[simp] theorem openAfter_char (c : ℕ) (rest : List PeritextElt) (acc : OpenSet) :
    openAfter (PeritextElt.char c :: rest) acc = openAfter rest acc := rfl
@[simp] theorem openAfter_open (id : ℕ) (mk : Mark) (rest : List PeritextElt) (acc : OpenSet) :
    openAfter (PeritextElt.bound id mk true :: rest) acc = openAfter rest ((id, mk) :: acc) := rfl
@[simp] theorem openAfter_close (id : ℕ) (mk : Mark) (rest : List PeritextElt) (acc : OpenSet) :
    openAfter (PeritextElt.bound id mk false :: rest) acc
      = openAfter rest (acc.filter (fun p => p.1 != id)) := rfl

/-- The per-character render: one entry per char, in reading order, tagged with the
open-mark set active at it. -/
def renderAux : List PeritextElt → OpenSet → List Rendered
  | [], _ => []
  | PeritextElt.char c :: rest, acc => (c, acc) :: renderAux rest acc
  | PeritextElt.bound id mk true :: rest, acc => renderAux rest ((id, mk) :: acc)
  | PeritextElt.bound id _mk false :: rest, acc =>
      renderAux rest (acc.filter (fun p => p.1 != id))

@[simp] theorem renderAux_nil (acc : OpenSet) : renderAux [] acc = [] := rfl
@[simp] theorem renderAux_char (c : ℕ) (rest : List PeritextElt) (acc : OpenSet) :
    renderAux (PeritextElt.char c :: rest) acc = (c, acc) :: renderAux rest acc := rfl
@[simp] theorem renderAux_open (id : ℕ) (mk : Mark) (rest : List PeritextElt) (acc : OpenSet) :
    renderAux (PeritextElt.bound id mk true :: rest) acc = renderAux rest ((id, mk) :: acc) := rfl
@[simp] theorem renderAux_close (id : ℕ) (mk : Mark) (rest : List PeritextElt) (acc : OpenSet) :
    renderAux (PeritextElt.bound id mk false :: rest) acc
      = renderAux rest (acc.filter (fun p => p.1 != id)) := rfl

/-- The rendered spans of a reading-order element list. -/
def renderSpans (es : List PeritextElt) : List Rendered := renderAux es []

/-- The Boolean formatting query: is any open mark equal to `mk`? -/
def formatOf (acc : OpenSet) (mk : Mark) : Bool := acc.any (fun p => decide (p.2 = mk))

/-- The reading-order element sequence of the document. -/
def docElts (s : St) (ids : List ℕ) : List PeritextElt := (document s ids).map (el s)

/-- **The rich-text read**: reading-order characters, each tagged with the
formatting predicate `Mark → Bool` active at it. -/
def renderRichText (s : St) (ids : List ℕ) : List (ℕ × (Mark → Bool)) :=
  (renderSpans (docElts s ids)).map (fun r => (r.1, formatOf r.2))

/-! ## §6  Predicates for the positional theorem -/

/-- The element list carries no boundary for mark-instance `id`. -/
def NoBoundId (id : ℕ) (es : List PeritextElt) : Prop :=
  ∀ e ∈ es, ∀ (mk : Mark) (b : Bool), e ≠ PeritextElt.bound id mk b

/-- No open pair has mark-instance `id`. -/
def NoIdOpen (id : ℕ) (acc : OpenSet) : Prop := ∀ mk, (id, mk) ∉ acc

/-- Some open pair has mark-instance `id`. -/
def HasIdOpen (id : ℕ) (acc : OpenSet) : Prop := ∃ mk, (id, mk) ∈ acc

/-- Mark-instance `id` is active at a rendered character. -/
def IdActive (id : ℕ) (r : Rendered) : Prop := HasIdOpen id r.2

theorem noBoundId_tail {id : ℕ} {e : PeritextElt} {rest : List PeritextElt}
    (h : NoBoundId id (e :: rest)) : NoBoundId id rest :=
  fun e' he' mk b => h e' (List.mem_cons_of_mem _ he') mk b

theorem noBoundId_head_ne {id id' : ℕ} {mk' : Mark} {b' : Bool} {rest : List PeritextElt}
    (h : NoBoundId id (PeritextElt.bound id' mk' b' :: rest)) : id' ≠ id := by
  intro he
  exact h (PeritextElt.bound id' mk' b') (List.mem_cons_self ..) mk' b' (by rw [he])

theorem noId_filter (id : ℕ) (acc : OpenSet) :
    NoIdOpen id (acc.filter (fun p => p.1 != id)) := by
  intro mk h
  rw [List.mem_filter] at h
  obtain ⟨_, hne⟩ := h
  simp at hne

/-! ## §7  The two fold-invariants: id stays absent / stays present across a
segment with no boundary for it -/

/-- If `id` is absent from the open set and the segment opens/closes no boundary for
`id`, then `id` stays absent — and no rendered character in the segment carries it. -/
theorem noId_render (id : ℕ) :
    ∀ (es : List PeritextElt) (acc : OpenSet),
      NoIdOpen id acc → NoBoundId id es →
      (∀ r ∈ renderAux es acc, ¬ IdActive id r) ∧ NoIdOpen id (openAfter es acc) := by
  intro es
  induction es with
  | nil =>
    intro acc hacc _
    refine ⟨fun r hr => ?_, by simpa using hacc⟩
    simp only [renderAux_nil] at hr
    cases hr
  | cons e rest ih =>
    intro acc hacc hnb
    have hnbrest : NoBoundId id rest := noBoundId_tail hnb
    cases e with
    | char c =>
      obtain ⟨ihr, iho⟩ := ih acc hacc hnbrest
      refine ⟨?_, by rw [openAfter_char]; exact iho⟩
      intro r hr
      rw [renderAux_char] at hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · intro hact; obtain ⟨mk, hmk⟩ := hact; exact hacc mk hmk
      · exact ihr r hr'
    | bound id' mk' b =>
      have hid' : id' ≠ id := noBoundId_head_ne hnb
      cases b with
      | true =>
        have hacc' : NoIdOpen id ((id', mk') :: acc) := by
          intro mk h
          rcases List.mem_cons.mp h with heq | hmem
          · exact hid' (congrArg Prod.fst heq).symm
          · exact hacc mk hmem
        obtain ⟨ihr, iho⟩ := ih ((id', mk') :: acc) hacc' hnbrest
        exact ⟨by intro r hr; rw [renderAux_open] at hr; exact ihr r hr,
               by rw [openAfter_open]; exact iho⟩
      | false =>
        have hacc' : NoIdOpen id (acc.filter (fun p => p.1 != id')) := by
          intro mk h; rw [List.mem_filter] at h; exact hacc mk h.1
        obtain ⟨ihr, iho⟩ := ih _ hacc' hnbrest
        exact ⟨by intro r hr; rw [renderAux_close] at hr; exact ihr r hr,
               by rw [openAfter_close]; exact iho⟩

/-- If `id` is present in the open set and the segment opens/closes no boundary for
`id`, then `id` stays present — and every rendered character in the segment carries
it. -/
theorem hasId_render (id : ℕ) :
    ∀ (es : List PeritextElt) (acc : OpenSet),
      HasIdOpen id acc → NoBoundId id es →
      (∀ r ∈ renderAux es acc, IdActive id r) ∧ HasIdOpen id (openAfter es acc) := by
  intro es
  induction es with
  | nil =>
    intro acc hacc _
    refine ⟨fun r hr => ?_, by simpa using hacc⟩
    simp only [renderAux_nil] at hr
    cases hr
  | cons e rest ih =>
    intro acc hacc hnb
    have hnbrest : NoBoundId id rest := noBoundId_tail hnb
    cases e with
    | char c =>
      obtain ⟨ihr, iho⟩ := ih acc hacc hnbrest
      refine ⟨?_, by rw [openAfter_char]; exact iho⟩
      intro r hr
      rw [renderAux_char] at hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact hacc
      · exact ihr r hr'
    | bound id' mk' b =>
      have hid' : id' ≠ id := noBoundId_head_ne hnb
      cases b with
      | true =>
        obtain ⟨mk0, hmk0⟩ := hacc
        have hacc' : HasIdOpen id ((id', mk') :: acc) :=
          ⟨mk0, List.mem_cons_of_mem _ hmk0⟩
        obtain ⟨ihr, iho⟩ := ih ((id', mk') :: acc) hacc' hnbrest
        exact ⟨by intro r hr; rw [renderAux_open] at hr; exact ihr r hr,
               by rw [openAfter_open]; exact iho⟩
      | false =>
        obtain ⟨mk0, hmk0⟩ := hacc
        have hne : id ≠ id' := fun h => hid' h.symm
        have hacc' : HasIdOpen id (acc.filter (fun p => p.1 != id')) := by
          refine ⟨mk0, ?_⟩
          rw [List.mem_filter]
          exact ⟨hmk0, by simp only [bne_iff_ne, ne_eq]; exact hne⟩
        obtain ⟨ihr, iho⟩ := ih _ hacc' hnbrest
        exact ⟨by intro r hr; rw [renderAux_close] at hr; exact ihr r hr,
               by rw [openAfter_close]; exact iho⟩

/-! ## §8  The decomposition and the GENUINE positional intent theorem -/

/-- Splitting the render over a concatenation. -/
theorem renderAux_append (xs ys : List PeritextElt) (acc : OpenSet) :
    renderAux (xs ++ ys) acc = renderAux xs acc ++ renderAux ys (openAfter xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons e xs ih =>
    cases e with
    | char c =>
      rw [List.cons_append, renderAux_char, renderAux_char, openAfter_char, ih, List.cons_append]
    | bound id mk b =>
      cases b with
      | true => rw [List.cons_append, renderAux_open, renderAux_open, openAfter_open, ih]
      | false => rw [List.cons_append, renderAux_close, renderAux_close, openAfter_close, ih]

/-- The render of a well-nested document splits at the two boundary nodes: a
`before` block, the `inside` block (rendered with `id` open), and an `after` block
(rendered with `id` closed).  Pure and unconditional (no well-nesting needed). -/
theorem renderSpans_decompose
    (before inside after : List PeritextElt) (id : ℕ) (mk : Mark) :
    renderSpans (before ++ PeritextElt.bound id mk true ::
        (inside ++ PeritextElt.bound id mk false :: after))
      = renderAux before []
        ++ renderAux inside ((id, mk) :: openAfter before [])
        ++ renderAux after
            ((openAfter inside ((id, mk) :: openAfter before [])).filter (fun p => p.1 != id)) := by
  unfold renderSpans
  rw [renderAux_append, renderAux_open, renderAux_append, renderAux_close,
      List.append_assoc]

/-- **No backward leak**: every character positioned *before* a mark's start
boundary (in reading order) carries no activation of that mark instance.  This is
exactly the guarantee the frozen-path product design fails: there, deleting the
mark's anchor migrates the boundary backward and leaks formatting to earlier text
(`Peritext_Composed/MarkIntent.lean`).  Here the boundary is a live node, so a character's
formatting is decided by its reading-order position — no migration. -/
theorem render_span_before (before : List PeritextElt) (id : ℕ)
    (hb : NoBoundId id before) :
    ∀ r ∈ renderAux before ([] : OpenSet), ¬ IdActive id r :=
  (noId_render id before [] (fun _ h => by simp at h) hb).1

/-- **Formatted between**: every character positioned strictly *between* the two
boundaries carries the mark instance. -/
theorem render_span_inside (before inside : List PeritextElt) (id : ℕ) (mk : Mark)
    (hi : NoBoundId id inside) :
    ∀ r ∈ renderAux inside ((id, mk) :: openAfter before []), IdActive id r :=
  (hasId_render id inside _ ⟨mk, List.mem_cons_self ..⟩ hi).1

/-- **No forward leak**: every character positioned *after* a mark's end boundary
carries no activation of that mark instance. -/
theorem render_span_after (before inside after : List PeritextElt) (id : ℕ) (mk : Mark)
    (ha : NoBoundId id after) :
    ∀ r ∈ renderAux after
        ((openAfter inside ((id, mk) :: openAfter before [])).filter (fun p => p.1 != id)),
      ¬ IdActive id r :=
  (noId_render id after _ (noId_filter id _) ha).1

/-- **THE GENUINE POSITIONAL INTENT THEOREM.**  For a well-nested document
(mark-instance `id`'s only boundaries are the named start/end nodes), a rendered
character carries mark `id` **iff** it lies, in reading order, strictly between
`id`'s start boundary and its end boundary — i.e. iff it belongs to the `inside`
block.  The right-hand side is a decomposition of the reading-order element list,
computed independently of the open-set fold, so this is a correctness theorem, not a
restatement of the read. -/
theorem render_id_active_iff_between
    (before inside after : List PeritextElt) (id : ℕ) (mk : Mark)
    (hb : NoBoundId id before) (hi : NoBoundId id inside) (ha : NoBoundId id after)
    (r : Rendered)
    (hr : r ∈ renderSpans
        (before ++ PeritextElt.bound id mk true :: (inside ++ PeritextElt.bound id mk false :: after))) :
    IdActive id r ↔ r ∈ renderAux inside ((id, mk) :: openAfter before []) := by
  rw [renderSpans_decompose] at hr
  constructor
  · intro hact
    rcases List.mem_append.mp hr with hL | hAfter
    · rcases List.mem_append.mp hL with hBefore | hIn
      · exact absurd hact (render_span_before before id hb r hBefore)
      · exact hIn
    · exact absurd hact (render_span_after before inside after id mk ha r hAfter)
  · intro hIn
    exact render_span_inside before inside id mk hi r hIn

/-! ## §9  Bridge to the Boolean read and read-convergence for rich text -/

/-- The Boolean formatting query reflects mark membership in the open set. -/
theorem formatOf_true_iff (acc : OpenSet) (mk : Mark) :
    formatOf acc mk = true ↔ ∃ id, (id, mk) ∈ acc := by
  unfold formatOf
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hdec⟩
    have hpm : p.2 = mk := of_decide_eq_true hdec
    exact ⟨p.1, by rw [← hpm]; exact hp⟩
  · rintro ⟨id, hid⟩
    exact ⟨(id, mk), hid, by simp⟩

/-- Convergence of the rich-text read: `≈`-converged states render the same rich
text (identities and formatting). -/
theorem renderRichText_convergent {s₁ s₂ : St} (h : eq s₁ s₂) (ids : List ℕ) :
    renderRichText s₁ ids = renderRichText s₂ ids := by
  have hdoc : docElts s₁ ids = docElts s₂ ids := by
    unfold docElts
    rw [document_convergent h ids]
    apply List.map_congr_left
    intro c hc
    have hlive : contains s₂ c = true := (document_sound s₂ ids c hc).1
    obtain ⟨hcc, hcs⟩ := h c
    show (sel s₁ c).1 = (sel s₂ c).1
    rw [hcs (by rw [hcc]; exact hlive)]
  unfold renderRichText
  rw [hdoc]

/-! ## Axiom audit — the read model and the genuine intent theorems are kernel-clean -/

section AxiomAudit
#print axioms document_sound
#print axioms mem_document_iff
#print axioms del_not_in_document
#print axioms del_document_mem
#print axioms document_convergent
#print axioms renderRichText_convergent
#print axioms render_span_before
#print axioms render_span_inside
#print axioms render_span_after
#print axioms render_id_active_iff_between
#print axioms formatOf_true_iff
end AxiomAudit

end Sal.ConditionedMRDTs.Peritext.Read

/-! ## §10  Axiom audit + concrete contrast SPOT

The genuine intent theorems are kernel-clean; the contrast scenario is `native_decide`
on a concrete trace (SPOT convention: general theorems kernel-clean, concrete facts by
`native_decide`). -/

namespace Sal.ConditionedMRDTs.Peritext.ReadSPOT

open Sal.ConditionedMRDTs.Peritext
open Sal.ConditionedMRDTs.Peritext.Read

/-- Build a concrete `PeritextElt` RGA state from `(id, element, anchor)` records
(the payload analogue of the core's ℕ-only `mk`). -/
def build (recs : List (ℕ × PeritextElt × ℕ)) : St :=
  recs.foldl (fun s r => upd s r.1 (r.2.1, r.2.2)) (init_st (α := PeritextElt))

/-- A concrete document: chain `0 ← A ← startBold ← B ← C ← endBold`, i.e.
characters A B C with a bold mark spanning [B, C].  Ids ascend along the chain so
the reading order is `[1,2,3,4,5]` (each node the sole child of the previous). -/
def docBold : St :=
  build [ (1, PeritextElt.char 65, 0)               -- 'A'
      , (2, PeritextElt.bound 100 Mark.bold true, 1)   -- <bold>
      , (3, PeritextElt.char 66, 2)               -- 'B'
      , (4, PeritextElt.char 67, 3)               -- 'C'
      , (5, PeritextElt.bound 100 Mark.bold false, 4) ] -- </bold>

/-- The rendered rich text: A is plain, B and C are bold. -/
theorem docBold_render :
    (renderRichText docBold [5, 4, 3, 2, 1]).map (fun r => (r.1, r.2 Mark.bold))
      = [(65, false), (66, true), (67, true)] := by native_decide

/-- **The fused design stays correct under deletion of the mark's start anchor.**
Delete `A` (id 1), the character the start boundary is anchored to.  The boundary
node `2` survives and rehomes to the root; the reading order becomes `[2,3,4,5]` and
the render is B(bold) C(bold) — A is gone, and crucially **no earlier text became
bold**.  In the frozen-path product design deleting an anchor migrates the boundary
backward along tree-ancestry and leaks bold to preceding text
(`Peritext_Composed/MarkIntent.lean`, the retracted `mark_*_no_leak`); here it cannot. -/
theorem fused_no_leak_spot :
    (renderRichText (do_ docBold (9, 1, .Del [] 1)) [5, 4, 3, 2]).map (fun r => (r.1, r.2 Mark.bold))
      = [(66, true), (67, true)] := by native_decide

/-- **No backward leak, concretely.**  Delete the interior character `B` (id 3):
`C` rehomes under the start boundary, and `A` — positioned before the start boundary
— stays plain while `C` stays bold.  The mark's span shrank to exactly its surviving
member; nothing before the start boundary was formatted. -/
theorem fused_delete_interior_no_leak :
    (renderRichText (do_ docBold (9, 1, .Del [2, 1] 3)) [5, 4, 2, 1]).map (fun r => (r.1, r.2 Mark.bold))
      = [(65, false), (67, true)] := by native_decide

/-! ### The inherited residual, concretely — the loss, not just the wins

The two SPOTs above are the favorable cases.  The header's "honest scope"
paragraph owes the unfavorable one a witness: the fused design inherits the
RGA's delete-reorder anomaly (`del_can_reorder_survivors`,
`RGA_Tombstone_Free_SPOT.lean`), and at the render layer that anomaly is a
**span-membership change**: deleting a plain character can move a surviving
character across a mark boundary, re-formatting text the delete never touched.
Single replica, `do_`-built (KC's `s_bac` shape lifted to `char ⊕ boundary`),
invisible to the convergence capstone (`oq:linspec`). -/

/-- KC's reordering witness at the rich-text payload, built through `do_`:
`⟨bold⟩`(1) ← `X`(2), then two siblings under `X` — `P`(3, plain char) and
`⟨/bold⟩`(4, newer, so it reads first) — and `C`(5) under `P`.  Reading order
`[⟨bold⟩, X, ⟨/bold⟩, P, C]`: the bold span is exactly `{X}`. -/
def docResidual : St :=
  do_ (do_ (do_ (do_ (do_ (init_st (α := PeritextElt))
    (1, 0, .Ins (PeritextElt.bound 100 Mark.bold true) [] 0))
    (2, 0, .Ins (PeritextElt.char 88) [] 1))          -- 'X'
    (3, 0, .Ins (PeritextElt.char 80) [1] 2))         -- 'P'
    (4, 0, .Ins (PeritextElt.bound 100 Mark.bold false) [1] 2))
    (5, 0, .Ins (PeritextElt.char 67) [2, 1] 3)       -- 'C'

/-- Before the delete: `X` is bold; `P` and `C` are plain. -/
theorem docResidual_render :
    (renderRichText docResidual [5, 4, 3, 2, 1]).map (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (80, false), (67, false)] := by native_decide

/-- **Deleting the plain character `P` re-formats `C`.**  `C` rehomes to `X`
and, being newest among `X`'s children (id 5 > 4), leapfrogs the close
boundary: reading order becomes `[⟨bold⟩, X, C, ⟨/bold⟩]` and `C` is now
INSIDE the bold span.  The delete touched neither `C` nor any boundary. -/
theorem fused_delete_moves_char_into_span :
    (renderRichText (do_ docResidual (9, 0, .Del [2, 1] 3)) [5, 4, 2, 1]).map
        (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (67, true)] := by native_decide

/-- The refutation shape (mirroring `del_a_breaks_survivor_order`): the
post-delete render is NOT the pre-delete render with the deleted character
removed — formatting of an untouched survivor changed.  This is the sequential
(single-replica) spec failure the fused Peritext inherits from the rehoming
RGA's `do_`, at the layer users read. -/
theorem fused_delete_reformats_survivor :
    (renderRichText (do_ docResidual (9, 0, .Del [2, 1] 3)) [5, 4, 2, 1]).map
        (fun r => (r.1, r.2 Mark.bold))
      ≠ ((renderRichText docResidual [5, 4, 3, 2, 1]).map
          (fun r => (r.1, r.2 Mark.bold))).filter (fun r => r.1 ≠ 80) := by
  native_decide

end Sal.ConditionedMRDTs.Peritext.ReadSPOT
