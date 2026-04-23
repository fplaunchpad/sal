import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Sal.Interfaces.Set_Extended
import Sal.Tactic.Sal
import Sal.MRDTs.Peritext.Peritext_MRDT

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

/-! ## Read-side projection and rich-text merge-semantic characterizations

Mirror of the CRDT additions — see `Sal/CRDTs/Peritext_CRDT.lean` for
the full scope, caveats, and semantic motivation. The MRDT's state
shape differs (chars as a flat `set CharRec` of `(id, after, ch)`
triples, a `set OpId` tombstone set, and the `set AnchorAttachment`
component), so the concrete definitions adapt; the theorems carry
the same content.

Tiers covered:
1. `readRichText_convergent` — pointwise-`eq` implies identical rich-text read.
2. `expand_contract_{end,start}_{after,before}` — anchor sides decide
   whether concurrent boundary inserts fall inside the mark.
3. `add_beats_remove` — concurrent `AddMark` wins over concurrent
   `RemoveMark` for every covered character (state-based form).
4. `anchors_survive_tombstones` — tombstoning any interior character
   leaves the formatting of the other visible characters unchanged.
-/

open Classical

/-- Lexicographic max on `OpId` (MRDT-local copy; used by the priority rule). -/
def opid_max (a b : OpId) : OpId :=
  if a.1 > b.1 then a
  else if b.1 > a.1 then b
  else if a.2 ≥ b.2 then a
  else b

@[simp] def chars_of   (s : concrete_st) : set CharRec         := Prod.fst s
@[simp] def removed_of (s : concrete_st) : set OpId            := Prod.fst (Prod.snd s)
@[simp] def marks_of   (s : concrete_st) : set AnchorAttachment := Prod.snd (Prod.snd s)

/-- Is mark op `m` present in state `s`?  Present iff either of its
two canonical anchor attachments appears in the marks set. -/
@[simp]
def mark_present (s : concrete_st) (m : MarkOp) : Bool :=
  marks_of s ⟨m.startId, m.startSide, m⟩ ||
  marks_of s ⟨m.endId, m.endSide, m⟩

/-- Is `c` visible in `s`: some `CharRec` has id `c` and `c` is not
tombstoned.  Noncomputable: the existential requires Classical. -/
noncomputable def visible (s : concrete_st) (c : OpId) : Bool :=
  decide (∃ after ch, chars_of s (c, after, ch) = true) && !(removed_of s c)

/-- Was `c` inserted with `after = target`? -/
noncomputable def after_of (s : concrete_st) (c target : OpId) : Bool :=
  decide (∃ ch, chars_of s (c, target, ch) = true)

/-- Boundary-case covering predicate — same content as the CRDT's
version (see its docstring for the anchor-side semantics). -/
noncomputable def in_span_boundary (s : concrete_st) (m : MarkOp) (c : OpId) : Bool :=
  if c = m.startId then !m.startSide
  else if c = m.endId then m.endSide
  else if after_of s c m.startId = true then m.startSide
  else if after_of s c m.endId = true then m.endSide
  else false

/-- Priority: Add beats Remove, else LWW by opId.

**Deliberate departure from paper §4.4.** See the CRDT's `mark_beats`
docstring for the full discussion. In short: the paper uses pure LWW
by `opId` (ignoring `isAdd`); we add an "Add beats Remove" clause so
concurrent formatting doesn't get silently overridden by a stale
`RemoveMark` with a higher `opId`. The paper's own framing calls
Ex 5 "arbitrary deterministic," so both rules satisfy the paper's
intent — ours picks the more user-friendly branch. -/
def mark_beats (a b : MarkOp) : Bool :=
  if a.isAdd && !b.isAdd then true
  else if !a.isAdd && b.isAdd then false
  else decide (opid_max a.opId b.opId = a.opId)

/-- Is `m` the winning covering mark for `(c, mt)` in state `s`? -/
noncomputable def mark_wins (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_boundary s m c = true ∧
  m.markType = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_boundary s m' c = true →
        m'.markType = mt →
        m' ≠ m →
        mark_beats m m' = true

/-- Is visible char `c` formatted with mark type `mt` in state `s`? -/
noncomputable def formatted (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins s m c mt ∧ m.isAdd = true)
  else false

/-- Per-character rich-text read: `some formatting` if visible, else
`none`. The list-valued form would require an RGA traversal
formalization that's out of scope; this per-char function is the
abstraction the convergence theorem is stated against. -/
noncomputable def readRichText (s : concrete_st) : OpId → Option (ℕ → Bool) :=
  fun c => if visible s c = true then some (fun mt => formatted s c mt) else none

set_option maxHeartbeats 0

/-- **Tier 1 — Convergence.** Pointwise `eq` implies identical
rich-text read at every character id.

Proof: the MRDT's `eq` is `∀ x, s₁.i x == s₂.i x` componentwise,
which lifts via `funext` to full functional equality on each set
component, and then to `s₁ = s₂` via `Prod.ext`. `readRichText` is
a pure function of state, so the result follows by `rw`. -/
theorem readRichText_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readRichText s₁ = readRichText s₂ := by
  intro h
  rcases h with ⟨hch, hrm, hmk⟩
  have hch'' : Prod.fst s₁ = Prod.fst s₂ := by
    funext x; have := hch x; simpa using this
  have hrm'' : Prod.fst (Prod.snd s₁) = Prod.fst (Prod.snd s₂) := by
    funext x; have := hrm x; simpa using this
  have hmk'' : Prod.snd (Prod.snd s₁) = Prod.snd (Prod.snd s₂) := by
    funext x; have := hmk x; simpa using this
  have h_eq : s₁ = s₂ := Prod.ext hch'' (Prod.ext hrm'' hmk'')
  rw [h_eq]

/-- **Tier 4 — Anchors survive tombstones.**

Tombstoning any character `c_rm` does not change the formatting of
any other visible character `c ≠ c_rm`.  Parameterized over all
states, all mark types, and all replica ids.  The MRDT's `Remove`
op extends the `removed` set with `c_rm`; `chars` and `marks` are
untouched, and the `removed` lookup at `c` is invariant because
`c ≠ c_rm`. -/
theorem anchors_survive_tombstones
    (s : concrete_st) (c c_rm : OpId) (mt : ℕ) (ts rid : ℕ) :
    c ≠ c_rm →
    formatted s c mt = formatted (do_ s (ts, rid, app_op_t.Remove c_rm)) c mt := by
  intro hne
  -- Removing `c_rm` only adds `c_rm` to the `removed` set; `chars` and
  -- `marks` are untouched. For `c ≠ c_rm`, `removed` lookup at `c`
  -- is invariant: `add c_rm rm c = rm c || (c = c_rm) = rm c`.
  have h_rm_inv : add c_rm (Prod.fst (Prod.snd s)) c = Prod.fst (Prod.snd s) c := by
    simp [add, union, _root_.singleton, hne]
  simp only [formatted, visible, do_, mark_present, marks_of, chars_of,
             removed_of, in_span_boundary, after_of, mark_wins, h_rm_inv]

/-- **Tier 3 — Concurrent Add beats concurrent Remove.**

Same semantic content as the CRDT theorem — see
`Peritext_CRDT.add_beats_remove` for the state-based-vs-op-based
caveat on "concurrent."  If an `AddMark` is present and beats every
other same-type covering mark, the covered character is formatted. -/
theorem add_beats_remove
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp : MarkOp) :
    addOp.isAdd = true →
    addOp.markType = mt →
    mark_present s addOp = true →
    in_span_boundary s addOp c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt_a h_pres_a h_cov_a h_vis h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩

/-- **Tier 2 — Expand/contract at the `endId` boundary (expand case).**

With `endSide = true`, a character inserted immediately after `endId`
is covered — the mark *expands* to include the concurrent boundary
insert. -/
theorem expand_contract_end_after
    (s : concrete_st) (c_new : OpId) (mt : ℕ) (m : MarkOp) :
    m.isAdd = true →
    m.endSide = true →
    m.markType = mt →
    mark_present s m = true →
    visible s c_new = true →
    after_of s c_new m.endId = true →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    ¬ after_of s c_new m.startId = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c_new = true →
           m'.markType = mt →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c_new mt = true := by
  intro h_add h_eSd h_mt h_pres h_vis h_after h_ne_s h_ne_e h_ns_after h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, ?_, h_mt, h_beats⟩, h_add⟩
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Contract at the `endId` boundary.**

With `endSide = false`, the same boundary insert is *not* covered —
the mark *contracts* away from the concurrent boundary insert. -/
theorem expand_contract_end_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.endSide = false →
    m.endId ≠ c_new →
    c_new ≠ m.startId →
    after_of s c_new m.endId = true →
    ¬ after_of s c_new m.startId = true →
    in_span_boundary s m c_new = false := by
  intro h_eSd h_ne h_ne_s h_after h_ns_after
  have h_ne' : c_new ≠ m.endId := fun h => h_ne h.symm
  simp only [in_span_boundary, h_ne_s, h_ne', h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Start-side expansion.** -/
theorem expand_contract_start_after
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.startSide = true →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    after_of s c_new m.startId = true →
    in_span_boundary s m c_new = true := by
  intro h_sSd h_ne_s h_ne_e h_after
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd]
  grind

/-- **Tier 2 (symmetric) — Start-side contraction.** -/
theorem expand_contract_start_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    m.startSide = false →
    c_new ≠ m.startId →
    c_new ≠ m.endId →
    after_of s c_new m.startId = true →
    ¬ after_of s c_new m.endId = true →
    in_span_boundary s m c_new = false := by
  intro h_sSd h_ne_s h_ne_e h_after h_not_after_end
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd, h_not_after_end]
  grind

/-- **Paper Ex 2 — Partially overlapping Adds of the same type.**

If no Remove of type `mt` covers `c`, and some `AddMark` `m` covers
`c` and beats every other covering Add by LWW, then `c` is formatted.
Captures the "union of overlapping bolds is bold" semantics. -/
theorem partial_overlap_all_adds_formatted
    (s : concrete_st) (c : OpId) (mt : ℕ) (m : MarkOp) :
    m.isAdd = true →
    m.markType = mt →
    mark_present s m = true →
    in_span_boundary s m c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m'.isAdd = false →
           False) →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m'.isAdd = true →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt h_pres h_cov h_vis h_no_rem h_beats_adds
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, h_cov, h_mt, ?_⟩, h_add⟩
  intro m' h_pres' h_cov' h_mt' h_ne
  match h_isAdd : m'.isAdd with
  | true  => exact h_beats_adds m' h_pres' h_cov' h_mt' h_isAdd h_ne
  | false => exact absurd (h_no_rem m' h_pres' h_cov' h_mt' h_isAdd) id

/-- **Paper Ex 3 — Different-type Adds coexist.**

Two Adds with distinct `markType` at the same character both apply:
the character is formatted as both. Captures the paper's independence
of mark types. -/
theorem different_type_adds_coexist
    (s : concrete_st) (c : OpId) (mB mI : MarkOp) :
    mB.isAdd = true →
    mI.isAdd = true →
    mB.markType ≠ mI.markType →
    mark_present s mB = true →
    mark_present s mI = true →
    in_span_boundary s mB c = true →
    in_span_boundary s mI c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           m'.markType = mB.markType → m' ≠ mB →
           mark_beats mB m' = true) →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           m'.markType = mI.markType → m' ≠ mI →
           mark_beats mI m' = true) →
    formatted s c mB.markType = true ∧ formatted s c mI.markType = true := by
  intro h_addB h_addI _ h_presB h_presI h_covB h_covI h_vis h_beatsB h_beatsI
  refine ⟨?_, ?_⟩
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mB ⟨⟨h_presB, h_covB, rfl, h_beatsB⟩, h_addB⟩)
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mI ⟨⟨h_presI, h_covI, rfl, h_beatsI⟩, h_addI⟩)

/-- **Paper Ex 5 (negative case) — No covering Add → unformatted.**

If no `AddMark` of type `mt` covers `c` at the boundary, then `c` is
not formatted with `mt`. Holds regardless of priority rule — depends
only on the definition of `formatted`. -/
theorem no_add_cover_implies_unformatted
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    (∀ m, mark_present s m = true →
          in_span_boundary s m c = true →
          m.markType = mt →
          m.isAdd = false) →
    formatted s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins s m c mt ∧ m.isAdd = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : w.isAdd = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl
