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

/-- **Paper Ex 5 (positive case) — concurrent Add wins over concurrent
Remove.** Our rule's key departure from paper §4.4 — see the CRDT
`Peritext_ReadSide.lean` for the full docstring. -/
theorem add_wins_over_concurrent_remove
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp remOp : MarkOp) :
    addOp.isAdd = true →
    remOp.isAdd = false →
    addOp.markType = mt →
    remOp.markType = mt →
    mark_present s addOp = true →
    mark_present s remOp = true →
    in_span_boundary s addOp c = true →
    in_span_boundary s remOp c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           m'.markType = mt →
           m' ≠ addOp → m' ≠ remOp →
           mark_beats addOp m' = true) →
    formatted s c mt = true := by
  intro h_add h_rem h_mt_a _ h_pres_a _ h_cov_a _ h_vis h_beats
  refine add_beats_remove s c mt addOp h_add h_mt_a h_pres_a h_cov_a h_vis ?_
  intro m' h_pres' h_cov' h_mt' h_ne_add
  by_cases h_eq : m' = remOp
  · subst h_eq
    simp [mark_beats, h_add, h_rem]
  · exact h_beats m' h_pres' h_cov' h_mt' h_ne_add h_eq

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

/-! ## Interior-span coverage (paper Ex 1)

Mirror of the CRDT's interior-coverage section. See the CRDT
`Peritext_ReadSide.lean` for the full scope discussion — in short,
`covered_interior` is a sound-but-incomplete approximation of the
paper's "insertion within a span" semantics, built as the transitive
closure of `in_span_boundary` under the `after_of` relation. Fully
capturing Ex 1 requires formalizing the RGA's visible-order
traversal and is deferred as follow-up work. -/

inductive afters_reach (s : concrete_st) : OpId → OpId → Prop where
  | refl (c : OpId) : afters_reach s c c
  | step {c c_parent anc : OpId} :
      after_of s c c_parent = true →
      afters_reach s c_parent anc →
      afters_reach s c anc

inductive covered_interior (s : concrete_st) (m : MarkOp) : OpId → Prop where
  | boundary (c : OpId) :
      in_span_boundary s m c = true → covered_interior s m c
  | propagate {c c_parent : OpId} :
      covered_interior s m c_parent →
      after_of s c c_parent = true →
      c ≠ m.startId →
      c ≠ m.endId →
      covered_interior s m c

theorem covered_interior_of_boundary
    (s : concrete_st) (m : MarkOp) (c : OpId) :
    in_span_boundary s m c = true → covered_interior s m c :=
  covered_interior.boundary c

/-- Paper Ex 1, one-step form: a concurrent insert at an already-
covered interior character inherits the mark. -/
theorem covered_interior_propagate
    (s : concrete_st) (m : MarkOp) (c c_parent : OpId) :
    covered_interior s m c_parent →
    after_of s c c_parent = true →
    c ≠ m.startId →
    c ≠ m.endId →
    covered_interior s m c :=
  fun h_cov h_after h_ne_s h_ne_e =>
    covered_interior.propagate h_cov h_after h_ne_s h_ne_e

/-- Chain-form propagation over `afters_reach`. See the CRDT
`Peritext_ReadSide.lean` for the docstring. -/
theorem covered_interior_of_reach
    (s : concrete_st) (m : MarkOp) (c_start c_end : OpId) :
    afters_reach s c_start c_end →
    covered_interior s m c_end →
    (∀ c', afters_reach s c' c_end → afters_reach s c_start c' →
           c' ≠ m.startId ∧ c' ≠ m.endId) →
    covered_interior s m c_start := by
  intro h_reach
  induction h_reach with
  | refl c => intro h _; exact h
  | @step c mid anc h_after h_reach' ih =>
    intro h_cov_end h_interior
    have h_interior_mid :
        ∀ c', afters_reach s c' anc → afters_reach s mid c' →
              c' ≠ m.startId ∧ c' ≠ m.endId :=
      fun c' h1 h2 => h_interior c' h1 (afters_reach.step h_after h2)
    have h_cov_mid : covered_interior s m mid := ih h_cov_end h_interior_mid
    have h_reach_c : afters_reach s c anc := afters_reach.step h_after h_reach'
    have h_bounds : c ≠ m.startId ∧ c ≠ m.endId :=
      h_interior c h_reach_c (afters_reach.refl c)
    exact covered_interior.propagate h_cov_mid h_after h_bounds.1 h_bounds.2

/-! ## RGA visible-order relation (mirror)

See the CRDT `Peritext_ReadSide.lean` for the full docstring. -/

inductive visible_lt (s : concrete_st) : OpId → OpId → Prop where
  | parent_child {p c : OpId} : after_of s c p = true → visible_lt s p c
  | sibling {p c₁ c₂ : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      visible_lt s c₁ c₂
  | left_descendant_of_sibling {p c₁ c₂ d : OpId} :
      after_of s c₁ p = true → after_of s c₂ p = true →
      c₁ ≠ c₂ → opid_max c₁ c₂ = c₁ →
      afters_reach s d c₁ → d ≠ c₁ →
      visible_lt s d c₂
  | trans {c₁ c₂ c₃ : OpId} :
      visible_lt s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃

def visible_le (s : concrete_st) (c₁ c₂ : OpId) : Prop :=
  c₁ = c₂ ∨ visible_lt s c₁ c₂

theorem visible_lt_of_afters_reach
    (s : concrete_st) (c anc : OpId) :
    afters_reach s c anc → c ≠ anc → visible_lt s anc c := by
  intro h_reach h_ne
  induction h_reach with
  | refl c => exact absurd rfl h_ne
  | @step c mid anc h_after h_reach' ih =>
    by_cases h_eq : mid = anc
    · subst h_eq
      exact visible_lt.parent_child h_after
    · have h_mid : visible_lt s anc mid := ih h_eq
      have h_c : visible_lt s mid c := visible_lt.parent_child h_after
      exact visible_lt.trans h_mid h_c

theorem visible_le_refl (s : concrete_st) (c : OpId) : visible_le s c c :=
  Or.inl rfl

theorem visible_le_trans
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_le s c₁ c₂ → visible_le s c₂ c₃ → visible_le s c₁ c₃ := by
  intro h12 h23
  rcases h12 with h12 | h12
  · subst h12; exact h23
  · rcases h23 with h23 | h23
    · subst h23; exact Or.inr h12
    · exact Or.inr (visible_lt.trans h12 h23)

theorem visible_lt_of_lt_le
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_lt s c₁ c₂ → visible_le s c₂ c₃ → visible_lt s c₁ c₃ := by
  intro h12 h23
  rcases h23 with h23 | h23
  · subst h23; exact h12
  · exact visible_lt.trans h12 h23

theorem visible_lt_of_le_lt
    (s : concrete_st) (c₁ c₂ c₃ : OpId) :
    visible_le s c₁ c₂ → visible_lt s c₂ c₃ → visible_lt s c₁ c₃ := by
  intro h12 h23
  rcases h12 with h12 | h12
  · subst h12; exact h23
  · exact visible_lt.trans h12 h23

/-- Cross-sibling traversal. See the CRDT ReadSide for the full
docstring. -/
theorem visible_lt_of_cross_sibling
    (s : concrete_st) (p c₁_top c₂_top c₁ c₂ : OpId) :
    after_of s c₁_top p = true →
    after_of s c₂_top p = true →
    c₁_top ≠ c₂_top →
    opid_max c₁_top c₂_top = c₁_top →
    afters_reach s c₁ c₁_top →
    afters_reach s c₂ c₂_top →
    visible_lt s c₁ c₂ := by
  intro h_after_1 h_after_2 h_ne h_order h_reach_1 h_reach_2
  have step_a : visible_lt s c₁ c₂_top := by
    by_cases h_eq1 : c₁ = c₁_top
    · subst h_eq1
      exact visible_lt.sibling h_after_1 h_after_2 h_ne h_order
    · exact visible_lt.left_descendant_of_sibling h_after_1 h_after_2 h_ne
        h_order h_reach_1 h_eq1
  by_cases h_eq2 : c₂ = c₂_top
  · subst h_eq2; exact step_a
  · have step_b : visible_lt s c₂_top c₂ :=
      visible_lt_of_afters_reach s c₂ c₂_top h_reach_2 h_eq2
    exact visible_lt.trans step_a step_b

/-- Paper-faithful span-membership predicate. See the CRDT
`Peritext_ReadSide.lean` for full semantics and the relationship
to `in_span_boundary`. -/
def in_span_visible (s : concrete_st) (m : MarkOp) (c : OpId) : Prop :=
  (if m.startSide = true then visible_lt s m.startId c
   else visible_le s m.startId c) ∧
  (if m.endSide = true then visible_le s c m.endId
   else visible_lt s c m.endId)

theorem startId_in_span_visible
    (s : concrete_st) (m : MarkOp) :
    m.startSide = false →
    (if m.endSide = true then visible_le s m.startId m.endId
     else visible_lt s m.startId m.endId) →
    in_span_visible s m m.startId := by
  intro h_sSide h_nondeg
  refine ⟨?_, h_nondeg⟩
  show (if m.startSide = true then visible_lt s m.startId m.startId
        else visible_le s m.startId m.startId)
  rw [h_sSide]; simp
  exact visible_le_refl s m.startId

theorem endId_in_span_visible
    (s : concrete_st) (m : MarkOp) :
    m.endSide = true →
    (if m.startSide = true then visible_lt s m.startId m.endId
     else visible_le s m.startId m.endId) →
    in_span_visible s m m.endId := by
  intro h_eSide h_nondeg
  refine ⟨h_nondeg, ?_⟩
  show (if m.endSide = true then visible_le s m.endId m.endId
        else visible_lt s m.endId m.endId)
  rw [h_eSide]; simp
  exact visible_le_refl s m.endId

/-- Paper-faithful "mark wins" predicate using `in_span_visible`.
See the CRDT `Peritext_ReadSide.lean` for discussion. -/
noncomputable def mark_wins_visible
    (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_visible s m c ∧
  m.markType = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_visible s m' c →
        m'.markType = mt →
        m' ≠ m →
        mark_beats m m' = true

noncomputable def formatted_visible
    (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins_visible s m c mt ∧ m.isAdd = true)
  else false

noncomputable def readRichText_visible (s : concrete_st) :
    OpId → Option (ℕ → Bool) :=
  fun c =>
    if visible s c = true then
      some (fun mt => formatted_visible s c mt)
    else
      none

/-- Demonstration: paper-faithful LWW-add-winner. Analogue of
`formatted_of_lww_add_winner` against `in_span_visible`. -/
theorem formatted_visible_of_lww_add_winner
    (s : concrete_st) (c : OpId) (mt : ℕ) (addOp : MarkOp) :
    addOp.isAdd = true →
    addOp.markType = mt →
    mark_present s addOp = true →
    in_span_visible s addOp c →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           m'.markType = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted_visible s c mt = true := by
  intro h_add h_mt_a h_pres_a h_cov_a h_vis h_beats
  simp only [formatted_visible, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩

/-- Paper Ex 5 negative, visible-order version. -/
theorem no_add_cover_implies_unformatted_visible
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    (∀ m, mark_present s m = true →
          in_span_visible s m c →
          m.markType = mt →
          m.isAdd = false) →
    formatted_visible s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins_visible s m c mt ∧ m.isAdd = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : w.isAdd = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted_visible]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl

/-- Paper-faithful Ex 5 positive: Add wins over concurrent Remove. -/
theorem add_wins_over_concurrent_remove_visible
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp remOp : MarkOp) :
    addOp.isAdd = true →
    remOp.isAdd = false →
    addOp.markType = mt →
    remOp.markType = mt →
    mark_present s addOp = true →
    mark_present s remOp = true →
    in_span_visible s addOp c →
    in_span_visible s remOp c →
    visible s c = true →
    (∀ m', mark_present s m' = true →
           in_span_visible s m' c →
           m'.markType = mt →
           m' ≠ addOp → m' ≠ remOp →
           mark_beats addOp m' = true) →
    formatted_visible s c mt = true := by
  intro h_add h_rem h_mt_a _ h_pres_a _ h_cov_a _ h_vis h_beats
  refine formatted_visible_of_lww_add_winner s c mt addOp
    h_add h_mt_a h_pres_a h_cov_a h_vis ?_
  intro m' h_pres' h_cov' h_mt' h_ne_add
  by_cases h_eq : m' = remOp
  · subst h_eq
    simp [mark_beats, h_add, h_rem]
  · exact h_beats m' h_pres' h_cov' h_mt' h_ne_add h_eq
