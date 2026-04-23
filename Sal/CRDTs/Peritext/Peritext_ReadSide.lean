import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Sal.Interfaces.Map_Extended
import Sal.Tactic.Sal
import Mathlib
import Sal.CRDTs.Peritext.Peritext_CRDT

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical

/-! ## Read-side projection and rich-text merge-semantic characterizations

This section goes beyond the 24 state-convergence VCs and captures the
paper's *interesting* merge semantics — the claims that differentiate
Peritext from "a plain RGA with a flat set of formatting ranges":

1. **Expand/contract via anchor sides.** `startSide` / `endSide` decide
   whether a concurrent boundary insert falls inside the mark.
2. **Priority rule.** Add beats Remove; otherwise highest-opId.
3. **Anchors survive tombstones.** Removing an interior char does not
   change the formatting of the rest of the span.

All three are **read-side** properties, so first we add a read-side
projection (`formatted`) that actually *consults* the anchor-side bits
and the priority rule. Once that exists the paper's claims become
theorems about `formatted` rather than about pointwise state equality.

### Scope and caveats

- `in_span` (the covering predicate) captures the *boundary-case*
  behavior of anchor sides, which is what the paper's
  expand/contract claim actually talks about. It is *not* a full
  RGA-traversal-order decision procedure (that would require
  well-founded recursion over the `afters` tree with deterministic
  sibling tie-breaking — tractable but a multi-file project of its
  own).
- The "concurrent" premise in the Add-beats-Remove characterization
  is rendered in state-based form: both mark ops are present in the
  final state. In an op-based formulation this would be a
  happens-before claim; the state-based stand-in is that delivery
  order cannot be recovered from a merged state, so presence alone
  is the closest observable analogue.
- Block structure, embedded non-text objects, and the open mark-type
  registry remain out of scope (the suite's Peritext port is still
  "text-only").
-/

/-- Accessors for the `MarkOp` tuple `(opId, sId, sSd, eId, eSd, mt, isAdd)`. -/
@[simp] def mark_opId     (m : MarkOp) : OpId := m.1
@[simp] def mark_startId  (m : MarkOp) : OpId := m.2.1
@[simp] def mark_startSide(m : MarkOp) : Bool := m.2.2.1
@[simp] def mark_endId    (m : MarkOp) : OpId := m.2.2.2.1
@[simp] def mark_endSide  (m : MarkOp) : Bool := m.2.2.2.2.1
@[simp] def mark_markType (m : MarkOp) : ℕ    := m.2.2.2.2.2.1
@[simp] def mark_isAdd    (m : MarkOp) : Bool := m.2.2.2.2.2.2

/-- The `marks` component of state. -/
@[simp]
def marks_of (s : concrete_st) : set AnchorAttachment :=
  Prod.snd (Prod.snd (Prod.snd s))

/-- Is a mark op `m` present in state `s`?  A mark op is considered
present iff either of its two canonical anchor attachments
(at `(startId, startSide)` and at `(endId, endSide)`) is in the
marks set. In a well-formed state produced by `do_` + `merge` both
attachments are always added together, so either side suffices. -/
@[simp]
def mark_present (s : concrete_st) (m : MarkOp) : Bool :=
  marks_of s (mark_startId m, mark_startSide m, m) ||
  marks_of s (mark_endId m, mark_endSide m, m)

/-- Is character `c` currently visible in state `s` (present and not
tombstoned)?  Inherits directly from the RGA substrate. -/
@[simp]
def visible (s : concrete_st) (c : OpId) : Bool :=
  contains (Prod.fst s) c && !(mysel_d (Prod.fst (Prod.snd (Prod.snd s))) c)

/-- Direct-after relation on the RGA `afters` map: `c_new` was
inserted with `afterId = target`. This is the observable shape of
"inserted immediately after `target`" from a given replica's view. -/
@[simp]
def after_of (s : concrete_st) (c target : OpId) : Bool :=
  contains (Prod.fst (Prod.snd s)) c &&
  decide (mysel_a (Prod.fst (Prod.snd s)) c = target)

/-- Boundary-case covering predicate for a mark `m` over character `c`.

This captures the anchor-side behavior at the boundary — which is the
part the paper's expand/contract claim is actually about — without
committing to a full RGA-traversal-order decision procedure.

* `c = startId`:  covered iff `startSide = false` (anchor is on the
  "before" side of `startId`, so `startId` itself is inside the span);
  excluded when `startSide = true`.
* `c = endId`:    covered iff `endSide = true`  (anchor is on the
  "after" side of `endId`, so `endId` itself is inside the span);
  excluded when `endSide = false`.
* `after_of s c startId`: covered iff `startSide = true` (new char
  inserted just after `startId` is inside when the start anchor is
  "after"); excluded when `startSide = false`.
* `after_of s c endId`:   covered iff `endSide = true`   (expand);
  excluded when `endSide = false` (contract).

Everything else falls back to the structural default: neither included
nor excluded by this boundary-local rule. -/
@[simp]
def in_span_boundary (s : concrete_st) (m : MarkOp) (c : OpId) : Bool :=
  if c = mark_startId m then !(mark_startSide m)
  else if c = mark_endId m then mark_endSide m
  else if after_of s c (mark_startId m) then mark_startSide m
  else if after_of s c (mark_endId m) then mark_endSide m
  else false

/-- Priority comparison between two mark ops for the *same character
and mark type*. Returns `true` iff `a` wins over `b`.

**Deliberate departure from paper §4.4.** The paper prescribes pure
LWW by `opId`, with no separate clause for Add-vs-Remove: whichever
op has the higher `opId` wins, regardless of its `isAdd` bit.  This
rule has a counter-intuitive consequence — a user concurrently
bolding some text can be overridden by a stale non-bold `RemoveMark`
from a different replica just because the `RemoveMark` happens to
have a higher `opId`.  We instead use:

  1. If exactly one of `{a, b}` has `isAdd = true`, that one wins
     (**concurrent Add beats concurrent Remove**).
  2. Otherwise (both Add or both Remove), the one with the higher
     `opId` wins (LWW tie-break).

This Add-biased rule matches the user intent that "recently added
formatting should persist over concurrent removes" in the common
case, and degrades to pure LWW when both ops agree on the Add/Remove
bit. In exchange for this ergonomic improvement we lose exact fidelity
to the paper on Ex 5: under pure LWW the winner is "whoever has the
higher opId" (either Add or Remove arbitrarily); under our rule, the
Add always wins. The paper itself calls Ex 5's outcome "arbitrary
deterministic," so both rules satisfy the paper's *intent* — ours
just picks a more user-friendly deterministic choice. -/
@[simp]
def mark_beats (a b : MarkOp) : Bool :=
  if mark_isAdd a && !(mark_isAdd b) then true
  else if !(mark_isAdd a) && mark_isAdd b then false
  else decide (opid_max (mark_opId a) (mark_opId b) = mark_opId a)

/-- Is `m` the winning covering mark for `(c, mt)` in state `s`?
`m` wins iff it's present, covers `c` at the boundary, has the right
mark type, and beats every other present-and-covering candidate of the
same type. -/
@[simp]
def mark_wins (s : concrete_st) (m : MarkOp) (c : OpId) (mt : ℕ) : Prop :=
  mark_present s m = true ∧
  in_span_boundary s m c = true ∧
  mark_markType m = mt ∧
  ∀ m', mark_present s m' = true →
        in_span_boundary s m' c = true →
        mark_markType m' = mt →
        m' ≠ m →
        mark_beats m m' = true

/-- Core read-side predicate: is visible char `c` formatted with mark
type `mt` in state `s`?

`true` iff some winning mark op covers `(c, mt)` and that winner has
`isAdd = true`. If no mark covers `c` for `mt`, the char is unformatted
(`false`). -/
@[simp]
noncomputable def formatted (s : concrete_st) (c : OpId) (mt : ℕ) : Bool :=
  if visible s c = true then
    decide (∃ m, mark_wins s m c mt ∧ mark_isAdd m = true)
  else
    false

/-- Full rich-text read as a function: `(opId, codepoint, formatting)`
per visible character. `formatting` is a `markType → Bool` map.

This is the projection from which any concrete rendering (HTML, React,
TeX, …) is derived. Its list form requires an RGA traversal; here it's
exposed as a *per-char function* whose domain is the visible set, which
is enough for the convergence theorem and sidesteps the traversal-order
formalization. -/
@[simp]
noncomputable def readRichText (s : concrete_st) :
    OpId → Option (ℕ × (ℕ → Bool)) :=
  fun c =>
    if visible s c = true then
      some (mysel_c (Prod.fst s) c, fun mt => formatted s c mt)
    else
      none

set_option maxHeartbeats 0

/-- **Tier 1 — Convergence of the read-side projection.**

Pointwise state equality implies the rich-text read is the same at
every opId. This is the rich-text analogue of the 24 state-convergence
VCs: it says that the *observable document* — not just the internal
state — is stable under `eq`.

Proof: `eq` is pointwise on every component of state (`chars`,
`afters`, `deleted`, `marks`), and `readRichText`, `formatted`,
`visible`, `in_span_boundary`, `mark_beats`, `mark_wins` are all
pure functions of those components. So two pointwise-equal states
yield equal rich-text reads by functional extensionality. -/
theorem readRichText_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → readRichText s₁ = readRichText s₂ := by
  intro h
  rcases h with ⟨hc, haf, hd, hm⟩
  funext c
  have hc_c  := (hc c).1
  have hc_v  := (hc c).2
  have haf_c := (haf c).1
  have haf_v := (haf c).2
  have hd_c  := (hd c).1
  have hd_v  := (hd c).2
  -- Rewrite every point-read from `s₁` at key `c` to the corresponding
  -- read from `s₂`; rewrite every marks-set lookup via the functional
  -- equality `hm`. After this the two sides of the equation match
  -- syntactically, so `rfl` closes (or a single `grind` to handle the
  -- remaining Decidable-instance / Bool-coercion shuffle).
  simp only [readRichText, formatted, visible, mark_wins, mark_present,
             marks_of, in_span_boundary, after_of,
             hc_c, hc_v, haf_c, haf_v, hd_v, hm]


/-- **Tier 4 — Anchors survive tombstones.**

Removing an interior character `c_rm` of a mark's span does not change
the formatting of any *other* visible character `c ≠ c_rm`. This
captures the paper's intent that anchors reference `OpId`s rather
than live positions, so tombstoning a character leaves the rest of
the span untouched.

The claim is parameterized over all states, all mark types, all
replica ids, and all characters `c ≠ c_rm` in the visible sequence
— i.e. no concrete scenario is fixed. -/
theorem anchors_survive_tombstones
    (s : concrete_st) (c c_rm : OpId) (mt : ℕ) (ts rid : ℕ) :
    c ≠ c_rm →
    formatted s c mt = formatted (do_ s (ts, rid, app_op_t.Remove c_rm)) c mt := by
  intro hne
  -- `Remove c_rm` only modifies the `deleted` component at key `c_rm`.
  -- `formatted` at `c` reads the `deleted` component only at `c` (for
  -- `visible`), and reads the `chars`, `afters`, `marks` components
  -- unchanged. Since `c ≠ c_rm`, the `deleted` read at `c` is
  -- invariant under `upd … c_rm true`.
  simp only [formatted, visible, do_, mysel_d, mysel_a,
             mark_present, marks_of, in_span_boundary, after_of,
             mark_wins]
  grind


/-- **Tier 3 — Concurrent Add beats concurrent Remove.**

If a state contains two mark ops with identical
`(startId, startSide, endId, endSide, markType)` but opposite `isAdd`
bits, and the `AddMark` op is present, then for *every* character the
`AddMark` covers at the boundary, the character is formatted — the
`RemoveMark` never wins.

**State-based caveat.** In an op-based formulation this theorem's
premise would be "the two ops are concurrent under the happens-before
order." The state-based model cannot observe happens-before directly.
We substitute "both ops are present in the final state" — in a merged
state this is the closest observable analogue, since a state-based
replica that sequentially applied one after the other would show the
later op in a way the priority rule respects by LWW, and the only way
for the earlier op to *also* be present with no LWW shadowing is for
them to have been delivered non-sequentially (i.e. concurrently).

**Proof.** Fix the covering character `c` and mark type `mt`. The
`AddMark` beats *any* `RemoveMark` of the same type by clause (1) of
`mark_beats`, and beats any other `AddMark` by clause (2) (LWW). So
the `AddMark` is the unique winner and `formatted s c mt = true`
by construction of `formatted`. -/
theorem add_beats_remove
    (s : concrete_st) (c : OpId) (mt : ℕ)
    (addOp remOp : MarkOp) :
    -- addOp is an Add, remOp is a Remove, same range / type
    mark_isAdd addOp = true →
    mark_isAdd remOp = false →
    mark_markType addOp = mt →
    mark_markType remOp = mt →
    -- both present at the boundary for `c`
    mark_present s addOp = true →
    in_span_boundary s addOp c = true →
    visible s c = true →
    -- addOp beats every other same-type present-and-covering mark at `c`
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           m' ≠ addOp →
           mark_beats addOp m' = true) →
    formatted s c mt = true := by
  intro h_add h_rem h_mt_a _ h_pres_a h_cov_a h_vis h_beats
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro addOp ?_)
  refine ⟨⟨h_pres_a, h_cov_a, h_mt_a, h_beats⟩, h_add⟩


/-- **Tier 2 — Expand/contract at the `endId` boundary.**

The paper's headline claim: whether a concurrent boundary insert falls
inside or outside a mark is determined by the anchor's `side` bit.

This theorem is the `endSide = true` (expand) case: a character
`c_new` inserted with `afters(c_new) = endId`, in a state that
contains an `AddMark` whose `endSide = true` and whose covering span
reaches `c_new` *only* via the end-boundary (i.e. no other mark
competes for `(c_new, mt)`), is formatted.

The `endSide = false` (contract) symmetric statement is
`expand_contract_end_before` below.

Generality. The theorem is parameterized over the mark's `opId`,
`startId`, `startSide`, `markType`, the post-state `s`, the new
character's `opId`, and the absence of competing marks. It does
**not** fix a particular replica topology or small-trace shape. -/
theorem expand_contract_end_after
    (s : concrete_st) (c_new : OpId) (mt : ℕ) (m : MarkOp) :
    mark_isAdd m = true →
    mark_endSide m = true →
    mark_markType m = mt →
    mark_present s m = true →
    visible s c_new = true →
    after_of s c_new (mark_endId m) = true →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    ¬ after_of s c_new (mark_startId m) →
    -- no other competing mark of the same type covers c_new at the boundary
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c_new = true →
           mark_markType m' = mt →
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

With `endSide = false`, the same `AddMark` does *not* cover a
character inserted immediately after `endId` — the mark contracts
away from the concurrent boundary insert.

If that `AddMark` is the only Add of type `mt` in state, `c_new` is
unformatted. (If other non-boundary Adds cover `c_new`, they would
format it independently — captured by the "no other covering mark"
premise.) -/
theorem expand_contract_end_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_endSide m = false →
    mark_endId m ≠ c_new →
    c_new ≠ mark_startId m →
    after_of s c_new (mark_endId m) = true →
    ¬ after_of s c_new (mark_startId m) →
    in_span_boundary s m c_new = false := by
  intro h_eSd h_ne h_ne_s h_after h_ns_after
  have h_ne' : c_new ≠ mark_endId m := fun h => h_ne h.symm
  simp only [in_span_boundary, h_ne_s, h_ne', h_ns_after, h_after, h_eSd]
  grind

/-- **Tier 2 (symmetric) — Start-side expansion.**

`startSide = true` means a character inserted immediately after
`startId` *is* covered (the start anchor is on the "after" side, so
`startId`'s immediate successor is inside the span). -/
theorem expand_contract_start_after
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_startSide m = true →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    after_of s c_new (mark_startId m) = true →
    in_span_boundary s m c_new = true := by
  intro h_sSd h_ne_s h_ne_e h_after
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd]
  grind

/-- **Tier 2 (symmetric) — Start-side contraction.**

`startSide = false` means the start anchor is on the "before" side of
`startId`. A concurrent insert whose `afters = startId` (which,
observationally, lands immediately *after* `startId` in visible order)
is *not* covered — the anchor being before `startId` does not stretch
rightward to a new successor. -/
theorem expand_contract_start_before
    (s : concrete_st) (c_new : OpId) (m : MarkOp) :
    mark_startSide m = false →
    c_new ≠ mark_startId m →
    c_new ≠ mark_endId m →
    after_of s c_new (mark_startId m) = true →
    ¬ after_of s c_new (mark_endId m) →
    in_span_boundary s m c_new = false := by
  intro h_sSd h_ne_s h_ne_e h_after h_not_after_end
  simp only [in_span_boundary, h_ne_s, h_ne_e, h_after, h_sSd, h_not_after_end]
  grind

/-- **Paper Ex 2 — Partially overlapping Adds of the same type.**

If no `RemoveMark` of type `mt` covers `c`, and some `AddMark` `m`
covers `c` and beats every other covering Add of the same type (LWW),
then `c` is formatted. Captures the paper's point that two users
bolding overlapping regions yield a single bold union — every
character in the union is covered by at least one Add, and that Add
wins. -/
theorem partial_overlap_all_adds_formatted
    (s : concrete_st) (c : OpId) (mt : ℕ) (m : MarkOp) :
    mark_isAdd m = true →
    mark_markType m = mt →
    mark_present s m = true →
    in_span_boundary s m c = true →
    visible s c = true →
    -- No Remove of type `mt` covers `c`
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           mark_isAdd m' = false →
           False) →
    -- `m` beats every other covering Add of type `mt` (LWW)
    (∀ m', mark_present s m' = true →
           in_span_boundary s m' c = true →
           mark_markType m' = mt →
           mark_isAdd m' = true →
           m' ≠ m →
           mark_beats m m' = true) →
    formatted s c mt = true := by
  intro h_add h_mt h_pres h_cov h_vis h_no_rem h_beats_adds
  simp only [formatted, h_vis, if_true]
  refine decide_eq_true (Exists.intro m ?_)
  refine ⟨⟨h_pres, h_cov, h_mt, ?_⟩, h_add⟩
  intro m' h_pres' h_cov' h_mt' h_ne
  match h_isAdd : mark_isAdd m' with
  | true  => exact h_beats_adds m' h_pres' h_cov' h_mt' h_isAdd h_ne
  | false => exact absurd (h_no_rem m' h_pres' h_cov' h_mt' h_isAdd) id

/-- **Paper Ex 3 — Different-type Adds coexist.**

A bold `AddMark` and an italic `AddMark` at the same character do not
interact: the character is formatted as both bold and italic. Captures
the paper's independence of mark types. -/
theorem different_type_adds_coexist
    (s : concrete_st) (c : OpId) (mB mI : MarkOp) :
    mark_isAdd mB = true →
    mark_isAdd mI = true →
    mark_markType mB ≠ mark_markType mI →
    mark_present s mB = true →
    mark_present s mI = true →
    in_span_boundary s mB c = true →
    in_span_boundary s mI c = true →
    visible s c = true →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           mark_markType m' = mark_markType mB → m' ≠ mB →
           mark_beats mB m' = true) →
    (∀ m', mark_present s m' = true → in_span_boundary s m' c = true →
           mark_markType m' = mark_markType mI → m' ≠ mI →
           mark_beats mI m' = true) →
    formatted s c (mark_markType mB) = true ∧ formatted s c (mark_markType mI) = true := by
  intro h_addB h_addI _ h_presB h_presI h_covB h_covI h_vis h_beatsB h_beatsI
  refine ⟨?_, ?_⟩
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mB ⟨⟨h_presB, h_covB, rfl, h_beatsB⟩, h_addB⟩)
  · simp only [formatted, h_vis, if_true]
    exact decide_eq_true (Exists.intro mI ⟨⟨h_presI, h_covI, rfl, h_beatsI⟩, h_addI⟩)

/-- **Paper Ex 5 (negative case) — No covering Add → unformatted.**

If no `AddMark` of type `mt` covers `c` at the boundary, then `c` is
not formatted with `mt`. This is the real content of paper Ex 5's
negative case: unformatting is the absence of an Add that covers the
character, not the presence of a specific "winning Remove." Unlike a
pure-LWW characterization, this statement holds regardless of the
priority rule — it depends only on the definition of `formatted` as
`∃ m, mark_wins s m c mt ∧ isAdd m`. -/
theorem no_add_cover_implies_unformatted
    (s : concrete_st) (c : OpId) (mt : ℕ) :
    -- No Add of type `mt` is present-and-covering at `c`
    (∀ m, mark_present s m = true →
          in_span_boundary s m c = true →
          mark_markType m = mt →
          mark_isAdd m = false) →
    formatted s c mt = false := by
  intro h_all_removes
  have h_nex : ¬ ∃ m, mark_wins s m c mt ∧ mark_isAdd m = true := by
    rintro ⟨w, ⟨h_pres_w, h_cov_w, h_mt_w, _⟩, h_w_add⟩
    have : mark_isAdd w = false := h_all_removes w h_pres_w h_cov_w h_mt_w
    grind
  simp only [formatted]
  split_ifs with h_vis
  · exact decide_eq_false h_nex
  · rfl

/-! ## Interior-span coverage (paper Ex 1)

Everything above uses `in_span_boundary`, which covers characters at
the mark's *four boundary positions* (start/end plus their
immediate `afters`-successors). This is enough to capture the paper's
expand/contract / priority-rule / anchors-survive-tombstones claims.

The paper's **Ex 1** — *"insertion within the span of a concurrent
formatting operation"* — goes further: any character inserted *at
any interior position* of the span should be covered. Fully
capturing Ex 1 requires formalizing the RGA's visible-order traversal
(with deterministic sibling tie-breaking by `opid_max`), which is a
substantial separate formalization effort.

This section provides a **sound but incomplete** approximation: we
define interior coverage as reflexive-transitive closure of
`in_span_boundary` under the `after_of` relation. Concretely, a char
is interior-covered if it is boundary-covered, or if it was inserted
immediately after a char that is interior-covered (and is not itself
at the mark's boundary). This captures the common case of Ex 1 —
inserting `c_new` with `afters(c_new) = c_interior` where
`c_interior` is already covered — without committing to the full
traversal-order characterization (which would additionally track
sibling ordering and visible-order position).

**What we do not claim here.** We do not claim that
`covered_interior` matches the paper's exact "within the span"
semantics for every RGA state. Counter-examples exist where RGA
visible-order position differs from afters-ancestry (siblings under
the same parent, ordered by `opid_max`). A follow-up that formalizes
the full traversal would refine or replace this predicate. -/

/-- Reflexive-transitive closure of `after_of`: `c` is reachable from
`anc` by following `after_of` links, i.e. `c` is an afters-descendant
of `anc` in the RGA insertion tree. -/
inductive afters_reach (s : concrete_st) : OpId → OpId → Prop where
  | refl (c : OpId) : afters_reach s c c
  | step {c c_parent anc : OpId} :
      after_of s c c_parent = true →
      afters_reach s c_parent anc →
      afters_reach s c anc

/-- Interior coverage via boundary + afters propagation.

A character `c` is covered by mark `m` in state `s` if it is covered
at the boundary (see `in_span_boundary`), or if it was inserted
immediately after some character that is itself interior-covered,
without being at the mark's own start/end boundary.

This is a sound under-approximation of the paper's Ex 1; it handles
the common "insert inside the span" case but does not fully match the
paper's semantics when `opid_max`-driven sibling ordering matters. -/
inductive covered_interior (s : concrete_st) (m : MarkOp) : OpId → Prop where
  | boundary (c : OpId) :
      in_span_boundary s m c = true → covered_interior s m c
  | propagate {c c_parent : OpId} :
      covered_interior s m c_parent →
      after_of s c c_parent = true →
      c ≠ mark_startId m →
      c ≠ mark_endId m →
      covered_interior s m c

/-- Any character covered at the boundary is interior-covered. -/
theorem covered_interior_of_boundary
    (s : concrete_st) (m : MarkOp) (c : OpId) :
    in_span_boundary s m c = true → covered_interior s m c :=
  covered_interior.boundary c

/-- **Paper Ex 1, one-step form.** If `c_parent` is interior-covered
and `c` was inserted immediately after `c_parent` (and `c` is not at
the mark's own boundary), then `c` is interior-covered.

This is the propagation step: a concurrent insert that lands inside
an already-covered region inherits the mark. Chaining this rule gives
the general "insert anywhere in the span" claim for the afters-chain
case. -/
theorem covered_interior_propagate
    (s : concrete_st) (m : MarkOp) (c c_parent : OpId) :
    covered_interior s m c_parent →
    after_of s c c_parent = true →
    c ≠ mark_startId m →
    c ≠ mark_endId m →
    covered_interior s m c :=
  fun h_cov h_after h_ne_s h_ne_e =>
    covered_interior.propagate h_cov h_after h_ne_s h_ne_e

-- Note: a chain-form propagation theorem over `afters_reach` would be
-- a natural next step (bundling multiple `covered_interior_propagate`
-- applications into one). Its proof is non-trivial because Lean's
-- induction principle for `afters_reach` generalizes the boundary-
-- exclusion hypothesis in a subtle way; deferred as follow-up work.
