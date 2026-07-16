import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Rehoming.Peritext
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Rehoming.Peritext_Read

/-!
# Peritext on the embedded-chain kernel — the re-based fused instance (#85)

Rich text as ONE embedded-chain RGA over `PeritextElt = char ⊕ boundary`:
the fused design of `Peritext_Rehoming/`, re-based from the rehoming kernel
onto the embed kernel. The payload types (`PeritextElt`, `Mark`) and the
entire pure render layer (`renderSpans`, `formatOf`, the positional intent
theorems) are REUSED from the rehoming instance's read file — they are
statements about element lists, blind to which RGA produced the list.

What changes by re-basing, and why this instance exists:

* **The state is the document.** The embed instance state is the canonical
  sorted record list, so the read is `map`, not a fueled traversal: no
  candidate-id list, no fuel, no `wf`/`mono` hypotheses anywhere in the
  read layer.
* **The residual is FIXED.** The rehoming-based instance inherits the
  delete-reorder anomaly at the render (`fused_delete_reformats_survivor`:
  deleting a plain character re-formats an untouched survivor). Here
  coordinates are immutable birth constants and delete is `List.filter`,
  so deletion never reorders survivors — and the general theorem
  `renderIds_del` holds: **deleting a character leaves every other
  character's formatting untouched** (its render is the old render minus
  exactly the deleted entries). The SPOT block replays the rehoming
  witness trace and watches it come out clean (PASS + FAIL shaped).
* **Convergence is inherited**, exactly as before: the capstone is
  `embed_ra_linearizable3` at `α := PeritextElt`, a pure instantiation —
  the payload is opaque to the embed kernel, so specialising from `ℕ` to
  `char ⊕ boundary` costs no new convergence proof, and the honesty
  contract is the embed's single `EHonest` (delete names an observed
  insert; mints are birth-chain coordinates), uniform over characters and
  boundaries.

The positional intent theorems (`render_id_active_iff_between`,
`render_span_before/inside/after`, no-backward-leak) are element-list-level
statements in `Peritext_Rehoming/Peritext_Read.lean` §§6–9 and apply to
this instance's `docElts` verbatim — nothing to re-prove.
-/

namespace Sal.ConditionedMRDTs.PeritextEmbed

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode unaryCode binaryCode)
open Sal.ConditionedMRDTs.Peritext (PeritextElt Mark)
open Sal.ConditionedMRDTs.Peritext.Read (OpenSet Rendered renderSpans
  renderAux formatOf openAfter)

set_option linter.unusedSimpArgs false

/-! ## §1  The instance and its capstone — pure instantiation -/

/-- The embed state at the rich-text payload: the canonical sorted record
list, which IS the document in reading order. -/
abbrev ESt : Type := EState PeritextElt

/-- **The embed-based fused Peritext is RA-linearizable, per version, at
every honestly reachable configuration** — `embed_ra_linearizable3` at
`α := PeritextElt`, verbatim; parametric in the coordinate code `Γ`. -/
theorem peritextEmbed_ra_linearizable3 {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ PeritextElt)} (hReach : EReach Γ C) :
    IsRALinearizable3 C :=
  embed_ra_linearizable3 hReach

#print axioms peritextEmbed_ra_linearizable3

/-! ## §2  The read — `map`, not traversal -/

/-- The reading-order element sequence: the state's own order. -/
def docElts (s : ESt) : List PeritextElt := s.map (fun r => r.2.1)

/-- The rich-text read: reading-order characters, each tagged with the
formatting predicate active at it (the pure open-set fold of the read
layer, applied to the state's own element order). -/
def renderRichText (s : ESt) : List (ℕ × (Mark → Bool)) :=
  (renderSpans (docElts s)).map (fun r => (r.1, formatOf r.2))

/-- The id-tagged render: each character record's id, codepoint, and
formatting — the theorem-bearing form (ids let the delete theorem say
"minus exactly the deleted entries"). -/
def renderIdsAux : List (ERec PeritextElt) → OpenSet → List (ℕ × ℕ × (Mark → Bool))
  | [], _ => []
  | (t, PeritextElt.char c, _) :: rest, acc =>
      (t, c, formatOf acc) :: renderIdsAux rest acc
  | (_, PeritextElt.bound id mk true, _) :: rest, acc =>
      renderIdsAux rest ((id, mk) :: acc)
  | (_, PeritextElt.bound id _ false, _) :: rest, acc =>
      renderIdsAux rest (acc.filter (fun p => p.1 != id))

def renderIds (s : ESt) : List (ℕ × ℕ × (Mark → Bool)) := renderIdsAux s []

@[simp] theorem renderIdsAux_nil (acc : OpenSet) : renderIdsAux [] acc = [] := rfl
@[simp] theorem renderIdsAux_char (t c : ℕ) (co : List Bool)
    (rest : List (ERec PeritextElt)) (acc : OpenSet) :
    renderIdsAux ((t, PeritextElt.char c, co) :: rest) acc
      = (t, c, formatOf acc) :: renderIdsAux rest acc := rfl
@[simp] theorem renderIdsAux_open (t id : ℕ) (mk : Mark) (co : List Bool)
    (rest : List (ERec PeritextElt)) (acc : OpenSet) :
    renderIdsAux ((t, PeritextElt.bound id mk true, co) :: rest) acc
      = renderIdsAux rest ((id, mk) :: acc) := rfl
@[simp] theorem renderIdsAux_close (t id : ℕ) (mk : Mark) (co : List Bool)
    (rest : List (ERec PeritextElt)) (acc : OpenSet) :
    renderIdsAux ((t, PeritextElt.bound id mk false, co) :: rest) acc
      = renderIdsAux rest (acc.filter (fun p => p.1 != id)) := rfl

/-- The two reads agree: `renderRichText` is `renderIds` with the ids
projected away. -/
theorem renderAux_map_eq (acc : OpenSet) : ∀ (l : List (ERec PeritextElt)),
    (renderAux (l.map (fun r => r.2.1)) acc).map (fun r => (r.1, formatOf r.2))
      = (renderIdsAux l acc).map (fun e => (e.2.1, e.2.2))
  | [] => rfl
  | (t, el, co) :: rest => by
      cases el with
      | char c => simp [renderAux_map_eq acc rest]
      | bound id mk b =>
          cases b with
          | true => simp [renderAux_map_eq ((id, mk) :: acc) rest]
          | false => simp [renderAux_map_eq (acc.filter (fun p => p.1 != id)) rest]

theorem renderRichText_eq_renderIds (s : ESt) :
    renderRichText s = (renderIds s).map (fun e => (e.2.1, e.2.2)) :=
  renderAux_map_eq [] s

/-! ## §3  THE FIX — deleting a character never re-formats another

The rehoming-based fused Peritext provably violates this
(`fused_delete_reformats_survivor`): its delete re-homes and re-sorts
survivors, which can move a character across a mark boundary. Here delete
is `List.filter` on an order-canonical state, and character entries are
open-set-neutral, so the render of the survivors is bitwise the old render
with the deleted entries filtered out. -/

/-- Filtering out records of a character id commutes with the render fold:
the dropped records touch neither the open set nor any surviving entry. -/
theorem renderIdsAux_filter (x : ℕ) :
    ∀ (l : List (ERec PeritextElt)) (acc : OpenSet),
    (∀ rec ∈ l, rec.1 = x → ∃ c, rec.2.1 = PeritextElt.char c) →
    renderIdsAux (l.filter (fun r => decide (r.1 ≠ x))) acc
      = (renderIdsAux l acc).filter (fun e => decide (e.1 ≠ x))
  | [], _, _ => rfl
  | (t, el, co) :: rest, acc, h => by
      have hrest : ∀ rec ∈ rest, rec.1 = x → ∃ c, rec.2.1 = PeritextElt.char c :=
        fun rec hrec => h rec (List.mem_cons_of_mem _ hrec)
      by_cases hx : t = x
      · obtain ⟨c, hc⟩ := h (t, el, co) List.mem_cons_self hx
        simp only at hc
        subst hc
        subst hx
        have IH := renderIdsAux_filter t rest acc hrest
        simp only [ne_eq, decide_not] at IH
        simp [List.filter_cons, IH]
      · cases el with
        | char c =>
            have IH := renderIdsAux_filter x rest acc hrest
            simp only [ne_eq, decide_not] at IH
            simp [List.filter_cons, hx, IH]
        | bound id mk b =>
            cases b with
            | true =>
                have IH := renderIdsAux_filter x rest ((id, mk) :: acc) hrest
                simp only [ne_eq, decide_not] at IH
                simp [List.filter_cons, hx, IH]
            | false =>
                have IH := renderIdsAux_filter x rest
                  (acc.filter (fun p => p.1 != id)) hrest
                simp only [ne_eq, decide_not] at IH
                simp [List.filter_cons, hx, IH]

/-- **Deleting a character never re-formats another character**: if id `x`
is a character (no boundary record carries it), the post-delete render is
the pre-delete render with exactly `x`'s entries removed — every surviving
character keeps its codepoint AND its formatting predicate, bitwise. -/
theorem renderIds_del (Γ : OrderedPrefixCode) (s : ESt) (ts r x : ℕ)
    (hchar : ∀ rec ∈ s, rec.1 = x → ∃ c, rec.2.1 = PeritextElt.char c) :
    renderIds (eUpdate Γ s (ts, r, .del x))
      = (renderIds s).filter (fun e => decide (e.1 ≠ x)) :=
  renderIdsAux_filter x s [] hchar

/-- The user-facing corollary at the plain rich-text read. -/
theorem renderRichText_del (Γ : OrderedPrefixCode) (s : ESt) (ts r x : ℕ)
    (hchar : ∀ rec ∈ s, rec.1 = x → ∃ c, rec.2.1 = PeritextElt.char c) :
    renderRichText (eUpdate Γ s (ts, r, .del x))
      = ((renderIds s).filter (fun e => decide (e.1 ≠ x))).map
          (fun e => (e.2.1, e.2.2)) := by
  rw [renderRichText_eq_renderIds, renderIds_del Γ s ts r x hchar]

#print axioms renderIds_del

/-! ## §4  SPOT — the rehoming witness trace, replayed on this kernel

PASS and FAIL shaped (convention): the pre-delete render matches the
rehoming instance's (both kernels agree while nothing is deleted); the
post-delete render keeps `C` plain (the fix), is exactly the pre-delete
render minus `P` (the general theorem, concretely), and is NOT the
rehoming kernel's anomalous output (the pin: the two kernels genuinely
diverge here, and this one is right). Trace = `docResidual` of
`Peritext_Rehoming/Peritext_Read.lean` §10, built through the embed fold
with the honest mints (prefix = anchor's stored coordinate, unary code). -/

namespace SPOT

/-- `⟨bold⟩`(1)←root, `X`(2)←1, `P`(3)←2, `⟨/bold⟩`(4)←2, `C`(5)←3. -/
def opsE : List (Op (EOp PeritextElt)) :=
  [ (1, 0, .ins (PeritextElt.bound 100 Mark.bold true) [] 0)
  , (2, 0, .ins (PeritextElt.char 88) [true, false] 1)
  , (3, 0, .ins (PeritextElt.char 80) [true, false, true, false] 2)
  , (4, 0, .ins (PeritextElt.bound 100 Mark.bold false) [true, false, true, false] 2)
  , (5, 0, .ins (PeritextElt.char 67) [true, false, true, false, true, false] 3) ]

def sResidual : ESt := eFold unaryCode opsE

/-- Before the delete: reading order `[⟨bold⟩, X, ⟨/bold⟩, P, C]`, so `X`
is bold and `P`, `C` are plain — the SAME render the rehoming instance
computes on this trace (`docResidual_render`). -/
theorem residual_render :
    (renderRichText sResidual).map (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (80, false), (67, false)] := by native_decide

/-- **The fix, concretely**: delete the plain `P`. `C`'s coordinate still
begins with `P`'s chain (dead ancestors survive as coordinate bits), so `C`
stays exactly where it was — outside the span — and stays plain. The
rehoming kernel re-formats it on this very trace
(`fused_delete_moves_char_into_span`). -/
theorem residual_delete_clean :
    (renderRichText (eUpdate unaryCode sResidual (9, 0, .del 3))).map
        (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (67, false)] := by native_decide

/-- The general theorem, watched concretely: post-delete = pre-delete minus
`P`'s entry, id for id, format for format. -/
theorem residual_delete_is_filter :
    (renderIds (eUpdate unaryCode sResidual (9, 0, .del 3))).map
        (fun e => (e.1, e.2.1, e.2.2 Mark.bold))
      = ((renderIds sResidual).map
          (fun e => (e.1, e.2.1, e.2.2 Mark.bold))).filter
            (fun e => decide (e.1 ≠ 3)) := by native_decide

/-- Should-FAIL pin: the output is NOT the rehoming kernel's anomalous
`[(88, true), (67, true)]` — the two kernels diverge at exactly this
delete, and the divergence is the repaired anomaly, not a rendering
artifact. -/
theorem residual_not_rehoming_anomaly :
    (renderRichText (eUpdate unaryCode sResidual (9, 0, .del 3))).map
        (fun r => (r.1, r.2 Mark.bold))
      ≠ [(88, true), (67, true)] := by native_decide

end SPOT

end Sal.ConditionedMRDTs.PeritextEmbed
