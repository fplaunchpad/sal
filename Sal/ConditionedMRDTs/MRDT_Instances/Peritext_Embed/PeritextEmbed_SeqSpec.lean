import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec

/-!
# Sequential-spec soundness — tier 4: fused Peritext vs the naive editor

The campaign's final tier, against the canonical embed-based fused Peritext:
on every sequentially honest single-replica history, the
datatype's rendered rich text IS the screen of a **naive marked-text
editor** — the sequential program a programmer would write for this op
alphabet with no replication in mind:

* the editor's document is a plain buffer of `(id, element)` entries;
* insert splices its entry immediately after the anchor (at the head for
  the start sentinel), delete removes its entry;
* the editor's screen walks the buffer once, left to right, keeping the
  set of currently open marks: a start boundary opens its mark, the
  matching close removes it, characters display with the marks open at
  them, boundaries are invisible.

The proof is a composition: tier 3's buffer soundness (`embed_seq_sound`,
payload-generic) says the fold's `(id, element)` sequence IS the naive
buffer, and the render layers of the
datatype and the editor are literally the same pure fold over that
sequence. The rehoming-based fused Peritext fails this theorem at the
four-op witness (`fused_delete_reformats_survivor`): its delete departs
from the naive buffer, and the render inherits the departure.

SPOT shape (PASS and FAIL): the equality is watched concretely on the
witness trace; the FAIL half shows the editor is not trivially agreeing —
deleting a *boundary* genuinely re-formats text on both sides (which is
why `renderIds_del`'s character hypothesis is load-bearing), while
deleting a *character* re-formats on neither.
-/

namespace Sal.ConditionedMRDTs.PeritextEmbed

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode unaryCode)
open Sal.ConditionedMRDTs.Peritext (PeritextElt Mark)
open Sal.ConditionedMRDTs.Peritext.Read (OpenSet renderSpans formatOf)

/-! ## §A  The naive marked-text editor -/

/-- The editor's document: a plain `(id, element)` buffer. -/
abbrev EditorBuf : Type := List (ℕ × PeritextElt)

/-- The editor program: the campaign's naive sequential buffer at the
rich-text payload — splice after the anchor, filter delete. -/
def editorFold (ρ : List (Op (EOp PeritextElt))) : EditorBuf := eSpecFold ρ

/-- The editor's screen: one left-to-right walk with the open-mark set. -/
def editorRender (B : EditorBuf) : List (ℕ × (Mark → Bool)) :=
  (renderSpans (B.map (fun p => p.2))).map (fun r => (r.1, formatOf r.2))

/-- The id-tagged screen (for the theorem that also matches identities). -/
def editorRenderIdsAux : EditorBuf → OpenSet → List (ℕ × ℕ × (Mark → Bool))
  | [], _ => []
  | (t, PeritextElt.char c) :: rest, acc =>
      (t, c, formatOf acc) :: editorRenderIdsAux rest acc
  | (_, PeritextElt.bound id mk true) :: rest, acc =>
      editorRenderIdsAux rest ((id, mk) :: acc)
  | (_, PeritextElt.bound id _ false) :: rest, acc =>
      editorRenderIdsAux rest (acc.filter (fun p => p.1 != id))

def editorRenderIds (B : EditorBuf) : List (ℕ × ℕ × (Mark → Bool)) :=
  editorRenderIdsAux B []

/-! ## §B  The two render folds agree over `eProj` -/

theorem editorRenderIdsAux_map_eProj (acc : OpenSet) :
    ∀ (l : List (ERec PeritextElt)),
    editorRenderIdsAux (l.map eProj) acc = renderIdsAux l acc
  | [] => rfl
  | (t, el, co) :: rest => by
      cases el with
      | char c =>
          simp only [List.map_cons, eProj, editorRenderIdsAux,
            renderIdsAux_char]
          rw [editorRenderIdsAux_map_eProj acc rest]
      | bound id mk b =>
          cases b with
          | true =>
              simp only [List.map_cons, eProj, editorRenderIdsAux,
                renderIdsAux_open]
              rw [editorRenderIdsAux_map_eProj ((id, mk) :: acc) rest]
          | false =>
              simp only [List.map_cons, eProj, editorRenderIdsAux,
                renderIdsAux_close]
              rw [editorRenderIdsAux_map_eProj
                (acc.filter (fun p => p.1 != id)) rest]

/-! ## §C  The tier-4 theorems -/

/-- **Tier 4, id-tagged**: on every sequentially honest history, the fused
Peritext's id-tagged render is the naive editor's id-tagged screen —
identity for identity, codepoint for codepoint, formatting predicate for
formatting predicate. -/
theorem peritextEmbed_seq_sound_ids {Γ : OrderedPrefixCode}
    {ρ : List (Op (EOp PeritextElt))} (hOK : eSeqOK Γ ρ) :
    renderIds (eFold Γ ρ) = editorRenderIds (editorFold ρ) := by
  unfold renderIds editorRenderIds editorFold
  rw [← embed_seq_sound hOK, editorRenderIdsAux_map_eProj]

/-- **Tier 4**: on every sequentially honest history, the fused Peritext
renders exactly what the naive marked-text editor shows. -/
theorem peritextEmbed_seq_sound {Γ : OrderedPrefixCode}
    {ρ : List (Op (EOp PeritextElt))} (hOK : eSeqOK Γ ρ) :
    renderRichText (eFold Γ ρ) = editorRender (editorFold ρ) := by
  have hbuf : docElts (eFold Γ ρ) = (editorFold ρ).map (fun p => p.2) := by
    unfold editorFold docElts
    rw [← embed_seq_sound hOK, List.map_map]
    rfl
  unfold renderRichText editorRender
  rw [hbuf]

#print axioms peritextEmbed_seq_sound
#print axioms peritextEmbed_seq_sound_ids

/-! ## §D  SPOT — the theorem watched, PASS and FAIL shaped -/

namespace SPOT

open Sal.ConditionedMRDTs.PeritextEmbed.SPOT (opsE sResidual)

/-- PASS: on the witness trace, the datatype's render and the editor's
screen agree, entry for entry (the tier-4 equality, concretely). -/
theorem editor_agrees :
    (renderRichText sResidual).map (fun r => (r.1, r.2 Mark.bold))
      = (editorRender (editorFold opsE)).map (fun r => (r.1, r.2 Mark.bold)) := by
  native_decide

/-- The editor's own screen, hand-derived: `X` bold, `P` and `C` plain. -/
theorem editor_screen :
    (editorRender (editorFold opsE)).map (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (80, false), (67, false)] := by native_decide

/-- Deleting a **boundary** re-formats text — on the editor exactly as on
the datatype (both extend the bold span over `P` and `C` when `⟨/bold⟩`
goes): the agreement is not vacuous, and `renderIds_del`'s character
hypothesis is load-bearing. -/
theorem editor_boundary_delete :
    (renderRichText (eUpdate unaryCode sResidual (9, 0, .del 4))).map
        (fun r => (r.1, r.2 Mark.bold))
      = [(88, true), (80, true), (67, true)] := by native_decide

/-- FAIL pin: the `renderIds_del` equation is REFUTED when the deleted id
is a boundary (a boundary emits no render entry, so "minus the deleted
entries" removes nothing, yet the formats changed) — the theorem's
character hypothesis is necessary, not decorative. -/
theorem boundary_delete_breaks_filter_eq :
    (renderIds (eUpdate unaryCode sResidual (9, 0, .del 4))).map
        (fun e => (e.1, e.2.1, e.2.2 Mark.bold))
      ≠ ((renderIds sResidual).map
          (fun e => (e.1, e.2.1, e.2.2 Mark.bold))).filter
            (fun e => decide (e.1 ≠ 4)) := by
  native_decide

end SPOT

end Sal.ConditionedMRDTs.PeritextEmbed
