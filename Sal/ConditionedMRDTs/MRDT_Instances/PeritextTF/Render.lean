import Sal.ConditionedMRDTs.Metatheory.ProductEq
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.PeritextTF.MarkStore

/-!
# The Peritext read layer — resolve marks against the character sequence

Read-time coupling is free (memo `Development/COMPOSITION_PENPAPER.md` §3.4):
no update, merge, or guard reads across the components — only this observer
does. Each live mark's endpoints are resolved against the RGA component by
the RGA's OWN path-climbing resolution `resolve`
(`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean:84`): the recorded
endpoint character id followed by its recorded ancestor path, climbed to the
nearest SURVIVING character. A live endpoint short-circuits (the path tail is
never read); a deleted endpoint rehomes to its nearest surviving ancestor;
`0` means every recorded ancestor died — the endpoint collapsed to the
document root. Every live mark is rendered with its rehomed endpoints (this is
the total form of "marks whose endpoints survive or rehome"; a client wanting
to hide root-collapsed marks filters `resolvedStart ≠ 0 ∧ resolvedEnd ≠ 0`
downstream — a `Finset.filter`, congruent for free given
`peritextRender_congr`).

`peritextRender_congr` is memo §3.4's "one new VC", delivered as a standalone
theorem rather than by extending the product signature's `Query` (no sig
surgery): `(≈₁ × Eq)`-related product states render identically. The RGA-side
ingredient is `resolve_dom_eq` — resolution reads only the `contains`
observations, which the RGA's observational `≈` fixes. NOTE the honest scope:
this is *render congruence* (the read is well-defined on the quotient the
capstone speaks about). Semantic theorems about resolution (e.g. the resolved
span lies in the original span's surviving neighborhood) additionally need
mark-anchor honesty — recorded endpoint paths accurate at issue, the mark-side
analogue of born accuracy (memo §4 item 4) — and are out of scope here.
-/

namespace Sal.ConditionedMRDTs.PeritextTF

open Sal.Emulation
open Sal.ConditionedMRDTs.ProductEq
open Sal.ConditionedMRDTs (prodSig)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')

/-- A rendered mark: `(markId, markType, resolvedStart, resolvedEnd)` —
endpoints are the surviving characters the recorded paths climb to (`0` =
collapsed to the document root). -/
abbrev RenderedMark : Type := ℕ × ℕ × ℕ × ℕ

/-- Resolve one mark record against the character component: climb each
endpoint's recorded path (`resolve` short-circuits on a live endpoint). -/
def resolveMark (σ : concrete_st) (m : MarkPayload) : RenderedMark :=
  (m.1, m.2.1,
    resolve σ (m.2.2.1.1 :: m.2.2.1.2),
    resolve σ (m.2.2.2.1 :: m.2.2.2.2))

/-- **The Peritext read layer**: every live mark record, with its endpoints
resolved (rehomed) against the RGA component by the RGA's own path-climbing
resolution. -/
def peritextRender (s : (prodSig RGACondSig' MarkStore).State) :
    Finset RenderedMark :=
  Finset.image (fun q : OSElem MarkPayload => resolveMark (s.1 : concrete_st) q.2.2)
    (s.2 : MarkState)

/-- **Render congruence — memo §3.4's one new VC**: `(≈₁ × Eq)`-related
product states render identically. Characters up to the RGA's observational
`≈` (resolution reads only `contains`, which `≈` fixes — `resolve_dom_eq`);
marks literally. This is exactly the congruence a signature-level
`resolveMarks` query would owe `CongVC.query_congr`, delivered standalone. -/
theorem peritextRender_congr {s s' : (prodSig RGACondSig' MarkStore).State}
    (h : (prodEqEquiv (D₂ := MarkStore) rgaEqEquiv').eqv s s') :
    peritextRender s = peritextRender s' := by
  obtain ⟨h₁, h₂⟩ := h
  have h₁' : eq (s.1 : concrete_st) (s'.1 : concrete_st) := h₁
  have hres : ∀ cands : List ℕ,
      resolve (s.1 : concrete_st) cands = resolve (s'.1 : concrete_st) cands :=
    fun cands => resolve_dom_eq _ _ cands (fun c _ => (h₁' c).1)
  unfold peritextRender
  rw [← h₂]
  apply Finset.image_congr
  intro q _
  unfold resolveMark
  simp only [hres]

/-! ## Axiom audit -/

#print axioms peritextRender_congr

end Sal.ConditionedMRDTs.PeritextTF
