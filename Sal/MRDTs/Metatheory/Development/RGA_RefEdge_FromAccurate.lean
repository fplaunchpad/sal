import Sal.MRDTs.Metatheory.Development.RGA_NoopFeasible_CanonFold

/-!
# `RefEdge` from accuracy — the reference-freshness the engine needs, without a config primitive

*Additive; modifies no existing file; 0 `sorry`.*

KC's point: the only use of `RefEdge` in `canonStepOK_of_noopFeasible` is `hnoRef` — that no earlier
op references the fresh id `o.1`. That falls out of `accurate`: an op accurate at a state cannot
reference an id absent from that state. Since `o.1` is inserted nowhere in the prefix (id-uniqueness),
it is absent from every prefix, so no accurately-applied earlier op references it. No `reference ⟹ vis`
config primitive is needed.

`not_ref_of_accurate` is the core fact. (The no-op-delete corner — a `Del` of `o.1` before `o` — is
excluded separately by applicability-at-generation, `hBA`.)
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGARefEdgeFromAccurate

open Sal.Emulation
open RGANoopFeasible (refsOf)

/-- **Accuracy forbids referencing an absent id.**  If `z` is `accurate` at `s` and `c ≠ 0` is not
live in `s`, then `z` does not reference `c` (`c ∉ refsOf z`): the accurate op's leaf and every path
entry are live in `s`. -/
theorem not_ref_of_accurate (z : op_t) (s : concrete_st) (c : ℕ)
    (hacc : accurate z s) (hc0 : c ≠ 0) (hc : contains s c = false) :
    c ∉ refsOf z := by
  intro hmem
  simp only [refsOf, List.mem_cons] at hmem
  rcases hacc with ⟨hleaf0, hpath0⟩ | ⟨hcontains, hpath⟩
  · rcases hmem with h | h
    · exact hc0 (h.trans hleaf0)
    · rw [hpath0] at h; simp at h
  · rcases hmem with h | h
    · subst h; rw [hcontains] at hc; exact Bool.noConfusion hc
    · have hlive := isAncPath_mem s (opLeaf z.2.2) (opPath z.2.2) hpath c h
      rw [hlive] at hc; exact Bool.noConfusion hc

#print axioms not_ref_of_accurate

end Sal.Metatheory.RGARefEdgeFromAccurate
