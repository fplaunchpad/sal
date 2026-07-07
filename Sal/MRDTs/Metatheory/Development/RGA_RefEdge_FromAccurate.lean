import Sal.MRDTs.Metatheory.Conditioned.RGA_NoopFeasible_CanonFold

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

open RGACanonConvergence (insertedIn)
open RGACanonFoldOK (insertedIn_of_contains_fold)
open RGAMergeLinearization (applySeqR)

/-- **Accuracy: referenced ids are live.**  The positive direction of `not_ref_of_accurate`. -/
theorem ref_live_of_accurate (z : op_t) (s : concrete_st) (c : ℕ)
    (hacc : accurate z s) (hmem : c ∈ refsOf z) (hc0 : c ≠ 0) :
    contains s c = true := by
  by_contra hcon
  have hcf : contains s c = false := by
    cases h : contains s c with
    | true => exact absurd h hcon
    | false => rfl
  exact not_ref_of_accurate z s c hacc hc0 hcf hmem

/-- **The config-independent core of `reference ⟹ vis`.**  From a version's canonical witness (its
event enumeration `ρ` with `applySeqR init ρ ≈ s`) and an op `z` accurate at that version's state `s`,
every id `z` references (other than root) is *inserted in the version's event set* — its creator is
present. Combined with the `apply` step's `ev → new op` visibility, this yields `reference ⟹ vis`
without any config-level primitive. Uses only `insertedIn_of_contains_fold` (unconditional). -/
theorem insertedIn_ev_of_ref (ρ : List op_t) (ev : Set op_t) (s : concrete_st) (z : op_t) (c : ℕ)
    (hperm : listPermOf ρ ev) (hfold : eq (applySeqR init_st ρ) s)
    (hacc : accurate z s) (hmem : c ∈ refsOf z) (hc0 : c ≠ 0) :
    ∃ r e p a, (c, r, .Ins e p a) ∈ ev := by
  have hlive : contains s c = true := ref_live_of_accurate z s c hacc hmem hc0
  have hfoldlive : contains (applySeqR init_st ρ) c = true := by
    rw [(hfold c).1]; exact hlive
  obtain ⟨r, e, p, a, hin⟩ := insertedIn_of_contains_fold ρ c hfoldlive
  exact ⟨r, e, p, a, (hperm.2 _).mp hin⟩

#print axioms ref_live_of_accurate
#print axioms insertedIn_ev_of_ref

end Sal.Metatheory.RGARefEdgeFromAccurate
