import Sal.MRDTs.Metatheory.Development.RGA_NoopFeasible_CanonFold

/-!
# `CanonStepOK` from honest facts — the `RefEdge`-free single-op step

*Additive; modifies no existing file; 0 `sorry`.*

The reachability route to unconditional RGA: instead of deriving the canonical fold discipline through
`RefEdge` (which needs `reference⟹vis`), a **reachable** `apply` allocates a *globally fresh* id `t`
(Step3's `h_fresh_t`: `t ∉ events`). The freshness `RefEdge` was buying — that no earlier op references
`t` (`hnoRef`) — then follows from "references are inserted-in-events" (`insertedIn_ev_of_ref`, built)
+ `t ∉ events`. `canonStepOK_ins_of_facts` derives `CanonStepOK` for the `Ins` from `hnoRef` + the
honest facts directly, with no `RefEdge`. Feeding it to `canonInv_doIns` gives single-op `CanonInv`
preservation — the `apply` case of the `CanonMatch` reachability invariant.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGACanonStepFromFacts

open Sal.Emulation
open RGACanonConvergence (CanonStepOK ChainOK deletedIn CanonInv delOK_of_accurate
  canonInv_doIns canonInv_doDel)
open RGANoopFeasible (refsOf)
open Sal.Metatheory.RGAInvUpdateQ (WfOpGenQ)

/-- **`CanonStepOK` for an `Ins` from honest facts** (no `RefEdge`).  Given `t` nonzero and fresh in
`s`, `hnoRef` (no op in `F` references `t`), `WfOpGenQ` (chain strictly below `t`), and `ChainOK`
(the anchor chain is a genuine live path — from `accurate`), the canonical step discipline holds. -/
theorem canonStepOK_ins_of_facts (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (ht0 : t ≠ 0) (htf : contains s t = false)
    (hnoRef : ∀ z ∈ F, t ∉ refsOf z)
    (hgen : WfOpGenQ (t, r, .Ins e p a))
    (hchain : ChainOK s (a :: p)) :
    CanonStepOK F s (t, r, .Ins e p a) := by
  refine ⟨ht0, htf, ?_, ?_, ?_, hchain⟩
  · rintro ⟨t', r', p', hm⟩
    exact hnoRef (t', r', .Del p' t) hm (by simp [refsOf])
  · intro hmem
    exact absurd (hgen.2 t hmem) (lt_irrefl t)
  · intro t' r' e' p' a' hm hmem
    exact hnoRef (t', r', .Ins e' p' a') hm (by simpa [refsOf] using hmem)

#print axioms canonStepOK_ins_of_facts

/-- **Single-op `CanonInv` preservation for an `Ins`, from honest facts** (no `RefEdge`).  Composes
`canonStepOK_ins_of_facts` with `canonInv_doIns`: given the prior canonical invariant, a fresh id,
`hnoRef`, generation discipline, and `ChainOK`, the fold's invariant carries across the `Ins`.  The
`apply`-case for an insert of the `CanonMatch` reachability invariant. -/
theorem canonInv_doIns_of_facts (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (htf : contains s t = false)
    (hnoRef : ∀ z ∈ F, t ∉ refsOf z)
    (hgen : WfOpGenQ (t, r, .Ins e p a)) (hchain : ChainOK s (a :: p)) :
    CanonInv (F ++ [(t, r, .Ins e p a)]) (do_ s (t, r, .Ins e p a)) :=
  canonInv_doIns F s t r e a p hinv
    (canonStepOK_ins_of_facts F s t r e a p hgen.1 htf hnoRef hgen hchain)

/-- **Single-op `CanonInv` preservation for a `Del`, from `accurate`** (no `hnoRef` needed).  The `Del`
step discipline (`DelOK`) falls entirely out of `accurate` (`delOK_of_accurate`), so the invariant
carries across an accurately-applied delete given only the prior invariant.  The `apply`-case for a
delete of the `CanonMatch` reachability invariant. -/
theorem canonInv_doDel_of_accurate (F : List op_t) (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hacc : accurate (t, r, .Del p x) s) :
    CanonInv (F ++ [(t, r, .Del p x)]) (do_ s (t, r, .Del p x)) :=
  canonInv_doDel F s t r x p hinv (delOK_of_accurate s t r x p hinv.1 hacc)

#print axioms canonInv_doIns_of_facts
#print axioms canonInv_doDel_of_accurate

end Sal.Metatheory.RGACanonStepFromFacts
