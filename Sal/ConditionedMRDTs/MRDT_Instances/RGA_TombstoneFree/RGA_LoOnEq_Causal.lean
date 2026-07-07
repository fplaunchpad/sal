import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance

/-!
# `loOnEq` collapses to pure causal non-commutation for the RGA

*Additive; modifies no existing file; 0 `sorry`.*

The δ-A unlock.  `loOnEq` (`GenericEqQuotient`) has two disjuncts: (A) causal non-commutation
`vis a b ∧ ¬ eqCommutesOn a b`, and (B) a concurrent tiebreak requiring `D.rc a b = RcRes.Fst_then_snd`.
The RGA's conflict-resolution is `RGAM.rc = fun _ _ => RcRes.Either` (`RGA_EqQuotient` §, `G2_Transport_Probe`),
so `rc a b = Either ≠ Fst_then_snd` **always** — clause (B) is unsatisfiable.  Hence for the RGA
`loOnEq` is EXACTLY clause (A): a purely causal order (`loOnEq ⊆ vis`), with no concurrent tiebreak.

Consequences (used by δ-A / `hEnum`): every `loOnEq` edge is a `vis` edge; eq-commuting pairs are
`loOnEq`-unordered in BOTH directions; so any causal linearization that additionally orders inserts
before concurrent deletes-of-their-anchor is `loOnEq`-respecting (the tiebreak can't forbid it).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGALoOnEqCausal

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq eqCommutesOn fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')

/-- **The RGA's `rc` is constantly `Either`.**  Definitional (`RGAM.rc = fun _ _ => RcRes.Either`). -/
theorem rga_rc_either (a b : op_t) : RGACondSig'.rc a b = RcRes.Either := rfl

/-- **`loOnEq` is purely causal for the RGA.**  Clause (B)'s `rc = Fst_then_snd` is impossible
(`rc = Either`), so `loOnEq` reduces to clause (A): `vis a b ∧ ¬ eqCommutesOn a b`. -/
theorem loOnEq_causal_iff (W : op_t → concrete_st → Prop) (vis : op_t → op_t → Prop)
    (ev : Set op_t) (a b : op_t) :
    loOnEq rgaEqEquiv' W vis ev a b ↔ (vis a b ∧ ¬ eqCommutesOn rgaEqEquiv' W a b) := by
  unfold loOnEq
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by rw [rga_rc_either]; exact fun h => RcRes.noConfusion h)
  · exact fun h => Or.inl h

/-- **`loOnEq ⊆ vis`.**  Every `loOnEq` edge is a causal (`vis`) edge — the RGA order carries no
concurrent tiebreak. -/
theorem loOnEq_imp_vis (W : op_t → concrete_st → Prop) (vis : op_t → op_t → Prop)
    (ev : Set op_t) (a b : op_t) (h : loOnEq rgaEqEquiv' W vis ev a b) : vis a b :=
  ((loOnEq_causal_iff W vis ev a b).mp h).1

end Sal.ConditionedMRDTs.RGALoOnEqCausal
