import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance

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
set_option linter.unusedSectionVars false
namespace Sal.ConditionedMRDTs.RGALoOnEqCausal

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq eqCommutesOn fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')

/-- **The RGA's `rc` is constantly `Either`.**  Definitional (`RGAM.rc = fun _ _ => RcRes.Either`). -/
theorem rga_rc_either (a b : op_t α) : (RGACondSig' α).rc a b = RcRes.Either := rfl

/-- **`loOnEq` is purely causal for the RGA.**  Clause (B)'s `rc = Fst_then_snd` is impossible
(`rc = Either`), so `loOnEq` reduces to clause (A): `vis a b ∧ ¬ eqCommutesOn a b`. -/
theorem loOnEq_causal_iff (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (ev : Set (op_t α)) (a b : op_t α) :
    loOnEq (rgaEqEquiv' α) W vis ev a b ↔ (vis a b ∧ ¬ eqCommutesOn (rgaEqEquiv' α) W a b) := by
  unfold loOnEq
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by rw [rga_rc_either]; exact fun h => RcRes.noConfusion h)
  · exact fun h => Or.inl h

/-- **`loOnEq ⊆ vis`.**  Every `loOnEq` edge is a causal (`vis`) edge — the RGA order carries no
concurrent tiebreak. -/
theorem loOnEq_imp_vis (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (ev : Set (op_t α)) (a b : op_t α) (h : loOnEq (rgaEqEquiv' α) W vis ev a b) : vis a b :=
  ((loOnEq_causal_iff W vis ev a b).mp h).1

/-- **Eq-commuting pairs are `loOnEq`-unordered.**  If `a` and `b` eq-commute, neither `loOnEq a b`
nor `loOnEq b a` holds — so a linearization is free to order them either way. -/
theorem not_loOnEq_of_eqCommutes (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (ev : Set (op_t α)) (a b : op_t α) (hcomm : eqCommutesOn (rgaEqEquiv' α) W a b)
    (hcomm' : eqCommutesOn (rgaEqEquiv' α) W b a) :
    ¬ loOnEq (rgaEqEquiv' α) W vis ev a b ∧ ¬ loOnEq (rgaEqEquiv' α) W vis ev b a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ((loOnEq_causal_iff W vis ev a b).mp h).2 hcomm
  · exact ((loOnEq_causal_iff W vis ev b a).mp h).2 hcomm'

/-- **A `vis`-respecting linearization respects `loOnEq`.**  Since `loOnEq ⊆ vis`, a backward `loOnEq`
edge would be a backward `vis` edge; so any causal (`vis`-respecting) enumeration is automatically
`loOnEq`-respecting.  Reduces the δ-enum's semantic order obligation (`respects … (loOnEq …)`) to a
clean causal one (`respects … vis`). -/
theorem respects_loOnEq_of_respects_vis (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (ev : Set (op_t α)) (π : List (op_t α)) (h : respects π vis) :
    respects π (loOnEq (rgaEqEquiv' α) W vis ev) :=
  List.Pairwise.imp (fun hnv hlo => hnv (loOnEq_imp_vis W vis ev _ _ hlo)) h

/-- **No backward `loOnEq` edge without a backward `vis` edge.**  Contrapositive of `loOnEq_imp_vis`:
if `a` does not causally see `b` (`¬ vis a b`), then there is no `loOnEq a b` edge — regardless of
commutation.  THIS, not eq-commutation, is the correct tool for δ-A: to move an insert before a
concurrent delete-of-its-anchor, rule out the forced order `loOnEq (Del) (Ins)` via `¬ vis (Del) (Ins)`
— an insert in a `noopFeasible` branch never causally follows the deletion of its own anchor (else it
would be applied at a dead anchor, non-accurate and non-noop).  Eq-commutation is UNRELIABLE here
(`Del` can reparent an insert into/out of accuracy, flipping the `doW` guard), so the visibility route
is the only sound one — and it needs no commutation lemma. -/
theorem not_loOnEq_of_not_vis (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (ev : Set (op_t α)) (a b : op_t α) (hnv : ¬ vis a b) : ¬ loOnEq (rgaEqEquiv' α) W vis ev a b :=
  fun hlo => hnv (loOnEq_imp_vis W vis ev a b hlo)

/-- **No cross-branch `loOnEq` edge into a causally-closed set.**  If `evBranch` is `vis`-closed
(`fullClosureRel`) and `i ∈ evBranch` while `d ∉ evBranch`, there is no `loOnEq d i` (for any ambient
`evAmb`): `loOnEq d i ⟹ vis d i ⟹ d ∈ evBranch` (closure), contradicting `d ∉ evBranch`.  In the merge
delta this kills every `loOnEq` edge from a branch-2-only op to a branch-1-only op (and vice versa) —
the cross-branch half of the delta order's acyclicity, so the two branches' deltas never force an
interleaving. -/
theorem not_loOnEq_cross_branch (W : op_t α → concrete_st α → Prop) (vis : op_t α → op_t α → Prop)
    (evBranch evAmb : Set (op_t α)) (hcl : fullClosureRel (D := (RGACondSig' α)) vis evBranch)
    (d i : op_t α) (hi : i ∈ evBranch) (hd : d ∉ evBranch) :
    ¬ loOnEq (rgaEqEquiv' α) W vis evAmb d i :=
  not_loOnEq_of_not_vis W vis evAmb d i (fun hvis => hd (hcl d i hvis hi))

#print axioms rga_rc_either
#print axioms loOnEq_causal_iff
#print axioms loOnEq_imp_vis
#print axioms not_loOnEq_of_eqCommutes
#print axioms respects_loOnEq_of_respects_vis
#print axioms not_loOnEq_of_not_vis
#print axioms not_loOnEq_cross_branch

end Sal.ConditionedMRDTs.RGALoOnEqCausal
