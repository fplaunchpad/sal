import Sal.CRDTs.Grow_Only_Set_CRDT
import Sal.Emulation.RA_Linearizability

/-!
# Grow-Only Set as an emulation `CRDTSig`

Smoke test for the Phase 1 architecture: wrap `Sal/CRDTs/Grow_Only_Set_CRDT.lean`
as a `Sal.Emulation.CRDTSig` and discharge `SatisfiesVCs` by
plugging the file's existing 24 `by sal`-closed theorems into the
struct fields. If this compiles, we have end-to-end confidence that
the Prop-valued preservation lemmas align with the Bool-valued
Sal-paper statements.

Namespace notes:
* `Grow_Only_Set_CRDT.lean` is un-namespaced — `concrete_st`, `init_st`,
  `do_`, `merge`, `rc`, and all 24 theorems live at the top level after
  import. We qualify with `_root_.` where disambiguation is needed.
* The local `rc_res` and `Sal.Emulation.RcRes` are different types;
  a small `toRcRes` conversion bridges them.
-/

open Sal.Emulation Classical

namespace Sal.Emulation.Instances.GrowOnlySet

/-- Convert the per-file `rc_res` into the generic `RcRes`. -/
def toRcRes : _root_.rc_res → RcRes
  | .Fst_then_snd => .Fst_then_snd
  | .Snd_then_fst => .Snd_then_fst
  | .Either       => .Either

@[simp] theorem toRcRes_Either : toRcRes .Either = RcRes.Either := rfl
@[simp] theorem toRcRes_Fst    : toRcRes .Fst_then_snd = RcRes.Fst_then_snd := rfl
@[simp] theorem toRcRes_Snd    : toRcRes .Snd_then_fst = RcRes.Snd_then_fst := rfl

/-- `app_op_t` doesn't carry a `DecidableEq` instance in the source
file; derive one here via classical choice (since its constructors are
`Add n` for `n : ℕ`, a structural decidability would also work). -/
noncomputable instance : DecidableEq _root_.app_op_t :=
  fun a b => Classical.propDecidable (a = b)

/-- The Grow-Only Set as a `CRDTSig`. -/
noncomputable def D : CRDTSig where
  State := _root_.concrete_st
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := _root_.init_st
  AppOp := _root_.app_op_t
  dec_op := inferInstance
  Query := Unit
  Value := _root_.concrete_st
  update := _root_.do_
  merge := _root_.merge
  query := fun s _ => s
  rc := fun o₁ o₂ => toRcRes (_root_.rc o₁ o₂)

/-! ## Plumbing the 24 VCs

The existing Sal theorems use `distinct_ops o1 o2` (a Bool-valued
function returning `Prod.fst o1 != Prod.fst o2`) while our
`distinctOps` is `o₁.time ≠ o₂.time` (Prop-valued). The bridging
`simp` lemma below unifies them. -/

@[simp] theorem distinctOps_iff (o₁ o₂ : _root_.op_t) :
    distinctOps (D := D) o₁ o₂ ↔ (_root_.distinct_ops o₁ o₂ = true) := by
  unfold distinctOps; simp [_root_.distinct_ops, Op.time]

@[simp] theorem differentReplicas_iff (o₁ o₂ : _root_.op_t) :
    differentReplicas (D := D) o₁ o₂ ↔ (_root_.get_rid o₁ != _root_.get_rid o₂) := by
  unfold differentReplicas
  rcases o₁ with ⟨t₁, r₁, a₁⟩
  rcases o₂ with ⟨t₂, r₂, a₂⟩
  simp [Op.rep]

/-! ## The SatisfiesVCs instance

`rc := Either` makes most VCs trivial: `Fst_then_snd` never holds, so
premises involving `rc … = Fst_then_snd` are vacuous. Those cases
close by `intro h; exact absurd h (by decide)` or `simp`.

For the cases that aren't vacuous (commutativity-style), the existing
theorem does the work. -/

/-- Satisfies the 24 VCs. Each field plugs in the corresponding
per-file theorem; the type mismatch between Prop-valued `distinctOps`
and Bool-valued `distinct_ops` is bridged by `simp` with the
`@[simp]` lemmas above.

Currently closes `merge_comm` and `merge_idem` as a sanity check that
the plumbing works. The other 22 fields are marked `sorry`; each is a
mechanical unpacking of the corresponding Sal theorem (roughly a day
of focused work total). -/
theorem D_satisfies_VCs : SatisfiesVCs D where
  rc_non_comm := by sorry
  no_rc_chain := by sorry
  cond_comm_base := by sorry
  merge_comm := fun a b => _root_.merge_comm a b
  merge_idem := fun s => _root_.merge_idem s
  base_2op := by sorry
  ind_lca_2op := by sorry
  inter_right_base_2op := by sorry
  inter_left_base_2op := by sorry
  inter_right_2op := by sorry
  inter_left_2op := by sorry
  inter_lca_2op := by sorry
  ind_right_2op := by sorry
  ind_left_2op := by sorry
  base_1op := by sorry
  ind_lca_1op := by sorry
  inter_right_base_1op := by sorry
  inter_left_base_1op := by sorry
  inter_right_1op := by sorry
  inter_left_1op := by sorry
  inter_lca_1op := by sorry
  ind_left_1op := by sorry
  ind_right_1op := by sorry
  lem_0op := by sorry

end Sal.Emulation.Instances.GrowOnlySet
