import Sal.CRDTs.Grow_Only_Set.Grow_Only_Set_CRDT
import Sal.CRDTs.Metatheory.RA_Linearizability
import Mathlib.Data.List.Induction

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

/-- For the Grow-Only Set, `D.rc` is always `Either`. Many VCs become
vacuous because their premises require `Fst_then_snd`. -/
@[simp] theorem D_rc_Either (o₁ o₂ : Op D.AppOp) :
    D.rc o₁ o₂ = RcRes.Either := by
  show toRcRes (_root_.rc o₁ o₂) = RcRes.Either
  simp

/-- Fst_then_snd never holds; used to discharge vacuous premises. -/
@[simp] theorem D_rc_not_Fst (o₁ o₂ : Op D.AppOp) :
    D.rc o₁ o₂ ≠ RcRes.Fst_then_snd := by
  rw [D_rc_Either]; decide

@[simp] theorem D_rc_Fst_iff_False (o₁ o₂ : Op D.AppOp) :
    (D.rc o₁ o₂ = RcRes.Fst_then_snd) ↔ False := by simp

/-! ## The SatisfiesVCs instance

`rc := Either` makes most VCs trivial: `Fst_then_snd` never holds, so
premises involving `rc … = Fst_then_snd` are vacuous. Those cases
close by `intro h; exact absurd h (by decide)` or `simp`.

For the cases that aren't vacuous (commutativity-style), the existing
theorem does the work. -/

/-- Satisfies all 24 VCs. **No sorries.** Structure of each field:

* Vacuous VCs (premise requires `Fst_then_snd`, impossible since
  `D.rc = Either` always): closed by `intros; simp_all` using the
  `@[simp]` lemmas `D_rc_Fst_iff_False` / `D_rc_Either`.
* `rc_non_comm`: delegates to `_root_.rc_non_comm`, bridging the Prop
  premise conjunction to the Bool one.
* `base_2op`, `ind_lca_2op`, `ind_left_2op`, `base_1op`, `ind_lca_1op`,
  `ind_left_1op`, `ind_right_1op`, `lem_0op`, `merge_comm`,
  `merge_idem`: plumb directly to the corresponding per-file Sal
  theorems.

This validates the Prop-valued `SatisfiesVCs` matches the Bool-valued
theorem statements in the Sal-paper file, end-to-end, for at least one
concrete CRDT. -/
theorem D_satisfies_VCs : SatisfiesVCs D where
  -- `rc = Either` is total → commutes_with holds (Sal proved this for real).
  rc_non_comm := by
    intro o₁ o₂ h_d h_r
    have hb : _root_.distinct_ops o₁ o₂ ∧ _root_.get_rid o₁ != _root_.get_rid o₂ := by
      refine ⟨?_, ?_⟩
      · rwa [← distinctOps_iff]
      · rwa [← differentReplicas_iff]
    have h := _root_.rc_non_comm o₁ o₂ hb
    simp only [D_rc_Either, true_iff]
    intro s
    exact (h.mp rfl) s
  rc_non_comm_directional := by
    -- For Grow-Only Set, `D.rc = Either` always, so RHS
    -- `rc=Fst ∨ rc(swap)=Fst` is `False`. LHS `¬ commutes` is also
    -- `False` because all G-Set ops commute (set add commutes
    -- regardless of replica). Hence iff `False ↔ False` holds.
    intro o₁ o₂ _
    simp only [D_rc_Fst_iff_False, or_self, iff_false]
    intro h_nc
    apply h_nc
    intro s
    rcases o₁ with ⟨_, _, ⟨n₁⟩⟩
    rcases o₂ with ⟨_, _, ⟨n₂⟩⟩
    show D.update (D.update s _) _ = D.update (D.update s _) _
    simp [D, _root_.do_]
    grind
  -- Vacuous: D.rc = Either always, so D.rc = Fst_then_snd is impossible.
  no_rc_chain := by intros; simp_all
  cond_comm_base := by intros; simp_all
  cond_comm_lift := by intros; simp_all
  merge_comm := fun a b => _root_.merge_comm a b
  merge_idem := fun s => _root_.merge_idem s
  -- Real content: delegate to Sal's base_2op.
  base_2op := by
    intro o₁ o₂ _ h_diff h_dis
    apply _root_.base_2op
    exact ⟨Or.inr rfl, by rwa [← differentReplicas_iff], by rwa [← distinctOps_iff]⟩
  ind_lca_2op := by
    intro l o₁ o₂ ol _ h_diff h_d12 h_d13 h_d23 h_eq
    apply _root_.ind_lca_2op
    exact ⟨Or.inr rfl, by rwa [← differentReplicas_iff],
           by rwa [← distinctOps_iff], by rwa [← distinctOps_iff],
           by rwa [← distinctOps_iff], h_eq⟩
  inter_right_base_2op := by intros; simp_all
  inter_left_base_2op := by intros; simp_all
  inter_right_2op := by intros; simp_all
  inter_left_2op := by intros; simp_all
  inter_lca_2op := by intros; simp_all
  ind_right_2op := by intros; simp_all
  ind_left_2op := by
    intro a b o₁ o₂ o₁' _ h_diff h_d12 h_d13 h_d23 h_eq
    apply _root_.ind_left_2op
    exact ⟨Or.inr rfl, by rwa [← differentReplicas_iff],
           by rwa [← distinctOps_iff], by rwa [← distinctOps_iff],
           by rwa [← distinctOps_iff], h_eq⟩
  base_1op := fun o => _root_.base_1op o
  ind_lca_1op := by
    intro l o₁ ol h_dis h_eq
    apply _root_.ind_lca_1op
    exact ⟨by rwa [← distinctOps_iff], h_eq⟩
  inter_right_base_1op := by intros; simp_all
  inter_left_base_1op := by intros; simp_all
  inter_right_1op := by intros; simp_all
  inter_left_1op := by intros; simp_all
  inter_lca_1op := by intros; simp_all
  ind_left_1op := by
    intro a b o₁ o₁' ol h_d11 h_d1l h_d1l' h_eq
    apply _root_.ind_left_1op
    exact ⟨by rwa [← distinctOps_iff], by rwa [← distinctOps_iff],
           by rwa [← distinctOps_iff], h_eq⟩
  ind_right_1op := by
    intro a b o₂ o₂' ol h_d22 h_d2l h_d2l' h_eq
    apply _root_.ind_right_1op
    exact ⟨by rwa [← distinctOps_iff], by rwa [← distinctOps_iff],
           by rwa [← distinctOps_iff], h_eq⟩
  lem_0op := fun a b ol => _root_.lem_0op a b ol
  merge_init := by
    intro s
    show _root_.merge _root_.init_st s = s
    simp [_root_.merge, _root_.init_st]
    ext x; simp
  merge_peel_comm := by
    -- For Grow-Only Set, the conclusion is set associativity:
    -- (a ∪ {e}) ∪ ⋃π = (a ∪ ⋃π) ∪ {e}.
    -- The hypothesis `∀ x ∈ π, commutes e x` is irrelevant — G-Set
    -- has all ops commuting, so the conclusion holds unconditionally.
    intro a e π _
    -- The key fact: for any set b, merge (do_ a e) b = do_ (merge a b) e.
    -- Prove this directly in G-Set, regardless of how b was constructed.
    have key : ∀ b : _root_.concrete_st,
        _root_.merge (_root_.do_ a e) b = _root_.do_ (_root_.merge a b) e := by
      intro b
      rcases e with ⟨_, _, ⟨n⟩⟩
      simp [_root_.merge, _root_.do_]
      ext x; simp
      cases a x <;> cases b x <;> simp
    exact key _
  shared_peel_1op := by
    -- For Grow-Only Set, this is just set-union associativity:
    -- (a ∪ {ol} ∪ {o₁}) ∪ (b ∪ {ol}) = (a ∪ {ol} ∪ b ∪ {ol}) ∪ {o₁}.
    intro o₁ ol _ a b
    rcases o₁ with ⟨_, _, ⟨n₁⟩⟩
    rcases ol with ⟨_, _, ⟨nol⟩⟩
    simp [D, _root_.merge, _root_.do_]
    ext x
    cases a x <;> cases b x <;> simp <;> grind

end Sal.Emulation.Instances.GrowOnlySet
