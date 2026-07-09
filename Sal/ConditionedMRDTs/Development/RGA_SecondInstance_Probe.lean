import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.Framework.MRDTSig

/-!
# PROBE: the payload-parametric tombstone-free RGA is NOT `ℕ`-in-disguise

The core (`RGA_Tombstone_Free_MRDT.lean`) and reachability layer
(`RGA_Reachability_Invariant.lean`) are now generalized over the element type
`α` (defaulting to `ℕ`).  This file is the **acceptance witness** that the
generalization is *genuinely* parametric: everything instantiates at a SECOND,
structurally different element type — here `Bool` and `ℕ ⊕ ℕ` — with kernel-clean
axioms.

If the generalization were secretly pinned to `ℕ` (e.g. via a hidden `Zero`/`Ord`
use on the element), these instantiations would fail to typecheck.  They do not:
`concrete_st`, `do_`, `merge`, `rc_non_comm'`, `merge_idem`, the commutation
lemmas, and a full `ConditionedMRDTSig`-analogue (mirroring
`RGAInstance.RGACondSig'`) all instantiate at both payloads.

This does NOT build the full Peritext instantiation (`α := char ⊕ boundary`);
that is the next task.  It only certifies parametricity of the core + signature.
-/

open Classical
open Sal.Emulation
open Sal.ConditionedMRDTs

namespace RGA_SecondInstance_Probe

/-! ## §1  Instantiate the core at `α := Bool` (a structurally different payload) -/

-- The state carries a `Bool` element in the `.1` of each value pair.
example : concrete_st Bool = map ℕ (Bool × ℕ) := rfl

-- The three convergence-spine results instantiate at `Bool`.
example : ∀ (o1 o2 : op_t Bool),
    (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
    → (rc o1 o2 = rc_res.Either ↔ commutes_with' o1 o2) :=
  rc_non_comm' (α := Bool)

example : ∀ (s : concrete_st Bool), wf s → eq (merge s s s) s :=
  merge_idem (α := Bool)

example : ∀ (s : concrete_st Bool) (t1 r1 : ℕ) (p1 : List ℕ) (x1 t2 r2 : ℕ)
    (p2 : List ℕ) (x2 : ℕ), contains s 0 = false →
    accurate (t1, r1, .Del p1 x1) s → accurate (t2, r2, .Del p2 x2) s →
    eq (do_ (do_ s (t1, r1, .Del p1 x1)) (t2, r2, .Del p2 x2))
       (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Del p1 x1)) :=
  deldel_comm (α := Bool)

/-! ## §2  A `ConditionedMRDTSig`-analogue at `α := Bool`

Mirrors `RGAInstance.RGACondSig'` (`Inv := wf ∧ root-free ∧ id_mono`,
`applicable := accurate ∧ fresh_ts`) but at the `Bool` payload, using the
parametric core + reachability layer.  Typechecking this is the "signature
`RGACondSig'`-analogue at that `α`" acceptance clause. -/

noncomputable def RGAM_Bool : MRDTSig where
  State := concrete_st Bool
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := init_st (α := Bool)
  AppOp := app_op_t Bool
  dec_op := inferInstance
  Query := Unit
  Value := Unit
  update := fun s o => do_ s o
  merge := fun a b => _root_.merge (init_st (α := Bool)) a b
  query := fun _ _ => ()
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => _root_.merge l a b
  merge_init_slice := fun _ _ => rfl

noncomputable def RGACondSig'_Bool : ConditionedMRDTSig where
  toMRDTSig := RGAM_Bool
  Inv := fun s => wf s ∧ contains s 0 = false ∧ id_mono s
  applicable := fun o s => accurate o s ∧ fresh_ts o s

-- The reachability invariants instantiate at `Bool` (structural checks).
example : RgaInv (init_st (α := Bool)) := Inv_init
example : id_mono (init_st (α := Bool)) := id_mono_init

/-! ## §3  A THIRD payload, `α := ℕ ⊕ ℕ` (sum type)

A different structural shape again (tagged union), to rule out any `Bool`-specific
coincidence. -/

abbrev Elt := ℕ ⊕ ℕ

example : concrete_st Elt = map ℕ (Elt × ℕ) := rfl

example : ∀ (o1 o2 : op_t Elt),
    (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
    → (rc o1 o2 = rc_res.Either ↔ commutes_with' o1 o2) :=
  rc_non_comm' (α := Elt)

example : ∀ (s : concrete_st Elt), wf s → eq (merge s s s) s :=
  merge_idem (α := Elt)

noncomputable def RGACondSig'_Sum : ConditionedMRDTSig where
  toMRDTSig :=
    { State := concrete_st Elt
      dec_state := fun a b => Classical.propDecidable (a = b)
      init := init_st (α := Elt)
      AppOp := app_op_t Elt
      dec_op := inferInstance
      Query := Unit
      Value := Unit
      update := fun s o => do_ s o
      merge := fun a b => _root_.merge (init_st (α := Elt)) a b
      query := fun _ _ => ()
      rc := fun _ _ => RcRes.Either
      mergeL := fun l a b => _root_.merge l a b
      merge_init_slice := fun _ _ => rfl }
  Inv := fun s => wf s ∧ contains s 0 = false ∧ id_mono s
  applicable := fun o s => accurate o s ∧ fresh_ts o s

/-! ## §4  Axiom audit — instantiations are kernel-clean at the new payloads -/

theorem rc_non_comm'_Bool : ∀ (o1 o2 : op_t Bool),
    (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
    → (rc o1 o2 = rc_res.Either ↔ commutes_with' o1 o2) :=
  rc_non_comm' (α := Bool)

theorem merge_idem_Sum : ∀ (s : concrete_st Elt), wf s → eq (merge s s s) s :=
  merge_idem (α := Elt)

#print axioms rc_non_comm'_Bool
#print axioms merge_idem_Sum
#print axioms RGACondSig'_Bool
#print axioms RGACondSig'_Sum

end RGA_SecondInstance_Probe
