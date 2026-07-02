import Sal.MRDTs.Metatheory.MRDTSig
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Tauto

/-!
# Ternary verification-condition bundle `SatisfiesVCsT` (Phase-0, step **S4**)

This is the S4 deliverable of the Neem soundness meta-theory (Phase-0, TTL+RV design;
see `Sal/MRDTs/Metatheory/PHASE0_PLAN.md` §1.6 and §4 S4). It builds directly on S1's
`MRDTSig` (`Sal/MRDTs/Metatheory/MRDTSig.lean`) and its reuse contract `merge_init_slice`.

## What this file provides

* `SatisfiesVCsT (D : MRDTSig)` — the **ternary** VC bundle. It has the same 29 fields as
  the binary `Sal.Emulation.SatisfiesVCs`, but the merge/peel VCs are restated with the LCA
  state `l` first-class (`D.mergeL l a b` in place of the binary `D.merge a b`). The
  `do_`/`rc`-only side conditions (`rc_non_comm`, `rc_non_comm_directional`, `no_rc_chain`,
  `cond_comm_base`, `cond_comm_lift`) are carried **verbatim** from the binary shape.

* `satisfiesVCs_of_T` — **THE reuse contract.** `SatisfiesVCsT D → SatisfiesVCs D.toCRDTSig`.
  Every ternary merge field, instantiated at the LCA slice `l := D.init` and rewritten
  through `merge_init_slice`, collapses to exactly the corresponding binary field. So the
  proved binary machinery (`Sal/CRDTs/Metatheory/Merge_Linearization.lean`) applies to the
  init-LCA sub-family with no change.

* `GSet_satisfiesVCsT : SatisfiesVCsT GSet` — the S1 Grow-Only Set discharges the whole
  ternary bundle, witnessing the bundle is dischargeable on the simplest flat RDT.

## Design: the uniform ternary transform (deviation from §1.6, documented)

Each binary merge VC becomes its ternary counterpart by a single uniform transform:
prepend a fresh universally-quantified LCA state (`l`, or `lca` where the binary field
already binds an `l`) and replace every `D.merge X Y` by `D.mergeL l X Y`. At `l := D.init`,
`merge_init_slice : mergeL init a b = merge a b` turns each ternary field back into its
binary original — which is exactly what `satisfiesVCs_of_T` exploits.

This means, in particular:

* `merge_comm_T : ∀ l a b, mergeL l a b = mergeL l b a` (slices to `merge_comm`);
* `merge_idem_T : ∀ l s, mergeL l s s = s` (slices to `merge_idem`);
* `merge_init_T : ∀ l s, mergeL l init s = s` (slices to `merge_init`).

DEVIATION from PHASE0_PLAN §1.6, which sketched `merge_idem_T : ∀ a, mergeL a a a = a` and
`merge_bot_T : ∀ l b, mergeL l l b = b`. The `merge_bot_T` form does slice to `merge_init`
(`mergeL init init b → merge init b = b`), but `mergeL a a a = a` does **not** slice to the
binary `merge_idem : merge s s = s = mergeL init s s` (the LCA argument stays `s`, not
`init`). Since the required reuse contract (§4 S4 exit) is precisely `satisfiesVCs_of_T`,
we adopt the uniform-transform forms above, which slice cleanly to all three binary axioms.
The §1.6 forms remain available as strictly derivable specializations for the S6 merge
induction (`merge_idem_T`'s `l := a` instance is `mergeL a a a = a`).

The conditioning layer (`commutesOn`, `Inv`/`applicable` guards from `ConditionedMRDTSig`)
is intentionally **not** part of this bundle: S4 is stated at the unconditioned `MRDTSig`
level so the reuse contract is a clean slice. Conditioning is layered on in S5/S6.
-/

namespace Sal.Metatheory

open Sal.Emulation

/-! ## §1.6 — The ternary VC bundle -/

/-- **Ternary verification-condition bundle.** The 29-field ternary analogue of
`Sal.Emulation.SatisfiesVCs`. The `do_`/`rc`-only side conditions are carried verbatim; the
merge/peel VCs are restated with the LCA state first-class (`D.mergeL l …`). See the module
docstring for the uniform transform and the `satisfiesVCs_of_T` reuse contract. -/
structure SatisfiesVCsT (D : MRDTSig) : Prop where
  /-- rc-nonComm (verbatim). -/
  rc_non_comm :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (D.rc o₁ o₂ = RcRes.Either ↔ D.commutes o₁ o₂)

  /-- rc-nonComm directional form (verbatim). -/
  rc_non_comm_directional :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ →
      (¬ D.commutes o₁ o₂ ↔
       (D.rc o₁ o₂ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Fst_then_snd))

  /-- no-rc-chain (verbatim). -/
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         D.rc o₂ o₃ = RcRes.Fst_then_snd)

  /-- cond-comm base case (verbatim). -/
  cond_comm_base :
    ∀ (s : D.State) (o₁ o₂ o₃ : Op D.AppOp),
      distinctOps o₁ o₂ → distinctOps o₂ o₃ → distinctOps o₁ o₃ →
      D.rc o₁ o₂ = RcRes.Fst_then_snd →
      D.rc o₂ o₃ ≠ RcRes.Either →
      D.update (D.update (D.update s o₁) o₂) o₃
        = D.update (D.update (D.update s o₂) o₁) o₃

  /-- MergeCommutativity, ternary: `merge(l,a,b) = merge(l,b,a)`. -/
  merge_comm_T : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a

  /-- MergeIdempotence, ternary (uniform transform of `merge s s = s`):
  merging two equal branches over any LCA `l` returns that branch. -/
  merge_idem_T : ∀ l s : D.State, D.mergeL l s s = s

  /-- Base step of the bottom-up 2-op induction, ternary. -/
  base_2op :
    ∀ (l : D.State) (o₁ o₂ : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ → distinctOps o₁ o₂ →
      D.mergeL l (D.update D.init o₁) (D.update D.init o₂)
        = D.update (D.mergeL l D.init (D.update D.init o₂)) o₁

  /-- LCA induction step for the 2-op bottom-up rule, ternary. The prepended `lca` is the
  first-class LCA state; the binary field's own LCA-like base state is `l`. -/
  ind_lca_2op :
    ∀ (lca l : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      D.mergeL lca (D.update l o₁) (D.update l o₂)
        = D.update (D.mergeL lca l (D.update l o₂)) o₁ →
      D.mergeL lca (D.update (D.update l ol) o₁) (D.update (D.update l ol) o₂)
        = D.update (D.mergeL lca (D.update l ol) (D.update (D.update l ol) o₂)) o₁

  /-- Right-side base case for a single `ob` interposed, ternary. -/
  inter_right_base_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.mergeL l (D.update a o₁) (D.update b o₂)
        = D.update (D.mergeL l a (D.update b o₂)) o₁ →
      D.mergeL l (D.update a o₁) (D.update (D.update b ob) o₂)
        = D.update (D.mergeL l a (D.update (D.update b ob) o₂)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.mergeL l (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁

  /-- Left-side base case, symmetric to `inter_right_base_2op`, ternary. -/
  inter_left_base_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      D.rc ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.mergeL l (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- Inductive step for the right-side interposition, ternary. -/
  inter_right_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.mergeL l (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.mergeL l (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update (D.update b o) ob) ol) o₂)
        = D.update (D.mergeL l (D.update a ol)
                      (D.update (D.update (D.update (D.update b o) ob) ol) o₂)) o₁

  /-- Inductive step for the left-side interposition, ternary. -/
  inter_left_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      D.rc ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.mergeL l (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁ →
      D.mergeL l (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update (D.update (D.update a o) ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- LCA-side 2-op inductive step, ternary. -/
  inter_lca_2op :
    ∀ (l a b : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      (∃ o, D.rc o ol = RcRes.Fst_then_snd) →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update a ol) (D.update b ol)) o₁ →
      D.mergeL l (D.update a o₁) (D.update b o₂)
        = D.update (D.mergeL l a (D.update b o₂)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.mergeL l (D.update a ol) (D.update (D.update b ol) o₂)) o₁

  /-- 2-op right-hand inductive step, ternary. -/
  ind_right_2op :
    ∀ (l a b : D.State) (o₁ o₂ o₂' : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₂' → distinctOps o₂ o₂' →
      D.mergeL l (D.update a o₁) (D.update b o₂)
        = D.update (D.mergeL l a (D.update b o₂)) o₁ →
      D.mergeL l (D.update a o₁) (D.update (D.update b o₂') o₂)
        = D.update (D.mergeL l a (D.update (D.update b o₂') o₂)) o₁

  /-- 2-op left-hand inductive step, ternary. -/
  ind_left_2op :
    ∀ (l a b : D.State) (o₁ o₂ o₁' : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₁' → distinctOps o₂ o₁' →
      D.mergeL l (D.update a o₁) (D.update b o₂)
        = D.update (D.mergeL l a (D.update b o₂)) o₁ →
      D.mergeL l (D.update (D.update a o₁') o₁) (D.update b o₂)
        = D.update (D.mergeL l (D.update a o₁') (D.update b o₂)) o₁

  /-- Base case for the 1-op bottom-up induction, ternary. -/
  base_1op :
    ∀ (l : D.State) (o₁ : Op D.AppOp),
      D.mergeL l (D.update D.init o₁) D.init
        = D.update (D.mergeL l D.init D.init) o₁

  /-- LCA induction for the 1-op rule, ternary. -/
  ind_lca_1op :
    ∀ (lca l : D.State) (o₁ ol : Op D.AppOp),
      distinctOps o₁ ol →
      D.mergeL lca (D.update l o₁) l = D.update (D.mergeL lca l l) o₁ →
      D.mergeL lca (D.update (D.update l ol) o₁) (D.update l ol)
        = D.update (D.mergeL lca (D.update l ol) (D.update l ol)) o₁

  /-- Right-side base case for the 1-op rule, ternary. -/
  inter_right_base_1op :
    ∀ (l a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      (D.rc ob o₁ = RcRes.Fst_then_snd →
         D.mergeL l (D.update a o₁) (D.update b ob)
           = D.update (D.mergeL l a (D.update b ob)) o₁) →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update a ol) (D.update b ol)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.mergeL l (D.update a ol) (D.update (D.update b ob) ol)) o₁

  /-- Left-side base case for the 1-op rule, ternary. -/
  inter_left_base_1op :
    ∀ (l a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update a ol) (D.update b ol)) o₁ →
      D.mergeL l (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁

  /-- Right-side inductive step for the 1-op rule, ternary. -/
  inter_right_1op :
    ∀ (l a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.mergeL l (D.update a ol) (D.update (D.update b ob) ol)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b o) ob) ol)
        = D.update (D.mergeL l (D.update a ol)
                      (D.update (D.update (D.update b o) ob) ol)) o₁

  /-- Left-side inductive step for the 1-op rule, ternary. -/
  inter_left_1op :
    ∀ (l a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.mergeL l (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁ →
      D.mergeL l (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update b ol)
        = D.update (D.mergeL l (D.update (D.update (D.update a o) ob) ol)
                            (D.update b ol)) o₁

  /-- LCA-side inductive step for the 1-op rule, ternary. -/
  inter_lca_1op :
    ∀ (l a b : D.State) (o₁ ol oi : Op D.AppOp),
      distinctOps o₁ ol → distinctOps o₁ oi → distinctOps ol oi →
      (∃ o, D.rc o ol = RcRes.Fst_then_snd) →
      (∃ o, D.rc o oi = RcRes.Fst_then_snd) →
      D.mergeL l (D.update (D.update a oi) o₁) (D.update b oi)
        = D.update (D.mergeL l (D.update a oi) (D.update b oi)) o₁ →
      D.mergeL l (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update a ol) (D.update b ol)) o₁ →
      D.mergeL l (D.update (D.update (D.update a oi) ol) o₁)
              (D.update (D.update b oi) ol)
        = D.update (D.mergeL l (D.update (D.update a oi) ol)
                            (D.update (D.update b oi) ol)) o₁

  /-- 1-op left-hand inductive step, ternary. -/
  ind_left_1op :
    ∀ (l a b : D.State) (o₁ o₁' ol : Op D.AppOp),
      distinctOps o₁ o₁' → distinctOps o₁ ol → distinctOps o₁' ol →
      D.mergeL l (D.update a o₁) (D.update b ol)
        = D.update (D.mergeL l a (D.update b ol)) o₁ →
      D.mergeL l (D.update (D.update a o₁') o₁) (D.update b ol)
        = D.update (D.mergeL l (D.update a o₁') (D.update b ol)) o₁

  /-- 1-op right-hand inductive step, ternary. -/
  ind_right_1op :
    ∀ (l a b : D.State) (o₂ o₂' ol : Op D.AppOp),
      distinctOps o₂ o₂' → distinctOps o₂ ol → distinctOps o₂' ol →
      D.mergeL l (D.update a ol) (D.update b o₂)
        = D.update (D.mergeL l (D.update a ol) b) o₂ →
      D.mergeL l (D.update a ol) (D.update (D.update b o₂') o₂)
        = D.update (D.mergeL l (D.update a ol) (D.update b o₂')) o₂

  /-- Zero-op closure (BottomUp-0-OP), ternary: a shared LCA event peels out. -/
  lem_0op :
    ∀ (l a b : D.State) (ol : Op D.AppOp),
      D.mergeL l (D.update a ol) (D.update b ol)
        = D.update (D.mergeL l a b) ol

  /-- cond-comm lift (verbatim). -/
  cond_comm_lift :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.rc e e' = RcRes.Fst_then_snd →
      ¬ D.commutes e' e'' →
      D.update (applySeq D.toCRDTSig (D.update (D.update s e') e) π) e''
        = D.update (applySeq D.toCRDTSig (D.update (D.update s e) e') π) e''

  /-- Merge-init identity, ternary (uniform transform of `merge init s = s`). -/
  merge_init_T : ∀ l s : D.State, D.mergeL l D.init s = s

  /-- Merge-peel commutativity, ternary. -/
  merge_peel_comm :
    ∀ (l a : D.State) (e : Op D.AppOp) (π : List (Op D.AppOp)),
      (∀ x ∈ π, D.commutes e x) →
      D.mergeL l (D.update a e) (applySeq D.toCRDTSig D.init π)
        = D.update (D.mergeL l a (applySeq D.toCRDTSig D.init π)) e

  /-- Shared-element 1-op peel, ternary. -/
  shared_peel_1op :
    ∀ (o₁ ol : Op D.AppOp), distinctOps o₁ ol →
      ∀ (l a b : D.State),
        D.mergeL l (D.update (D.update a ol) o₁) (D.update b ol)
          = D.update (D.mergeL l (D.update a ol) (D.update b ol)) o₁

/-! ## THE reuse contract: ternary VCs at the `l := init` slice give the binary VCs

`satisfiesVCs_of_T` is the S4 exit criterion. Every merge field of `SatisfiesVCsT D`, taken
at the LCA slice `l := D.init` and rewritten through `merge_init_slice`, is definitionally
the corresponding field of `Sal.Emulation.SatisfiesVCs D.toCRDTSig`; the `do_`/`rc`-only
fields transfer verbatim. -/

/-- **The reuse linchpin.** Instantiate every ternary merge field at `l := init`, rewrite
through `merge_init_slice`, and recover the binary 29-field `SatisfiesVCs` bundle, so the
existing binary bridge (`Merge_Linearization.lean`) runs unchanged on the init-LCA
sub-family. -/
theorem satisfiesVCs_of_T {D : MRDTSig} (hT : SatisfiesVCsT D) :
    SatisfiesVCs D.toCRDTSig where
  rc_non_comm := hT.rc_non_comm
  rc_non_comm_directional := hT.rc_non_comm_directional
  no_rc_chain := hT.no_rc_chain
  cond_comm_base := hT.cond_comm_base
  cond_comm_lift := hT.cond_comm_lift
  merge_comm := by simpa only [D.merge_init_slice] using hT.merge_comm_T D.init
  merge_idem := by simpa only [D.merge_init_slice] using hT.merge_idem_T D.init
  base_2op := by simpa only [D.merge_init_slice] using hT.base_2op D.init
  ind_lca_2op := by simpa only [D.merge_init_slice] using hT.ind_lca_2op D.init
  inter_right_base_2op := by
    simpa only [D.merge_init_slice] using hT.inter_right_base_2op D.init
  inter_left_base_2op := by
    simpa only [D.merge_init_slice] using hT.inter_left_base_2op D.init
  inter_right_2op := by simpa only [D.merge_init_slice] using hT.inter_right_2op D.init
  inter_left_2op := by simpa only [D.merge_init_slice] using hT.inter_left_2op D.init
  inter_lca_2op := by simpa only [D.merge_init_slice] using hT.inter_lca_2op D.init
  ind_right_2op := by simpa only [D.merge_init_slice] using hT.ind_right_2op D.init
  ind_left_2op := by simpa only [D.merge_init_slice] using hT.ind_left_2op D.init
  base_1op := by simpa only [D.merge_init_slice] using hT.base_1op D.init
  ind_lca_1op := by simpa only [D.merge_init_slice] using hT.ind_lca_1op D.init
  inter_right_base_1op := by
    simpa only [D.merge_init_slice] using hT.inter_right_base_1op D.init
  inter_left_base_1op := by
    simpa only [D.merge_init_slice] using hT.inter_left_base_1op D.init
  inter_right_1op := by simpa only [D.merge_init_slice] using hT.inter_right_1op D.init
  inter_left_1op := by simpa only [D.merge_init_slice] using hT.inter_left_1op D.init
  inter_lca_1op := by simpa only [D.merge_init_slice] using hT.inter_lca_1op D.init
  ind_left_1op := by simpa only [D.merge_init_slice] using hT.ind_left_1op D.init
  ind_right_1op := by simpa only [D.merge_init_slice] using hT.ind_right_1op D.init
  lem_0op := by simpa only [D.merge_init_slice] using hT.lem_0op D.init
  merge_init := by simpa only [D.merge_init_slice] using hT.merge_init_T D.init
  merge_peel_comm := by simpa only [D.merge_init_slice] using hT.merge_peel_comm D.init
  shared_peel_1op := by
    intro o₁ ol h a b
    simpa only [D.merge_init_slice] using hT.shared_peel_1op o₁ ol h D.init a b

/-! ## §4 S4 exit — the Grow-Only Set discharges the ternary bundle

The S1 `GSet` (`Sal/MRDTs/Metatheory/MRDTSig.lean`) has `mergeL l a b = a ∪ b` (independent of the
LCA `l`), `update s o = insert o.2.2 s`, `init = ∅`, and `rc _ _ = Either`. Every merge/peel
field is then an unconditional set identity of the `insert`/`∪` algebra; the `rc`-gated side
conditions are vacuous (their `rc = Fst_then_snd` premises are `Either = Fst_then_snd`). -/

section GSet

/-- G-Set commutation: `insert` commutes, so every op-pair commutes. -/
private theorem gset_commutes (o₁ o₂ : Op GSet.AppOp) : GSet.toCRDTSig.commutes o₁ o₂ := by
  intro s
  simp only [GSet]
  apply Set.ext; intro x; simp only [Set.mem_insert_iff]; tauto

/-- The 24 merge/peel VCs of G-Set are all the same unconditional `insert`/`∪` identity;
this closes any of them after unfolding `GSet` and discarding hypotheses. -/
macro "gset_merge_vc" : tactic =>
  `(tactic| (intros; simp only [GSet]; apply Set.ext; intro x;
             simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_empty_iff_false]; tauto))

/-- The `rc`-gated side conditions are vacuous: a `rc = Fst_then_snd` premise is
`RcRes.Either = RcRes.Fst_then_snd`. -/
macro "gset_vacuous" h:ident : tactic =>
  `(tactic| (simp only [GSet] at $h:ident; exact absurd $h (by decide)))

/-- **G-Set discharges the ternary bundle.** Witnesses that `SatisfiesVCsT` is inhabited on
the simplest flat RDT, through the S1 `GSet` `MRDTSig`. -/
theorem GSet_satisfiesVCsT : SatisfiesVCsT GSet where
  rc_non_comm := by
    intro o₁ o₂ _ _
    exact ⟨fun _ => gset_commutes o₁ o₂, fun _ => rfl⟩
  rc_non_comm_directional := by
    intro o₁ o₂ _
    refine ⟨fun hnc => absurd (gset_commutes o₁ o₂) hnc, ?_⟩
    rintro (h | h) <;> gset_vacuous h
  no_rc_chain := by
    intro o₁ o₂ o₃ _ _ hpair
    obtain ⟨h, _⟩ := hpair; gset_vacuous h
  cond_comm_base := by
    intro s o₁ o₂ o₃ _ _ _ h _; gset_vacuous h
  cond_comm_lift := by
    intro s e e' e'' π _ _ _ h _; gset_vacuous h
  merge_comm_T := by gset_merge_vc
  merge_idem_T := by gset_merge_vc
  merge_init_T := by gset_merge_vc
  base_2op := by gset_merge_vc
  ind_lca_2op := by gset_merge_vc
  inter_right_base_2op := by gset_merge_vc
  inter_left_base_2op := by gset_merge_vc
  inter_right_2op := by gset_merge_vc
  inter_left_2op := by gset_merge_vc
  inter_lca_2op := by gset_merge_vc
  ind_right_2op := by gset_merge_vc
  ind_left_2op := by gset_merge_vc
  base_1op := by gset_merge_vc
  ind_lca_1op := by gset_merge_vc
  inter_right_base_1op := by gset_merge_vc
  inter_left_base_1op := by gset_merge_vc
  inter_right_1op := by gset_merge_vc
  inter_left_1op := by gset_merge_vc
  inter_lca_1op := by gset_merge_vc
  ind_left_1op := by gset_merge_vc
  ind_right_1op := by gset_merge_vc
  lem_0op := by gset_merge_vc
  merge_peel_comm := by gset_merge_vc
  shared_peel_1op := by gset_merge_vc

end GSet

end Sal.Metatheory
