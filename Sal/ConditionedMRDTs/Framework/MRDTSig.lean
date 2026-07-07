import Sal.CRDTs.Metatheory.RA_Linearizability

/-!
# Ternary MRDT signature and conditioned linearization (Phase-0, step **S1**)

This is the foundation step of the Neem soundness meta-theory (Phase-0, TTL+RV
design; see `Sal/MRDTs/Metatheory/PHASE0_PLAN.md` §1.1–§1.2 and §4 S1). It lays down the
*Thin-Ternary-Layer* over the existing binary `Sal.Emulation.CRDTSig`:

* `MRDTSig extends CRDTSig` — adds the ternary merge `mergeL l a b`
  (paper `merge(σ_⊤, σ₁, σ₂)`) and pins the inherited binary `merge` to be exactly
  its `l := init` slice via `merge_init_slice`. Because `MRDTSig` *extends* `CRDTSig`,
  `D.toCRDTSig` is a *literal* `CRDTSig` and the entire binary machinery
  (`Configuration`, `lo`, `SatisfiesVCs`, the proved bridge cases) applies verbatim to
  the `l := init` slice.
* `ConditionedMRDTSig extends MRDTSig` — adds the state-shape `Inv` and the
  generation-time `applicable` guard (Design-3 conditioning split).
* `commutesOn` — commutation required only on `Inv`/`applicable` reachable states.
* the ternary `lo` — the linearization order with `commutes → commutesOn` at the two
  ⇄-sites, otherwise identical in shape to `Sal.Emulation.lo`.

**Exit criteria (PHASE0_PLAN §4 S1), all discharged in this file:**
1. compiles clean, no `sorry`;
2. `commutesOn` / `lo` collapse to their binary counterparts (`CRDTSig.commutes` /
   `Sal.Emulation.lo`) whenever `Inv`/`applicable` are trivially true — see
   `commutesOn_iff_commutes`, `commutesOn_eq_commutes`, `lo_iff_binary`, `lo_eq_binary`;
3. a `Grow_Only_Set` (G-Set) `MRDTSig` instance (`GSet`) supplies `mergeL` and makes
   `merge_init_slice` hold **definitionally**.

Downstream (S2 Configuration + ranked store, S6 merge induction) build on the `def`/
`structure` seams here; see the NOTE comments below for the exact hand-off points.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-! ## §1.1 — The ternary signature -/

/-- **Ternary MRDT signature.** Inherits `init`/`AppOp`/`update`/`query`/`merge`/`rc`
UNCHANGED from `CRDTSig`; adds the ternary `mergeL l a b` (paper `merge(σ_⊤,σ₁,σ₂)`)
and pins the inherited binary `merge` field to be exactly its `l := init` slice.

`merge_init_slice` is *the reuse contract*: it makes `D.toCRDTSig` a literal `CRDTSig`
whose `merge` is the `l := init` restriction of `mergeL`, so the binary emulation corpus
runs on the init-LCA sub-family without change. -/
structure MRDTSig extends CRDTSig where
  /-- Ternary merge with an explicit LCA state `l`: paper `merge(l, a, b)`. -/
  mergeL : State → State → State → State
  /-- The reuse contract: the inherited binary `merge` is the `l := init` slice of
  `mergeL`. -/
  merge_init_slice : ∀ a b, mergeL init a b = merge a b

/-- **Conditioned ternary signature.** Adds the Design-3 conditioning split:

* `Inv` — a state-SHAPE reachability over-approximation (e.g. RGA's `RgaInv`), inductive
  under `update`;
* `applicable` — a GENERATION-TIME guard on an event at a state; it MAY read the op
  timestamp, and is *not* a shape predicate (e.g. RGA's `accurate ∧ fresh_ts`).

Flat RDTs take both trivially true, collapsing everything to the binary framework
(see the collapse lemmas below). -/
structure ConditionedMRDTSig extends MRDTSig where
  /-- State-shape reachability over-approximation. -/
  Inv : State → Prop
  /-- Generation-time applicability guard on an event at a state. -/
  applicable : Op AppOp → State → Prop

/-- **Conditioned commutation** (PHASE0_PLAN §1.1; `BLUEPRINT.md:437`). Commutation of
`o₁, o₂` is required ONLY at states that are `Inv`-reachable and at which both events are
`applicable`. This is the conditioned replacement for `CRDTSig.commutes` at every ⚑ site
of the proof skeleton. -/
def ConditionedMRDTSig.commutesOn (D : ConditionedMRDTSig) (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.Inv s → D.applicable o₁ s → D.applicable o₂ s →
    D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁

/-! ## §1.2 — The linearization order over `commutesOn`

Identical in shape to `Sal.Emulation.lo` (`RA_Linearizability.lean:88`), with
`commutes → commutesOn` at the two ⇄-sites (spec ⚑1). Paper-faithful because `lo C` is
only ever read at events of a *reachable* `C`.

NOTE for S2: `lo` reads only `C.vis` off the configuration. It is stated here over the
*binary* `Configuration D.toCRDTSig` (whose replica-keyed core is, per PHASE0_PLAN §1.3,
retained VERBATIM in the ternary configuration). When S2 introduces the ranked-version
store, either make the ternary `Configuration` carry / extend this binary core, or restate
`lo` over the new structure reading its `.vis`; `lo_eq_binary` shows the two coincide on
the flat slice. -/
def lo (D : ConditionedMRDTSig) (C : Configuration D.toCRDTSig) (e₁ e₂ : Op D.AppOp) :
    Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutesOn e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, C.vis e₂ e₃ ∧ ¬ D.commutesOn e₂ e₃ )

/-! ## Collapse lemmas: `commutesOn`/`lo` reduce to the binary counterparts

The exit criterion asks that, under `Inv := fun _ => True` / `applicable := fun _ _ => True`,
`commutesOn` and `lo` reduce to `CRDTSig.commutes` and `Sal.Emulation.lo`.

DEVIATION (minor, expected): the reduction is a propositional `Iff`/`Eq` closed by `simp`,
*not* strict `rfl`. `commutesOn` carries three guard arrows `Inv s → applicable o₁ s →
applicable o₂ s → …`; even when each guard is `True`, `True → P` is not definitionally `P`
in Lean, so the guards must be *discharged* rather than *erased*. The hypothesis form below
(`∀ s, D.Inv s` and `∀ o s, D.applicable o s`) is strictly more general than the literal
`= fun _ => True`, and is what the `ReachInv`-backed discharge at each ⚑ site will supply. -/

/-- `commutesOn` collapses to the binary `CRDTSig.commutes` (pointwise) when `Inv` and
`applicable` hold everywhere. -/
theorem commutesOn_iff_commutes (D : ConditionedMRDTSig)
    (hInv : ∀ s, D.Inv s) (hApp : ∀ (o : Op D.AppOp) (s), D.applicable o s)
    (o₁ o₂ : Op D.AppOp) :
    D.commutesOn o₁ o₂ ↔ D.toCRDTSig.commutes o₁ o₂ := by
  unfold ConditionedMRDTSig.commutesOn CRDTSig.commutes
  exact ⟨fun h s => h s (hInv s) (hApp o₁ s) (hApp o₂ s), fun h s _ _ _ => h s⟩

/-- Function-level form of the `commutesOn` collapse, convenient for rewriting. -/
theorem commutesOn_eq_commutes (D : ConditionedMRDTSig)
    (hInv : ∀ s, D.Inv s) (hApp : ∀ (o : Op D.AppOp) (s), D.applicable o s) :
    D.commutesOn = D.toCRDTSig.commutes := by
  funext o₁ o₂
  exact propext (commutesOn_iff_commutes D hInv hApp o₁ o₂)

/-- The ternary `lo` collapses to the binary `Sal.Emulation.lo` (pointwise) when `Inv`
and `applicable` hold everywhere. -/
theorem lo_iff_binary (D : ConditionedMRDTSig)
    (hInv : ∀ s, D.Inv s) (hApp : ∀ (o : Op D.AppOp) (s), D.applicable o s)
    (C : Configuration D.toCRDTSig) (e₁ e₂ : Op D.AppOp) :
    lo D C e₁ e₂ ↔ Sal.Emulation.lo C e₁ e₂ := by
  unfold Sal.ConditionedMRDTs.lo Sal.Emulation.lo
  simp only [commutesOn_iff_commutes D hInv hApp]

/-- Function-level form of the `lo` collapse: the ternary and binary orders are literally
the same relation on the flat slice. -/
theorem lo_eq_binary (D : ConditionedMRDTSig)
    (hInv : ∀ s, D.Inv s) (hApp : ∀ (o : Op D.AppOp) (s), D.applicable o s)
    (C : Configuration D.toCRDTSig) :
    lo D C = Sal.Emulation.lo C := by
  funext e₁ e₂
  exact propext (lo_iff_binary D hInv hApp C e₁ e₂)

/-! ## §4 S1 exit — the Grow-Only Set (G-Set) instance

The simplest flat RDT: state is `Set ℕ`, `update` adds the op's element, and both binary
`merge` and ternary `mergeL` are set union — so `mergeL` *ignores* the LCA state `l`
(join-semilattice: the LCA is irrelevant for a G-Set) and `merge_init_slice` holds by
`rfl`. This witnesses that `MRDTSig` is inhabited and that the reuse contract is
definitional for a flat RDT. -/

/-- G-Set as an `MRDTSig`. `mergeL l a b := a ∪ b` drops `l`; `merge_init_slice` is `rfl`.
`noncomputable` only because `Set ℕ` equality is supplied classically. -/
noncomputable def GSet : MRDTSig where
  State     := Set Nat
  dec_state := fun a b => Classical.propDecidable (a = b)
  init      := (∅ : Set Nat)
  AppOp     := Nat
  dec_op    := inferInstance
  Query     := Unit
  Value     := Set Nat
  update    := fun s o => insert o.2.2 s
  merge     := fun a b => a ∪ b
  query     := fun s _ => s
  rc        := fun _ _ => RcRes.Either
  mergeL    := fun _l a b => a ∪ b
  merge_init_slice := fun _ _ => rfl

/-- G-Set conditioned trivially: `Inv`/`applicable := True`. This is the flat-RDT
instance on which the collapse lemmas fire, collapsing the ternary layer to the proved
binary framework. -/
noncomputable def GSetCond : ConditionedMRDTSig where
  toMRDTSig  := GSet
  Inv        := fun _ => True
  applicable := fun _ _ => True

/-- Sanity: on the trivially-conditioned G-Set, `commutesOn` *is* the binary `commutes`. -/
theorem GSet_commutesOn_eq (o₁ o₂ : Op GSetCond.AppOp) :
    GSetCond.commutesOn o₁ o₂ ↔ GSetCond.toCRDTSig.commutes o₁ o₂ :=
  commutesOn_iff_commutes GSetCond (fun _ => trivial) (fun _ _ => trivial) o₁ o₂

/-- Sanity: on the trivially-conditioned G-Set, the ternary `lo` *is* the binary `lo`. -/
theorem GSet_lo_eq (C : Configuration GSetCond.toCRDTSig) (e₁ e₂ : Op GSetCond.AppOp) :
    lo GSetCond C e₁ e₂ ↔ Sal.Emulation.lo C e₁ e₂ :=
  lo_iff_binary GSetCond (fun _ => trivial) (fun _ _ => trivial) C e₁ e₂

end Sal.ConditionedMRDTs
