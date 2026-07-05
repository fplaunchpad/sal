import Sal.MRDTs.Metatheory.Development.GenericEqQuotient
import Sal.MRDTs.Metatheory.Development.RGA_EqQuotient
import Sal.MRDTs.Metatheory.Development.G2_Transport_Probe

/-!
# Packaging the RGA's *easy* conditioned VCs for `RA_linearizable_up_to_eq`

The generic `≈`-quotient metatheorem `GenericEqQuotient.RA_linearizable_up_to_eq`
consumes five VCs over a `ConditionedMRDTSig D`:

* `EqEquiv D`      — the observational `≈` with its equivalence proof;
* `InvPres D`      — `Inv` at `init`, preserved (UNCONDITIONALLY) by `update`/`mergeL`;
* `CongVC D E`     — `update`/`mergeL`/`query` respect `≈` on `Inv`-states;
* `InvInvVC D E`   — `applicable` is `≈`-invariant on `Inv`-states;
* `EqJoinLemma3C`  — the `≈`-Join.

This file supplies the RGA's instances of the EASY ones — everything except the
`mergeL` merge-congruence field of `CongVC` and the `≈`-Join, which are separate
workstreams. The datatype is `G2Probe.RGACondSig`
(`State = concrete_st`, `update = do_`, `mergeL = merge`, `≈ = eq`,
`Inv = RgaInv = (contains · 0 = false) ∧ wf`,
`applicable = accurate ∧ fresh_ts`, `Query = Unit`).

Delivered here, all by assembly of existing lemmas:

* `rgaEqEquiv : EqEquiv RGACondSig`               — `⟨eq, eq_equiv⟩`.
* `rgaInvInvVC : InvInvVC RGACondSig rgaEqEquiv`   — `applicable_congr` from the
  `≈`-invariance of `accurate`/`fresh_ts`.
* `rga_update_congr`                              — `CongVC.update_congr` (do_eq_congr).
* `rga_query_congr`                               — `CongVC.query_congr` (Query = Unit).

**`rgaInvPres` is NOT delivered — it cannot be, as a structural gap** (see §5).
The generic `InvPres` demands *unconditional* preservation of `Inv` by both
`update` and `mergeL`; the RGA satisfies neither on `RGACondSig`'s `Inv`. What
DOES hold (the conditioned forms) is recorded as `rga_inv_init`,
`rga_inv_update_of_applicable`, `rga_inv_mergeL_of_idmono` to pin the exact gap.
-/

namespace Sal.Metatheory.RGAVCPackage

open Sal.Emulation
open Sal.Metatheory
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAConditionedConvergence
open Sal.Metatheory.RGAEqQuotient
open Sal.Metatheory.G2Probe

/-! ## §1. `EqEquiv` — the observational relation `≈` = `eq`. -/

/-- **`EqEquiv RGACondSig`** — the RGA's observational `eq` with its equivalence
proof `eq_equiv` (from `RGA_EqQuotient`). -/
def rgaEqEquiv : EqEquiv RGACondSig where
  eqv := eq
  equiv := eq_equiv

/-! ## §2. The two easy `CongVC` fields (the third — `mergeL_congr` — is a
separate agent; here only the unconditional `update`/`query` congruences). -/

/-- **`CongVC.update_congr` for the RGA** — `do_` respects `≈`, unconditionally
(`do_eq_congr`). The `Inv` hypotheses are unused. -/
theorem rga_update_congr (o : Op RGACondSig.AppOp) {s s' : RGACondSig.State}
    (_hs : RGACondSig.Inv s) (_hs' : RGACondSig.Inv s')
    (h : rgaEqEquiv.eqv s s') :
    rgaEqEquiv.eqv (RGACondSig.update s o) (RGACondSig.update s' o) :=
  do_eq_congr s s' h o

/-- **`CongVC.query_congr` for the RGA** — the read is vacuous: `Query = Value =
Unit`, `query _ _ = ()`, so `≈`-invariance of the read is `rfl`. -/
theorem rga_query_congr (q : RGACondSig.Query) {s s' : RGACondSig.State}
    (_hs : RGACondSig.Inv s) (_hs' : RGACondSig.Inv s')
    (_h : rgaEqEquiv.eqv s s') :
    RGACondSig.query s q = RGACondSig.query s' q :=
  rfl

/-! ## §3. `InvInvVC` — `applicable` is `≈`-invariant on `Inv`-states. -/

/-- **`InvInvVC RGACondSig rgaEqEquiv`** — `applicable = accurate ∧ fresh_ts` is
`≈`-invariant. From `accurate_eq_iff` and `fresh_ts_eq_iff` (`RGA_EqQuotient`
§3); the `Inv` hypotheses are unused. -/
def rgaInvInvVC : InvInvVC RGACondSig rgaEqEquiv where
  applicable_congr := by
    intro o s s' _hs _hs' h
    exact and_congr (accurate_eq_iff o h) (fresh_ts_eq_iff o h)

/-! ## §4. `InvPres` — the STRUCTURAL GAP.

The generic `InvPres RGACondSig` would require, verbatim:

* `inv_update  : ∀ s o, Inv s → Inv (update s o)`   — UNCONDITIONAL in `o`;
* `inv_mergeL  : ∀ l a b, Inv l → Inv a → Inv b → Inv (mergeL l a b)`.

Neither holds for `RGACondSig` (`Inv = RgaInv = (contains · 0 = false) ∧ wf`):

* **`inv_update` is FALSE.** `RGACondSig.update = do_` has NO generation guard:
  `do_ s (0, r, .Ins e pre a) = upd s 0 …`, which sets `contains · 0 = true` and
  breaks root-freeness. More generally `Inv_doIns` needs `accurate ∧ fresh_ts` and
  `Inv_doDel` needs `accurate` — exactly `RGACondSig.applicable`. So the RGA's
  `Inv` is preserved by `update` only on `applicable` ops, never unconditionally.

* **`inv_mergeL` is FALSE.** `Inv_merge` requires the EXTRA premise `id_mono l`,
  and `merge_breaks_wf` (`RGA_Reachability_Invariant`) is a machine-checked
  refutation that `wf` (hence `RgaInv`) is NOT preserved by `merge` from
  `RgaInv l/a/b` alone. Since `RgaInv` does not carry `id_mono`, that premise is
  unavailable at this signature. (Note the design mismatch: the intended
  `≈`-quotient invariant `RGA_EqQuotient.qInv = wf ∧ root-free ∧ id_mono` is
  STRICTLY stronger — it carries `id_mono` — and would discharge `inv_mergeL`;
  but even `qInv` does not rescue `inv_update`, which still needs `applicable`.)

Conclusion: `rgaInvPres : InvPres RGACondSig` cannot be constructed. Hosting the
RGA needs either (a) an `applicable`-conditioned `InvPres` in the generic layer,
and (b) `RGACondSig.Inv` strengthened to include `id_mono` (i.e. use `qInv`).
The conditioned forms that DO hold are recorded below as the honest artifacts. -/

/-- `Inv` holds at `init` (the only `InvPres` field that survives; `= Inv_init`). -/
theorem rga_inv_init : RGACondSig.Inv RGACondSig.init := Inv_init

/-- The `applicable`-CONDITIONED `inv_update`: `do_` preserves `Inv` on
`applicable` ops (`Inv_doIns`/`Inv_doDel`). This is what the RGA supplies in
place of the generic unconditional `inv_update`. -/
theorem rga_inv_update_of_applicable (s : RGACondSig.State) (o : Op RGACondSig.AppOp)
    (hs : RGACondSig.Inv s) (happ : RGACondSig.applicable o s) :
    RGACondSig.Inv (RGACondSig.update s o) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a => exact Inv_doIns s t r e a pre hs happ.1 happ.2
  | Del pre x => exact Inv_doDel s t r x pre hs happ.1

/-- The `id_mono`-CONDITIONED `inv_mergeL`: `merge` preserves `Inv` under the
extra `id_mono l` premise (`Inv_merge`). This is what the RGA supplies in place
of the generic unconditional `inv_mergeL`. -/
theorem rga_inv_mergeL_of_idmono (l a b : RGACondSig.State)
    (hl : RGACondSig.Inv l) (ha : RGACondSig.Inv a) (hb : RGACondSig.Inv b)
    (ml : id_mono l) :
    RGACondSig.Inv (RGACondSig.mergeL l a b) :=
  Inv_merge l a b hl ha hb ml

/-! ## §5. Axiom audit of the delivered VCs. -/

#print axioms rgaEqEquiv
#print axioms rgaInvInvVC
#print axioms rga_update_congr
#print axioms rga_query_congr
#print axioms rga_inv_init
#print axioms rga_inv_update_of_applicable
#print axioms rga_inv_mergeL_of_idmono

end Sal.Metatheory.RGAVCPackage
