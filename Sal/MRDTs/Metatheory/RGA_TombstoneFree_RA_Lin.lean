import Sal.MRDTs.Metatheory.Development.RGA_Honest_Residual

/-!
# RGA (tombstone-free) — RA-linearizability up to observational equivalence

**The mainline entry point** for the conditioned-metatheory result: the tombstone-free,
path-carrying RGA (`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`) is per-version
RA-linearizable **up to observational equivalence `≈`** at every reachable configuration of the
ternary execution model, assuming only honest delivery.

This RDT cannot go through the standard 24-VC schema: its commutation VC holds only
*conditioned* on reachable/accurate states (tombstone-freedom forces rehoming, and rehoming is
only correct against states that reflect the op's causal past — see
`RGA_Tombstone_Free/doc/why-the-path-matters.pdf` and the prefix-free impossibility).  The
result here is instead a DIRECT end-to-end theorem through the applicability-conditioned
metatheory:

* **Target** (`IsRALinearizable3Eq`, `Development/GoodConfig3H.lean`): every version of every
  reachable configuration is the class of a representative that is the raw `do_`-fold of a
  `lo`-respecting linearization of its events, up to `≈`.
* **Assumption** (`HonestDelivery`, `Development/RGA_Honest_Residual.lean`) — per apply step:
  1. *born accuracy* — the delivered op was generated accurately against a causal fold of the
     events its replica had seen (how an RGA client actually works: it reads its replica's
     state).  This is the generation discipline forced by tombstone-freedom, and it is the
     ONLY irreducible assumption;
  2. *born-applicable delivery* — the op is applicable at its head class (`qapplicable`), and
     `applicable ⟹ WfOpA` for it.
  Lamport clocks, timestamp uniqueness and visibility-support are structural fields of
  `Configuration` (dishonest-clock executions are unrepresentable); nonzero ids and nonzero
  delete targets are derived from the delivered op's own wellformedness.

**Proof architecture** (all kernel-clean, 0 `sorry`, axioms ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}; the chain lives under [`Development/`](Development), culminating in):

* `Development/GenericEqQuotient*.lean`, `GoodConfig3H.lean` — the `D ↦ D≈` quotient functor,
  the H-disciplined canonical-witness layer, the raw-`≈` reachability induction;
* `Development/RGA_CanonConvergence.lean`, `RGA_CanonFoldOK.lean` — the RGA's canonical-state
  engine (`CanonInv`/`CanonMatch`/`canon_fold`) and the per-event generation discipline
  (`GenDisc2C`, discharged from born accuracy);
* `Development/RGA_Skeleton3.lean` + the discharge files (`RGA_HEnum_Discharge`,
  `RGA_HcausHdec_Discharge`, `RGA_Hbridge_Discharge`, `RGA_HHext_Discharge`) — the capstone
  skeleton and the discharged leaves (delta enumeration, merge-canonicity bundle, discipline
  extension);
* `Development/RGA_Final_Assembly.lean` — `rga_RA_linearizable_final` (explicit residual form:
  take `hHon`/`hBA` as premises instead of `HonestDelivery`, e.g. to substitute a different
  execution model);
* `Development/RGA_Honest_Residual.lean` — the residual reduced to `HonestDelivery`.
-/

namespace Sal.Metatheory

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3H
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.Metatheory.RGASkeleton3 (HonestDelivery)

/-- **The tombstone-free RGA is RA-linearizable up to `≈`** at every reachable configuration of
the ternary execution model, under honest delivery (`HonestDelivery`: born accuracy +
born-applicable delivery — see the module docstring). -/
theorem rga_tombstone_free_ra_linearizable3_eq
    (hHD : HonestDelivery)
    (C : Configuration (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
      (initConfig (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA C :=
  RGASkeleton3.rga_RA_linearizable_honest hHD C hReach

/-! ## Axiom audit -/

#print axioms rga_tombstone_free_ra_linearizable3_eq

end Sal.Metatheory
