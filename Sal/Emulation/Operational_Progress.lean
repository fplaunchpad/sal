import Sal.Emulation.Transfer

/-!
# Operational progress for conditioned transition systems

`VerifiedMRDT` is intentionally a safety certificate: it proves
RA-linearizability for honest reachable configurations.  Its `Step3V`
semantics is relational and places the invariant-bearing post-configuration
in each constructor, so safety alone does not construct enabled successors.

Emulation additionally needs progress.  This module packages that independent
obligation without strengthening every verified datatype.  Enablement remains
datatype-specific (fresh-message disciplines, delivery policy, and so on),
while the certificate guarantees an actual widened conditioned step whenever
the declared enablement predicate holds.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

/-- Constructive availability of the administrative and client transitions
used by an emulation proof. Query progress needs no field: `Step3.query` uses
the source configuration itself as its target once a replica state is known. -/
structure ConditionedOperationalProgress (D : ConditionedMRDTSig)
    (Honest : Sal.ConditionedMRDTs.Configuration D → Prop)
    (hInit : D.Inv D.init) where
  /-- The precise generation-side condition under which an operation may be
  issued. For the Shapiro endpoint this includes fresh-message preparation. -/
  CanApply : Sal.ConditionedMRDTs.Configuration D → Replica → D.AppOp → Prop
  /-- The precise delivery/synchronization condition for merging `source`
  into `target`. -/
  CanMerge : Sal.ConditionedMRDTs.Configuration D → Replica → Replica → Prop
  initHonest : Honest (Sal.ConditionedMRDTs.initConfig D hInit)
  createReplica : ∀ {C r}, Honest C → C.N r = none →
    ∃ C', Step3V D C (.createReplica r) C'
  apply : ∀ {C r op}, Honest C → CanApply C r op →
    ∃ t C', Step3V D C (.apply t r op) C'
  merge : ∀ {C target source}, Honest C → CanMerge C target source →
    ∃ C', Step3V D C (.merge target source) C'

namespace ConditionedOperationalProgress

variable {D : ConditionedMRDTSig}
  {Honest : Sal.ConditionedMRDTs.Configuration D → Prop}
  {hInit : D.Inv D.init}

/-- Queries are operationally available at every initialized replica and do
not require an extra progress axiom. -/
theorem query {C : Sal.ConditionedMRDTs.Configuration D} {r : Replica}
    {q : D.Query} {s : D.State} (hs : C.N r = some s) :
    Step3V D C (.query r q (D.query s q)) C := by
  exact .base (.query hs rfl)

end ConditionedOperationalProgress

/-- The complete input needed by the concrete emulation construction: Sal's
safety certificate plus a separate operational-progress certificate over the
same honesty discipline. -/
structure OperationalTransferInput (D : OpCRDTSig)
    (hb : D.Msg → D.Msg → Prop) extends ConditionedTransferInput D hb where
  progress : ConditionedOperationalProgress
    (shapiroConditionedG D schedule)
    (fun C => verified.Honest (Sal.ConditionedMRDTs.Configuration.core C))
    verified.initInv

namespace OperationalTransferInput

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

def semantic (I : OperationalTransferInput D hb) :
    ConditionedTransferInput D hb := I.toConditionedTransferInput

end OperationalTransferInput

end Sal.Emulation
