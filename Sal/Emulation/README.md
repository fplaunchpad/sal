# Operation-to-conditioned-state emulation

This directory formalizes the connection between operation-based CRDTs and
Sal's corrected conditioned MRDT framework.

The architecture is:

```text
OpCRDTSig
  └─ Shapiro (s_m, M, D) emulator
       └─ ConditionedMRDTSig
            └─ VerifiedMRDT
                 └─ Liittschwager weak-trace transfer
```

The construction follows Shapiro et al. (2011). The emulating state contains
the materialized op-based state `s_m`, finite known-message set `M`, and
delivered-message set `D`. Merge learns `M ∪ M'` and causally drains
`(M ∪ M') \ D`. It is intentionally not replaced with the message-set-only
variant: the original directional drain is represented explicitly.

Liittschwager et al. (arXiv:2504.05398) supplies the formal target: weak
simulation, weak-trace transport, and representation independence. The
generic results and a two-direction GSet canary are complete. The remaining
datatype-generic proof is the forward simulation from `opLabeledTS` to the
actual Shapiro emulator system; safety transfer needs only that direction.

## Files

- `Op_Based_TS.lean`: op-based configurations, preparation/effect, broadcast,
  causally enabled delivery, and silent delivery transitions.
- `Disciplined_Op_TS.lean`: well-formed source semantics restricting update
  generation by the freshness and causal obligations required by Shapiro's
  `PrepareEnabled`; query and causal-delivery rules are unchanged.
- `Emulation.lean`: `EmulatorState`, causal schedules, preparation, internal
  delivery, draining, Shapiro merge, and representation-invariant proofs.
- `Conditioned_Emulation.lean`: embeds the emulator into
  `ConditionedMRDTSig`; `Inv` is `D ⊆ M` plus causal down-closure, and
  `applicable` is the generation-side causal/freshness obligation.
- `Conditioned_Trace_TS.lean`: client-observation view of the authoritative
  conditioned ternary `Step3` semantics, including the honesty-restricted
  target systems, widened virtual-LCA production target, and the
  op-to-conditioned label morphisms.
- `Operational_Progress.lean`: optional constructive progress certificate,
  separate from `VerifiedMRDT` safety, with datatype-specific apply/merge
  enablement.
- `Operational_Observed.lean`: turns certified apply, merge, and query
  progress into weak steps of the conditioned client-observation LTS.
- `Conditioned_Network_TS.lean`: Liittschwager-style state network envelope
  buffering immutable conditioned versions; historical snapshot delivery is
  proved to preserve `StoreInv` and `GoodConfig3` through the existing
  virtual-LCA Join theorem; `networkRALinearizable` packages the complete
  reachability induction for the envelope.
- `Conditioned_Network_Progress.lean`: constructive apply-and-broadcast and
  historical-delivery progress, exposed as weak client steps.
- `Shapiro_Forward_Simulation.lean`: the concrete coupling interface and the
  proved generic assembly `ShapiroNetworkCoupling.forward : WeakSimM`; only
  the message/version and state-preservation coupling leaves remain.
- `Shapiro_Coupling_Invariant.lean`: dynamic message-to-version, replica,
  delivered-set, and packet correspondence; initial coupling and query
  preservation are proved without assuming messages embed into version ids.
- `Weak_Simulation.lean`: label-morphic weak simulation, weak-trace transport,
  two-direction trace equivalence, and representation independence. The old
  same-label API remains as a compatibility specialization.
- `Instances/GSet_Emulation_Canary.lean`: two proved simulations between
  distinct op/state label grammars for a grow-only set; message delivery and
  singleton-state merge are silent, and client trace properties are proved
  representation independent.
- `Transfer.lean`: genuine universal weak-trace RA property, the explicit
  trace-realization bridge from `VerifiedMRDT.ra_linearizable`, and one-way
  and two-way end-to-end transfer theorems. It contains no vacuous `True`
  theorem.

## Current status

The Shapiro construction, conditioned endpoint, label-morphic emulation
metatheory, first two-direction canary, and abstract RA trace-transfer theorem
are kernel checked with no `sorry`. Priority 5 now consists of constructing
the concrete Shapiro system simulation and conditioned trace realizer listed
in the repository-root `PRIORITIZED_REMAINING_WORK.md`.
