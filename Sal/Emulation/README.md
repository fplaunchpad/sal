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
  generation by freshness, `PrepareEnabled`, and the causal-broadcast law
  that every issuer-incorporated message precedes the new message; query and
  causal-delivery rules are unchanged.
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
  historical-delivery progress, indexed by the exact immutable snapshot and
  exposed as weak client steps.
- `Shapiro_Forward_Simulation.lean`: the concrete coupling interface and the
  proved generic assembly `ShapiroNetworkCoupling.forward : WeakSimM`, with
  explicit recipient-buffer and delivery-snapshot matching obligations.
- `Shapiro_Coupling_Invariant.lean`: dynamic message-to-version, replica,
  delivered-set, and packet correspondence; initial coupling and query
  preservation are proved without assuming messages embed into version ids.
  Update preservation is complete, including immutable-version causal
  contents and the fact that buffered packets remain unincorporated at their
  targets. Historical-delivery preservation and the final concrete
  `forwardSimulation` assembly are also complete.
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
- `Network_Transfer.lean`: canonical weak-trace endpoint realization for the
  snapshot network, reachability proof, network RA transfer, and the
  end-to-end disciplined-op theorem.
- `Instances/GSet_Conditioned_Transfer_Canary.lean`: concrete grow-only-set op
  signature specializing the complete conditioned transfer while keeping
  certificate, progress, and observable adequacy evidence explicit.

## Current status

The Shapiro construction, conditioned endpoint, label-morphic emulation
metatheory, both concrete coupling directions, canonical network trace
realizer, end-to-end transfer theorem, and conditioned GSet specialization
are kernel checked with no `sorry`. Deployments must still supply the
deliberately separate safety certificate, constructive network progress, and
observable trace-adequacy evidence.
