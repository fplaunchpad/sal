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

Liittschwager et al. (arXiv:2504.05398) supplies the formal target: two weak
simulations, weak-trace equivalence, and representation independence. Those
proofs are the next project phase; they do not change the Shapiro state
machine.

## Files

- `Op_Based_TS.lean`: op-based configurations, preparation/effect, broadcast,
  causally enabled delivery, and silent delivery transitions.
- `Emulation.lean`: `EmulatorState`, causal schedules, preparation, internal
  delivery, draining, Shapiro merge, and representation-invariant proofs.
- `Conditioned_Emulation.lean`: embeds the emulator into
  `ConditionedMRDTSig`; `Inv` is `D ⊆ M` plus causal down-closure, and
  `applicable` is the generation-side causal/freshness obligation.
- `Weak_Simulation.lean`: label-morphic weak simulation, weak-trace transport,
  two-direction trace equivalence, and representation independence. The old
  same-label API remains as a compatibility specialization.
- `Instances/GSet_Emulation_Canary.lean`: two proved simulations between
  distinct op/state label grammars for a grow-only set; message delivery and
  singleton-state merge are silent, and client trace properties are proved
  representation independent.
- `Transfer.lean`: the typed certification boundary. A transfer input contains
  a causal schedule and `VerifiedMRDT` certificate. It deliberately contains
  no vacuous `True` theorem.

## Current status

The Shapiro construction, conditioned endpoint, label-morphic emulation
metatheory, and first two-direction canary are kernel checked with no `sorry`.
The end-to-end RA-linearizability connection is Priority 5 in the repository
root `PRIORITIZED_REMAINING_WORK.md`.
