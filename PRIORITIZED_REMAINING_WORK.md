# Prioritized Remaining Work

This is the canonical, durable cross-project backlog for Sal. It merges the
unfinished editorial deliverables, metatheory cleanup, emulation transfer,
intent layer, sequence refinements, and runtime certification work. Completed
subsystem roadmaps are historical evidence; this file determines what comes
next.

## Priority order

### 1. Split `sal-mrdts` into two standalone papers — completed 2026-08-01

- Paper A: corrected and conditioned metatheory, Join doctrines, virtual LCAs,
  and composition.
- Paper B: sequence designs, intent, compaction, runtime, lower bounds, and
  evaluation.
- Extract shared notation and bibliography support.
- Make both papers build independently.

Delivered by `Sal/ConditionedMRDTs/PAPER_SPLIT_PLAN.md` and the two entry
points under `Sal/ConditionedMRDTs/papers/`. Shared notation remains
single-source in the canonical manuscript preamble; both selected papers and
the consolidated manuscript build with Tectonic. Remaining prose compression,
claim synchronization, and expanded per-paper audit tables belong to Priority
10, not to the structural split.

### 2. Retire the legacy global-`lo` proof route completely — completed 2026-08-01

- Decouple corrected metatheory from `Merge_Linearization.lean`.
- Remove or archive its six remaining proof placeholders.
- Ensure production builds contain no path through legacy `sorryAx` results.

Delivered by the merge-independent
`Sal/CRDTs/Metatheory/Linearization_Basics.lean` and the archived historical
source `Sal/CRDTs/Development/Merge_Linearization_GlobalLo.lean.disabled`.
The corrected set-relative theory no longer imports the global-`lo` attempt;
the active Lean tree contains no `sorry` commands, and the binary corrected
bridge plus the conditioned refactor ledger build successfully.

### 3. Correct the operation-to-state emulator — completed 2026-08-01

- Replace the current `Set Msg` scaffold with Shapiro et al.'s
  `(s_m, M, D)` construction.
- Model preparation, known messages, delivered messages, enabled delivery,
  and internal delivery steps.
- Treat Shapiro et al. 2011 as the construction blueprint and Liittschwager et
  al. 2025 as the formal simulation and transfer target.

Delivered in `Sal/Emulation/Emulation.lean` and
`Sal/Emulation/Conditioned_Emulation.lean`. The emulator now uses the original
materialized/known/delivered tuple, causal schedules, generation preparation,
enabled internal delivery, and causal-downset invariants. Its verification
endpoint is `VerifiedMRDT (shapiroConditionedG ...)`; the old 24-VC/`True`
transfer scaffold was removed.

### 4. Formalize Liittschwager-style emulation — completed 2026-08-01

- Generalize weak simulation from label equality to label morphisms.
- Prove the required weak simulations between the original and emulating
  transition systems.
- Prove weak-trace and representation-independence results.
- Use the grow-only set as the first concrete canary.

Delivered by the label-morphic `WeakSimM`, `LabelMorphism`, `LabelIso`, and
`EmulationEquivalence` interfaces in `Sal/Emulation/Weak_Simulation.lean`.
Weak-step/execution lifting, trace transport, two-way trace equivalence, and
representation independence are proved generically. The grow-only-set canary
proves both simulations between distinct op/state label grammars, including
silent message-delivery/singleton-merge steps. Priority 5 connects this
behavioral layer to the conditioned RA-linearizability certificate.

### 5. Finish the RA-linearizability transfer — in progress

- [x] Define op-based RA-linearizability as a genuine universal weak-trace
  property, parameterized by a concrete RA trace legality judgment.
- [x] Define the explicit conditioned trace-realization obligation connecting
  `VerifiedMRDT.ra_linearizable` to observable state-system traces.
- [x] Prove one-way weak-simulation and two-way emulation transfer theorems.
- [x] Define the actual certificate-scoped conditioned `Step3` system view and
  observable label map: updates/queries are visible; timestamps, replica
  creation, merge, and message delivery are handled through τ-observation.
- [ ] Prove the datatype-generic forward weak simulation from
  `opLabeledTS D hb` to that state system (full label isomorphism is neither
  necessary nor generally available for silent administrative labels).
- [ ] Construct the trace realizer into conditioned ternary configurations and
  discharge its honest-reachability and adequacy obligations.
- [ ] Instantiate the complete theorem for the grow-only-set canary.

### 6. Complete the intent column for the production catalogue

- Start with tombstoned RGA: anchor closure, timestamp freshness, grave
  closure, and the genuine-sequence theorem.
- Continue with OR-set, queue, Peritext, registers, and the remaining
  production datatypes.

### 7. Finish Tree-RGA observational refinement

- Generalize beyond root-only insertion.
- Strengthen causal consistency over evolving prefixes.
- Prove `visible_apply_merge` for multi-replica executions.

### 8. Develop a declarative replacement for the absorber clause

- Specify arbitration over surviving conflicts.
- Prove equivalence with `loOn` for conditional-commutativity instances.
- Investigate whether joint absorption requires a strictly more general
  specification.

### 9. Strengthen runtime certification

- Determine whether EmbedRGA's continuation certificate can be lifted to a
  complete DAG-level `StabilityVC`.
- Formalize divergent-epoch joins and certificate transport.

### 10. Final editorial and artifact pass

- Synchronize both papers with the final Lean theorem names.
- Give each paper an independent mechanization map.
- Add CI gates for Lean builds, axiom audits, and Tectonic builds.

## Dependency summary

- Priority 1 can begin immediately and should not wait for the emulation
  project.
- Priorities 3--5 are one proof project and should be executed in order.
- Priorities 6--9 can proceed independently once ownership is clear.
- Priority 10 follows the substantive work relevant to each paper.

## Completed foundation

The next active item is Priority 5. The consolidation work underlying this backlog is recorded in
`Sal/ConditionedMRDTs/REFACTOR_ROADMAP.md`. Its checklist is complete. In
particular, the repository now has production `VerifiedMRDT` certificates,
EmbedRGA continuation-aware runtime recoding, a concrete heterogeneous
product, unified ledgers, representation lower bounds, and a retired Shesha
positive capstone whose premise was formally refuted.
