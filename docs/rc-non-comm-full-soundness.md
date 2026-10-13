# Distinct-operation guards and full soundness

The answer depends on the sequential bridge. Replacing the metadata guards in
`rc-non-comm` with operation inequality preserves the **total simulation**
soundness theorem. It does not suffice for the **existential execution-scoped
history** theorem. These are different existing contracts, not interchangeable
proof presentations.

## What is held fixed

The experiment changes only the replay-law field: for different application
operations, concrete noncommutation is equivalent to an `rc` edge in either
direction. Concrete commutation still means equality of implementation states.
The other replay laws, all five merge VCs, representation uniqueness, initial
and finite representations, canonical replay, support, replay supply and
representation of every certified version are retained. Independent sequential
specifications and execution/issuance rules retain their existing definitions.
No production datatype is modified.

`DistinctVCReplayConditions` mirrors `VCReplayConditions`, replacing only
`GuardedReplay.Laws` with `DistinctOperationReplay.Laws`. The total and scoped
extensions likewise retain their respective original bridge fields.

## Why the total bridge works

`EventFoldHistorySound` explains every concrete replay in the independent
specification. The canonical replay of the actual stored state is therefore a
valid witness. Commutation compatibility ensures that this same witness respects
specification-conflicting visibility. No comparison with another replay is
needed, and replay uniqueness is unnecessary.

`DistinctVCConditions.versions`, `.executions` and `.executionsV` prove this for
ordinary and virtual certified executions. The five VCs still derive
representation Join through `.join`. The final bridge theorem uses the supplied
canonical-version evidence; it does not itself derive that evidence from five
algebraic equations alone. The revised law field is not used by this final
lifting step.

## Why the scoped bridge can fail

Use two concurrent events with identical application operations:

```text
a = (timestamp 1, replica 0, tick)
b = (timestamp 2, replica 1, tick)
```

The implementation updates its register to the event timestamp and merges by
maximum. Its independent sequential specification is a minimum-timestamp
register, initially empty. Both update functions are total; neither
history admission nor the operation labels inspect implementation states.
Issuance permits only these two events, each from implementation state zero.
The certified trace forks an empty replica, issues one event at each replica,
and merges. The singleton branches agree with the specification; the merged
implementation state is **2**.

The represented state for an event set is its maximum timestamp. All five VCs
hold on these representations. Representation uniqueness and replay supply
hold; the latter peels the largest timestamp. Every certified version has such
a representation, including under virtual merges. The two-event stored state
has canonical replay `[a,b]`, whose concrete fold is 2.

The existing scoped bridge is nevertheless satisfied: it can select `[b,a]`,
whose concrete fold is 1 and whose query is accepted by the minimum-register
specification. That bridge explains a fold, not necessarily the stored state.
Every permutation of the two events returns **1** in the independent
specification, so **no** witness can explain the stored answer 2.

The policy is empty. Distinct-operation exactness holds because both events
carry `tick`; equal-operation events are precisely the exempted case under
investigation. No-chain and conditional commutation hold. In addition, the
minimum specification's updates commute, so even requiring the existing
commutation-compatibility condition does not repair this counterexample.
The original guarded replay laws reject this same model, as checked by
`original_laws_fail`.

## Consequence for the paper

The `rc-non-comm` revision cannot be presented as preserving all existing
soundness routes unchanged. In the replay-law and uniqueness discussion,
separate these conclusions:

- With a total simulation, use the stored state's own canonical witness.
- With an existential issued/execution-scoped bridge, explain why its selected
  replay has the same answer as the stored state. The revised policy law and
  five VCs do not establish this by themselves.

Replay uniqueness is one sufficient justification for the second step. An
exact-history bridge tying the selected replay to the stored state is another;
strengthening the bridge in that way is an explicit additional obligation.
Representation uniqueness alone compares represented states and cannot identify
an arbitrary history selected by the existing scoped bridge.

## Lean evidence

- [Revised full contracts and total soundness](../Sal/MRDTs/Paper1/DistinctOperationSoundness.lean)
- [Countermodel signature and proposed laws](../Sal/MRDTs/Paper1/DistinctOperationFullModel.lean)
- [All five VCs and representation/replay-supply proofs](../Sal/MRDTs/Paper1/DistinctOperationFullCounterexample.lean)
- [Representation of every certified version](../Sal/MRDTs/Paper1/DistinctOperationFullExecution.lean)
- [Independent specification and scoped history bridge](../Sal/MRDTs/Paper1/DistinctOperationFullHistory.lean)
- [Full hypothesis bundle and rejection of every witness](../Sal/MRDTs/Paper1/DistinctOperationFullResult.lean)
- [Concrete certified fork/update/update/merge trace](../Sal/MRDTs/Paper1/DistinctOperationFullTrace.lean)
- [Nonvacuous VC applications and positive/negative controls](../Sal/MRDTs/Paper1/DistinctOperationFullControls.lean)

`full_counterexample` combines the complete revised scoped hypothesis bundle,
the certified execution and failure of the public head-only RA criterion in
one kernel-checked statement. Its axiom closure contains only `propext`,
`Classical.choice` and `Quot.sound`.
The controls populate every indexed premise of causal, local-redistribution
and shared-event VC applications. They also check an accepted singleton answer
and reject the constant-zero alternative. Empty visibility and the restricted
event carrier are derived from the issuer for all certified executions; they
are not extra filters on the counterexample trace.

Validation: both `sh scripts/check-paper1.sh` and
`sh scripts/check-mrdt-refactor.sh` pass, including 187 runtime tests and 569
benchmark-result validations. A direct field comparison checks that the total
and scoped contract copies differ from their existing counterparts only in
the intended replay-law type. Production datatype definitions are unchanged.
