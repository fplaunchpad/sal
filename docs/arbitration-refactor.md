# Consolidate MRDT arbitration

## Claim

A single semantic interaction policy replaces `ArbitrationSpec.Commutes` and
the old datatype-level replay resolver. The framework uses visibility for
causally related conflicts and the policy's direction for concurrent conflicts.
It does not need `no_rc_chain` as a public datatype requirement.

Status: machine-checked and migrated

Formal oracle: `Instances/InteractionSPOT.lean`, followed by the complete
`Sal.MRDTs.Metatheory.RefactorLedger` build and the public `VerifiedMRDT`
theorem ledger.

Falsifier: either small datatype cannot express its sequential semantics with
the proposed interaction policy, or an existing production instance cannot
recover its checked convergence and sequential-correctness theorem after
the datatype-level replay resolver is removed.

Positive controls:

- three concurrent LWW writes linearize in increasing timestamp order;
- a concurrent OR-set remove linearizes before an add of the same element and
  produces add-wins;
- an OR-set remove that observed an add follows that add and removes it.

Negative controls:

- the LWW three-write order refutes the old `no_rc_chain` condition;
- reversing the concurrent OR-set edge produces remove-wins and must not match
  the add-wins sequential observation.

PBT gate: not required for theorem closure. Directed PASS/FAIL controls pin the
finite behavior, while `canonical_respects` and `verified` discharge the
general interaction and correctness claims. Randomized reachable-trace testing
would validate an executable runtime correspondence, which is not implemented
for this Lean-only instance.

Trusted definitions: the chosen LWW timestamp policy, observed-remove payload,
and independent sequential specifications. Lean checks consequences of these
definitions but does not establish that they are the intended external APIs.

Reality oracle: compare the SPOT outcomes with the conventional LWW and
add-wins observed-remove behavior, then retain the examples as executable
semantic fixtures.

Result: `InteractionSpec` uses
`independent | conflict concurrentOrder` with swap coherence. The public
set-relative order uses visibility for causal conflicts and the supplied
direction for concurrent conflicts. It retains the set-relative absorber
clause. Each `SequentialCorrectnessCertificate` must provide an actual legal
witness, so this definition does not impose `no_rc_chain` on datatypes.

The existing absorber proof remains one internal convergence construction. It
is parameterized by `ReplayPolicy`; neither `UpdateSig` nor `MRDTSig` stores
that policy. The low-priority unconstrained policy removes vacuous per-datatype
boilerplate. `IsReplayLinearizableWith` remains an internal research hook for a
specialized replay theorem; the generic certified Join route uses the default.

The production `Instances/LWWRegister.lean` package now closes the full
positive example. Its `max` update and merge prove all-context Join with the
default proof-local policy. `replay_lo_false` checks that this raw replay order
is empty; `canonical_respects` constructs the timestamp-sorted public witness;
and `verified` packages convergence and refinement to the total overwrite
register. The chronological/reversed-delivery PASS controls and the
lower-timestamp-winner FAIL control pin the intended observation.
