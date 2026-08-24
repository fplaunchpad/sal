# Consolidate MRDT arbitration

## Claim

A single semantic interaction policy replaces
`ArbitrationSpec.Commutes` and `CRDTSig.rc`. The framework uses visibility
for causally related conflicts and the policy's direction for concurrent
conflicts. It does not need `no_rc_chain` as a public datatype requirement.

Status: machine-checked and migrated

Formal oracle: `Instances/InteractionSPOT.lean`, followed by the complete
`Sal.MRDTs.Metatheory.RefactorLedger` build and the public `VerifiedMRDT`
theorem ledger.

Falsifier: either small datatype cannot express its sequential semantics with
the proposed interaction policy, or an existing production instance cannot
recover its checked convergence and sequential-correctness theorem after
`CRDTSig.rc` is removed.

Positive controls:

- three concurrent LWW writes linearize in increasing timestamp order;
- a concurrent OR-set remove linearizes before an add of the same element and
  produces add-wins;
- an OR-set remove that observed an add follows that add and removes it.

Negative controls:

- the LWW three-write order refutes the old `no_rc_chain` condition;
- reversing the concurrent OR-set edge produces remove-wins and must not match
  the add-wins sequential observation.

PBT gate: staged. First keep the interaction model finite and executable and
pin the directed controls with `native_decide`. Add randomized reachable-trace
testing only if the SPOTs expose a non-local interaction or acyclicity claim
that is not discharged structurally.

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
is parameterized by `ReplayPolicy`; `CRDTSig` and `MRDTSig` do not store that
policy. The low-priority unconstrained policy removes vacuous per-datatype
boilerplate. `IsRALinearizableWith` remains an internal research hook for a
specialized replay theorem; the generic certified Join route uses the default.
