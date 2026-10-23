# Owner-ordered access control in certified executions

The owner-ordered positive result is now proved. Actual issuance-certified
ordinary and canonical recursive-base executions satisfy the independent
ordinary ACL/name specification. One concrete-event witness per registered
version supplies event coverage, required ordering, specification visibility
and the actual name-query result.

The issuer binds each payload ID to its framework event timestamp, binds
its authenticated actor to its issuing replica, and reserves one issuing replica
for the owner. It requires the payload precursor set to equal the current local
carrier's IDs and checks causal authorisation locally. These executable
conditions, together with the finite-store five VCs, establish source
well-formedness, causal admission and an owner chain for every registered
version. These source properties are conclusions, not additional invariants
supplied to the public correctness theorem.

A falsifier would have been an issuance-certified execution whose payload predecessor
relation differs from visibility, whose owner events are concurrent, or whose
name query cannot be explained by an order preserving causal dependencies.
`CapabilityGroupProtocol.lean` is the framework oracle;
`CapabilityGroupOwnerLinearization.lean` and
`CapabilityGroupOwnerRefinement.lean` provide the independent finite-history
construction and ACL fold proof. Those claims have been checked in Lean.

The reality oracle remains the fixed-owner specialisation of Spec. 2 of
[Jacob, Stuber and Hartenstein, PaPoC 2026](https://arxiv.org/html/2604.23560).
Authentication is an explicit replica-to-actor binding, with no cryptographic
implementation claim. Recipients can have several replicas. The original
counterexample with concurrent owner and recipient devices stays available.
The new issuer rejects owner operations on a second replica; this supplies a
proved sufficient discipline, not a necessity theorem that owners must always
have only one physical device.

## The proof chain

| Result | Declaration |
| --- | --- |
| The five VCs derive the finite-carrier representation through the existing metatheory | `Protocol.fiveVCs`, `Protocol.replayConditions` |
| Payload predecessor membership equals actual visibility | `Protocol.before_iff_visibility` |
| Registered versions are well formed, causally admitted and owner ordered | `Protocol.registered_source` |
| A complete causal ordering realises the administrative cuts | `OwnerLinearization.canonical_respects`, `canonical_adminPrefix` |
| Actual sequential permission checks equal source authorisation | `OwnerRefinement.assignment_run_guard` |
| Actual sequential live entries and name values equal the source result | `run_entries_eq_source`, `run_names_eq_source` |
| The same lifted concrete events enumerate the stored version and explain its query | `Certificate.version_witnessV` |
| Stronger projected and full-event RA hold, including canonical recursive bases | `Certificate.projectedRAV`, `eventRAV`, `executionsV` |
| The actual five-VC/scoped-history sufficient-condition interface is instantiated | `Certificate.conditions` |
| Every certified registered state also has a source issue/reconcile derivation | `Protocol.registered_source_reachable` |

The source replay construction orders grants and revocations along the owner's
chain. It places an assignment after every administrative event that is not
its causal successor, including concurrent revocations, and before its
administrative successors. Assignments within each gap follow causality.
An owner's own assignment is treated as an assignment rather than as an
administrative event.

The ACL fold proof establishes its permission tables and live name entries
over every actual sequential prefix. It does not assume equality with a
precomputed source summary. Concrete event lifting preserves full visibility,
which supplies specification-conflict visibility without a false global
assumption that implementation commutation implies specification commutation.

## Non-vacuity and scope

`ProtocolNonempty.reach` constructs two actual framework applies: owner 0
grants itself permission and assigns name 10. Mint provenance, raw transitions
and local guards are proved. `CertificateSPOT.actual_nonempty_public_control`
applies the public ordinary and virtual-semantics certificates and checks
`{10}` rather than an empty answer. Other paired controls cover concurrent
revocation, preserved causal predecessors, fresh regranting, recipient devices,
spoofed actors and an authenticated owner on the wrong issuing replica.

The guarantee is the repository's per-version/head RA criterion and its
execution predicate. It does not construct one prefix-compatible order of
all successive reads. As delayed revocations arrive, different versions may
need different witnesses. The exposed sequential query returns name values;
authorisation properties and capability queries have their separate source
theorems.

Source correspondence constructs a source derivation for every registered
state; it is not a step-by-step replica bisimulation. Authentication and the
replica/principal binding are model inputs. No cryptographic or Byzantine
network implementation is proved. The paper's event-valued name query is
observed through its name-value projection, as documented in the model note.

```sh
sh scripts/check-capability-group-research.sh
lake build Sal.MRDTs.Metatheory.CapabilityGroupLedger
```

The ledger imports the public certificates, source correspondence, old
counterexample and nonempty controls. The main release gate builds this ledger.
The independently reviewed endpoints use only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms. The complete local release gate
passed 3,910 Lean jobs, 18 public certificate contracts, 13 certificate tests,
187 runtime tests and 569 benchmark records after this integration.
