# Natural sequential specifications: remaining families

Audit of the current production declarations, 2026-10-14. This distinguishes
an independent sequential reference from a projection to a metadata-free client
request API. The former does not automatically establish the latter. No public
contract was changed during this audit.

| Family | Sequential state and update | Boundary established today |
|---|---|---|
| LWW register | `Option Nat`; every write overwrites | Natural overwrite-register semantics; event metadata selects the serialization witness |
| Enable/disable-wins flags | `Bool`; enable/disable set it | Natural Boolean semantics with both source polarities and full event histories |
| Published Balegas counter | Integer value plus per-replica balances; mint, spend, transfer | Natural escrow-account semantics with affordability, value and local-rights queries |
| TreeMove | Current parent/edge-label tree; cycle-producing moves have no effect | Natural move effect, with event-order and causal-origin legality retained |
| MVR/MVRLive | Live `(write identity, value)` pairs; remove explicitly observed identities then add a write | Observed-overwrite message semantics, shared by both representations |
| AegisSheet | Incremental axis tokens, positions, cell/range versions and purges | Independent causal message machine; visible-sheet-only deterministic state is refuted for the current message alphabet |

## LWW register

`Sal/MRDTs/Instances/LWWRegister.lean`: `LWWOp.write`, `valueOf`, `spec`,
`stateRel`, `fold_refines_sorted`, `sequentialCorrectness`, `verified`.
The abstract state is `Option Nat`, initially `none`; a write replaces it by
`some value`. Its transition ignores timestamp and replica. Legality is `True`.
The concrete maximum timestamped write is related through `read`.
`sequentialCorrectness` chooses a `canonical` history sorted by `writeLE`, proves
that order respects the execution order, and applies `fold_refines_sorted`.
Timestamp/replica/value tie breakers belong to witness selection, not abstract
register state. This is already a natural sequential register. The certificate
is an existential ordered-history explanation, not a claim that arbitrary
delivery order implements overwrite.

## Source flags

`Paper1/NeemFlagEvent.lean`: `boolStep`, `machine`, `simulation`, `historySound`.
State is exactly `Bool`; a winning request sets the selected polarity and a
reset sets its opposite. Event timestamps and replica identities are ignored.
`EnableWinsFlagEvent` instantiates `(initialFlag,invert)=(false,false)`;
`DisableWinsFlagEvent` instantiates `(true,true)`. Both public flags start
disabled, and their source enable/disable names map to opposite physical
constructors in the disable-wins variant.

`Paper1/NeemFlagCertificate.lean` supplies `conditions`, `certifiedV` and
`certified`, using the common five-equation proof and independent Boolean
history soundness. This covers ordinary and recursive merge-base versions.
The concrete source stores integer counters and Boolean bits per replica; none
occur in the abstract state. The F* App_mrdt artifacts provide no query:
`Instances/EnableWinsFlag.lean` and `DisableWinsFlag.lean` explicitly document
the added Boolean interpretation. Thus the query interpretation is an exposed
formalization choice supported by the source result prose, not a query copied
from App_mrdt.

## Published Balegas bounded counter

`Paper1/BalegasBoundedCounterEvent.lean`: `Accounts`, `accountStep`,
`validIssuer`, `affordable`, `accountQuery`, `machine`, `project_update`,
`query_refines`. The independent state consists of an integer value and integer
account balances. Increment credits its issuer and increases the value;
decrement debits its issuer and decreases the value; transfer debits its issuer
and credits a distinct target without changing the value. The machine checks
replica bounds and affordability. Its query exposes the counter value or one
replica's local rights. Timestamps are ignored; replica identity has an actual
accounting role and cannot be erased while retaining transfer and rights queries.

`Paper1/BalegasBoundedCounterCertificate.lean`: `certifiedV`, `certified`,
`versions_safeV`. Reachable causal histories are proved affordable at their
serialization prefixes. No implementation matrix occurs in the abstract state.
This is a natural escrow interface. A value-only counter with decrement enabled
whenever the total exceeds the bound would be a different contract: published
issuance checks local rights. A separate value-only client projection could hide
accounts as internal protocol state, but should not silently replace this
operation legality.

## TreeMove

`Instances/TreeMove.lean`: `Move`, `Tree`, `setParent`, `doMove`, `spec`,
`SequentialLegal`, `ClientLegal`, `sequentialSpec`, `sequentialCorrectness`,
`verified`. A move requests parent, child and edge metadata (a user-visible edge
label, not an event timestamp). `doMove` updates the current tree exactly when
the resulting parent graph is acyclic, otherwise retaining the tree. The
independent machine never sorts or replays its previous events. The observation
is `visibleTree`, excluding the trash subtree.

The full contract's legality still contains deterministic event-key ordering,
no duplicates and a causal-origin applicability witness in a subset of the
serialization prefix. The issuer checks a visible destination, visibility or
freshness of the child, and reserved-node restrictions. Applicability is checked
at the origin, not reasserted against the whole merged prefix. This is a natural
tree transition with a metadata-enriched legal-history contract. It does not
yet present a metadata-free move-request history theorem. A useful small
projection would map `Op Move` to `Move` and preserve tree updates and reads;
the remaining legal-history guarantee must explicitly retain or quantify away
the origin witness. No such new theorem is claimed here.

## MVR and compact MVRLive

`Instances/MVRContract.lean`: `clientStep`, `clientLegal`, `queryValues`,
`clientSpec`, `issued_overwrite`, `replayOrder_iff_overwrite_of_execution`,
`clientSequentialCorrectness`. A write contains a value and explicit overwrite
identities. The abstract machine removes those live identities and inserts the
new timestamp/value pair. Queries return the set of remaining values. Legality
requires fresh write identities and that overwrite targets were born earlier;
targets need not still be live. The latter matters because two concurrent
writes may supersede the same earlier write.

`Instances/MVRLive.lean`: `spec` reuses `MVR.clientStep` and `MVR.clientLegal`;
`spec_run_eq` establishes equality with the historical contract's run.
`MVRLiveContract.lean`: `replay_legal`, `sequentialCorrectness`, `mvr_correct`
certify the production compact implementation. Sharing already exists and should
be retained. Replica is not used by the abstract transition, but write identity
and observed overwrite identities are semantic data for this message alphabet.

`Paper1/MVRClient.lean` now supplies `prepare`, accepting a value and replication
metadata and collecting the complete live write-ID set. `prepared_targets_exact`
proves that collection complete; `issuance_prepare_iff` and
`historical_issuance_prepare_iff` establish the exact source guards.
The compact source checks live-ID freshness; the historical source additionally
rejects reuse of a dead prior write's ID. The adapter retains that distinction.
`prepared_replaces` and `prepared_public_read` prove that the local write
replaces the live set and reads as the requested singleton.

The global contract remains an independent observed-overwrite machine. A
singleton register whose every write replaces the whole current value set
would lose the distinction between concurrent and causally subsequent writes.
The checked local adapter does not claim that stronger concurrent contract.
No impossibility theorem for all alternative client abstractions is inferred.

## AegisSheet

`Instances/AegisSheet.lean`: `AxisUpdate`, `CellUpdate`, `RangeUpdate`, `Purge`,
`Action`, `Command`, `SheetOp`. Events include exact seen timestamps, overwritten
versions, and checked undo targets/inverse actions. These are protocol messages
with an observed context; they are not plain row/column/cell UI requests.

`Instances/AegisSheetSequential.lean`: `State`, `applyAxis`, `applyCell`,
`applyRange`, `applyPurge`, `step`, `view`, `CausalOriginLegal`, `clientSpec`.
The reference stores live tokens and active versions incrementally, rather than
an event log or the concrete replay result. Queries expose the sheet `View`.
Legality retains a causal origin contained in the merged prefix, allowing
operations that were valid locally even when the serialization prefix includes
unseen concurrent changes. `verified`, `spec_linearizable` and
`spec_linearizableV` certify this independent machine for ordinary and recursive
merge-base executions.

`Instances/AegisSheetAbstraction.lean` contains decisive checked boundaries:
`token_views_equal` and `row_tokens_distinguish_future` show that equal visible
sheets can react differently to the same removal; `no_view_only_step` refutes
a deterministic next-state function on `View` satisfying both continuations.
`cell_views_equal`/`cell_versions_distinguish_future` and
`range_views_equal`/`range_versions_distinguish_future` similarly expose version
identity. The obstruction concerns the existing Event alphabet and those
continuations. It does not refute every possible natural client request API,
nor an abstraction that retains causally meaningful identities or is relational.

The next useful refinement question is an explicit UI-request elaboration into
these observed-context messages, preserving stable row/column references,
multi-value reads, undo and purge semantics. Replacing the machine by its
visible sheet alone would contradict the checked token counterexample. No
replacement or new projection theorem was implemented in this audit.

## Verification scope

This report reads current definitions and theorem statements, including the
new checked local MVR adapter. It does not add new global certificates. The source flags,
bounded counter, LWW, TreeMove, MVRLive and AegisSheet already have production
certificates; their different abstraction boundaries are recorded above.
The adjacent OR-set consolidation was separately built: the shared natural
Finset insert/erase machine and complete-history alphabet-renaming theorem
`Paper1.ORSetSharedSpecification.admits_iff` passed Lean with only standard
axioms. That equality does not identify different concrete conflict policies.
