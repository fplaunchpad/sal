# Live-state MVR migration

Status: machine-checked public certificate; compact implementation registered.

Goal: retain only live tagged values in the concrete MVR, without weakening
the existing observed-supersession and concurrent-survival contract.

Proved claim: updating a live set by removing the event's observed tags
and inserting its fresh tagged value, together with ancestor-relative
three-way set merge, represents exactly the surviving writes of the history.
An issued local write leaves a singleton. Concurrent replay must remove only
the carried targets, not every value in the replay state.

Falsifier: a superseded write survives merge, a concurrent write disappears,
or a sequential write retains an older value. Also test equal payload values
with different tags, repeated synchronization, and a nonempty ancestor.

Formal oracle: `MVRLiveContract.lean`, its implementation/history/virtual-base
proofs, and the executable SPOT campaign. The public gate checks the exact
replacement signature and both required contract theorems. A mutation test
rejects the former grow-only certificate for this different state type.

Reality oracle: the user's MVR contract and hand-derived fork/write/merge
examples. No separate runtime implementation is being claimed. Historical
version storage and overwrite payloads are separate from the live state size.

Trusted definitions: identity freshness, exact observed targets at issuance,
and the semantics of surviving concurrent writes. The history-based tests
preceded the general execution proof. The production registry now selects
`MVRLive.verified`; the old implementation remains internal proof/reference
material, not another production MVR.

## Checked core

`MVRLive.State` is a finite set of timestamp/value pairs. There is no history
field or overwrite-log field. `issued_write_singleton` proves that an issued
write replaces its observed live set with one tagged value. `update_live`
preserves the history representation when the new tag is neither previously
overwritten nor self-overwritten. `merge_shared_history` proves the three-way
formula using the actual event intersection, unique event identities in the
union, and presence of each branch's overwrite targets in that branch.

`fold_live` connects chronological replay to the independent surviving-write
history definition. It reuses the existing sequential-machine refinement,
not the old all-commuting update or merge proofs. `spec_run_eq` preserves the
existing abstract machine definition; `rc_acyclic` preserves the existing
observed-supersession policy. The principal representation theorems use only
the standard Lean axioms.

Controls cover local overwrite, concurrent survival, no resurrection from an
unchanged branch, repeated equal values with distinct tags, deduplicated value
queries, exact-target issuance, and rejection of omitted targets. A separate
control proves that the replacement updates do not all commute. Clearing the
whole state during replay and using union as merge both fail named controls.

The executable campaign generates two successive fork/synchronization rounds,
allocating unique tags and exact observed payloads by construction. It compares
against a history oracle, not another invocation of compact merge. Three
500-case seeds (17, 91, 2026), size 20, consume at most ten choices per case;
a deterministic check covers all 1,024 ten-choice binary words. This is bounded
testing, not a proof of arbitrary distributed or virtual-base executions.

Validation: all three seeds passed 500 cases with no `gaveUp`; the union
mutation was detected and shrunk in three steps to `[0,0,0]`, already pinned
by `harness_rejects_union`. The deterministic backstop and all literal controls
pass. The refactor and public-certificate ledgers build successfully. All 23 production
contracts, now including the exact compact implementation, pass their public
gate and axiom audit.

## Closed execution and release proof

`MVRLiveHistory.issued_overwrite` derives target presence and causal precedence
from mint honesty. `MVRLiveVirtual.virtualMergeBaseState_represents` proves
the surviving-write characterization for recursively constructed antichain
bases. `represented_of_mintCertifiedV` maintains that invariant and canonical
replay for the entire widened execution, including ordinary operations.

`MVRLiveContract.verified` connects that replay theorem to the same live-set
sequential machine and legality predicate, now with equality as the state
relation. `mvr_correct` proves same-execution causal maximality for every stored
version; `linear_register` proves the ordinary sequential special case. The
public manifest requires both obligations for the new signature. The proofs
use only `propext`, `Classical.choice`, and `Quot.sound`, with no new assumptions.

The production collection classification is now exact-state: normal writes
discard superseded values directly. This does not collect historical commit
versions or event payloads, and makes no standalone runtime or memory benchmark
claim. Human review of the semantic contract remains separate from the proof gate.

Final release validation: `check-mrdt-refactor.sh` passes, including all 13
public-gate tests, 187 existing runtime regression tests, and validation of
569 stored benchmark-result schemas. These runtime/benchmark checks are
repository regressions, not measurements of a new MVR runtime. The full
working-paper gate passes; all PDFs are rebuilt and the MVR pages inspected.
