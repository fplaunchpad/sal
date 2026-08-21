# GC theorem coverage audit

Status date: 2026-08-21. This document treats Lean declaration types as the
source of truth. A package containing two theorems does not establish their
composition unless a third theorem has the composed conclusion.

## Status vocabulary

- **Proved**: one named Lean theorem has the stated scope.
- **Executable**: the handwritten JavaScript path exists and has directed or
  randomized tests. This is not extraction from Lean.
- **Separate**: all listed ingredients exist, but no theorem composes them.
- **Open**: a required theorem or implementation does not exist.

## Coverage matrix

| Merge semantics | Execution | Collection | Scope | Trace/query result | Lean evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| unique LCA (`Step3`) | global | commit history | generic | finite trace and head reads | `gc_safety` | Proved |
| unique LCA (`Step3`) | global | root-free compressed commit history | generic | payload simulation and compression facts use independently supplied carriers | `gc_safety_compressed` is only a catalogue conjunction | **Separate** |
| virtual LCA (`Step3V`) | global | commit history | generic | finite trace and head reads | `gc_safetyV` | Proved |
| virtual LCA (`Step3V`) | global | root-free compressed commit history | generic | no composed theorem | `gc_safetyV` and `gc_safety_compressed` have different transition systems | **Separate** |
| n/a | asynchronous local stores | commit holdings | generic protocol | finite execution refines a no-GC world; reads agree pointwise | `distributed_execution_refines_noGC`, `world_read_preserved` | Proved |
| unique LCA (`Step3`) | distributed physical stores | commit history | generic MRDT | silent fetch/GC erasure to a finite `Step3` trace | `distributedConfig_refines_Step3` | Proved |
| unique LCA (`Step3`) | distributed physical stores | root-free commit history | generic MRDT | local collection retains heads and MCAs, and compressed LCA lookup is exact | `LocalGCCertificate.mca_closed`, `collect_lca_preserved` | Proved |
| virtual LCA (`Step3V`) | distributed physical stores | commit history | generic MRDT | finite traces erase to `Step3V`; one fetch from an MCA-repair source establishes merge availability | `distributedConfig_refines_Step3V`, `stepAvailableV_merge_after_repair` | Proved, conditional on a repair source |
| unique LCA (`Step3`) | global | state | generic callback | stability simulation and read preservation under `StabilityVC` | `stability_simulation` | Proved |
| virtual LCA (`Step3V`) | global | state | generic callback | no virtual-LCA stability simulation | none | **Open** |
| unique LCA (`Step3`) | local epoch | state | Sided Peritext | certified collection preserves rendered state; two-epoch composition | `frontier_collectStableBase_safe`, `collectStableBase_twoEpoch` | Proved |
| unique LCA (`Step3`) | distributed physical stores | commit history + state | Sided Peritext | arbitrary finite interleavings erase to `Step3`; endpoint held-version queries agree | `combinedSteps_refines_Step3`, `combinedTrace_query_eq` | Proved |
| virtual LCA (`Step3V`) | distributed physical stores | commit history + state | Sided Peritext | finite traces erase to `Step3V`; repair fetch transfers every MCA compact input; merge result is installed head-only without materializing the virtual LCA; endpoint queries agree | `fetchResult_virtualMerge_ready`, `HeadOnlyMergeCertificate.related`, `MaterializationDelta.headOnlyMergeInstall`, `combinedStepsV_refines_Step3V`, `combinedTraceV_query_eq` | Proved certificate-driven composition; JavaScript open |

## Package boundaries

`PeritextFlagshipCertificate` contains virtual semantic RA-linearizability,
ordinary root-free commit GC, abstract distributed commit-holding GC, and a
Peritext state-GC theorem as separate fields. Its type does not state that
these features can interleave.

`PeritextSided.ProductionCertificate` exposes both physical interaction
theorems. `interactionRefinesV` and `interactionQueriesV` cover widened
traces; `virtualRepairReady` proves the fetch-side availability/materialization
boundary; `headOnlyVirtualMerge` proves that the compact result needs no
materialized virtual LCA.

`UnifiedVerifiedMRDT.ra_linearizableV` and `SafetyCertificate.preservationV`
concern virtual semantic reachability and datatype safety. They do not add
virtual transitions to `DistributedConfigStep` or `CombinedStep`.

## JavaScript boundary

| Feature | Runtime status | Evidence boundary |
| --- | --- | --- |
| distributed fetch/head sync | Executable | handwritten runtime and tests |
| unique-LCA merge | Executable | handwritten runtime and differential tests |
| commit-history GC | Executable | handwritten runtime and never-collected-twin tests |
| Sided Peritext state GC | Executable | handwritten runtime, fail-closed evidence audit, and twin tests |
| both collectors under unique-LCA merge | Executable | directed cross-epoch and randomized tests; not extracted |
| virtual-LCA merge | Executable | `DistributedReplica` recursively folds MCA antichains; directed and randomized criss-cross tests |
| MCA-closure commit GC | Executable | `keepSet` computes recursive MCA closure; certified materialized-boundary records transfer compressed cut nodes without discarded parents |
| both collectors under virtual-LCA merge | Executable directed + randomized | `combined-virtual-gc.test.js` compares with a never-collected twin; `crossepoch-crisscross.test.js` composes virtual merges, both collectors, and boundary repair |

## Corrections required by this audit

1. Qualify the consolidated draft's combined-GC theorem as ordinary
   `Step3` only.
2. Do not call `PeritextFlagshipCertificate.distributedV` distributed storage
   correctness. It is virtual-LCA correctness of the semantic configuration.
3. Do not present the catalogue conjunction `gc_safety_compressed` as one
   linked root-free execution theorem. The linked ordinary result lives at the
   distributed physical-store layer.
4. Do not present root-free compressed commit GC as already composed with
   `Step3V`.
5. Reserve “fully end-to-end” for a matrix cell backed by one theorem and, when
   discussing the shipped system, a matching executable path.

## Proof work exposed by the audit

The widened physical interaction semantics and its finite-trace/query safety
theorems now exist. The proposed compact virtual-LCA fold turned out to be
unnecessary for Peritext. `HeadOnlyMergeCertificate.related` constructs the
post-merge continuation relation from the two branch-head result and
`MaterializationDelta.headOnlyMergeInstall` installs it while keeping the
virtual LCA entirely in ghost semantics.

Protocol liveness still needs a repair-source discovery mechanism. MCA closure is not preserved by union:
two independently collected singleton head stores are each MCA-closed, but
their fetch union can omit the cross-head MCAs. A virtual fetch must therefore
request or reconstruct the missing cross-store MCA closure before head sync;
plain holding union is insufficient. Once such a source is selected,
`stepAvailableV_merge_after_repair` and `fetchResult_virtualMerge_ready` prove
that one ordinary fetch transfers both closure commits and their compact
Peritext materializations.

The JavaScript audit refined and closed this boundary. `DistributedReplica`
already implements virtual LCAs and cross-epoch lifting. Transport after
independent collection now uses a certified materialized-boundary record with
the original version id, remaining compressed parents, epoch identity, closed
roster, encoded state, fingerprint, and integrity checksum. The trusted
receiver checks this certificate before installing the boundary without
replaying discarded parents. This is an integrity/simulation check under the
trusted-peer threat model, not Byzantine authentication. If independently
compressed stores have no shared physical ancestor, only a datatype exposing
the proved `headOnlyMerge` capability may proceed; Peritext does.

The generic prerequisite is a root-free compressed representation theorem for
the MCA-closure keep set. Without it, the virtual theorem can preserve behavior
but cannot support the production bounded-history claim.
