# Efficient OR-set port

Completed: certify Neem's efficient
per-replica/per-element implementation, retaining the ordinary finite-set
specification and same-element remove-before-add `rc`.

Authority: `_references/neem_fstar_repo/code/mrdts/OR-set-efficient/App_mrdt.fst`.
State is a finite set of `(replica, timestamp, element)` records. Add replaces
the issuer's records for the element. Remove erases all records for the element.
Merge is `(L ∩ A ∩ B) ∪ (A \ L) ∪ (B \ L)`.

Candidate claim: exact certified executions admit a legal `loOn`-respecting
replay of the ordinary set, with the same membership observations. Falsifiers
include losing a concurrent add, resurrecting an observed removed element,
and retaining old local add records after replacement.

The formal oracle is the new `EfficientORSet` implementation, reduction tests,
and public certificate. The reference F★ definitions and hand-derived
traces are the independent semantic oracle. The new package is registered as
`efficient-or-set`. The older tagged `or-set` package has been removed from
production and the paper. Its Lean model and JavaScript module remain only
as historical regression/comparison fixtures; the JavaScript module has not
been relabelled as the efficient implementation.

Proof-route concern: repeated adds at the same replica do not commute as raw
record updates, although `rc` leaves add/add pairs unordered. The optional
all-state `ReplayLaws.noncomm_covered` route therefore cannot be reused as-is.
Do not change `rc` or the implementation merely to satisfy this stronger
sufficient condition. Execution-local proofs must respect the replica history.

## Evidence

Machine-checked in `Sal/MRDTs/Instances/EfficientORSet.lean`:

- `elements_update`, `elements_fold`, `sequential_refinement`: projection to
  the ordinary finite set commutes with every step and every sequential fold.
- `sequentialCorrectness`: the public sequential-correctness component, taking
  the framework's replay witness as a premise. It is not replay adequacy.
- `rc_acyclic`, `keyUnique_update`, `keyUnique_fold`.
- Reduction controls for repeated adds, multiple replicas, tombstone-free
  removal, concurrent add-wins, and the incorrect union merge.
- `all_state_replay_laws_unavailable` refutes the optional all-state update-law
  route for the exact public `rc`.
- `incompatible_replays_merge_not_a_fold`: three different replay permutations
  of the same three local adds end in three different records; merging those
  independently selected states produces two records for the same replica/key.
  That state cannot be any sequential fold. This is not a reachable-execution
  counterexample; it rules out dropping replica-history compatibility from
  the merge proof.

The fork campaign in `EfficientORSetSPOT.lean` compares efficient-merge
membership with an independent observed-remove history model and checks unique
replica/element keys. It generates a common prefix and two branches with distinct
replicas and fresh timestamps, up to nine events total. Seeds 17 and 91 each use
500 cases, maximum list size 30; both campaigns pass. A literal negative control
checks that union resurrects an observed removed element.

The execution proof is closed in `EfficientORSetCertified.lean`:

- `represented_of_mintCertifiedV` proves the store invariant, replay adequacy,
  and causal live-record characterization for every stored version of a
  certified virtual execution. Ordinary executions embed into this semantics.
- `represents_merge` in `EfficientORSetHistory.lean`
  proves preservation by the exact three-way merge; `canonical_of_represents`
  constructs an exact-state replay respecting the public `loOn`.
- `virtualMergeBaseState_represents` covers recursive maximal-common-ancestor
  folds, not just one fork or a single registered GCA.
- `verified` assembles replay adequacy and ordinary finite-set sequential
  correctness. Its axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

The sorting key is proof-local: removes and adds with a future observed
same-element remove come first; adds with no such remove come second. Each phase is
ordered by timestamp. It preserves the causal replacements needed by the
compact representation without strengthening the public `rc`.

No admits or replacement axioms are introduced. Runtime migration is separate
from this Lean certificate and is not claimed by it.

The GC registry supplies a non-collecting exact-state baseline, not an
impossibility result. [Minimum-timestamp GC research](efficient-orset-gc-research.md)
records a checked counterexample to mixing a compacted merge base with an
uncollected branch, general uniform-erasure lemmas, and bounded continuation
tests. A distributed collecting certificate remains staged.
