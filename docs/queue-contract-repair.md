# Queue contract repair

Status: completed public Queue certificate, registered and release-gated.

Source of truth: the requested queue behavior, then the abstract contract,
then Lean theorem statements, then executable tests. Historical fold examples
do not decide whether every permitted linearization fails.

## Contract and proof

Prove FIFO behavior for all issuance-certified executions: enqueue appends;
dequeue selects the head visible to its issuer; concurrent dequeues may select
the same tagged element; causally ordered dequeues cannot select it twice;
surviving concurrent enqueues are ordered by timestamp. In a linear execution,
the behavior is ordinary FIFO. The final public proof must include the exact
implementation, issuance, semantic `rc`, legal abstract replay and observations.

The sequential specification is a list of tagged values with enqueue at
the tail and dequeue of the named head. A repeated dequeue of an already
removed target has no effect. Legality must exclude deletion of a different
live element and targets never enqueued. Issuance, not replay position,
must justify that repeated targets come only from concurrent dequeues.
This is not arbitrary deletion from the middle of a list.

Proved witness construction: process removed enqueue/dequeue groups before
the surviving enqueues; each group enqueues one element and performs its
dequeues, then survivors retain their order in the implementation replay
witness. A separate execution invariant proves that actual version states
are timestamp ordered; arbitrary `loOn` witnesses need not be sorted because
the absorber clause can suppress edges. The load-bearing
obligation is compatibility with visibility between conflicting enqueues:
a surviving enqueue cannot causally precede an enqueue subsequently dequeued
as head. `head_predecessor_dequeued` proves this from head issuance, not an
additional history-honesty assumption.

Falsifiers: two visibility-ordered dequeues of the same tag admitted by
issuance; a surviving earlier visible enqueue skipped by a dequeue; or a
reachable history with no legal `loOn`-respecting witness for the proposed
abstract machine.

Formal oracle: Queue's certified-execution issuance theorem, exact fold-content
lemmas and named contract tests. Generated valid fork/merge traces check the
constructed witness; the general legalization proof covers all certified
executions. Ordinary `queue_seq_sound` is retained as a special case.

Reality oracle: the user-specified head-selection, duplicate-concurrency and
timestamp rules; hand-derived literal examples. There is no independent Queue
runtime implementation in this repository to use as a differential oracle.

Trusted definitions: client operation meaning, issuance semantics and event
identity. Existing replay adequacy alone is not the desired FIFO theorem.
Residual: there is no proved or tested independent Queue runtime correspondence.
The repository-wide human semantic-contract audit remains open.

## Mechanized results

`QueueContract.lean` defines `clientSpec` and proves:

- `issued_dequeue_no_visible_dequeue`: the issuer has not observed a dequeue
  of the same target;
- `duplicate_dequeues_concurrent`: two dequeues of the same target are not
  visibility-ordered;
- `queue_version_contents`: every stored version contains exactly the
  enqueued identities with no dequeue in that version's event set;
- `client_linear_fifo`: under linear minting, the candidate abstract machine
  has exactly the ordinary FIFO value sequence.

`QueueLegalization.lean` proves that `legalize` is an exact permutation,
prefix-legal, state-preserving, and `loOn`-respecting for every certified
version. `queue_legal_witness` supplies the public sequential certificate;
`verified` packages the exact implementation, issuance, `rc`, specification,
equality relation and observations for ordinary and virtual executions.

`QueueCorrectness.lean` proves `queue_versions_sorted` and combines public
linearizability, exact surviving identities, timestamp order, and concurrency
of duplicate targets in `queue_correct`, all for the same certified execution.
The ordinary special case and this combined contract are explicit required
obligations in `public-contracts.json`, checked with the public certificate.

These proofs are kernel-checked and use only `propext`, `Classical.choice`,
and `Quot.sound` (the linear theorem does not need choice).

`QueueContractSPOT.lean` checks the proved `legalize` witness against the actual
`qUpdate` and `qMerge`, not just the abstract fold. The generator builds a
shared prefix of at most two operations and two branches of at most three
operations each, with globally fresh timestamps and actual-head dequeues.
An empty-queue dequeue request instead generates an enqueue; there are no
discarded preconditions. Values can repeat. This scope does not include
arbitrary repeated synchronization or virtual merge bases.

The test checks exact event permutation, `loOn` respect, abstract legality,
and equality of the complete tagged queue with the merged implementation.
`lo_eq_loOn` proves that the executable ordering test is the framework
definition, given its executable visibility view.

PBT: 500 cases each at seeds 1, 37, and 2026, maximum sampled-list size 12
(the generator consumes at most eight choices). All 1,500 passed, with no
`gaveUp`. A deterministic backstop checked all 6,561 eight-choice words over
delete/enqueue-value-1/enqueue-value-2; all passed. Before those campaigns,
the same harness detected a deliberately added extra pop, with the minimal
counterexample `[0]` and zero shrinking steps. `extra_pop_rejected` retains
that control. Literal tests also reject a live non-head target, a never-enqueued
target, and an already-deleted target at issuance, while allowing concurrent
duplicate targets and ordinary distinct-target pops.

The executable literal controls using `native_decide` trust Lean's compiler;
the general contract theorems above do not. Tests provide bounded evidence
for the construction, not a substitute for production certification.

Queue is the twentieth production entry. Its exact-state GC entry is a
non-collecting baseline, not a reclamation result. The old `replayAdequate`
companion remains available and is still rejected by the production type gate;
the gate accepts only the completed `verified` package with the selected contract.
