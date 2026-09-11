# MVR public contract

Status: machine-checked public certificate, registered and release-gated.

The production implementation is now `MVRLive.verified`, with a concrete
finite live set and no grow-only write/overwrite logs. The same sequential
machine and legality predicate are retained. See `mvr-live-state.md` for the
replacement execution and virtual-base proofs; the evidence below records
the original contract repair and its historical grow-only implementation.

Source of truth: the requested multi-value behavior, the public abstract
specification and issuance, then theorem statements and executable controls.

Goal: certify the actual multi-value register for ordinary and virtual
executions. Its query returns the set of surviving values, not internal logs.
The abstract state is a finite set of live tagged values. A write removes its
observed identities and inserts its fresh tagged value; no tombstones remain
in that abstract state. Legality requires unique identities and earlier births
for overwrite targets. Issuance requires the exact observed live identities.

Proved claim: every certified version refines a legal abstract replay;
its live tagged writes are exactly the visibility-maximal writes in its event
set. Concurrent maximal writes survive together, and linear execution yields
the last written value. The sole `rc` orders a write before a later write
naming it in the overwrite payload, not concurrent writes against each other.

Falsifiers: a lost concurrent maximal write, an observed write surviving its
overwriter, a fabricated or omitted overwrite target accepted at issuance,
or an extra value in a linear execution.

Formal oracle: Lean public certificate, same-execution maximal-write theorem,
and named literal/Plausible controls. Test reachable fork/merge histories with
exact overwrite payloads, including repeated values; first detect a deliberate
single-winner mutation. Preserve the existing single-register counterexample
as a rejection of that specification, not of MVR.

Reality oracle: user-stated observed-supersession and concurrent-survival
semantics, with hand-derived examples. No independent MVR runtime is available
in this repository. The formal query uses a mathematical set of values;
runtime representation and correspondence remain outside this increment.

Trusted definitions: event identity, visibility, origin issuance, abstract
write and query meanings. A checked theorem does not replace human review of
these choices.

## Evidence

`MVRContract.lean` proves `issued_overwrite`, `rc_implies_visibility`, and
`overwrite_iff_successor` from exact origin issuance. `version_maximal`
characterizes every stored version, not just a selected fork. `fold_refines`
and `chronological_legal` construct the public finite-set replay;
`verified` supplies ordinary and canonical-virtual correctness. `mvr_correct`
combines public linearizability and causal-maximality for the same execution.
`linear_register` proves equality of the actual value-set query with the
ordinary last-value register on linear mint histories.

These proofs depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The production manifest selects the exact implementation, issuance, `rc`,
specification and state relation, and additionally requires the combined
maximal-write contract and ordinary-register special case. MVR is the
twenty-first production entry. GC remains staged: no log-reclamation theorem
is claimed by the live-set abstraction.

The executable control uses a shared prefix of at most two writes and two
branches of at most three writes each, fresh disjoint timestamp ranges, exact
observed overwrite sets, and one merge at the actual shared ancestor. Expected
survivors are calculated independently from the generated visibility records.
The checks compare tagged implementation contents and the abstract fold with
those maximal writes. Repeated values are generated; these are identities,
not a value-level LWW approximation. This bounded harness does not cover
arbitrary repeated synchronization or virtual-base construction; the general
theorem covers both certified execution modes.

Plausible passed 500 cases at each seed 1, 37, and 2026 (maximum list size 12,
at most eight choices consumed), with no `gaveUp`. The deterministic backstop
passed all 6,561 eight-choice words over three values. Before these campaigns,
the same harness detected a single-winner mutation and shrank it in 16 steps
to `[0,0,0,0,0,0]`; `shrunk_single_winner_wrong` preserves the case. Literal
controls also check observed supersession, an unseen surviving write, repeated
values, the actual value-set query, and rejection of fabricated/omitted targets.
`concurrent_fold_refines` instantiates the general refinement theorem.

The previous `concurrentState_no_sequential_register` remains checked. Its
replay-only companion cannot enter production; `MVR.verified` can. Human
semantic review across all datatypes and independent runtime correspondence
remain open.
