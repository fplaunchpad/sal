# Proof obligations as properties: the ra-pbt library

## Research question

The framework proves an MRDT RA-linearizable by discharging five
verification conditions, the rc conditions, and sequential conformance. Can
the same conditions, stated as executable properties over generated
executions, find the defects of deployed replicated data types that have no
proof, and agree with the proofs where proofs exist? If so, the verification
framework doubles as a testing framework: one set of conditions, discharged
by Lean for the verified datatypes and checked by search on the others.

Candidate claim: an implementation that fails any property fails the
corresponding obligation of the framework, and an implementation whose
verified counterpart passes every obligation passes every property. The
falsifiers are a verified datatype failing a property (a bug in the library
or a mismatch between the runtime and its proof) and a known defect that no
property detects.

## Two layers

The **law layer** (`ra-pbt/src/laws.js`) checks, over seeded event sets
built from honest operations, that every linear extension of the visibility
order folds to one state, that merge of two branches equals the canonical
state of their union, VC1 to VC5 as stated in the paper, and the rc
conditions where an rc relation is supplied. A failure names the obligation
and gives a shrunk event set. This layer needs only a state-based datatype
(`init`, `apply`, `merge3`, `read`) and an event generator.

The **end-to-end layer** (`ra-pbt/src/checks.js`) generates schedules over
replicas of a running implementation, with deliveries, out-of-order sends
and opened replicas, and checks convergence, RA-linearizability of every
version by an exact witness search over the causal order, local edit
meaning, determinism and conservation. The witness search asks for a
linear extension of the whole causal order, program order included, as in
the standard definition of RA-linearizability; the paper's criterion
orders only dependent and non-commuting pairs, so the two differ where
commuting operations are program-ordered. A pinned OR-set case shows the
difference: two replicas each add one element and remove the other's
unseen element, the runtime shows both, the paper's order explains it and
no extension of the causal order does. The end-to-end verdict is therefore
causal-order RA-linearizability, bounded as stated under limits; the law
layer evaluates the paper's order. A failure is a replayable schedule
shrunk to a representative. This layer needs an adapter that can create
replicas, issue requests and report the identities the implementation
assigned, deliver updates and expose views.

When the law layer passes and the end-to-end layer fails, the defect is in
issuance or in the protocol rather than in merge, which is where the Notion
block merge failed. When the law layer fails, the counterexample is a direct
countermodel to a named proof obligation.

## Instances

- **Sal runtime, OR-set and RGA** (`ra-pbt/instances/sal-runtime/`): the
  JavaScript counterparts of two verified MRDTs, with honest event
  generators, plain sequential specifications and the paper's rc
  relations. They are the positive control for the law layer.
- **Two broken datatypes** in the same directory: an OR-set whose merge
  forgets concurrently added instances and an RGA whose placement orders by
  element rather than identity. They are the negative control: every
  verification condition must catch at least one of them.
- **Yjs text** (`ra-pbt/instances/yjs/`): the strong list specification
  with marks, the adapter over the pinned library with created and opened
  replicas, and the mechanism classifier. `experiments/yjs-oracle` runs on
  it unchanged in its commands and outputs.

## Results

**Law layer, Sal runtime (seed 1, 150 trials, up to twelve steps over
three replicas; non-vacuous runs in brackets).**

| Property | OR-set | RGA | broken OR-set | broken RGA |
|---|---|---|---|---|
| linear extensions agree, and merge equals the canonical union | pass (600) | pass (600) | fail | fail |
| VC1 merge-comm | pass (600) | pass (600) | fail, 1 event | fail |
| VC2 merge-init | pass (600) | pass (600) | fail | fail |
| VC3 local-redistribute | pass (515) | pass (519) | pass | fail |
| VC4 | pass (580) | pass (580) | fail, 2 events | pass |
| VC5 | pass (279) | pass (368) | pass | fail |
| rc-non-comm | pass (489) | pass (503) | pass | fail |
| no-rc-chain, cond-comm | pass | vacuous (rc empty) | pass | vacuous |
| spec-non-comm | pass (376) | **fail** | pass | vacuous |
| sequential conformance (clause 2 of RA-linearizability) | pass (600) | pass (600) | pass | vacuous |
| merge idempotence, merge-init | pass (600) | pass (600) | fail | fail |

The one failure on a verified datatype is a measured fact about the paper's
definitions, not a defect: the paper sets rc empty for RGA because its
effects commute, while the list specification does not commute an insertion
after x with the deletion of x, nor two insertions after one anchor. The
library reproduces, from random executions alone, the mismatch between the
paper's laws and its RGA that was found earlier by reading the two
definitions side by side, and RGA still passes sequential conformance. The
shrunk counterexamples of the negative controls have one to three events:
the broken OR-set fails VC1 on a single add, and the broken RGA gives two
readings `b a b` and `b b a` to the two extensions of three insertions.
Every verification condition catches at least one control.

**End-to-end layer, Sal runtime (seed 1, 100 trials each, 1,636 versions
checked per run).** The runtime's distributed replicas, one store each,
delivered whole states or single records in shuffled order with pending
records held back.

| Instance | Delivery | Failures |
|---|---|---|
| OR-set | whole state, and per record | none |
| RGA, anchor-retaining list specification | whole state, and per record | none |
| RGA, live-anchor list specification | per record | 2 trials, 7 RA-linearizability failures |
| broken OR-set | whole state | 85 trials; shortest schedule two adds on two replicas |

The live-anchor row is a result about specifications, not about the
runtime: a specification that requires an insertion's anchor to be live
forces the deletion of the anchor after every insertion under it, and the
runtime's ordering of root siblings by identity then has no witness. The
paper's sequence specifications retain the identities needed to interpret
anchors, and under that specification the runtime passes. The case is
pinned by a test.

The adapter also exposed a behaviour of the runtime's wire path, recorded
in `ra-pbt/instances/sal-runtime/README.md` with a reproduction: the codec
omits the content id of a commit whose child follows it in the same delta,
and `ingest` skips only commits whose id is on the wire, so a receiver fed
two deltas computed against the same have-set stores one commit twice and
diverges from the sender. `syncReplicas` never produces such deltas; a
transport with overlapping deltas in flight would. The runtime is
unmodified; the adapter ships only the commits the receiver lacks.

**End-to-end layer, Yjs.** See `docs/yjs-oracle.md`; the results there were
produced by the same code the library now exposes.

## Limits

Declared regressions compare the displayed view after `normalise` with the
raw observed value, so instances whose `normalise` drops information write
their negatives directly. The runtime has no opened replicas, so the
determinism check is skipped there. The law layer tests "for all states" over a pool of states folded from the
configuration's events, exhaustive up to four events and sampled beyond, so
a commutation claim is "no witness found" with the pool size reported. The
runtime's `apply` is partial (a duplicate tag, an insertion under a dead
anchor) and the adapters fall back to the paper's total effect where the
guard fails, which the paper's definitions require and the runtime never
issues. VC3 to VC5 are checked on random admissible event sets with a
maximal event, and are vacuous on configurations without one. The
end-to-end layer's witness search is exact but bounded, as in the Yjs
note.
