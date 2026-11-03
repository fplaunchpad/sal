# Proof obligations as properties: the ra-pbt library

## Research question

The framework proves an MRDT RA-linearizable by discharging five
verification conditions, the rc conditions, and sequential conformance. Can
the same conditions, stated as executable properties over generated
executions, find the defects of deployed replicated data types that have no
proof, and agree with the proofs where proofs exist? If so, the verification
framework doubles as a testing framework: one set of conditions, discharged
by Lean for the verified datatypes and checked by search on the others.

Candidate correspondence: a concrete counterexample to a faithfully
implemented property refutes the matching obligation for the tested model.
Checking that correspondence requires auditing the executable predicate,
specification, adapter and state equality. A JavaScript counterpart of a
verified Lean datatype is not automatically verified by the Lean proof.
Unexpected failures on such a control and known defects missed by the
properties are falsifiers to investigate. A bounded pass is only an absence
of counterexamples in the checked configurations.

## Two layers

The **law layer** (`ra-pbt/src/laws.js`) samples, over seeded event sets
built from honest operations, agreement of linear extensions of the
event-indexed `lo_E`, that merge of two branches equals the canonical
state of their union, VC1 to VC5 as stated in the paper, and the rc
conditions where an rc relation is supplied. A failure names the obligation
and gives a shrunk event set. This layer needs only a state-based datatype
(`init`, `apply`, `merge3`, `read`) and an event generator.

The **end-to-end layer** (`ra-pbt/src/checks.js`) generates schedules over
replicas of a running implementation, with deliveries, out-of-order sends
and opened replicas, and checks convergence, causal-history conformance of
sampled versions by an exact witness search over supplied dependencies, local edit
meaning, determinism and conservation. A failure is a replayable schedule
shrunk to a representative. This layer needs an adapter that can create
replicas, issue requests and report the identities the implementation
assigned, deliver updates and expose views.

The end-to-end API retains the historical key `raLinearizability`, but its
criterion metadata explicitly says `causal-history-conformance` and
`paperRaVerdict: 'not-checked'`. It respects every causal dependency among
the integrated records. It neither filters those dependencies by concrete
or specification commutativity nor adds implementation-policy `rc` edges
between concurrent events. `spec.rc` is an unused specification-conflict
annotation, not the implementation policy used by the paper's `lo_E`.

Consequently, the tested order and the paper order can be incomparable.
A found causal-history witness supplies a paper witness only after checking
that it respects the required implementation order and that the event,
query and specification interfaces correspond. A missing witness rejects
the stated causal-history criterion; it is not an unconditional paper-RA
counterexample. A genuine paper-RA rejection requires a separate argument
covering all paper-permitted witnesses. These limits also apply to the
historical `raLinearizability` classifications below.

The correct add-wins OR-set illustrates the distinction. One replica issues
`add x; remove y`, another `add y; remove x`, and their states merge to
`{x,y}`. The paper's order permits both removes before both adds, since the
cross-element visibility pairs commute. The full causal order requires
`add x < remove y` and `add y < remove x`; obtaining `{x,y}` would also
require `remove x < add x` and `remove y < add y`, forming a cycle.
The end-to-end checker therefore rejects this correct paper-style behavior.
Conversely, a causal witness can order concurrent conflicting writes in a
direction forbidden by the implementation's `rc` policy.

Versions with a partly integrated record are skipped and counted in
`witnessSkipsPartial`. Fully integrated records with missing dependencies
are still checked after dropping those edges, with the omissions counted
in `causalGaps`. Such slices are outside the paper's causally closed version
model; their verdicts concern only the restricted dependency history.
Search-bound skips are counted separately in `witnessSkips`.

Different results from the two layers can guide localization, but do not
prove a subsystem correct. In the Notion instance the law carrier's merge
unions transaction archives, whereas the editor's block-merge request emits
operations whose replay can lose text. Passing the former's laws does not
establish correctness of the latter. A law-layer failure is a candidate
countermodel to a named obligation until the predicate and instance's
correspondence to that obligation have been checked.

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

These tables preserve historical campaign output from source baseline
`14f073e`; they are not new runs on the integrated tree. Review found that
the law-layer commutation evaluator could produce incorrect verdicts.
Affected historical campaigns require rerunning. Fresh corrected Sal law
measurements and explicit inconclusive counts are recorded in
[`ra-pbt/instances/sal-runtime/README.md`](../ra-pbt/instances/sal-runtime/README.md).
Treat all
historical law verdicts, counts and explanations below as pre-review
candidates, including the RGA specification-noncommutation diagnosis and
the statement that every verification condition catches a control. They do
not establish a discrepancy in the paper's definitions.

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

The historical run reported `spec-non-comm` on the RGA counterpart and
interpreted it as a mismatch between the paper's empty rc relation and the
list specification. The old output alone does not support this diagnosis.
The corrected Sal run linked above reports the pair verdict using a
separate semantic commutation oracle. The same historical run reported no
sequential-conformance failure. The
shrunk counterexamples of the negative controls have one to three events:
the broken OR-set fails VC1 on a single add, and the broken RGA gives two
readings `b a b` and `b b a` to the two extensions of three insertions.
The historical report claimed that every verification condition caught at
least one control; the corrected table separates detected concrete failures
from unresolved checks.

**End-to-end layer, Sal runtime (seed 1, 100 trials each, 1,636 versions
checked per run).** The runtime's distributed replicas, one store each,
delivered whole states or single records in shuffled order with pending
records held back.

| Instance | Delivery | Failures |
|---|---|---|
| OR-set | whole state, and per record | none |
| RGA, anchor-retaining list specification | whole state, and per record | none |
| RGA, live-anchor list specification | per record | 2 trials, 7 causal-history failures (legacy `raLinearizability`) |
| broken OR-set | whole state | 85 trials; shortest schedule two adds on two replicas |

The live-anchor row is a result about specifications, not about the
runtime: a specification that requires an insertion's anchor to be live
forces the deletion of the anchor after every insertion under it, and the
runtime's ordering of root siblings by identity then has no witness. The
anchor-retaining specification retains the identities needed to interpret
anchors, and under that specification the measured causal-history checks pass. The case is
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
determinism check is skipped there. The law layer searches a pool of states
folded from the configuration's events, exhaustive over event subsets up to
four events and sampled beyond. This is not the universe of datatype states.
An audited concrete state witnessing noncommutation refutes commutation;
finding none in the pool cannot establish universal commutation. Historical
commutation-related verdicts are retained for provenance; the corrected
Sal table is linked above. The
runtime's `apply` is partial (a duplicate tag, an insertion under a dead
anchor) and the adapters fall back to the paper's total effect where the
guard fails, which the paper's definitions require and the runtime never
issues. VC3 to VC5 are checked on random admissible event sets with a
maximal event, and are vacuous on configurations without one. The
end-to-end layer's witness search is exact for its supplied dependency
history within the configured event bound, subject to the specification's
serialization and directed-search contracts. It does not decide the
paper's general implementation-policy criterion.
