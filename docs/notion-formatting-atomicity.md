# Per-segment priorities prevent an atomic formatting bridge

The maximal-run planner has a proved immediate selection effect, but its
per-segment Lamport priorities cannot implement each whole selection as one
atomic update. A reachable caller execution produces a visible result that
no atomic ordering of its formatting requests can explain. This settles the
attempted full atomic bridge negatively for the current candidate.

This is an obstruction in the candidate repair, not a sixth reported bug in
the original public demo. The original N-002/N-003 reproductions stay intact.

## The execution

Start with `abcde`, initially plain, and bold `bcd`. Two replicas then have
different legitimate views after concurrent splits and a corrected merge:

| Replica | Displayed selection | Current flags | Requested effect |
| --- | --- | --- | --- |
| A | `abde` in one block; `c` in another | `0110` on `abde` | Add bold throughout `abde` |
| B | `abcde`, selecting `bcd` | `111` on `bcd` | Remove bold throughout `bcd` |

The source instance still orders the characters `abcde`. A's correct maximal-run
plan therefore has two intervals, covering `ab` and `de`; B needs one interval
covering `bcd`. All parts of one selection share one Boolean verdict.

| Interval | Typed source ID | Value |
| --- | --- | --- |
| A's `ab` | `(10,A)` | true |
| B's `bcd` | `(10,B)` | false |
| A's `de` | `(11,A)` | true |

With session A before B, these priorities interleave in the displayed order
of this table. B wins on `b`, while A's second interval wins on `d`. The final
identity-indexed flags for `abcde` are `10011`. The actual nonempty display is
`abde` with flags `1011`, followed by `c` with flag `0`.

Every format selection in the history, including the initial `bcd` mark,
contains both `b` and `d`. Every atomic selection writes the same verdict to
both. Starting plain, every sequential ordering therefore keeps their flags
equal. Empty-block creation, split and merge do not change those identities'
marks. The implementation instead returns `b = false` and `d = true`.
Changing insertion-inheritance rules cannot resolve this example: no further
visible text is inserted after the common bootstrap.

## Checked evidence

| Claim | Evidence |
| --- | --- |
| Requests use actual positional preparation, current queries and executable reference checks | `NotionCoreRichNetwork.issue`, `RichAtomicCounterexample.final_reachable` |
| IDs come from fresh, globally disjoint reservations, including annotations and edit births | `allocation_reachable`, `new_annotations_fresh`, `actual_allocation_unique` |
| Complete format batches are stored and delivered as whole transactions | `NotionCoreRichPayload`, `NotionCoreRichMRDT.observe_carrierFor` |
| The actual finite-store query returns the fracture, with all five identities still visible | `actual_carrier_read`, `actual_visible_identity_control` |
| All atomic format orders fail, even with arbitrary prepared verdicts and structural reshapes | `NotionCoreFormattingAtomicSpec.no_plain_history`, `no_atomic_carrier_history` |
| Carrier convergence still holds for ordinary and canonical recursive-base executions | `NotionCoreRichMRDT.fiveVCs`, `convergence_ordinary`, `convergence_recursive` |

The atomic oracle is an independent necessary semantics for uniform selected
identity updates. The result is not a theorem negating the framework's named
RA predicates, nor a certified Sal version-DAG counterexample. It establishes
that the intended atomic selection bridge cannot hold for this reachable
caller and actual carrier observation. No weaker stamp-aware interval
specification is substituted for that intended contract.

The pinned JavaScript reproduction applies the separate candidate planner
through the source annotation operations and actual clock reservations. Both
corrected merge variants, and both delivery orders, produce `10011`. All six
atomic orders fail under both recomputed-toggle and retained-verdict semantics.
The original toggle compiler, candidate planner and cached source hashes are
unchanged by the runner. The typed witness uses one factory bootstrap in place
of JavaScript's create-plus-insert setup; its ID correspondence is manual,
not a whole-program extraction theorem.

```sh
lake build Sal.MRDTs.Metatheory.NotionFormattingLedger
python3 experiments/notion-formatting/run-atomic-fracture.py --cache /tmp/notion-formatting-sources
```

The complete requests, archives and observations are recorded in
[`atomic-fracture.json`](../experiments/notion-formatting/results/atomic-fracture.json).
An independent rerun exactly reproduced this saved JSON. The original source
controls also passed: 25 positive/negative controls, 21 candidate controls and
304 bounded coverage cases per variant, with N-002/N-003 still reproduced.
The Lean ledger builds in the complete release gate; its audited obstruction
and visible-identity results use only standard Lean axioms.

## Design consequence

Fresh annotation IDs and atomic delivery already hold in this counterexample.
They cannot supply the missing atomic-selection semantics. The most direct
candidate repair is to give every segment of a transaction one shared
arbitration priority, while retaining separate IDs for segment identity and
allocation. That changes the current per-annotation conflict resolution and
requires a new proof; it is not implemented or certified here.

Other choices change the contract: expose individual spans as separate
sequential updates, or restrict concurrent overlapping multi-span requests.
The latter cannot generally be checked locally without additional coordination.
The existing plain-text certificate and immediate exact-selection theorem
remain valid; the full atomic rich-text certificate is not claimed.
