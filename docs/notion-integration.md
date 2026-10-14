# Integration handoff for the paper session

## Current structured and executable implementation

The research commits `1b8ffa3` and `e79fd76` are integrated into `paper1` by
`376bf8d`. The active implementation maintains structural facts and explicit
indexes, with direct receipt and merge. Its renderer and executable query are
proved equal to the reference query on the unchanged honest protocol. This
reuses the existing independent document specification and history witness,
while adding structural transport and executable refinement proof support.
The current [catalogue](notion-catalogue.md) lists the exact endpoints; the
[executable research record](notion-executable-refinement.md) distinguishes the
checked algorithms, compiler/codec boundary and recorded performance limits.
The following original handoff documents the reference proof reused by this
implementation. Publication and final validation for this integration are
recorded below when complete.

## Reference protocol theorem

The typed create/insert/delete/split core now has a Sal same-witness RA theorem
for an explicit honest factory/client protocol. This is a document result over
the actual typed interpreter and renderer, beyond the earlier transaction-set
storage shell. It is not a JavaScript extraction theorem or a production Notion
verification claim.

`NotionCoreProtocol.versions_witness` derives a witness for every registered
version, including old ancestors, and `specification_ra` specializes it to
current heads. The same source-key-sorted **Sal event list** supplies event
coverage, required order, specification visibility, and independent sequential
query admission. Ordinary and canonical recursive-base Sal merges are covered.
Source IDs are payload metadata; globally fresh Sal timestamps are separate.
The theorem takes injective session assignment and actual `Protocol.Reach`,
with no free archive coupling, stored-state equality, or desired-answer premise.

The proof route is now complete inside this typed boundary:

- Honest whole-version issuance derives allocation freshness, complete origin
  providers, active-instance provenance, successful replay, normal slice shape,
  physical partition ownership, and empty inactive titles.
- Actual create/insert/erase/split replay projects to the existing independent
  retained-slot document. Display order is proved separately from RGA interval
  order. Transactions remain atomic groups in the history language.
- The finite carrier's five VCs supply registered state representation with the
  actual `Option` document query. Source execution pairing and the independent
  history proof supply the document meaning of that representation.
- `MRDTClient.issued_update` connects actual client issuance to concrete MRDT
  update/query. Its insert, split, and erase effect theorems give the requested
  local visible effects at supported bounds, including inherited zero gaps.
- Actual repeated split/move label lifecycle derives duplicate-key exclusion.
  Wire-name proofs preserve this result through source-shaped decimal names and
  composite mapping keys, including sessions containing separators.

Factory initialization is an explicit protocol action from the initial source
archive. A local empty carrier does not authorize a global bootstrap. Empty
forks may precede factory creation; `MachinePreallocation.finite_source_participants`
constructs such a real prefix for any finite participant set while leaving source
sessions, clocks, receipts, and archive unchanged. This proves finite availability,
not an arbitrary timed-source-trace rearrangement theorem. Post-factory Sal forks
copy current snapshots, so they are not silently equated with new empty replicas.

The full merge-block/formatting extension remains refuted by three honest-client
traces:

| Editing request | Observed failure |
| --- | --- |
| Concurrent splits of `ab`, then merge to `empty | ba`; bold `ba` | Neither selected character becomes bold. |
| Concurrent splits of `abc`, then merge to `ac | b`; bold `ac` | Also bolds `b` in the other block. |
| Reach `empty | aX` through merges/splits; split `aX` at zero | Produces `empty | X | a`, rather than `empty | empty | aX`. |

These editing merges are distinct from the verified Sal version merges, which
union immutable transaction sets. The fabricated long-run clock counterexample,
raw orphan deliveries, duplicate-session allocators, and inactive-title controls
remain boundary evidence; they do not increase the confirmed demo-bug count.

The external limits should accompany any paper claim. There is no mechanized
JavaScript object/Map, JSON, string/atom, or exception extraction proof for the
pinned demo. Wire-name printing corresponds to positive safe-integer counters;
UTF-16 session comparison and string-iterator atom positions are explicit.
Supported local deletion uses a nonempty in-range interval, rather than every
oversized/clamped JavaScript input. Formatting, merge-block editing, unrestricted
movement, removal, and production-service correspondence are outside the result.

The research contribution to assess for the paper is the issuance-derived core
refinement: whole-run knowledge and actual interval routing justify an independent
editing history, then one common archive connects that history to Sal's ordinary
and recursive same-witness criterion. The three extension failures delimit that
positive result. The protocol-scoped catalogue entry is recorded in
[notion-catalogue.md](notion-catalogue.md), separately from the eighteen
unrestricted production registry contracts. This handoff does not itself edit
the manuscript or establish completed branch integration/publication.

The research checkpoint at `986cc36` passed both maintained gates. The research gate completed
3,515 Lean jobs and all seventeen pinned result groups, including 575 systematic
cases with zero failures. The production gate completed 3,694 Lean jobs, eighteen
exact contracts and their axiom audit, thirteen contract controls, 187 JavaScript
tests, and validation of 569 benchmark records. These checks do not establish
JavaScript extraction or production-service correspondence. Notion remains outside the eighteen-entry `Production.registry`; catalogue
integration adds its distinct protocol entry to the `RefactorLedger` build.

The maintained commands are `scripts/check-notion-research.sh` and
`scripts/check-mrdt-refactor.sh`.
See [the current correspondence overview](notion-core-correspondence.md),
[the research evidence and exact traces](notion-research.md),
[the independent reviews](notion-core-review.md), and
[the pinned source manifest](../experiments/notion-oracle/sources.json).
Only `PRIORITIZED_REMAINING_WORK.md` records development tasks.

## Paper-writing questions and evidence selection

The proposed contribution is a separation theorem in practice: five-VC carrier
reuse establishes storage representation, while issuance-derived interval
invariants and a shared archive establish independent editing meaning on the
same RA witness. Stable identity is justified by a minimal positional replay
counterexample, not by adding the implementation's replay machinery to the
specification. The positive protocol includes recursive merge bases without
assuming an independently correct renderer or a pre-existing archive coupling.

Two research questions sharpen the paper claim. Which semantic identities are
necessary for ordinary positional preparation to survive concurrency? Which
issuance invariants suffice to make a transaction-set carrier refine that
independent semantics? The current result answers both for split/insert/delete;
the three editor-extension failures show why carrier convergence alone cannot
answer them for the full demo.

Include the crossing-delete `a | d` argument, the ID-dependent boundary
insertion pair, an inherited zero-gap local effect, the end-to-end protocol
statement, and one minimized extension failure in the main text. Keep literal
transaction traces, pinned hashes, the full bug catalogue and theorem-chain
links available as supporting evidence. Distinguish actual editor merge-block
requests from Sal version merging in every claim.

The automation claim is specific: existing finite-store VCs, `QueryLift` and
commuting-carrier representation induction are reused. Most new reasoning is
source-specific allocation/provenance, physical partition and inactive-title
invariants, client preparation, transition simulation and operational archive
coupling. The work provides no quantitative author-time or automation-rate
measurement; proof compression is not needed to support this contribution.

Once branch integration and public-claim checks pass, switch to paper writing.
Defer proof compression, wider editor features and JavaScript extraction unless
an explicit paper claim requires them. The maintained validation paragraph above
records the completed research checkpoint; it is not a claim that this new
catalogue/site integration has already passed its checks or been published.

## Catalogue integration and publication (14 October 2026)

The catalogue entry is `docs/notion-catalogue.md`. `NotionCoreLedger` registers
one checked protocol entry in the `RefactorLedger` build; the eighteen uniform
`Production.registry` packages are unchanged. The README and stable theorem
manifest distinguish these scopes. An independent Sol6.1 medium review checked
public claims, exact endpoints and pinned source links.

The integration gates passed: 3,791 Lean jobs in the production gate, eighteen
exact contracts/axiom audits, thirteen contract controls, 187 runtime tests and
569 benchmark records; the research gate passed 3,515 Lean jobs and all seventeen
pinned result groups, including 575 systematic cases with zero failures.

The existing [public reference](https://sal-datatype-reference.fizzyearth10.chatgpt.site/#notion-core)
published version 14 successfully, preserving its public audience. Site source
commit `9d37b4077a186674bdde8bf0b4cdd877273a4a12` adds the Notion entry with pinned
Lean snapshot `986cc36`, three recorded bugs and external correspondence limits.
Validation covered all 957 mathematical expressions, JavaScript syntax and the
rendered entry in Chrome. The site's overview now distinguishes its protocol entry.

The reviewed research branch was fast-forwarded into `paper1` at `b938dec`
and both branches were pushed. Hash checks confirmed all eleven pre-existing
unrelated files were unchanged. The public Notion entry was also checked in
Chrome after deployment. Integration is complete: the next phase is paper
writing, using the claims and evidence above. No additional proof-development
campaign is needed.


## Structured/native integration validation (14 October 2026)

The combined `paper1` gate passed 3,852 Lean build jobs, the existing eighteen
contract audits, 187 runtime tests and 569 benchmark-record validations.
`scripts/check-notion-incremental.sh` built the native executable (6,871 jobs),
audited 107 maintained endpoints with standard logical axioms only, and passed
fresh structured/native oracle smokes. The native smoke covered 20 cases and
1,011 query comparisons, plus typed-wire fixtures, atomic rollback and fork/merge
clock-gap controls. These are fresh regression checks; the published 200-case,
10,008-comparison native performance corpus is retained with its original hashes.

The new `NotionCoreStructuralRuntimeLedger.entry` retains exact theorem types
for structural RA/execution, the original protocol and local effects, native
operation/refinement and honest merge progress, registered-query agreement and
constructive loading from empty. It does not claim an unrestricted native
`Configuration` RA certificate or a universal JSON codec translation theorem.
The single Notion paper row includes this refinement chain rather than counting
it as another abstract datatype. Concrete certificate wrappers are included in
the datatype footprint; the earlier census mistakenly treated them as shared
metatheory because of their directory.
