# Property-testing review

Review of the imported source baseline `14f073e` and its integration on
2026-10-29. The research question remains useful: which concrete defects do
executable proof-obligation checks expose, and where do the implementation,
specification and formal order cease to correspond?

The principal correction is semantic. The generic end-to-end API key
`raLinearizability` checks **causal-history conformance**, preserving every
supplied dependency among integrated records. It adds no concurrent
implementation `rc` edges. Its order and the paper's `lo_E` can be
incomparable; current results state `paperRaVerdict: 'not-checked'`.
Neither a found nor a missing witness is an unconditional paper-RA verdict.
A separate order/interface correspondence argument is required.

The new criterion regression gives a concrete negative control: two
crossed add/remove branches of the correct add-wins OR-set retain both
elements under the paper order, while no full-causal-history witness yields
that result. Other regressions check that `spec.rc` is not consulted,
missing dependencies are dropped and counted, and partial records skip the
check. Skips and dependency gaps must accompany coverage reports; a slice
with dropped edges is not a causally closed paper-model version.

Further findings:

- Law-layer absence of a noncommutation witness in a finite state pool is
  inconclusive, not universal commutation. Historical law verdicts and
  counts need corrected reruns; an empty failure array is insufficient.
  [The library note](ra-pbt.md) records the corrected statuses and evidence.
- Bounded plain-text and marker-specification passes do not establish that
  a library generally satisfies a specification. The two rejected list
  refinements do not rule out all stronger specifications.
- Automerge's expanding end sentinel and emptied-mark A-003 are separate
  specification choices. The two non-expanding-boundary reproductions do
  not depend on the sentinel. Failing anchor-trial counts are not counts of
  implementation defects.
- Notion's transaction-archive union laws do not establish correctness of
  its editing `mergeBlock` request or replay. This campaign tests the demo
  and older `anchor-absorb` block-merge repair, not today's rich-text repair
  or the separately extracted production bundle. Selection-based bold
  matches the catalogue's intent contract; marker completion is needed to
  make the N-004 history interpretable.

The overlapping binary-delta ingestion bug is repaired in both runtime
clients. Six regressions check removal preservation, implicit identifiers,
parent references, duplicate delivery and endpoint validation. The complete
release gate passed: the Lean ledgers and public-contract axiom audit,
13 contract-checker tests, 193 runtime tests and 569 benchmark records.
The dependency-free PBT suite passed all 55 tests. The two added Yjs Lean
counterexamples also build; they check fixed semantic data, not JavaScript
source correspondence.

Validation boundary: the original campaign numbers were preserved as
historical output, not regenerated for the integrated implementation.
Independent source-baseline checks passed the Automerge hashes, 12 spec
tests, 18 regressions and three reproductions, plus 34 Notion regressions
against the hash-checked cache. Exact posted-source executions reproduced
all 15 public snippets on their pinned installations; the
[upstream review](upstream-report-review.md) records the timestamped inventory,
proposed corrections and narrower version coverage. It contains identifying
links and is outside the anonymous artifact.

Final criterion check on the integrated tree:
`node --test ra-pbt/test/criterion.test.js` — **3/3 passed**. No full campaign
was rerun for this final documentation pass.

The manuscript and anonymous package now distinguish law tests, bounded
causal-history searches and direct counterexamples. No upstream report has
been amended; proposed replacements are in the linked upstream review.

The fresh anonymous Lean build passed 3,619 jobs and audited all 260 selected
roots. Its 514 copied Lean sources and two generated Lean files match the
release export byte for byte. The final package passed 21 runner commands,
including package-hash checks, 55 harness tests, 38 packaged runtime tests,
26/12/17 Yjs/Automerge/Loro specification assertions, 28/18/54 corresponding
regressions and 34 Notion regressions. Archive metadata, the manifest and its
unexpected-source rejection control passed. The manuscript and supplement
compile and their changed pages were visually checked. Both the unchanged
manuscript parent and the revised version are 26 pages including references;
their data-availability sections are on page 24, so this is not a claim that
the body has been reduced to 23 pages.
