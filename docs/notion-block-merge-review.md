# Review of the Notion block-merge extension

Reviewed by Codex, 17 October 2026, 18:46 IST.
Scope: Sal `2d227ed` and paper `bbb1071`. This review does not alter either
implementation or manuscript.

## Findings, in priority order

### 1. The paper incorrectly says the target-selection rule is unchanged

`Sal_paper/implementation.tex:134–135` says the corrected merge “keeps the
demo's rule for choosing where the text goes”. The demo retains an end-item
anchor chosen by the issuer; the corrected merge finds the current holder of
the target block's root and appends at that holder's current end. These can
produce different visible documents even when neither implementation loses
text. The design note itself states the distinction at lines 45–52, but then
calls absorption the demo's own targeting rule at lines 57–58.

Independently replayed counterexample on the pinned sources and the `design`
patch:

1. Start with `ab | cd`.
2. Replica Z merges the second block into the first.
3. Concurrently, replica A splits the first block after `a`.
4. Exchange both complete transactions. The split precedes the merge in replay
   order in both implementations.

The demo displays `a | bcd`; the corrected design displays `acd | b`.
The saved [record](../experiments/notion-merge-design/results/review-target-placement.json)
contains both transactions and both replicas' final displays for each variant.
This is an observed semantic difference, not a refutation of the new Lean
specification.

Suggested replacement: “Our merge appends the source's whole tree to the
current live holder of the target block's root.” Explain the retained block
positions separately. Avoid describing the change as preserving the demo's
placement behaviour.

### 2. Table 1 still has the pre-extension proof sizes

At `Sal_paper/implementation_table.tex:34`, the Notion row remains
`729 / 112 / 73 / 18,082` for implementation/specification/VC/bridge.
An independent run of the existing measurement script on `2d227ed` produces
`766 / 133 / 73 / 20,630`.

Command: `python3 experiments/paper-implementation/measure.py --out
/private/tmp/notion-merge-review-counts`. The fresh audit completed successfully.
The generated current measurement files in the checkout already contain the
new figures but are uncommitted; the paper table has not been updated.
Refresh the maintained paper table and the packaged measurement snapshot
together. The table's bridge footprint includes the replay-based merge
extension even though the structural implementation remains merge-free.

### 3. “161,630 generated histories” has the wrong counting unit

`Sal_paper/implementation.tex:136` calls these generated histories, while
`docs/notion-merge-block-design.md:182` calls them distinct archives.
`ra-check.mjs:48–61` deduplicates archives inside one Node process;
`run.py:150–168` then sums the counts from separate harness processes.
The complete-exchange searches share the same directed split fixtures, so the
sum does not deduplicate archives across harnesses. It also counts intermediate
archives and probe extensions, rather than independent complete histories.

Use “161,630 archive/specification comparisons across the harnesses,
deduplicated within each run”. The reported agreement count remains useful;
it should not imply global uniqueness or independent histories.

### 4. The impossibility result is specific to the current projection

`NotionCoreStructuralRender.SPOT.merge_outside_scope` is a valid counterexample
for the current fact carrier: `merge_no_facts` proves that the projection
discards a merge entirely. The theorem does not show that every structural or
non-replaying implementation must fail to support merges.

The broad explanation in `NotionCoreMergeFree.lean:5–7` and the runtime comments
should say that the **current retained facts omit merge information**, rather
than suggesting that replay is inherently necessary. The manuscript's phrase
“over the retained structure alone” already scopes the claim appropriately.

## Checks and positive results

- Built `NotionCoreLedger` and `NotionCoreStructuralRuntimeLedger` successfully
  (3,544 jobs). The recorded theorem axiom reports contain only the standard
  logical axioms. The replay-based protocol and issuer's merge-effect result
  include merge; the structural carrier and native runtime explicitly retain
  the merge-free restriction.
- Independently reran specification controls, regression gates and litmus
  suites for the demo, corrected design and independent-removal variant.
  The design passed 52 expected final displays and 6,736 local-effect checks,
  with no exceptions or archive/specification disagreements in that suite.
- Reproduced the remaining formatting failures and the corrected split/merge
  results. The independent-removal variant again loses text in its litmus
  suite, confirming that the negative control remains effective.
- No error in the new Lean proof statements was identified in this review.
  The JavaScript comparison remains executable evidence, not a proof of
  JavaScript-to-Lean correspondence.
