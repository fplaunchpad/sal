# Preserved Notion demo bugs and counterexamples

Three confirmed failures violate ordinary local editing behaviour in the pinned
public demo. Every setup uses valid `Replica` requests with distinct sessions;
no fabricated payload is needed. The transaction-set adaptation preserves the
failures. These are findings about the educational demo, with no established
correspondence to Notion's production implementation.

The source snapshot is identified by the seven SHA-256 hashes in
[sources.json](../experiments/notion-oracle/sources.json). The permanent
[regression runner](../experiments/notion-oracle/regressions.mjs) reissues the
requests and asserts the anomaly and disagreement with the independent local
specification. [Saved regression records](../experiments/notion-oracle/regression-observations.jsonl)
retain literal transactions, expected answers and actual answers.

Reproduce all three bugs and the passing formatting control from the repository root:

```sh
python3 experiments/notion-oracle/run.py --trace regressions.mjs
```

Exit success means the known bugs reproduce; it does not mean they have been
fixed. `scripts/check-notion-research.sh` includes this regression runner.

## N-001: split at zero moves only part of the displayed suffix

**Trigger.** Start with `a`. Split at zero and insert `X` into the empty first
block. Two peers independently merge the second block, then exchange. Two peers
split the resulting `Xa` at zero and one, then exchange. Merge the split-at-zero
block into its predecessor. The visible state is `empty · aX`. Split `aX` at zero.

**Expected:** `empty · empty · aX`. **Actual:** `empty · X · a`.

The split moves a subtree containing `a`, leaving the later sibling branch
containing `X` in the old block. This is a local request after an honestly
reached state. The two merge requests have different transaction IDs; repeated
delivery is not the cause.

**Evidence.** Regression name `split-zero-leaves-suffix-sibling-failure`, with
before/after slice trees. The original generated failure is retained in
[reachable-observations.jsonl](../experiments/notion-oracle/reachable-observations.jsonl).
The [minimized record](../experiments/notion-oracle/minimized-observations.jsonl)
records 70 reissue/shrink attempts and a seven-request setup over seed text `a`.
It is one-minimal under deletion of the fixed requests, not globally minimal.

**Formal scope.** `NotionSplitSpec.minimized_split_zero_rejects_ordinary_contract`
checks that the recorded output disagrees with the independently specified
ordinary split. It does not mechanize the entire JavaScript setup/replay.

## N-002: bold selection changes neither selected character

**Trigger.** Start with `ab`. Concurrently split at zero and one, then exchange,
yielding `empty · b · a`. Merge `a` into `b`, yielding `empty · ba`. Toggle bold
on both characters of `ba`.

**Expected:** both b and a become bold. **Actual:** neither becomes bold.

Displayed selection order differs from the underlying text-instance order.
The generated interval has equal annotation anchors and selects no character.

**Evidence.** Regression name `reversed-bold-selected-effect-failure`. The nearby
`bold-control` merges the other block and successfully bolds only its selection.
Two characters suffice to reverse selection order; no globally minimal request
count is claimed.

**Formal scope.** `NotionFormattingCounterexample.two_character_reversal` checks
the source interval rule on the no-tombstone/no-prior-mark fixture against exact
selection semantics, with a nonempty positive control. Full source extraction
is not implied by this checked restricted model.

## N-003: bold selection changes an unselected character in another block

**Trigger.** Start with `abc`. Concurrently split at one and two, then exchange,
yielding `a · c · b`. Merge `c` into `a`, yielding `ac · b`. Toggle bold on `ac`.

**Expected:** a and c become bold; b stays plain. **Actual:** b also becomes bold.

The implementation emits an interval in original text-instance order containing
the intervening b, although b is displayed in a different block.

**Evidence.** Regression name `bold-outside-selected-block-failure`; the saved
record includes selected and unselected characters' bold flags. This is a small
directed fixture, with no global minimality claim.

**Formal scope.** `NotionFormattingCounterexample.noncontiguous_selection_overformats`
checks the restricted interval-rule counterpart. Its contiguous selection
control rules out constantly formatting every character.

## Preserved counterexamples that are not additional demo bugs

| Finding | What it refutes | Permanent evidence |
| --- | --- | --- |
| Concurrent split/delete has no serialization of unchanged numeric requests | A purely positional concurrent-history specification | `NotionSplitSpec.no_positional_serialization`; directed oracle |
| Fabricated `Z@10` run and `A@11` insertion violate immediate splicing | Transaction-first sorting without complete-run issuance knowledge | `allocation-controls-observations.jsonl`; `NotionRunAllocation.sorted_first_is_insufficient` |
| Two lone-surrogate atoms can display as one emoji | Treating displayed Unicode scalars as the source's editing atoms | `preparation-boundary-observations.jsonl` |
| Raw receipt permits missing dependencies; two allocators sharing a session collide | Unstated causal-closure or session-serialization assumptions | Preparation-boundary and replay-prefix instrumentation records |
| A new transaction can sort below an unrelated stored run item | A global-maximum premise stronger than origin-child dominance | `replay-prefix-instrumentation-observations.jsonl` |
| An existing global item ID is absent from another text instance | Global item knowledge used in place of selected-instance provenance | `payload-provenance-observations.jsonl`; `NotionCorePayloadNetwork.located_presence_control` |
| Two forests have identical parent edges but different sibling enumeration | Parent-edge correspondence without the source's descending sibling order | `NotionCoreParentCoupling.ordering_is_needed_control` |
| Item-provider admission accepts an unseeded START insertion followed by a split with no source slice | Missing block/instance creator provenance in the intermediate typed admission model; not an honest demo request trace | `NotionCoreCreatorNetwork.missing_creator_control` and `unseeded_insertion_excluded` |
| Replay origin owner differs from the originally requested block after a concurrent split | Requiring replay owner to equal the issuer-selected block | `client-provenance-observations.jsonl`, honest concurrent splits of `abc` |
| Alphabet-valid search labels `LL` and `D` decode to the same path | Label injection without the canonical five-bit-chunk invariant | `search-label-observations.jsonl`; these aliases are not generated by honest splitting |

The split/insert/delete-only core has no discovered ordinary-effect bug in the
recorded finite search; its universal proof remains incomplete. Preserve the
original traces if a repair is explored, and record repaired behaviour under a
separate implementation identity. Outstanding development work remains solely
in `PRIORITIZED_REMAINING_WORK.md`.

The focused deletion controls found no additional demo bug. They preserve a
useful distinction: source range expansion has counter/session order, which
can differ from visible selection order while retaining exactly the same
selected IDs (`delete-group-controls.mjs`). Do not count this ordering
counterexample as an editing failure.
