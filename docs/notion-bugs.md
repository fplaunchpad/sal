# Preserved Notion demo bugs and counterexamples

Five confirmed failures violate ordinary editing behaviour in the pinned public
demo. N-001 to N-003 give a local request the wrong effect; N-004 and N-005
lose text after split and block-merge requests alone. Every setup uses valid `Replica` requests with distinct sessions;
no fabricated payload is needed. The transaction-set adaptation preserves the
failures. These are findings about the educational demo, with no established
correspondence to Notion's production implementation. The verified core's
block merge, specified in [the merge design note](notion-merge-block-design.md),
removes N-001, N-004 and N-005; N-002 and N-003 concern formatting, which the
core does not cover. The records below describe the unmodified demo.

The paper's [Appendix B source](notion-bugs-appendix.tex) gives a self-contained
account of the five traces, their expected and observed results, and the
scope of the formal checks.

The [follow-up correctness campaign](notion-correctness-campaign.md) records the
generated histories. Its complete-exchange search found only variants of N-001
to N-003, including a six-request split/merge setup for N-001. Its search with
persistent replicas and partial causal delivery found N-004 and N-005.

The source snapshot is identified by the seven SHA-256 hashes in
[sources.json](../experiments/notion-oracle/sources.json). The permanent
[regression runner](../experiments/notion-oracle/regressions.mjs) reissues the
requests and asserts the anomaly and disagreement with the independent local
specification. [Saved regression records](../experiments/notion-oracle/regression-observations.jsonl)
retain literal transactions, expected answers and actual answers.

Reproduce all five bugs and the passing formatting control from the repository root:

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

**Verified fix.** Under the corrected merge of
[the merge design note](notion-merge-block-design.md), every slice tree is a
chain (`NotionCoreSliceForest.ChainForest`), so a split's moved node carries
the whole displayed suffix. `NotionCoreMRDTClient.split_effect` proves the
ordinary split effect at every honestly reachable state with merge in the
request set, and the [executable gate](../experiments/notion-merge-design/README.md)
reissues this trace and its six-request variant with the expected result.

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

## N-004: a block merge into a removed block hides the whole document

**Trigger.** Start with three blocks `a · b · c` and two replicas. A merges `c`
into `b` (`a · bc`), splits that block at zero (`a · empty · bc`), and merges
`bc` back into the empty block (`a · bc`). Concurrently, B merges `b` into `a`
(`ab · c`). B receives A's first two requests and sees `empty · abc`. B merges
`abc` into its predecessor, seeing `abc`. B then receives A's last merge.

**Expected:** `abc` remains visible; split and block merge never delete text.
**Actual:** no block is visible. All three characters remain stored, but only in
removed blocks. A reaches the same empty display after receiving B's merges.

A block merge is one transaction: split the source block's text, move it after
the target's last text slice, and remove the source block. The move locates its
target by the end item of a text slice and does not check whether the block that
now holds that slice is alive. When A's last merge reaches B, that slice lies in
a block that a merge has already removed, so the text moves into it.

**Evidence.** Regression name `merge-into-removed-block-loses-document-failure`;
the record keeps all five transactions and the stored characters. Two passing
controls change one ingredient and keep `abc` visible: B omits its first merge,
or B receives A's last merge before issuing its own. Found by the
persistent-replica search of the
[correctness campaign](notion-correctness-campaign.md) and shrunk to five requests;
no global minimality is claimed.

## N-005: a delayed block merge hides a character

**Trigger.** Start with one block `x` and two replicas. A splits at zero
(`empty · x`). Concurrently, B splits at one (`x · empty`) and merges the new
empty block back (`x`). A receives only B's split, sees `empty · empty · x`, and
merges `x` into its predecessor (`empty · x`). B's held merge then arrives.

**Expected:** `x` remains visible. **Actual:** `x` disappears; it is stored only
in a removed block.

The delayed merge would move text into a slice that now lies inside the slice
being moved. The source treats such cyclic moves as deterministic no-ops and
restores the slice, but the same transaction still removes the source block,
which now holds `x`. This trace never moves text into an already removed block,
so the cause is distinct from N-004.

**Evidence.** Regression name `cyclic-merge-removal-hides-character-failure`.
Three passing controls keep `x` visible: the held merge never arrives, A does
not merge, or the held merge arrives before A merges. Both replicas converge on
the same display after exchanging all transactions.

**Classification.** Both are failures of sequential correctness, not of
convergence: replicas that have received the same transactions show the same
display. No sequential order of split and merge requests removes a character,
so no linearization of the requests explains the observed display.

**Formal scope of N-004 and N-005.** Both need the demo's merge-block request,
whose removal step is separate from its move; the verified core's merge has no
such step. `NotionMergeLossCounterexample` models
a merge's move and block removal over a slice forest owned by blocks, with the
source's cycle no-op, and uses the slice trees dumped from the demo just before
each failing update. `merge_into_removed_block_hides_document` and
`cyclic_merge_removal_hides_character` check that the update hides the text
while it stays stored. `flatten_run` proves that every sequential history of
ordinary splits and merges preserves the document's characters in order, so
`document_loss_unexplained` and `character_loss_unexplained` rule out every
sequential explanation. `live_target_control` and `acyclic_target_control` are
positive controls. The model does not mechanise the JavaScript replay or the
split step that precedes the move.

**Verified fix of N-004 and N-005.** Both are one defect: the demo's removal
of the source block is separate from the move. In the corrected merge of
[the merge design note](notion-merge-block-design.md), removal is the move, a
merge into a merged-away target lands in the block that absorbed it
(`NotionCoreSpecMerge.merge_absorbed_target`), and a merge whose target is held
by the source is a no-op that removes nothing
(`NotionCoreSpecMerge.merge_cycle_noop`). `NotionCoreSpecMerge.merge_text_conserved`
proves that a merge preserves the visible text up to permutation, and
`NotionCoreProtocol.specification_ra` gives every honest history with merges a
sequential explanation. The [executable gate](../experiments/notion-merge-design/README.md)
found no text loss in 161,630 archive comparisons (deduplicated within each harness) and passes the N-005 regression.
The N-004 request history also keeps `abc` visible, though under the corrected
merge it no longer reaches the demo's precondition; the gate's litmus history
(b) is the targeted equivalent. A variant that restores independent removal
loses text again.

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
| Creator-aware raw insertion populates an attached block's own title while honest preparation selects the inherited leaf | Creator knowledge and normal tree shape implying inactive-title emptiness; not an honest request failure | `inactive-title-observations.jsonl`; `NotionCoreMachineInactiveTitleBoundary.raw_creator_admitted` and `empty_inactive_failure` |
| Replay origin owner differs from the originally requested block after a concurrent split | Requiring replay owner to equal the issuer-selected block | `client-provenance-observations.jsonl`, honest concurrent splits of `abc` |
| An honest empty-receipt `@1` create sorts before later-received `A1` bootstrap | Bootstrap being the first canonical transaction; its initial instance can be fresh even with a nonempty prefix | `active-instance-observations.jsonl`; `NotionCoreBootstrapProvenance.bootstrap_after_create_control` |
| Alphabet-valid search labels `LL` and `D` decode to the same path | Label injection without the canonical five-bit-chunk invariant | `search-label-observations.jsonl`; these aliases are not generated by honest splitting |

The verified core, including its corrected block merge, has machine-checked
local effects for insert, delete, split and merge at every honestly reachable
state; formatting is outside it. Preserve the
original traces if a repair is explored, and record repaired behaviour under a
separate implementation identity. Outstanding development work remains solely
in `PRIORITIZED_REMAINING_WORK.md`.

The focused deletion controls found no additional demo bug. They preserve a
useful distinction: source range expansion has counter/session order, which
can differ from visible selection order while retaining exactly the same
selected IDs (`delete-group-controls.mjs`). Do not count this ordering
counterexample as an editing failure.
