# Five reproducible editing failures in Notion's public CRDT demo

This report accompanies the JavaScript [interactive demo](https://www.notion.com/front-static/crdt-demo/index.html?embed=1)
linked from [How Notion handles concurrent editing with CRDTs](https://www.notion.com/blog/how-notion-handles-concurrent-editing-with-crdts).
It reports failures in that public demo; we have not established whether they
occur in Notion's production editor.

**Last reproduced: 23 October 2026.** We freshly downloaded all seven source
modules, checked their SHA-256 hashes against the snapshot first recorded on
14 October, and reproduced all five failures. The served files were unchanged.
See the [source manifest](../../experiments/notion-oracle/sources.json) and
[verification record](verification.json).

All cases use the demo's own `Replica` methods with distinct replica sessions.
They exchange whole transactions in causal order. They do not fabricate
editing payloads or reuse transaction IDs for different edits.

| Case | Observed failure | Reproduction record |
| --- | --- | --- |
| [N-001](#n-001-split-moves-only-part-of-the-displayed-suffix) | Split at zero moves only part of the displayed suffix | [Transactions and slice trees](traces/N-001.json) |
| [N-002](#n-002-bold-does-not-format-the-selected-characters) | Bold changes neither selected character | [Transactions and character flags](traces/N-002.json) |
| [N-003](#n-003-bold-formats-an-unselected-character-in-another-block) | Bold also changes an unselected character in another block | [Transactions and character flags](traces/N-003.json) |
| [N-004](#n-004-five-splitmerge-requests-hide-the-whole-document) | Split/merge requests leave no visible block | [Transactions and stored text](traces/N-004.json) |
| [N-005](#n-005-a-delayed-merge-hides-a-character) | A delayed merge hides the only character | [Transactions and stored text](traces/N-005.json) |

**Suggested starting point: N-005.** It needs one character, two replicas and
four split/merge requests. N-004 and N-005 exercise different paths through the
same move/remove mechanism: a removed target and a cycle no-op respectively.

## Run the reproductions

Requirements: Python 3, Node.js and `curl`. No Lean installation or build is
needed. The cases run the demo modules directly, without the browser UI.

From the repository root:

```sh
# Download and hash-check the public JavaScript files.
python3 artifact/paper1/scripts/reproduce-notion.py --download /tmp/notion-demo-sources

# Run locally and save freshly generated transactions and observations.
python3 artifact/paper1/scripts/reproduce-notion.py \
  --vendor-cache /tmp/notion-demo-sources \
  --output /tmp/notion-demo-results.jsonl
```

Expected summary:

```text
Reproduced 5 known demo bugs and 1 passing control (6 records).
```

Exit success means the reported failures reproduced, not that the demo passed
the editing contracts. The output file must not already exist. The second
command runs offline. If the served source changes, the download command stops
on a hash mismatch instead of silently testing a different version.

The [executable cases](../../experiments/notion-oracle/regressions.mjs)
regenerate requests through the client API and assert the observed failure,
the independently expected result, and nearby successful controls. The JSON
records linked above contain generated transactions and observations; use the
scripts and delivery schedules below to reproduce the client actions.

## Reading the traces

`a | b` means two displayed blocks, and `empty` means an empty block.
Positions are zero-based. A range `[start,end)` includes `start` and excludes
`end`. “Merge a block” means append it to the previous displayed block using
`Replica.mergeBlock(blockId)`. An editing merge is distinct from exchanging
replica updates.

Replicas start with the same seed transactions. “Concurrently” means neither
replica has received the other's requests yet. Session names matter for the
demo's ordering of concurrent IDs; the executable cases fix these names.

## N-001: split moves only part of the displayed suffix

1. Start with a block containing `a`. Session S splits it at zero, then inserts
   `X` into the empty first block: `X | a`.
2. A and B independently merge the second block into the first. Deliver B's
   merge to A.
3. C and D start from A's resulting archive. C splits the first block at zero;
   D concurrently splits it at one. Deliver D's split to C.
4. C merges the block created by its own split into its predecessor. The
   display is now `empty | aX`.
5. C splits the block containing `aX` at zero.

**Expected:** `empty | empty | aX`.
**Observed:** `empty | X | a`.

The requested split must move the entire displayed suffix. Instead, the
implementation moves the subtree containing `a`, leaving the sibling containing
`X` behind. The two merge requests in step 2 have distinct IDs; repeated
delivery is not responsible.

[Saved case](traces/N-001.json), including the before/after slice trees.
The assertion is named `split-zero-leaves-suffix-sibling-failure` in the
executable cases. A [shorter structural variant](../../experiments/notion-correctness/regressions.mjs)
also reproduces the problem after six setup requests, with a passing control
on the same displayed text reached without concurrent restructuring.

## N-002: bold does not format the selected characters

1. Start with `ab`. A splits at zero while B concurrently splits at one.
2. Deliver B's split to A. A sees `empty | b | a`.
3. A merges the last block into its predecessor: `empty | ba`.
4. A toggles bold over both characters of `ba`.

**Expected:** both selected characters become bold.
**Observed:** neither becomes bold.

Displayed character order differs from the order within the underlying text
instance. The generated annotation has equal endpoints and selects nothing.

[Saved case](traces/N-002.json). Assertion:
`reversed-bold-selected-effect-failure`. The [passing control](traces/bold-control.json)
merges the other split block and successfully formats only its selection.

## N-003: bold formats an unselected character in another block

1. Start with `abc`. A splits after `a` while B concurrently splits after `b`.
2. Deliver B's split to A. A sees `a | c | b`.
3. A merges the middle block into its predecessor: `ac | b`.
4. A toggles bold over `ac` only.

**Expected:** `a` and `c` become bold; `b` stays plain.
**Observed:** all three become bold, including `b` in the other block.

The selected display interval corresponds to nonadjacent characters in the
underlying text instance. The emitted annotation includes the intervening `b`.

[Saved case](traces/N-003.json). Assertion:
`bold-outside-selected-block-failure`.

## N-004: five split/merge requests hide the whole document

Start with `a | b | c` at A and B. Keep A's three transactions separate:

1. A merges `c` into `b` (`a | bc`), splits `bc` at zero
   (`a | empty | bc`), then merges `bc` back (`a | bc`). Call these A1, A2, A3.
2. Before receiving any of those transactions, B merges `b` into `a`:
   `ab | c`.
3. Deliver A1 and A2 to B, withholding A3. B sees `empty | abc`.
4. B merges `abc` into its predecessor and sees `abc`.
5. Deliver A3 to B. Finally deliver B's two merges to A.

**Expected:** the three characters remain visible. Split and block merge
requests do not delete text.
**Observed:** neither replica has a visible block. `abc` remains stored in a
removed block.

The delayed move resolves its destination slice inside an already removed
block. It moves the text there and then removes its source block. Nearby
controls retain `abc` when B omits its first merge, or receives A3 before its
last local merge.

[Saved case](traces/N-004.json), including both controls. Assertion:
`merge-into-removed-block-loses-document-failure`.

## N-005: a delayed merge hides a character

1. Start with `x`. A splits at zero: `empty | x`.
2. Concurrently, B splits at one (`x | empty`) and merges its new empty block
   back into the first (`x`). Call these B1 and B2.
3. Deliver B1 to A, withholding B2. A sees `empty | empty | x`.
4. A merges `x` into its predecessor: `empty | x`.
5. Deliver B2 to A. Deliver A's two requests to B to synchronise both replicas.

**Expected:** `x` remains visible.
**Observed:** only an empty block remains; `x` is stored in a removed block.

During replay, the delayed move's target now lies inside the subtree being
moved. The cycle handler skips the move, but the transaction still removes
the block holding `x`. No move in this replay targets an already removed
block, distinguishing this path from N-004.

Three controls retain `x`: omit the delayed delivery, omit A's merge, or
deliver B2 before A's merge.

[Saved case](traces/N-005.json), including the controls. Assertion:
`cyclic-merge-removal-hides-character-failure`.

## Why these are correctness failures

N-001–N-003 give a local request an incorrect effect on the document the client
is displaying. N-004 and N-005 lose visible text after requests that cannot
delete characters in any sequential order. For the text-loss cases, both
replicas agree after exchanging the same transactions: convergence alone
does not catch the failure.

The reproductions run the **unmodified** hash-pinned JavaScript. Experiments
with corrected implementations and formal models are separate and are not
needed to reproduce or assess this report.
