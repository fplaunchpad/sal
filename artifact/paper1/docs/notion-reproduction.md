# Reproduce the five public Notion demo bugs

This experiment reissues valid editing requests against seven hash-pinned
JavaScript modules from Notion's public educational CRDT demo. It checks three
violations of an independent ordinary local editing contract, two histories in
which split and block-merge requests hide text, and one passing formatting
control. **Exit code 0 means the known bugs reproduced.**

The findings concern the pinned demo. Correspondence to Notion's production
implementation has not been established.

## Requirements and source acquisition

Use Python 3 and Node.js 18 or newer. Source acquisition also requires `curl`.
No Python packages, npm packages, browser,
Lean installation, or service account are needed for this experiment. It was
checked with Python 3.14.6 and Node.js 26.3.1 on 17 October 2026.

The artifact includes these first-party experiment files:

| File | Role |
| --- | --- |
| `scripts/reproduce-notion.py` | Acquires or verifies sources and runs the experiment in a temporary directory |
| `notion/sources.json` | Seven original source URLs and SHA-256 hashes, observed 14 October 2026 |
| `notion/regressions.mjs` | Literal editing histories, assertions, and JSONL reporting |
| `notion/positional-spec.mjs` | Independent visible-list editing contract; imports no demo code |

The seven third-party modules are `replica.js`, `document.js`,
`text-slice-tree.js`, `ids.js`, `rga.js`, `rich-text.js`, and `search-labels.js`.
Their source licence has not been established; they are acquired separately
and are not redistributed in this artifact.

From the extracted artifact root, acquire them once with network access:

```sh
python3 scripts/reproduce-notion.py --download /tmp/sal-notion-demo
```

This command verifies each file against `notion/sources.json` before saving it.
Existing files must already match. A changed upstream source causes failure;
do not update the hashes to make a different snapshot pass. If the original
URLs become unavailable, use a previously retained cache with these exact
hashes. Source acquisition then remains an external prerequisite.

## Run offline

After acquisition, run without network access:

```sh
python3 scripts/reproduce-notion.py \
  --vendor-cache /tmp/sal-notion-demo \
  --output /tmp/sal-notion-regressions.jsonl
```

Choose a new output filename on each run: `--output` refuses to overwrite an
existing file. Omit `--output` to print JSONL to standard output. The runner
verifies all seven hashes before executing the demo modules, copies inputs to
a fresh temporary directory, and removes that directory after execution. It
does not modify the source cache or the supplied experiment files. A missing
or mismatched cache fails without attempting a download. The default cache,
when `--vendor-cache` is omitted, is `vendor/notion` under the artifact root.

Successful execution writes six JSONL records and prints this message to
standard error:

```text
Reproduced 5 known demo bugs and 1 passing control (6 records).
```

Each record includes the literal transactions, the visible state before the
request, the independent expected result, and the observed result. Check the
record names and `specAgreement` fields:

| Record | `specAgreement` | Expected local effect | Observed local effect |
| --- | --- | --- | --- |
| `reversed-bold-selected-effect-failure` (N-002) | `false` | In `empty · ba`, bold both `b` and `a` | Both remain plain |
| `bold-control` | `true` | In `b · a`, bold only `b` | Only `b` becomes bold |
| `bold-outside-selected-block-failure` (N-003) | `false` | In `ac · b`, bold `a` and `c`, leaving `b` plain | All three become bold |
| `split-zero-leaves-suffix-sibling-failure` (N-001) | `false` | Splitting the second block of `empty · aX` at zero yields `empty · empty · aX` | `empty · X · a` |
| `merge-into-removed-block-loses-document-failure` (N-004) | `false` | After all merges arrive, `abc` stays visible | No visible block |
| `cyclic-merge-removal-hides-character-failure` (N-005) | `false` | After the delayed merge arrives, `x` stays visible | `empty` |

Here `empty` denotes an empty block and `·` separates blocks. Bold requests
change character flags, so their `before` and `actual` text strings agree;
inspect each character's `bold` field to see the failure. The runner asserts
both the observed anomaly and disagreement with the independent contract.
Its nearby passing control rules out an experiment that always rejects bold.

## Histories and formal scope

N-001 starts with `a`, splits at zero, and inserts `X` into the first block.
Two peers independently merge the second block and exchange their distinct
transactions. Two peers then split `Xa` at zero and one and exchange. Merging
the split-at-zero block into its predecessor reaches `empty · aX`. The next
local split at zero moves only part of its displayed suffix.

N-002 starts with `ab`, concurrently splits at zero and one, and merges `a`
into `b`. The displayed selection `ba` reverses the underlying text-instance
order, and its annotation interval becomes empty. N-003 starts with `abc`,
concurrently splits at one and two, and merges `c` into `a`. The selected `ac`
spans `b` in text-instance order even though `b` is in another displayed block.
N-004 starts with blocks `a · b · c`. Replica A merges `c` into `b`, splits that
block at zero and merges `bc` back. Replica B concurrently merges `b` into `a`,
receives A's first two requests (`empty · abc`), and merges `abc` into its
predecessor. When A's last merge arrives, B shows no block. A merge locates its
target slice by an identifier rather than by block, and that slice now lies in
a block a merge has removed. N-005 starts with `x`. A splits at zero; B splits
at one and merges the empty block back. A receives only B's split and merges
`x` into its predecessor. B's delayed merge would move a slice inside itself;
the demo skips that move but still removes the block now holding `x`. In both
records, `storedCharacters` shows the hidden text is still stored, the
`controls` field holds displays of passing variants, and the replicas converge.
No sequential order of these split and merge requests removes a character, so
these are failures of sequential correctness, not of convergence.
All setups use valid `Replica` requests with distinct sessions; they do not
require fabricated payloads. The fixtures use ASCII text.

The Lean results have a separate, narrower role:

| Declaration (under `Sal.MRDTs.Instances`) | Machine-checked statement |
| --- | --- |
| `NotionSplitSpec.minimized_split_zero_rejects_ordinary_contract` | The recorded split result differs from the independently defined split-at-zero contract |
| `NotionFormattingCounterexample.two_character_reversal` | A restricted interval-rule model selects nothing for a reversed two-character selection |
| `NotionFormattingCounterexample.noncontiguous_selection_overformats` | That interval-rule model includes an unselected intervening character |
| `NotionFormattingCounterexample.contiguous_selection_control` | A contiguous selection agrees with the ordinary target set and is nonempty |
| `NotionMergeLossCounterexample.merge_into_removed_block_hides_document` | In a restricted merge model on the slice trees dumped before the update, merging into a removed block's slice hides `abc`, which stays stored |
| `NotionMergeLossCounterexample.document_loss_unexplained` | No sequential history of ordinary splits and merges from `a · b · c` produces that display |
| `NotionMergeLossCounterexample.live_target_control` | The same merge into a live block keeps `abc` visible |
| `NotionMergeLossCounterexample.cyclic_merge_removal_hides_character` | The delayed merge's move is skipped as cyclic and its block removal hides `x`, which stays stored |
| `NotionMergeLossCounterexample.character_loss_unexplained` | No sequential history of ordinary splits and merges from `x` produces that display |
| `NotionMergeLossCounterexample.acyclic_target_control` | Moving the same subtree under the live first block keeps `x` visible |

N-004 and N-005 need the editor's merge-block request, which is outside the
verified typed core. Their model keeps a merge's move and block removal, not
its preceding split step.

The formatting model has one text instance, no hidden characters, and no
prior annotations. These theorems do not mechanize the complete JavaScript
setup/replay or establish source extraction. The JavaScript execution is
measured source evidence; the Lean declarations check semantic counterparts.
The experiment does not establish universal source correctness or an
unrestricted local-preparation theorem.
