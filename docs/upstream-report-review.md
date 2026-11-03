# Review of posted upstream reports

Internal operational review, 2026-10-29. This file contains identifying
upstream links and must stay outside the anonymous artifact. No remote
issue or comment was edited or posted during this review. Claude's review
request is already recorded in the newest Codex entry of `claude_codex.md`;
the findings below are independent of a future response.

## Corrections applied and verified

Claude applied the agreed amendments in place on 29 October 2026, following
KC's choice of edits rather than follow-up comments. A fresh read of the
six live posts confirmed the corrected wording. No duplicate comment was
posted during this review. The original inventory and proposed replacements
below remain the record of what was reviewed.

- [yjs-828](https://github.com/yjs/yjs/issues/828): updated `2026-10-29T10:06:15Z`.
- [yjs-382-comment](https://github.com/yjs/yjs/issues/382#issuecomment-6490076110): updated `2026-10-29T10:06:21Z`.
- [yjs-385-comment](https://github.com/yjs/yjs/issues/385#issuecomment-6490076549): updated `2026-10-29T10:06:22Z`.
- [automerge-1649](https://github.com/automerge/automerge/issues/1649): updated `2026-10-29T10:06:17Z`.
- [loro-1240](https://github.com/loro-dev/loro/issues/1240): updated `2026-10-29T10:06:20Z`.
- [loro-1009-comment](https://github.com/loro-dev/loro/issues/1009#issuecomment-6491058132): updated `2026-10-29T10:06:23Z`.

The corrected live bodies are mirrored in the three `experiments/*-oracle/repro/upstream-drafts.md` files. `upstream-corrections.md` records the agreed amendments.

## Public-source inventory

Fetched actual issue bodies and all issue comments using read-only
`gh api repos/<owner>/<repo>/issues/<number>` and
`gh api 'repos/<owner>/<repo>/issues/<number>/comments?per_page=100'`.
Fetch completed **2026-10-29 08:39:15 UTC / 14:09:15 IST**. All eight
threads were open at that snapshot. These are the posted texts, not merely
the local drafts.

| Report under review | Posted or updated (UTC, 2026-10-29) | Replies/status at snapshot |
| --- | --- | --- |
| [Yjs #828](https://github.com/yjs/yjs/issues/828), Y-001–Y-003 | body updated 06:58:28 | Open; zero comments |
| [Yjs #829](https://github.com/yjs/yjs/issues/829), Y-007/Y-008 | body updated 06:57:57 | Open; zero comments |
| [Our Yjs #382 comment](https://github.com/yjs/yjs/issues/382#issuecomment-6490076110), Y-005 | 06:53:50 | Open; two comments total, the earlier comment predates ours; no reply to ours |
| [Our Yjs #385 comment](https://github.com/yjs/yjs/issues/385#issuecomment-6490076549), Y-004 | 06:53:51 | Open; our comment is the only comment |
| [Automerge #1649](https://github.com/automerge/automerge/issues/1649), A-001 | 07:35:20 | Open; zero comments |
| [Automerge #1650](https://github.com/automerge/automerge/issues/1650), A-002 | 07:35:21 | Open; zero comments |
| [Our Loro #1009 comment](https://github.com/loro-dev/loro/issues/1009#issuecomment-6491058132), L-001 | 07:49:04 | Open; two comments total, the earlier comment predates ours; no reply to ours |
| [Loro #1240](https://github.com/loro-dev/loro/issues/1240), L-002–L-005 | 07:49:10 | Open; zero comments |

Loro #1009 was opened on 2026-06-11. Its original report already describes
expand-after start-boundary absorption and undo residue on older bindings.
Our comment adds reproduction on 1.17.1, peer-order dependence and a proposed
mechanism. It does not establish that we discovered the original problem;
this review did not rerun its UndoManager example.

## Reproduction and code correspondence

Extracted the fifteen JavaScript fences from the eight actual posts and
ran each unchanged through `node --input-type=module`, with the working
directory set to the matching installed reproduction package in
`/Users/kc/repos/sal-yjs/experiments/*-oracle/repro/` (`v14/` for Yjs).
All fifteen matched the local source-baseline `14f073e` scripts after
discarding comments, blank lines and indentation. No executable-line
differences were found. This was a fresh check on Node **26.3.1**, using
existing installations; no packages were downloaded.

| Posted blocks | Installed pinned library | Fresh result |
| --- | --- | --- |
| Y-001, Y-002, Y-003, Y-004, Y-005, Y-007, `skip-plain` | `@y/y` 14.0.0-rc.29 | Seven print the reported mismatches; each exits 1; Y-007 and skip case converge after the missing update arrives |
| A-001, A-001-link, A-002 | `@automerge/automerge` 3.5.0 | Three print the reported failing output and nearby control; each exits 1 |
| L-001 through L-005 | `loro-crdt` 1.17.1 | Five print the reported failing output; each exits 1; L-001 flips when peer IDs swap |

Exit **1** intentionally means the reported phenomenon reproduced. No
inverted or nonmatching exit predicate was found for these pinned outputs.
Some predicates are narrower than the prose: for example, L-001 detects
either run styling `h`, rather than asserting the peer-order flip, and the
Yjs formatting predicates compare only the first replica with the expected
delta. The fresh printed results supply the missing observations here;
these scripts are reproductions, not exhaustive regression assertions.

Public JSON snapshots and execution outputs are in the temporary directory
`/tmp/sal-upstream-report-review/`, including `execution-results.json`.
The fresh executions above do not independently rerun the posts' additional
13.6.31/13.6.33 version claims or any full random campaign.

## Necessary corrections

1. **Yjs #828: remove the guaranteed shared fix.** The body says “a fix for
   one is a fix for all.” No fix was implemented or tested, so this does not
   follow from reproducing the failures. It also groups boundary ordering
   (#385/Y-004) with marker reuse/deletion (#828 and #382). A marker ownership
   repair alone need not change how a boundary is ordered against a
   concurrent insertion. Suggested replacement:

   > I grouped these three examples because they all involve formatting
   > boundaries whose reuse or cleanup changes another edit's formatting.
   > They may require separate fixes. #382 is related; #385 additionally
   > involves ordering a concurrent insertion against a format boundary.
   > These reproductions do not establish that one repair resolves them all.

   Also replace the “same cause” cross-references in our #382 and #385
   comments with this narrower distinction. Keep the measured examples.

2. **Loro #1240: the deleted-highlight variant also fails.** Shape 1 says
   the variant deleting the only highlighted character “is correct.” Fresh
   1.17.1 execution of insert `a`, highlight it with `hl/both`, delete `a`,
   insert `X` yields `[{"insert":"X","attributes":{"hl":true}}]`.
   The matching `bold/after` variant gives plain `X`. Suggested replacement:

   > The bold/expand-after control is correct. With highlight/expand-both,
   > deleting the only highlighted character and typing into the empty text
   > also produces a highlighted character.

3. **Automerge #1649: the controls change more than a counter.** The first
   control retains `x`; the second omits `z`. Consequently “differs only in
   a counter” and “both orders give the control's document” are inaccurate
   for the complete documents shown. Suggested replacement:

   > The additional delete or insert raises the operation counter and also
   > changes the text. Under the stated anchor interpretation, `h` should
   > remain plain in the first example and `x` should remain outside the
   > link in the second; these formatting expectations agree across the
   > compared traces, although their full text differs.

   A stronger, text-preserving counter control is available: using
   `doc.bump = true` outside the text object before the relevant mark or
   insert gives the same flip on 3.5.0. Fresh tests found `h` plain without
   the marker replica's metadata bump and bold with it; `x` outside the link
   without the inserter's bump and linked with it. No remote script has
   been replaced.

4. **Yjs #828: clarify what “both orders” means.** Shape 3's literal
   `insert(3, 'z', ...)` cannot be reissued unchanged after deletion leaves
   only `wv`. The sequential comparison uses decoded character identities
   and retained anchors, not unchanged numeric API positions. Suggested
   addition:

   > The sequential comparison interprets each edit using the character
   > identities/anchors recorded when issued. It does not reissue the same
   > numeric indices against a changed document. For example, the insert
   > after `b` remains anchored there after `b` becomes a tombstone.

## Scope clarifications and optional improvements

- **Yjs #829 already asks the right contract question.** It explicitly
  acknowledges convergence after all updates arrive and asks whether
  intermediate displayed versions must be causally closed. Neither fresh
  execution disproves the stated eventual-convergence guarantee. Keep the
  finding conditional on the stronger observation contract. The named
  provider/reconnection scenarios are possible delivery patterns, not
  reproduced failures of those providers. Its list of causal prefixes
  includes states requiring the withheld update; it is not literally a
  list of subsets of updates already received.
- **Automerge #1649/#1650 do not contain the custom expanding end-sentinel
  trace or A-003.** No withdrawal of those reports is needed on that basis.
  The boundary examples avoid that unspecified case. Ask maintainers to
  confirm whether expand governs concurrent inserts; the observed outputs
  remain valid even if the requested semantic contract is declined.
- **Loro #1240 shape 3 depends on a display-based insertion contract.** Two
  views can be equal while their hidden style anchors differ. The output
  difference is measured, but equal display alone does not prove the API
  promises equal subsequent edits. Likewise, the “both neighbours share a
  value” case should be stated explicitly in the proposed per-key contract.
  Present that expectation for maintainer confirmation.
- **Loro #1009: preserve attribution and scope.** Our concrete peer-swap
  example is expand-after at the start; its claim about every expand type
  rests on the local campaign, not this one posted code block. Distinguish
  that broader evidence from the earlier reporter's undo finding.
- **Bound the summary claims.** Loro #1240's final “Fugue list satisfies”
  sentence should say no checked plain-text version lacked a strong-list
  witness in 800 trials. Automerge #1649's comparison with Yjs should say
  the tested #828 shapes passed, rather than every possible concurrent
  formatting shape. The law-evaluator corrections do not invalidate these
  plain-library executions; no posted report claims a law-layer proof.
- **Optional predicate hardening:** parse deltas and assert exact outputs
  for both replicas and controls. This would make later reruns reject
  divergence or changed span grouping instead of relying on regex matches.

The appropriate next step is review of these concrete replacement texts,
including Claude's requested independent assessment, before any upstream
amendment. This file records proposals only; no upstream correction has
been applied.
