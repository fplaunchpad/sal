# AegisSheet materialised-merge campaign

Differential property-based testing of the candidate materialised three-way
AegisSheet against the current union-merge model. Harness: `model.py` in this
directory. Reproduce with `python3 model.py 1000 1` (three seeds, then the
growth table) and `python3 model.py 1000 7 --restricted-undo`.

## Claim H1

A materialised state (keep tokens, latest-position registers, active cell
versions, active range versions) with the componentwise three-way merge
`(l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)` for sets and last-writer-wins for registers
produces the same observation as the union-merge model on every reachable
version.

Status: validated on honest executions within the campaign scope below;
conjectured in general. Every generated event, after erasing `kills`, passes
a transcription of `applicableB` and `clockedB` (96,069 events over the
three seeds, 0 failures); the transcription is validated on five issuance
fixtures from `AegisSheet.lean`.

Formal oracle: none yet. The Lean target is a `Join` proof for the product
of the components.

Falsifier: a version whose observation differs between the two designs, two
merge topologies over the same event set with different observations, or a
merge whose result differs from timestamp-order replay of the union.

Positive control: the 20 Lean SPOT fixtures from `Instances/AegisSheet.lean`
reproduced by the Python transcription of the reference.

Negative controls: `binary` (merge ignores the ancestor) and `eager` (ranges
re-anchored at removal time) fail on every seed; see the table.

Generator rule: decision D1, an inverse cell write is issued only while its
axes are live (default); `--legacy-undo` restores the old rule.

PBT gate: generator builds reachable states by folding honest operations from
the empty sheet; before-images, overwrite lists, and killed-token lists are
read from the issuing state; fresh identifiers and Lamport timestamps by
construction; 2 to 4 replicas, 3 to 8 rounds, 1 to 3 operations per replica
per round, merge probability 0.7 per round, forced convergence along
different topologies at the end. Undo targets are the replica's own direct
events. Purge operations are not generated.

| seed | executions | versions | ops | registered-ancestor merges | virtual-base merges |
|---|---|---|---|---|---|
| 1 | 1000 | 38,552 | 31,199 | 7,097 | 256 |
| 2 | 1000 | 39,879 | 32,342 | 7,252 | 285 |
| 3 | 1000 | 40,043 | 32,528 | 7,222 | 293 |

Failing executions per design (first failure class in brackets):

| design | seed 1 | seed 2 | seed 3 |
|---|---|---|---|
| keep, named removal | 0 | 0 | 0 |
| keep, clear removal | 35 [FOLD] | 31 [FOLD] | 55 [FOLD] |
| ranges GC, named | 16 [DIFF pos] | 11 [DIFF pos] | 11 [DIFF pos] |
| all-dead GC, named | 9 [DIFF resolved] | 6 [DIFF resolved] | 9 [DIFF resolved] |
| keep, clear, binary merge | 179 [DIFF cells] | 156 [DIFF rows] | 141 [DIFF ranges] |
| ranges GC, clear, eager ranges | 646 [DIFF ranges] | 675 [DIFF ranges] | 684 [DIFF ranges] |

Under the legacy undo rule (revival allowed) the earlier run gave
0/0/0, 27/31/45, 28/23/16, 10/10/7, 186/173/146, 634/642/683.

FOLD means the merge converged and matched the reference, but differed from
the timestamp-order replay of the union event set. Clearing all live tokens
on removal makes a removal and a concurrent keep non-commuting; naming the
killed tokens makes concurrent pairs commute. Causally ordered pairs still
do not commute (a keep then the removal naming its token, or an overwrite
and the version it names), so the design is not all-commuting and needs the
conditioned Join route.

Trusted definitions: the Python reference transcribes `view`,
`directApplicable`, `validUndo`, `inverseFor`, and `resolveRange`. Its
agreement with the Lean model is validated only on the 20 fixtures.

Reality oracle: the Lean model, which is itself validated against Tables 3
and 4 of the AegisSheet paper.

Residual: purge is not modelled; undo of undo is not generated; merges are
only between replica heads.

## Claim H2

The latest position of a removed axis identifier can be dropped once the
identifier is dead and no live range names it.

Status: refuted.

Witnesses, hand-derived and checked by the executable reference:

1. Range resolution reads the dead endpoint's last position. Rows at
   positions 10, 20, 30, range (r0, r2). Removing r0 resolves the range to
   (r1, r2); moving r0 to 25 and then removing it resolves to (r2, r2). The
   live sheets coincide.
2. Eager re-anchoring at removal time disagrees with lazy resolution when a
   concurrent insert lands between the dead endpoint and its successor: the
   reference resolves to the inserted row, eager re-anchoring to r1.
3. Update-wins revival reads the dead row's last position. Branch A either
   moves r0 to 52 and removes it, or only removes it; the two branch states
   have identical live sheets. A concurrent write on branch B revives r0 in
   both merges, at positions 52 and 10 respectively.

Harness confirmation: the `ranges` GC variant fails 16 to 55 executions per
1000 on every seed, including with undo restricted to live axes (seed 7:
55 of 1000). The `all` variant fails range resolution.

Consequence: one position register per known axis identifier must be
retained while a revival is still possible. Under a no-revival undo policy
that is until the removal is causally stable, the condition the current
purge protocol establishes with roster acknowledgements; under the current
model an undo issued after observing the removal can still revive the row,
so stability does not suffice.

## Finding: undo revives a causally later removal

In the current model, undoing a cell write is itself a cell event and thus a
keep token for its row and column. Removing a row at t=4 and then undoing an
earlier write into it at t=5 (legal: own event, target observed) makes the
row live again at its last position with an empty cell. Reproduced by
`undo_revival_witness` in `model.py`. Whether this is intended is a
specification question; Table 4 covers only concurrent removal.

## Claim H3

Purge dissolves into ordinary version deletion once state is materialised.

Status: staged. The harness does not generate purge markers.

## Measured: state size growth

Timestamps stored at the final version of replica 0, mean over 20 executions
with 3 replicas, seed 1, 3 operations per replica per round.

| rounds | ops | reference (union) | materialised (keep, named) |
|---|---|---|---|
| 4 | 23 | 131 | 21 |
| 8 | 46 | 593 | 44 |
| 16 | 92 | 2,902 | 84 |
| 32 | 185 | 13,835 | 180 |

The reference stores each event's whole causal timestamp set, so its size is
quadratic in history length; the materialised state is linear.
