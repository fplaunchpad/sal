# AegisSheet materialised-merge campaign

Differential property-based testing of the candidate materialised three-way
AegisSheet against the current union-merge model. Harness: `model.py` in this
directory. Reproduce with `python3 model.py 1000 1` (three seeds, then the
growth table) and `python3 model.py 1000 7 --legacy-undo` (legacy control).
`--global-clock` replaces per-replica Lamport clocks by one global counter.

## Harness

Generator. Reachable states are built by folding honest operations from the
empty sheet. Before-images, overwrite lists, and killed-token lists are read
from the issuing state; identifiers are fresh by construction; timestamps
come from per-replica Lamport clocks (`(counter + 1) * 8 + replica`), so a
stale replica can issue events with timestamps below another replica's
cutoff. Operation kinds: axis insert, move, remove; cell write; range add,
edit, remove; undo of one's own direct event (decision D1: an inverse cell
write is issued only while its axes are live); purge marker by replica 0
under the Lean rule `purgeApplicable` (roster acknowledgements from frontier
evidence, all coordinates dead, covered entries at or below the cutoff, cutoff
= largest observed timestamp). Every generated event, after erasing `kills`,
is checked against a transcription of `applicableB` and `clockedB`.

Topology. 2 to 4 replicas, 3 to 8 rounds, 1 to 3 operations per replica per
round, a merge between two heads with probability 0.7 per round, and with
probability 0.5 one laggard replica that never merges until the forced
convergence phase, which then merges all heads along different topologies.
When a recorded version's event set equals the heads' intersection it is the
ancestor; otherwise the ancestor is the timestamp-order fold of the
intersection.

Checks at every version: observation equality with the reference (DIFF);
equal observations for versions reached by different topologies over one
event set (CONV); equal canonical states for the plain designs (CANON); merge
equal to the timestamp-order replay of the union (FOLD); transcribed
issuance of every generated event (ISSUANCE). A failing execution is counted
for every design that fails in it.

Reference validation: the Python transcription reproduces 20 SPOT fixtures
from `AegisSheet.lean`, 5 issuance fixtures, and 5 purge fixtures from
`AegisSheetGC.lean` (`check_fixtures`).

## Campaign (D1 rule, Lamport clocks, purge generated)

| seed | versions | ops | registered-ancestor merges | virtual-base merges | purges | writes masked by a concurrent marker |
|---|---|---|---|---|---|---|
| 1 | 36,747 | 30,154 | 6,442 | 151 | 41 | 7 |
| 2 | 36,890 | 30,272 | 6,457 | 161 | 28 | 6 |
| 3 | 36,923 | 30,433 | 6,341 | 149 | 40 | 12 |

All 90,859 generated events pass the transcribed `applicableB`.

Failing executions out of 1000 per seed:

| design | seed 1 | seed 2 | seed 3 | first failure class |
|---|---|---|---|---|
| named removal, masks, registers kept, no retirement | 0 | 0 | 0 | |
| same, retire dead tokens and `known` with descendant evidence | 0 | 0 | 0 | |
| same, retire with frontier evidence | 0 | 0 | 0 | |
| same, retire immediately when dead | 0 | 0 | 0 | |
| named removal, purge without masks | 6 | 3 | 3 | DIFF cells: masked concurrent write shown |
| named removal, drop unreferenced dead registers | 38 | 41 | 35 | DIFF pos: revived axis at stale position |
| clearing removal | 227 | 224 | 224 | FOLD: merge differs from replay |
| ancestor ignored (control) | 520 | 511 | 512 | DIFF rows, cells, ranges |
| eager range re-anchoring (control) | 747 | 720 | 746 | DIFF ranges |

## Claims

### H1: the materialised design matches the union model

Status: validated on honest executions within the campaign scope;
conjectured in general. Formal oracle: none yet (S3 and S3b of the plan).

The named-removal design with purge masks and registers kept has no failing
execution. Clearing removal converges and matches the reference but fails
FOLD: a removal that clears all tokens and a concurrent keep do not commute.
Naming the killed tokens makes concurrent pairs commute; causally ordered
pairs still do not, so the design is not all-commuting.

### H2: a dead axis's last position can be dropped

Status: refuted (three hand-derived witnesses checked by the reference:
range resolution, eager re-anchoring, update-wins revival; harness: 35 to 41
failing executions per 1000 for the register-dropping variant). The register
is kept for every identifier ever known; see retirement below. The three
witnesses are machine-checked in
`Sal/MRDTs/Instances/AegisSheetRetentionSPOT.lean`.

### H3: purge dissolves into ordinary version deletion

Status: refuted in the strict form, validated with a mask.

Strict deletion (drop cell versions at dead coordinates, store nothing)
diverges from the reference in 6, 3, and 3 executions per seed. Every case
is a cell write concurrent with a purge marker whose timestamp is at or below
the marker's cutoff: the reference masks it permanently (`cellOverwritten`'s
purge clause), the strict design keeps it, and the write's token revives the
axis so the difference is visible. Keeping a mask of (cutoff, coordinates)
per marker and filtering versions through it at apply and merge reproduces
the reference exactly. The mask is the irreducible purge residue; the
marker's covered entries and acknowledgements are not needed in the
materialised state.

Decision D2 (open): whether a write concurrent with a purge and below its
cutoff should be masked (current model) or kept (update-wins, what the
maskless design does). The harness implements the current model by default.

### Retirement of dead identifiers

Status: validated. Under D1, a dead identifier's token set and `known` entry
can be dropped as soon as it is dead, with no acknowledgement evidence:
immediate, frontier-evidence, and descendant-evidence retirement all have 0
failing executions. The reason is structural: a stale branch on which the
identifier is still live carries its own `known` entry and tokens, and the
merge unions `known` and applies `mvr` to tokens, so a late concurrent keep
revives the identifier correctly. The position register must be kept: it is
read by range resolution and by update-wins revival, and dropping it when no
live range names it fails (a range undo can re-reference the identifier, so
the drop would depend on the order of references, and the harness reports
canonical-state divergence).

Consequently the roster acknowledgement protocol of the current model is not
needed by the materialised design for convergence, for masking, or for
retirement. It remains an issuance policy on when a purge may be requested.

### Legacy control (`--legacy-undo`, seed 7)

With undo revival allowed (the current model's rule), retirement becomes
unsound: immediate retirement fails 53 of 1000 (an undone cell write revives
a retired identifier whose `known` entry is gone, so the reference shows it
live and the materialised state does not), descendant retirement fails 2 of
1000, and the register-dropping variant 69 of 1000. The no-retirement
baseline stays at 0. D1 is load-bearing for retirement and not for the
baseline.

### Finding: undo revives a causally later removal (legacy model)

In the current model, undoing a cell write is a keep token for its row and
column. Removing a row at t=4 and undoing an earlier write into it at t=5 is
legal and revives the row at its last position with an empty cell
(`undo_revival_witness`; machine-checked as `undo_revives_later_removal`).
Excluded by D1.

## Measured: state size growth

Stored items at the final version of replica 0, mean over 20 executions with
3 replicas, seed 1, 3 operations per replica per round. Reference: one per
event plus its `seen` set, overwrite list, and marker payload. Materialised:
tokens, registers, cell and range versions, mask entries, known identifiers.

| rounds | ops | reference | materialised (named, no retirement) | materialised (descendant retirement) |
|---|---|---|---|---|
| 4 | 23 | 122 | 30 | 30 |
| 8 | 44 | 469 | 53 | 53 |
| 16 | 88 | 2,154 | 101 | 99 |
| 32 | 176 | 10,076 | 192 | 187 |

A timestamp-count measurement consistent with quadratic versus linear
scaling; not an asymptotic result.

## Residual

Undo of undo is not generated; merges are only between replica heads; range
endpoints are chosen among live axes at issuance, so a range that names an
already dead identifier at creation is not exercised; a single roster (all
replicas of the execution) is used.
