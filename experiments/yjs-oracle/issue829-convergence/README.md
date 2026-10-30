# Issue 829: editing during causal gaps, then testing convergence

Run on 2026-10-30, Node v26.3.1, in the `sal-yjs` worktree at `aadbb5a`.
Packages: `@y/y` 14.0.0-rc.29 (the newest version on npm; the `latest` tag
points at rc.7) and `yjs` 13.6.31, both pinned under `../repro`; the stuck
case below was also run against `yjs` 13.6.33 and `@y/y` rc.7 from a scratch
install. Nothing was pushed or posted upstream. These are bounded randomised
negative results, not proofs of convergence, with one liveness finding.

## Question

yjs/yjs#829 reports that a replica can display a state that no
dependency-closed subset of the updates it has received produces: a delete
set is applied before the insert it was issued after, and in v14 a struct
whose same-client clock predecessor is missing is integrated behind a `Skip`
instead of being parked. The maintainer closed it as expected behaviour:
Yjs promises convergence once every update has arrived, not causal
consistency of intermediate states. The question here is the one that
survives that answer: can a user who edits on top of such a state cause
replicas that have received the same complete update set to disagree?

## Result

No convergence failure was found: in every experiment, replicas that
received the identical complete update set and had empty pending stores
displayed the same text and formatting, re-encoded to states that reload
identically, and reported one state vector. Coverage:

| Experiment | Mechanism targeted | Cases per version |
|---|---|---:|
| `search.mjs` (first campaign) | three gap shapes, 1 to 8 edits on gap-bearing replicas, shuffled, merged and duplicated delivery | 30,000 |
| E1 `e1-state-vector-sync.mjs` | a Skip counted by the state vector would hide the gap from sync | 4 shapes |
| E2 `e2-source-keeps-editing.mjs` | the author keeps editing around the withheld update: every delivery order of six updates with a receiver edit after each step, individually and merged; one to five updates withheld from a longer authored sequence | 17,280 + 10,000 |
| E3 `e3-interacting-gaps.mjs` | two clients holding gaps for each other, a late joiner, five closing protocols including sync only | 50,000 + 5,760 |
| E4 `e4-gc-and-gaps.mjs` | garbage collection, delete sets and reloads around a gap, two gaps of one client | 128 shapes + 10,000 |
| E5 `e5-latent-divergence.mjs` | four replicas, up to twenty edits, a second edit phase after convergence, skip stores and state vectors compared | 30,000 |
| E6 `e6-v2-encoding.mjs` | the v2 update encoding and mixed v1/v2 replicas, diffs carrying Skip structs | 180,000 |
| E7 `e7-loss-and-ghost.mjs` | edits aimed at the inconsistent view, judged for lost and ghost characters and for formatting intent against a causal control | 49,392 + 30,000 |

No character is lost or resurrected either: in E7, every character
someone typed and nobody deleted is in the converged document and every
deleted character is absent, on both versions. What editing an
inconsistent view does cost is formatting intent, measured in E7 against a
causal control of the same edits (see "What the weaker contract costs").

One finding falls outside the convergence oracle and is reported as a
liveness defect of the v14 line: a replica that receives every update
exactly once can be left with a parked update that nothing but a redelivery
or a state-vector sync releases. See "Stuck pending" below.

## Stuck pending on v14 after complete delivery

Found by E3 (one of 5,000 random seeds under mixed delivery and one of 720
delivery orders in its exhaustive part, both gc settings), minimised by the
agent that ran E3 into `e3-stuck-pending-replay.mjs`, and rebuilt from
scratch in `e3-stuck-pending-verify.mjs`, which takes the package directory
as an argument. Three clients, text only, gc off:

1. C types `xyz`; A and B receive it.
2. A types `A` at 0 (a1, client 1 clock 0, right origin `x`) and `a` at 3
   (a2, clock 1, origins `y` and `z`). B receives both.
3. B types `q` at 0 (client 2 clock 0, right origin `A`). A receives it.
4. A, in one transaction, types `k` at the end and `w` at 1 (one update
   `kw`: `k` has origin `z`, `w` has origin `q` and right origin `A`). B
   receives it. A and B show `qwAxyazk`.
5. C receives a2, q, kw and a1, each exactly once, a1 last.

On `@y/y` 14.0.0-rc.29 and rc.7, C shows `Axyazk` with a parked update
whose missing map says client 2 clock 0, which is `q` itself, inside the
parked update. On `yjs` 13.6.31 and 13.6.33 the same sequence converges.
A later edit by A, by B or by C does not release it; C's own edits reach A
and B, while everything A and B type at the start of the document parks at
C, so the replicas drift further apart. Delivering the same updates again,
or one state-vector exchange, converges. Splitting `kw` into two updates,
delivering a1 before kw, or delivering kw before q, converges.

Mechanism, from `src/utils/encoding.js` of rc.29. When `q` arrives it
parks, because its right origin `A` lies in the Skip for client 1. When
`kw` arrives, `k` integrates, which advances client 1's clock past the
parked update's recorded missing entry and triggers a retry of the parked
update; `w` is parked with it. The retry rebuilds the missing map from
scratch: `q` needs client 1 (the Skip), the reader turns to the update's
own client 1 structs and finds `w`, `w` needs `q`, which is already on the
stack, and `addStackToRestSS` records only the client that closed the cycle,
client 2 at its current clock 0. When a1 then arrives, the retry gate
(`ss.clients.has(client) || clock < store.getClock(client)` over the
missing map) sees client 1 in the update but only client 2 in the map,
whose clock is still 0 because `q` is still parked, so nothing fires. In
13.x the parked a2 keeps a client 1 entry in the map, and a1's arrival
triggers the retry. The shape needs the Skip path (origins present,
predecessor missing), a struct that depends on a struct that depends on
the gap, and the two in one update, which any transaction with two
inserts, a paste, or a format with its two markers can produce.

Status under the oracle of this directory: not a divergence, since the
pending store is not empty, and a state-vector sync repairs it. Status
under the documented contract ("updates can be applied in any order, and
all clients sync up once they have received all updates"): a violation,
since every update was applied once and the replica did not sync up. Any
transport that can deliver one client's updates out of order and does not
resend or exchange state vectors during a session leaves the replica
stale until a reconnect.

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-stuck-pending-replay.mjs 14   # exit 1: stayed pending
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-stuck-pending-replay.mjs 13   # exit 0: converged
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-stuck-pending-verify.mjs experiments/yjs-oracle/repro/v14/node_modules/@y/y src/index.js 14
```

The verify script's output on the four packages is in
`e3-stuck-pending-verify.log`.

## What the weaker contract costs: E7

yjs/yjs#829 measured intermediate states against a causal-consistency
model: every displayed state reachable by a dependency-closed subset of
the received operations. Yjs offers a join over structs and delete sets,
buffered only for structural dependencies, and promises convergence once
every update has arrived. The specification was stronger than the
contract, so the report described a mismatch, not a defect against the
contract. E7 (`e7-loss-and-ghost.mjs`, results
`e7-loss-and-ghost-results-v14.json` and `-v13.json`) asks what the weaker
contract costs a user who edits the inconsistent view.

Oracle. Every inserted character is unique, so intent is tracked by
identity. A character someone inserted and nobody deleted must be in the
converged document (else *lost*); a character someone deleted must be
absent (else *ghost*). For formatting, a character and key addressed by
exactly one intent (its insertion attributes, or a single format call that
covered it) should carry that value; a different converged value is a
*format* miss. Each case runs twice with the same edit script: with the gap,
the withheld update arriving after the edits, and as a control with it
arriving before them, so the editing replica sees a causal state. A
format miss present with the gap and absent in the control is attributed
to editing the inconsistent view. The edit menu is aimed at the gap:
insert at the start, end and after the first character, plain and bold;
delete the first, the last and everything; bold, unbold and italicise
everything; replace the first character and the whole text. Exhaustive
part: one or two edits on one gap-bearing replica, optionally one on the
other, relayed between them, under three closures (the withheld update
alone, merged with others, or by state-vector sync only): 2,744 scripts,
8,232 cases per family and gc setting. Random part: 5,000 seeds of one to
six menu edits. Both versions, gc on and off.

Result, identical on the two versions except where noted:

| Family | Cases | Lost | Ghost | Format misses with the gap | In the control | Gap only |
|---|---:|---:|---:|---:|---:|---:|
| plain-gap, exhaustive | 8,232 | 0 | 0 | 21 (v13: 32) | 22 | 0 (v13: 11) |
| delete-set-gap, exhaustive | 8,232 | 0 | 0 | 827 | 21 | 806 |
| insert-before-unformat, exhaustive | 8,232 | 0 | 0 | 1,806 | 24 | 1,788 |
| plain-gap, random | 5,000 | 0 | 0 | 22 | 21 | 2 |
| delete-set-gap, random | 5,000 | 0 | 0 | 458 | 21 or 22 | 438 |
| insert-before-unformat, random | 5,000 | 0 | 0 | 867 | 23 | 850 |

No divergence in any case. The control's misses are the concurrent
boundary behaviours the Yjs note records (a bold inserted next to a
concurrent format boundary); the gap-only misses are the same behaviours
reaching users who were not editing concurrently. The simplest instance,
in the delete-set family: A types `a` bold, then `b` plain, then unbolds
both; B receives the unbold before `b` and sees `a` plain; B bolds the one
character it sees. Both versions converge to `ab` entirely bold, so `b`,
which A typed plain and explicitly unbolded, is bold, and B's bold covers
a character B never saw. The same operation on the causal view gives `a`
bold and `b` plain. The gap turned two causally ordered operations, A's
insert and B's format, into concurrent ones, and the concurrent
resolution (the format's end marker and `b` both follow `a`, ordered by
client id) decided. In the reverse family the receiver sees `aqb` all
bold, where B typed `q` plain after unbolding; a bold insert by the
receiver joins the span it sees instead of creating markers of its own,
and a bold over the three characters creates none where the span already
reads bold, so when the withheld unbold deletes that span's markers the
inserted character, or `q`, comes out plain: 1,788 of 8,232 scripts. The plain gap costs almost
nothing, since no formatting surrounds it.

So the price of the weaker contract is paid in formatting intent, not in
characters, and it is the price of concurrency charged to sequential
edits. Whether that is a defect is the question the maintainer answered
on #829: under Yjs's contract it is not.

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e7-loss-and-ghost.mjs 14 5000
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e7-loss-and-ghost.mjs 13 5000
```

## Audit of the first campaign's harness

Read before the new experiments; each gap found is closed by one of them.

- The author of the withheld update never edits again after the gap
  opens (the edit loop targets the gap-bearing replicas only), so a later
  struct whose origin is the withheld struct, a delete set naming it, and
  markers around it were never delivered into a gap. E2 covers these,
  exhaustively over delivery orders for one author.
- One update is withheld per trial. E2 part 2 withholds one to five of a
  longer authored sequence; E3 makes two clients hold gaps for each other;
  E4 puts two gaps of one client in one store.
- State-vector anti-entropy runs only after every update has been
  delivered directly, so the sync protocol's own recovery of a gap is
  never exercised; a state vector that counted the Skip would have made
  y-protocols sync skip the predecessor for good. E1 checks it (the state
  vector stops at the first Skip, `getStateVector` in `StructStore.js`),
  and E3's sync-only protocol closes every trial by state vectors alone.
- The oracle compares views only. E5 adds a second edit phase after
  convergence and compares re-encoded states, state vectors and the skip
  store; `lib.mjs` gives every later experiment the reloaded fingerprint.
- Only the v1 encoding is used. E6 runs the v2 and mixed paths.
- The pending check reads `store.pendingStructs` and `store.pendingDs`,
  which are the field names in both packages, so it is live.
- Quiescence and pending are checked, but a quiescent exchange that leaves
  a pending store would have been counted as "unresolved" without saying
  that no further delivery could resolve it; E3 counts it separately as
  stuck and probes what releases it.

## E1: state-vector sync across a gap

`e1-state-vector-sync.mjs`. After B integrates `h` behind a Skip for A's
withheld `y`, B's state vector reports client A at clock 0 (v14) or omits
it (v13, where `h` is pending), so a state-vector exchange with A delivers
`y`, and a replica that joins from B alone and then syncs with A converges.
Both versions, gc on and off.

## E2: the author keeps editing around the withheld update

`e2-source-keeps-editing.mjs`, results `e2-source-keeps-editing-results-v14.json`
and `-v13.json`. Part 1: one author, six updates (the withheld `y`; `h`
behind the gap; `k` with origin `y`, which parks on both versions; a delete
set for `h`; bold markers around the whole text; `z` inside the bold run),
delivered to one receiver in each of the 720 orders, individually and as
merged pairs, with one of five deterministic receiver edits or none after
every step and the receiver's edits relayed to a third replica; then the
complete set and anti-entropy. 17,280 cases per version, gc on and off:
0 findings. The transient counts show the mechanism: on v13 the no-edit
policy never displays a non-causal state (`h` or `k` without `y`), on v14 it
does in 240 of 720 orders, and both do once the receiver edits. Part 2: the
author makes 6 to 20 random edits on a shared base, one to five of them
withheld from two receivers that edit on what they have and relay to each
other: 5,000 seeds per gc setting per version, 0 findings.

## E5: latent divergence after convergence

`e5-latent-divergence.mjs`, results `e5-latent-divergence-results-v14.json`
and `-v13.json`. The three families of `search.mjs` with four replicas and
1 to 20 edits on the gap-bearing ones, closed as before; then every replica
makes three more concurrent edits and the set is closed again. Both
closures are judged on views, re-encoded states, state vectors, pending
stores and the v14 skip store. 5,000 seeds per family per gc per version:
0 findings; the skip store is empty after every first closure.

## Reproduce

From the repository root, with `env -u NODE_OPTIONS` because a stale
preload in this environment breaks launches (no machine setting changed):

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/search.mjs 14 5000 1
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/search.mjs 13 5000 1
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e1-state-vector-sync.mjs 14
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e2-source-keeps-editing.mjs 14 5000
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e5-latent-divergence.mjs 14 5000
```

E3, E4 and E6 give their own commands below. `lib.mjs` is the shared
loader and oracle (view, reloaded fingerprint, state vector, pending
stores, state-vector sync).

## First campaign (`search.mjs`)

30,000 trials per installed version, 60,000 distinct version/schedule cases:

- `@y/y` 14.0.0-rc.29: 0 final text/format mismatches.
- `yjs` 13.6.31: 0 final text/format mismatches.
- Both: 0 mismatches after full update-set delivery even before anti-entropy,
  0 remaining pending structs/delete sets, 0 non-quiescent trials.

Three shapes: (1) issue 829's v14 plain-text clock gap, (2) the
unformat/delete-set update arriving before its predecessor insert, and
(3) an insertion arriving before the preceding unformat update. Each shape
with GC on/off and 5,000 deterministic seeds per version; trial `i` uses the
seed `imul(i, 0x9e3779b1) >>> 0`, then xorshift32. Three replicas, 1 to 8
local inserts, deletes and formats on the gap-bearing replicas while the
predecessor is withheld, some relayed; then the identical complete update
set to every replica, including update events generated during integration
and formatting cleanup, in shuffled order, batches of 1 to 3 sometimes
merged, deliveries sometimes duplicated; then all-pairs state-vector
exchange until stable (both phases capped at 12 rounds and checked for
quiescence). The oracle compares visible text and normalised formatting
deltas; a missing RA-linearizability witness is not a divergence. Baseline
assertions pin v14's partial view `bh` with no pending structs against v13's
`b` with a pending struct, plain `a` in the delete-set gap and bold `aqb` in
the reverse gap; `baseline-repros.log` holds the original reproduction
scripts' output (exit 1 is their defect-detection result). Results:
`results-v14-1-5000.json`, `results-v13-1-5000.json`; logs
`campaign-v14.log`, `campaign-v13.log`; the 100-seed smoke outputs predate
the final seed selection and are not counted.

## Limits

Three to four replicas, short documents, single-character structs, text
and formatting only: no embeds, maps, undo, subdocuments, provider message
framing or persistence beyond re-encoding. The stuck-pending case was
found by one seed in 5,000 and one order in 720, so the randomised counts
say little about its frequency under real transports.

## E3: interacting gaps across replicas

Script: `e3-interacting-gaps.mjs` (shared loader `lib.mjs`); results:
`e3-interacting-gaps-results.json`. Run on 2026-10-30 against the same two
installed packages, Node v26.3.1.

Mechanism targeted: two clients hold gaps for each other. Client A's second
struct a2 is delivered to B and to a relay C while a1 is withheld, and B's b2
is delivered to A and C while b1 is withheld, so on v14 each replica integrates
the foreign struct behind a Skip and on v13 parks it. A, B and C then make 1 to
8 edits on top of their partial states (inserts next to the foreign gap-after
characters, deletes and formats spanning them, relayed to one or both other
replicas but never a1 or b1). A fourth replica D joins late by one state-vector
sync from a randomly chosen gap-bearing replica. Closing protocols:
`direct-ab`, `direct-ba` (identical complete update set to every replica,
withheld pair last in that order), `direct-merged` (withheld pair merged into
one update), `direct-mixed` (each withheld update merged with one or two other
updates), all followed by all-pairs state-vector anti-entropy, and `sync-only`
(state-vector anti-entropy only, the withheld updates never delivered directly).
Seeds: trial `i` uses `imul(i, 0x9e3779b1) >>> 0`, 5,000 seeds per
version, gc setting and protocol (50,000 trials per version). Exhaustive part:
all 720 delivery orders of a fixed six-update case (a1, a2, b1, b2, a format
and a delete from C), each replica making one deterministic edit after each
delivery step and relaying it at once, D joining after the third delivery,
closed under four protocols and both gc settings (5,760 runs per version).

Oracle: a failure is counted only when every replica has received the same
complete update set, no replica has pending structs or a pending delete set,
exchange is quiescent, and views or reloaded fingerprints still differ. A
quiescent exchange that leaves pending state is counted separately as stuck.
Controls: a missing insert, a missing format and a reload mismatch are
detected; the no-edit mutual gap shows the version-specific partial state and
converges under every protocol.

Result: 0 failures, 0 stuck, 0 non-quiescent, 0 state-vector mismatches on
both versions, all protocols, both gc settings, random and exhaustive.
The `sync-only` protocol recovers both gaps in at most 2 rounds on both versions.

Transient (v14 only, not a failure under the oracle): after direct delivery of
the identical complete update set, one replica still held pending structs and a
stale view in 1 of 5,000 random seeds under `direct-mixed` (both gc settings,
seed 1272116326) and in 1 of 720 permutations under `direct-ab` (both gc
settings); anti-entropy cleared it in one round. Minimised and replayed with the
bare package in `e3-stuck-pending-replay.mjs`: a replica holding a2 behind a
Skip for a1 receives q (from B, right origin a1), then one update carrying k
(integrates, advancing client 1's clock) and w (origin q), then a1 last. Every
update has arrived exactly once, yet the replica shows `Axyazk` with pending
missing `[[2,0]]` while A and B show `qwAxyazk`. The parked update's missing
map was rebuilt during the retry triggered by k, and the dependency cycle
q -> Skip(a1) -> w -> q is recorded at client 2, so a1's arrival (client 1,
clock unchanged after the Skip fill) triggers no retry. On 13.6.31 the parked
a2 keeps a client 1 entry in the map and the same sequence converges. The state
clears on a duplicate delivery or a state-vector sync; further edits from
either client at the document start do not clear it. The random case is the
merged-tail route to the same condition (462 of 1,568 tail compositions of that
seed leave replica A pending after one pass and converged after a second).

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-interacting-gaps.mjs 14,13 5000 1
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-stuck-pending-replay.mjs 14   # exit 1: stayed pending
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e3-stuck-pending-replay.mjs 13   # exit 0: converged
```

Other transients recorded in the results file: on v14 a gap-bearing replica's
state vector reports the foreign client at the gap start while displaying the
gap-after struct (4,396 of 5,000 seeds), and the late joiner inherits that
state; on v13 the sync encoding forwards pending structs, so the late joiner
parks them too (4,991 of 5,000 seeds).

Limits: three editing replicas plus one late joiner, text and formatting only,
no undo, no GC interplay with a replica left pending (the stuck state was
always cleared before any further garbage collection could matter).

## E4: garbage collection and delete sets around a gap

Script `e4-gc-and-gaps.mjs`, results `e4-gc-and-gaps-results.json` (v14) and
`e4-gc-and-gaps-results-v13.json` (v13). Run on 2026-10-30, Node v26.3.1.

Every shape puts deleted, collected, formatted or re-encoded structs next to a
same-client clock gap on the gap-bearing replica before the gap is filled. On
v14 the gap is a `Skip` struct and the item behind it is visible; on v13 the
item behind the gap sits in `pendingStructs` and is invisible, so the v13
control cannot delete or format it (its hand expectations differ accordingly).
A deleted top-level character becomes an `Item` with `ContentDeleted`; a true
`GC` struct beside the `Skip` needs a nested node whose containing item is
deleted, so both forms are covered.

Mechanisms: (1) the item behind the gap deleted and collected beside the Skip,
then the predecessor arrives alone, merged with later updates, by state-vector
sync from the author, or by sync from a bystander; (2) the author's delete set
covering the gap and the item behind it arriving first, so part of it waits in
`pendingDs` (also re-encoded and reloaded while pending); (3) items whose
origin is the item behind the gap inserted, deleted and collected; (4) formats
spanning the gap position, with and without the unformat that deletes the
markers; (5) two gaps of the same client (clocks 0 and 2 missing, 1 and 3
present) with the present items deleted, filled in both orders, merged, by sync,
and one at a time around a reload; (6) the gap-bearing state re-encoded (v1 and
v2) and loaded into a fresh document before the predecessor arrives; plus the
gap relayed by sync to a bystander that also deletes behind it.

Result: 32 hand-built shapes, each run with gc on and off on both versions (128
shape runs), all converge with one state vector and empty pending stores, and
match their hand-derived expectations. Randomised campaign: 5,000 seeds with
gc:true and 5,000 with gc:false per version (seed `imul(i, 0x9e3779b1) >>> 0`),
20,000 trials, drawing 1 to 5 of the mechanisms above on the gap-bearing replica
or the bystander, then one of seven fill modes, then complete delivery and
anti-entropy: 0 divergences, 0 reload divergences, 0 unresolved pending stores,
0 non-quiescent trials, 0 exceptions. Oracle controls (missing insert, missing
format, missing nested insert, reload fingerprint) pass.

Transients, all resolved by complete delivery: on v14 every trial holds at least
one Skip before the fill and 760 of 10,000 also hold pending structs (a second
gap from a later author struct whose own predecessor was not delivered); a
partially applied author delete set (`pendingDs`) occurred in 1,508 v14 and
1,898 v13 trials; after the fill but before complete delivery 28 v14 and 52 v13
trials still had pending structs from such a second gap. One semantic
difference between the mechanisms, not a convergence failure: a format applied
over the gap position before the fill covers the item behind the gap on v14
(shape `formatSpanningGap_active` converges to `hbx` all bold) but not on v13
(`h` plain, `bx` bold), because v13 never showed that item to the user.

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e4-gc-and-gaps.mjs 14 5000 1 both
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e4-gc-and-gaps.mjs 13 5000 1 both
```

## E6: v2 update encoding and mixed v1/v2 encodings

`e6-v2-encoding.mjs` ports the three families and the local-edit loop of
`search.mjs` (same seed schedule, same edit draws) to the v2 update encoding
and to mixed encodings. Run on 2026-10-30 on the same two installed packages.

Encodings:

- `v2`: every apply, encode, merge and diff uses `applyUpdateV2`,
  `encodeStateAsUpdateV2`, `mergeUpdatesV2` and `diffUpdateV2`; replicas
  listen on `updateV2` only. Both packages emit `updateV2` for local and remote
  transactions (checked by a control). Neither package exports
  `encodeStateVectorV2`, so state vectors use `encodeStateVector`.
- `mixed`: each replica emits and applies in its own format, with at least one
  v1 and one v2 replica among the three (six assignments, drawn per seed);
  updates are converted with `convertUpdateFormatV1ToV2` / `V2ToV1` where the
  formats differ, merged batches take the format of their first element, and
  state-vector anti-entropy alternates v1 and v2 per exchange.

Deliveries of the complete update set:

- `individual`: shuffled, batches of 1 to 3 merged, deliveries sometimes
  duplicated (as `search.mjs`).
- `diff`: each replica receives `diffUpdateV2(merged complete set, its state
  vector)`, sometimes twice.
- `diff-partial`: for eight rounds the diff is taken from a merged random
  subset of the set, whose clock gaps make `diffUpdateV2` write Skip structs
  through the lazy struct writer; then the complete set until quiescent.

Oracle as before (views compared without a sequential specification, pending
stores, quiescence of delivery and anti-entropy, state vectors), plus the
reloaded fingerprint through both encodings (`reloaded`, `reloadedV2` from
`lib.mjs`). A convergence failure is counted only when the complete set was
delivered, no pending structs or delete sets remain, and views or reloaded
fingerprints still differ. Any exception from apply, merge, diff or convert is
a finding. Controls: the oracle rejects differing text and formatting, accepts
complete v2 and converted updates, the Skip detector sees a Skip in a merged
update with a same-client gap in both formats, and a negative control through
the whole pipeline (one replica starved of the delivery phase, no anti-entropy)
is reported as divergent for every family, encoding and delivery. The zero-edit
baseline assertions of `search.mjs` are kept per group.

Result: 360,000 trials (2 versions x 2 encodings x 3 deliveries x 3 families x
2 gc x 5,000 seeds), 0 convergence failures, 0 view divergences, 0 reloaded
fingerprint divergences (either encoding), 0 unresolved pending stores, 0
non-quiescent trials, 0 mismatches before anti-entropy, 0 state-vector
mismatches, 0 exceptions, 0 baseline failures. Of 14,682,336 deliveries,
237,172 carried a Skip struct on the wire: merged batches on the individual
path and `diff-partial` diffs (about 6,000 per version and encoding); a diff of
the merged complete set never carries a Skip, because the complete set has no
clock gaps. This is a bounded randomized negative result on the v2 and mixed
paths, with the same limits as the v1 campaign.

```sh
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e6-v2-encoding.mjs run 14 5000 1 v2,mixed individual,diff,diff-partial out-v14.json
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e6-v2-encoding.mjs run 13 5000 1 v2,mixed individual,diff,diff-partial out-v13.json
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e6-v2-encoding.mjs aggregate e6-v2-encoding-results.json out-v14.json out-v13.json
env -u NODE_OPTIONS node experiments/yjs-oracle/issue829-convergence/e6-v2-encoding.mjs one 14 plain-gap false 2654435761 mixed diff-partial
```

Machine-readable results: `e6-v2-encoding-results.json` (counts per
version, encoding, delivery, family and gc; no findings).
