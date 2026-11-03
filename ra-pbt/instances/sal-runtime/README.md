# Sal runtime instances for the law layer

Adapters that expose the Sal runtime's `orset` and `rga` datatypes
(`runtime/src/datatypes/`) to `ra-pbt/src/laws.js`, together with their
sequential specifications, rc relations and two negative controls. Every
law verdict below was remeasured on 2026-10-29 with seed 1, 150 trials,
`maxSize: 12`, `perTrial: 4`, three replicas and synchronization probability
0.3, using the corrected generation bound and inconclusive verdicts. The
12-step bound includes synchronization steps. `ra-pbt/test/laws.test.js`
asserts the main positive and negative controls.

## Adapters

| Export | Datatype | Operations and `do` | rc |
|---|---|---|---|
| `orsetDatatype` / `orsetInstance` | runtime OR-set | `add(el, tag)`; `rm(el)` removes every instance of `el` in the state it is applied to (the runtime `rm` of the tags `observe` reports) | `(rm_x, add_x)` |
| `orsetObservedTagsDatatype` / `orsetObservedTagsInstance` | runtime OR-set | `rm(el, tags)` kills exactly the tags its issuer observed (the runtime operation shape) | `rm` before `add` when the `rm` names the add's tag |
| `orsetObservedTagsElementRcInstance` | as above | as above | `(rm_x, add_x)` |
| `rgaDatatype` / `rgaInstance` | runtime RGA | `ins(id, anchorId, el)`, `del(id)`; grow-only, merged by union | empty |
| `rgaOrderingRcInstance` | runtime RGA | as above | insertion after x before deletion of x; sibling insertions by ascending id |
| `brokenOrsetDatatype` | negative control | OR-set with merge `(A ∩ B) ∪ (A ∖ L)` | `(rm_x, add_x)` |
| `brokenRgaDatatype` | negative control | list RGA ordering siblings by element, equal elements by arrival | empty |

The raw `do` of each adapter is total, as in the paper: an operation the
runtime would refuse at issuance (a duplicate OR-set tag, an RGA insertion
under a deleted anchor, a second deletion) is given its set-union effect, and
otherwise the runtime's `apply` runs. Honest generation never issues such an
operation; they arise only when a linear extension or a continuation reorders
events.

Sequential specifications: the ordinary set (`setSpec`) and the identified
list (`listSpec`: live ids `B` and allocated ids `I`; `ins` admitted when the
id is fresh and the anchor is the root or live, placed immediately after the
anchor; `del` always admitted). `specCommutes` is hand-derived from them.

## Measured verdicts (corrected checker)

| Property | orset | orset, observed tags | rga | brokenOrset | brokenRga |
|---|---|---|---|---|---|
| eventSetDeterminesState | pass (600) | pass (600) | pass (600) | **fail** (join half) | **fail** |
| vc1MergeComm | pass (600) | pass (600) | pass (600) | **fail** | **fail** |
| vc2MergeInit | pass (600) | pass (600) | pass (600) | **fail** | **fail** |
| vc3LocalRedistribute | pass (495) | pass (502) | pass (492) | pass (495) | **fail** |
| vc4CausalDelta | pass (571) | pass (571) | pass (576) | **fail** | pass (576) |
| vc5Redistribute | pass (321) | pass (364) | pass (383) | pass (321) | **fail** |
| rcNonComm | **inconclusive** (151 checked, 281 unresolved) | pass (443) | pass (449) | **inconclusive** (151 checked, 281 unresolved) | **fail** (1 checked, 37 unresolved before failure) |
| noRcChain | pass (150) | pass (150) | not applicable | pass (150) | not applicable |
| condComm | pass (340) | pass (102) | not applicable | pass (340) | not applicable |
| specNonComm | pass (321) | **fail** | **fail** | pass (321) | not applicable |
| specConformance | pass (600) | pass (600) | pass (600) | pass (600) | not applicable |
| mergeIdempotence | pass (600) | pass (600) | pass (600) | **fail** | **fail** |
| mergeInit | pass (600) | pass (600) | pass (600) | **fail** | **fail** |

Numbers in passing cells count checked candidates, excluding vacuous and
inconclusive candidates. A concrete failure takes precedence over earlier
unresolved candidates. These are sampled checks, not proofs of universal
laws or an exhaustive finite model classification. Historical JSON campaign
results have not been rewritten; older law counts used the previous checker,
whose last generation budget was 13 steps despite `maxSize: 12`.

The finite state pool cannot establish universal commutation from absence
of a non-commutation witness. The ordinary OR-set and its broken-merge
control therefore have an inconclusive `rcNonComm` result. The observed-tag
OR-set and RGA adapters provide separate trusted `semanticCommutes` oracles
derived from their effect algebra; the policy declaration `instance.commutes`
is never used as a semantic certificate. Their reported commutation failures
use those oracles. Specification searches use the default 50000-prefix
bound; none exhausted that bound in these runs. The order-determinacy check
enumerates at most 120 extensions and adds 40 sampled extensions when the
cap is reached; the other state and continuation searches are also bounded.

The additional observed-tags/element-rc run found `rcNonComm` failure after
4 checked candidates, `condComm` failure after 22, and `specNonComm` failure
after 1. The RGA ordering-rc run found `rcNonComm` failure after 2 checked
candidates, `noRcChain` after 37, and `specNonComm` after 1. Both variants
passed the sampled VC1–VC5 and specification-conformance checks.

### Why the failures occur

- **RGA, spec-non-comm.** The grow-only effects commute, so the paper's rc
  for RGA is empty, but the list specification does not commute
  `ins(1, root)` with `del(1)` (delete-then-insert leaves `[1]`), nor two
  insertions at the same anchor (the later-applied one goes first). A
  hand-derived example is `r1: ins(1, root)`, `r2: del(1)` with `r1` visible to
  `r2`. Strict issuance would make the first pair non-commuting, but sibling
  insertions commute under either reading, so the law fails regardless.
  The sampled canonical-state `specConformance` checks pass, with the witness
  order "insertions by ascending id, then deletions".
- **RGA with the ordering rc.** Sibling insertions commute in the
  implementation, so relating them by rc violates rc-non-comm (shrunk: two
  root insertions), and three root insertions form an rc chain.
- **OR-set with observed-tag removals, spec-non-comm.** `rm(b, [])` and
  `add(b, 1)` commute in the implementation (the removal names no tag) but
  not in the set specification. With the element-level rc, the same pair is
  rc-related yet commutes, so rc-non-comm fails; cond-comm fails with
  `o1 = rm(a, [1])`, `o2 = add(a, 1)` and `o3 = rm(a, [])`, which cannot
  absorb the difference.
- **brokenOrset.** Shrunk to a single event `p1: add(b, 1)`:
  `merge(∅, ∅, {1:b}) = ∅` but `merge(∅, {1:b}, ∅) = {1:b}` (VC1); the join of
  `E1 = ∅` and `E2 = {p1}` is `∅`, not `can({p1})`; VC2, merge-init and the
  fast-forward case of merge idempotence fail on the same event. VC4 fails
  on `E = {p2}` with `p2` an addition visible to another. Folds never
  involve merge, so the linear-extension half of `eventSetDeterminesState`
  passes (600 runs). VC3 and VC5 pass on the runs measured, so on this
  defect VC1, VC2 and VC4 are the conditions that discriminate.
- **brokenRga.** The extension-only check shrinks to three events:
  `q1: ins(1, root, b)`, `p1: ins(2, root, b)`, `p2: ins(3, after 2, a)`. The linear extensions
  `q1 p1 p2` and `p1 q1 p2` read `b a b` and `b b a`: equal elements at one
  anchor are ordered by arrival, so concurrent sibling insertions do not
  commute, and rc is empty. The runtime RGA reads `b a b` for both orders.

# End-to-end instances

`endtoend.js` runs the runtime's OR-set and RGA as replicas under the
schedule executor (`src/schedule.js`) and checks every version against a
sequential specification. `ra-pbt/test/endtoend-sal.test.js` holds the
hand-written schedules and the campaigns below.

## Replicas and transfers

| Member | Choice |
|---|---|
| replica | a `DistributedReplica` (`runtime/src/replica.js`) per replica: its own content-addressed store, so delivery is per replica and one-directional; criss-cross merges go through the runtime's virtual merge base |
| identities | the runtime's Lamport mint, stride 100, slot = replica number: RGA ids from `commitGenerated` (observed on ingest, so Lamport timestamps), OR-set tags from `mintTime` (unique, not observed) |
| `sync(to, from)` | one direction of `syncReplicas`: `to` ingests `from`'s delta against `to`'s ancestry through the binary wire codec and merges with `from`'s head; records `from` holds pending are handed on |
| `deliver(to, record)` | the record carries its commit's ancestry closure; it is held until every other authored commit in the closure is in `to`'s store, then the part `to` lacks is ingested and `to` merges with the record's commit |
| integrated | the record's commit is in the ancestry of the head |
| state vector | authored commits per author in the ancestry of the head |
| conservation | OR-set: tags added, tags removed, live `tag=el` entries; RGA: ids inserted, ids deleted, live `id=el` entries |
| opened replicas | none: the runtime builds replicas only empty and catches them up by delta sync (the one stored-state bootstrap, a compaction epoch base, is unavailable for these datatypes). `createReplica(id, { opened: true })` throws, `loadInto` is absent, so the determinism check is skipped, and `generateOptions` sets `openedReplicas = false` |

The part of a closure shipped on delivery must exclude commits the receiver
holds: the wire codec elides the content id of a commit that is the parent of
the next one, and `ingest` deduplicates only commits whose id is on the wire,
so a repeated commit is stored twice. A runtime-only reproduction: replica A
adds a (tag 1); D takes A's delta; A removes a; D takes a second delta
computed against the same have-set as the first and merges with A's head. D
then holds both operations and reads `[a]` while A reads `[]`. `syncReplicas`
computes each delta against the receiver's current ancestry, so it does not
reach this; a transport with overlapping deltas in flight does.

## Specifications and requests

- OR-set: the ordinary set (`setSpec`) over elements. Requests `add el` and
  `rm el` (`rm` kills the tags `observe` reports at the issuer); spec
  operations carry the tag or the observed tags. `localEdit` adds or removes
  the element.
- RGA: requests `insert index el` (anchored at the element displayed at
  `index - 1`, the root at 0) and `delete index`; spec operations
  `ins(id, anchorId, el)` and `del(id)` with the runtime's ids. Views list
  `[id, el]` pairs, so both list specifications are deterministic; reports
  and `localEdit` use the element list.
  - `rgaSpec` (instance `rgaReplicated`): the anchor-retaining list. Every
    allocated id stays in the sequence with a deleted flag; an insertion
    after a deleted anchor is admitted.
  - `rgaLiveAnchorSpec` (instance `rgaLiveAnchorReplicated`): `listSpec`, in
    which the anchor must be live.

## Hand-written schedules

Expected views are derived by hand from the mint rule and the datatypes'
semantics; each test also asserts a view that is not shown or not admitted.

| Schedule | Final view | Negative companion |
|---|---|---|
| OR-set, 2 replicas: `1: add a` (101), deliver 1→2, `1: rm a` (kills 101), `2: add a` (102), exchange | `[a]` at both; the specification admits `[]` and `[a]` | a regression claiming `[]` at replica 2 is rejected |
| OR-set, 3 replicas: `1: add a` (101) to 2 and 3, `2: rm a`, `3: rm a`, `1: add a` (201), deliver 2→3, 3→1 | replica 3 `[]`, replica 1 `[a]`, final `[a]` | `[a, b]` has no witness |
| RGA, 3 replicas: `1: a` (101) to 2 and 3, `2: b` after a (202), `3: c` after a (203), deliver 2→1, 3→1 | `a c b` (ids 101 203 202); admitted: `a c b`, `a b c` | `a b c` is admitted but not shown; `c a b` has no witness |
| RGA, 2 replicas: `1: a` (101), deliver 1→2, `1: delete a`, `2: b` after a (202), exchange | `b` (202) under both specifications | `a b` and `[]` have no witness |
| RGA, 2 replicas: `1: a` (101), `1: b` after a (201), send b, then a, to 2 | replica 2 `[]` and pending, then `a b` | b is not shown without its anchor |
| RGA, 2 replicas: `1: a` (101), deliver 1→2, `1: delete a`, `1: b` at 0 (201), `2: c` at 0 (202), `2: d` after a (302), deliver 1→2 | `c b d` (202 201 302) | the live-anchor list admits only `b c d` |

The last schedule separates the two list specifications. In the live-anchor
list `d` must precede the deletion of `a`, so `c` (before `d` at replica 2)
precedes the deletion, which precedes `b`; `b` is applied last and goes to
the front. The runtime orders root siblings by descending id and shows `c`
(202) before `b` (201). The anchor-retaining list admits `c b d` (order `a`,
delete `a`, `b`, `c`, `d`). Without the deletion both lists admit the
runtime's view.

## Measured campaigns

Seed 1, 100 trials, 12 steps, two or three replicas, witness bound 12, every
version checked (no witness skips, no causal gaps, no anomalies).

| Instance | Delivery | Edits | Deliveries / sends (pending) | Versions checked | Failing trials |
|---|---|---|---|---|---|
| OR-set | whole state | 982 | 654 / 0 | 1636 | 0 |
| OR-set | per record | 922 | 436 / 278 (109) | 1636 | 0 |
| RGA, anchor-retaining | whole state | 986 | 650 / 0 | 1636 | 0 |
| RGA, anchor-retaining | per record | 911 | 436 / 289 (129) | 1636 | 0 |
| RGA, live-anchor | per record | 911 | 436 / 289 (129) | 1636 | 2 (7 RA-linearizability failures, no convergence or conservation failure) |
| broken OR-set | whole state | 982 | 654 / 0 | 1636 | 85 (47 RA-linearizability, 7 convergence, 81 conservation) |

The determinism check is skipped on every edit (no opened replicas). With
whole-state delivery the live-anchor list fails at seed 2 (one trial) and
passes at seeds 1 and 3; the anchor-retaining list passes at seeds 1 to 3 in
both delivery modes.

Negative control: `brokenOrsetReplicated` is the runtime OR-set with the
merge of `brokenOrsetDatatype`. Every convergence and RA-linearizability
signature shrinks to at most four steps; the shortest is
`1: add a`, `2: add b` (two steps, the final sync supplies the transfer):
replica 2 merges replica 1's addition into its own head, keeps only its own
branch and shows `[b]` where the specification admits only `[a, b]`. The
same schedule passes every check on the runtime's own merge.
