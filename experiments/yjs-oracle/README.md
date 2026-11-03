# Yjs Y.Text oracle: replica layer and measured facts

Everything here is measured on the pinned release yjs@13.6.31 under Node
v26.3.1. Nothing in this directory is a proof.

## Running

```
(cd ../../ra-pbt/instances/yjs && npm install --ignore-scripts)   # once
node ../../ra-pbt/instances/yjs/verify-sources.js   # checks version, lockfile resolved/integrity, SHA-256 of yjs.mjs and package.json
node facts.mjs            # runs the facts below, writes results/facts.json, exits non-zero on a failed assertion
```

Apart from the install, no network access is used. `verifySources()`
(exported from `ra-pbt/instances/yjs/verify-sources.js`) throws on any
mismatch with the instance's `sources.json`; runners call it before and after
execution. Node may print a localStorage
ExperimentalWarning; it is harmless.

## Replica contract (`ra-pbt/instances/yjs/adapter.js`)

`new Replica(clientID)` wraps one `Y.Doc` with that `clientID`, `gc = false`
and the text `doc.getText('t')`. An id is a pair `[client, clock]`;
characters are UTF-16 code units.

| Method | Result |
| --- | --- |
| `insert(index, text, attrs?)` | op record with `chars: [{ id, ch, origin, rightOrigin, attrs, shown, yOrigin, yRightOrigin }]` |
| `delete(index, len)` | op record with `deleted: [id]` (visible characters removed, in order) |
| `format(index, len, attrs)` | op record with `range: { left, right, covered }` |
| `deliver(op)` | applies `op.update`; returns `{ pending, emitted }` |
| `syncFrom(other)` | applies the state `other` has and this replica lacks; same result shape |
| `stateVector()` | `{ client: clock }` |
| `hasPending()` | `doc.store.pendingStructs !== null` |
| `visible()` | `[{ ch, attrs }]` expanded from `text.toDelta()` |
| `visibleWithIds()` | `visible()` zipped with ids from the item walk; throws if characters disagree |
| `items()` | full item list: `{ id, len, kind, str?, key?, value?, deleted, origin, rightOrigin }` |
| `string()`, `snapshot()` | `text.toString()`; `{ visible, items, pending, sv }` |

Every op record has `replica`, `kind`, `request` (the index-level request as
issued), `svBefore`, `update` (base64 of the transaction's update), `markers`
(format items the op created, `{ id, key, value, deleted }`) and
`deletedMarkers` (previously live format items the op deleted).

- `chars[i].origin` / `rightOrigin` are the visible character neighbours at
  issue time (for i > 0 the origin is the previous inserted character).
  `yOrigin` / `yRightOrigin` are what Yjs encoded, which may be a format
  marker or a tombstone.
- `chars[i].attrs` is the attributes object passed. When attrs are omitted
  Yjs copies the attributes in effect at the left neighbour (fact b), so
  `attrs` is then the displayed attributes of the character right after the
  op. `shown` is always the displayed value.
- `deliver` and `syncFrom` report `emitted`: local updates Yjs produced while
  integrating a remote change (its formatting cleanup runs in a follow-up
  local transaction that can delete markers). These must be propagated like
  any other update. Fact k below triggers one on a created receiver.
- Attribute objects are copied before they reach Yjs, which otherwise writes
  negated keys (`{bold: null}`) into the caller's object.

## Measured facts

Notation: `*` marks bold; ids are `[client, clock]`; base text by client 1.

| Fact | Scenario | Observed | Negative companion (holds) |
| --- | --- | --- | --- |
| a | `abc`, `format(1,1,{bold:true})` | items a=[1,0], bold:true=[1,3], b=[1,1], bold:null=[1,4], c=[1,2] | markers are not deleted |
| b (explicit `{}`) | `a b* c`, insert X at 1, 2, 3; `{bold:true}` at 1 | `a X b* c`, `a b* X c`, `a b* c X`; `a X* b* c` | X at 2 is not bold |
| b (attrs omitted) | `a b* c`, insert X at 0, 1, 2, 3 | `X a b* c`, `a X b* c`, `a b* X* c`, `a b* c X` | X at 2 is not plain |
| c | `abc`; 4 bolds [0,3) ‖ 5 inserts X at 1 | both `a* X* b* c*` | X is not plain |
| d | `a b* c`; 10 bolds [0,2) ‖ 11 unbolds [1,3) | both `a* b* c*` | differs from both sequential outcomes `a* b c` and `a* b* c` |
| e | second of two updates delivered first | pending, text `''`; after the first: `abc`, not pending | text is not `abc` or `c` while pending |
| f | `a b* c`, `delete(0,2)` | `c`, markers [1,3] and [1,4] tombstoned | `c` is not bold |
| g | `abc`; 6 deletes b ‖ 7 bolds [0,3) | both `a* c*` | not `a* c`, `a c*`, nor b resurrected |
| h (observation) | `abc` with b deleted; 8 bolds [0,2) ‖ 9 inserts X at 1 | both `a* X* c*` (matches the interval reading) | X is not plain |
| i | `a b* c`; client 12 created (text type held before the state arrives), client 13 opened (state applied first); both insert X at 2 with attrs omitted | created `a b* X* c`, opened `a b* X c` | the two replicas do not agree |
| j | `a* b* c`; created and opened replicas both delete [1,2) | created `a* c`, opened `a* c*` (its delete removes marker bold:null [1,4]) | created deletes no marker |
| k | two concurrent identical bolds of b merged (4 live markers); a delete of b delivered to both kinds | created receiver emits 1 cleanup update and keeps 1 live marker; opened receiver emits 0 and keeps 4; both display `a c` | the displays agree |

Fact d mechanism (from the recorded item walks): client 10's bold inserts
bold:true [10,0] before a and deletes the now-redundant bold:true [1,3],
relying on the existing bold:null [1,4] to end the span. Client 11's unbold
creates no marker at all; it deletes both [1,3] and [1,4]. Merged, [10,0] is
the only live marker and nothing ends it, so `c`, which neither operation
ranged over, becomes bold.

In fact h, X's encoded origin is the tombstone b ([1,1]); its visible-neighbour
origin is a ([1,0]).

Facts i to k concern a root-level text type obtained after the document state
was applied, the class Y-006. `opened-document.mjs` runs the family in full
(eight scenarios with the list edit as oracle) and records the cause with
line numbers in
`results/opened-document.json`: the placeholder type that received the
formatting holds the flags, the `YText` built by a later `getText` does not,
so deletes and omitted-attribute inserts there take positions from the index
cache with an empty attribute map, and `cleanupFormattingGap` then deletes a
closing marker as redundant.

`formatting-exactness.mjs` is the dedicated falsifier for formatting
exactness: on every reachable state of seeded concurrent histories, forked as
a created and as an opened replica, every nonempty visible range receives
each attribute delta on a fresh copy and the view is compared with the list
edit; over-wide and under-wide expectations must be rejected wherever the
range leaves room. `node formatting-exactness.mjs --seed 41 --trials 60`
writes `results/formatting-exactness.json`.
