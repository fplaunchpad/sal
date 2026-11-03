# Upstream drafts

Two issues and two comments for github.com/yjs/yjs, posted from KC's
account on 2026-10-29: issue 1 is yjs/yjs#829, issue 2 is yjs/yjs#828, the
comments are on #382 and #385. Issue 2 and both comments were edited in place on 2026-10-29 (see `docs/upstream-corrections.md`); the texts below are the live ones.
Scripts are the `v14/` versions; on 13.6.33 replace `doc.get('t')` with
`doc.getText('t')` and read `toDelta()` directly. Each script exits
non-zero when the defect shows.

---

## Issue 1

**Title:** Delete sets, and v14 structs past a clock gap, are applied before the updates they depend on

**Checklist**

* [x] Are you reporting a bug? Use github issues for bug reports and feature requests.
* [x] Try to report your issue in the correct repository.

**Describe the bug**

A struct received out of order is held in `pendingStructs` until its clock predecessor and its origins are present. A delete set is applied as soon as the items it names exist, whatever else is missing. An update with no structs and only a delete set therefore never waits. Unformatting is such an update: `format(0, 2, { bold: null })` over a run whose markers already exist emits no new items, only the deletion of the two markers.

So a replica that receives the unbold before the insert it was issued after applies the unbold anyway, and shows a document that no causally consistent subset of the operations produces. Nothing is pending, so nothing tells the application the state is transient. The replica converges when the missing update arrives.

**To Reproduce**

```js
import * as Y from '@y/y';
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const updates = [];
d1.on('update', (u) => updates.push(u));
d1.get('t').insert(0, 'a', { bold: true });          // u0: bold "a"
d1.get('t').insert(1, 'b');                          // u1: plain "b" after it
d1.get('t').format(0, 2, { bold: null });            // u2: unbold "ab" (deletes the two markers)

const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
Y.applyUpdate(d2, updates[0]);
Y.applyUpdate(d2, updates[2]);                           // u2 arrives before u1
console.log('received u0 and u2 only:', show(d2), 'pending structs:', d2.store.pendingStructs, 'pending ds:', d2.store.pendingDs);
console.log('every causally closed state: ', JSON.stringify([{ insert: 'a', attributes: { bold: true } }]), '(u0 alone),',
  JSON.stringify([{ insert: 'a', attributes: { bold: true } }, { insert: 'b' }]), '(u0 u1), or', JSON.stringify([{ insert: 'ab' }]), '(all three)');
const wrong = show(d2) === JSON.stringify([{ insert: 'a' }]);
Y.applyUpdate(d2, updates[1]);
console.log('after u1 arrives:', show(d2), '(converges)');
process.exit(wrong ? 1 : 0);
```

Output on 14.0.0-rc.29:

```
received u0 and u2 only: [{"insert":"a"}] pending structs: null pending ds: null
after u1 arrives: [{"insert":"ab"}] (converges)
```

The same with `insert` and `format` swapped (an insert issued after an unbold, delivered before it) lands the inserted plain text inside a still-live bold span at the receiver.

**Expected behavior**

The documentation promises that updates can be applied in any order and that all clients sync up once they have received all updates. That holds here. The question is about the states in between. Every document a replica displays should be the result of applying some subset of the received updates that is closed under dependency, in an order consistent with it. Here the closed subsets are {u0}, {u0, u1} and {u0, u1, u2}, which show `a` bold, `a` bold followed by `b`, and `ab` plain. The replica shows `a` plain, which is none of them. 13.x gives structs this guarantee through `pendingStructs`, which is why I read it as intended. A delete set that arrives with structs could be held with them until they integrate. An update with no structs carries nothing to wait on in the current encoding, so for that case the choice is between adding the sender's state at issue time to the update and documenting that intermediate states are only meaningful when the provider delivers each client's updates in order.

**In v14 the same now holds for structs**

13.x holds a struct whose clock is ahead of the replica's state for its client in `pendingStructs`. rc.29 fills the gap with a `Skip` and integrates the struct when its origins exist. So a replica now also shows an insert whose author had typed other text before it that the replica has not received:

```js
import * as Y from '@y/y';
const show = (doc) => doc.get('t').toString();
const updatesOf = (doc) => { const us = []; doc.on('update', (u) => us.push(u)); return us; };

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
const u1 = updatesOf(d1); const u2 = updatesOf(d2); // u1[1] is d1 re-emitting b
d1.get('t').insert(0, 'y');                                 // 1:0
d2.get('t').insert(0, 'b');                                 // 2:0
Y.applyUpdate(d1, u2[0]);                                   // d1 has y and b
d1.get('t').insert(d1.get('t').toString().indexOf('b') + 1, 'h'); // 1:1, placed after b
Y.applyUpdate(d2, u1[2]);                                   // d2 receives 1:1 but not 1:0

console.log('d2 after receiving only the second update of client 1:', JSON.stringify(show(d2)),
  'pending structs:', d2.store.pendingStructs === null ? 'none' : 'some');
console.log('causally closed states at d2: "b" (no update of client 1), or ones containing "y" (both updates)');
const wrong = show(d2).includes('h') && !show(d2).includes('y');
Y.applyUpdate(d2, u1[0]);
console.log('after the first update arrives:', JSON.stringify(show(d2)), '(converges)');
process.exit(wrong ? 1 : 0);
```

Output: 13.6.33 shows `b` with the struct pending; rc.29 shows `bh` with nothing pending; both show `ybh` once the first update arrives. If this is intended, the two reports here are one question: is a document a replica displays meant to be reachable by some ordering of the operations it has received, closed under what those operations were issued after? If yes, delete sets (and in v14, structs past a gap) need the buffering structs had in 13.x. If no, it would help to say so in the documentation, since editors render these states and users edit on top of them, and the stated guarantee today is convergence once every update has arrived.

**Where it happens in the source**

`integrateStructs` (src/utils/encoding.js) holds a struct whose predecessor or origin is missing in 13.x; in rc.29 it inserts a `Skip` for the gap when the origins exist. `readAndApplyDeleteSet` (src/utils/ids.js in rc.29, src/utils/DeleteSet.js in 13.x), called from `readUpdateV2` after the structs, applies every range whose items exist and keeps only the rest in `pendingDs`. There is no check that the update's own structs, or the sender's earlier updates, have been integrated. Same in 13.6.33.

**Real-world scenario**

Any transport that can deliver a client's updates out of order or drop one for a while: y-webrtc with several peers, a client reconnecting after offline edits, a server forwarding updates from more than one connection. The visible effect is formatting that disappears or appears on text the user did not touch and then changes again when the late update arrives, and local edits made meanwhile are based on the wrong state.

**Environment**

* Node 26.3.1, macOS
* `@y/y` 14.0.0-rc.29; also `yjs` 13.6.33 and 13.6.31

**How this was found**

While checking Yjs text against a sequential specification of formatted text, as part of a verification project on replicated data types at IIT Madras (FP Launchpad). The reproductions come from a property-based testing harness, were minimised, and were checked by hand against the source; the harness was built with AI assistance. Happy to send a PR with a test if you agree with the expected behaviour.

---

## Issue 2

**Title:** Concurrent operations delete formatting markers that other operations rely on

**Checklist**

* [x] Are you reporting a bug? Use github issues for bug reports and feature requests.
* [x] Try to report your issue in the correct repository.

**Describe the bug**

Three shapes with one cause. A format's extent in the document depends on marker items the format did not create: `format` reuses an existing opening marker of the value it sets and then emits no closing marker of its own, and the cleanup passes (`cleanupYTextFormatting` after a transaction, `cleanupFormattingGap` during `delete`) remove markers judged redundant by their position in the item list, without knowing which span they close. A concurrent operation that removes one of those markers changes the extent of a format it never touched. In each shape below the two replicas converge, and the converged document is one neither order of the two concurrent operations produces.

**To Reproduce**

Shape 1, an insert that relies on an existing opener, concurrent with an unbold of a different range. User 1 types a bold `d` after bold `et`; user 2 unbolds `et`. Result: `d` is plain.

```js
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'et', { bold: true });
sync(d1, d2);
// concurrently:
d1.get('t').insert(2, 'd', { bold: true });        // user 1 types bold "d" after "et"
d2.get('t').format(0, 2, { bold: null });           // user 2 unbolds "et"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'et' }, { insert: 'd', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(unbold then insert, or insert then unbold: both give this)');
process.exit(show(d1) === expected ? 0 : 1);
```

Shape 2, two concurrent bolds, one nested in the other. User 1 bolds `au`; user 2 bolds `a`. Result: `u` is plain. The outer bold's opening marker is deleted by the cleanup as overwritten by the inner one, although the inner span closes earlier.

```js
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'au');
sync(d1, d2);
// concurrently:
d1.get('t').format(0, 2, { bold: true });           // user 1 bolds "au"
d2.get('t').format(0, 1, { bold: true });           // user 2 bolds "a"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'au', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(both orders bold both characters)');
process.exit(show(d1) === expected ? 0 : 1);
```

Shape 3, a delete concurrent with a bold insert after the deleted character. User 1 deletes the bold `b` at the end of `wv b`; user 2 types bold `z` after `b`. Result: `z` is plain. The delete's gap cleanup removes both markers of the span `z` was placed in.

```js
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'wv');
d1.get('t').insert(2, 'b', { bold: true });
sync(d1, d2);
// concurrently:
d1.get('t').delete(2, 1);                           // user 1 deletes the bold "b"
d2.get('t').insert(3, 'z', { bold: true });         // user 2 types bold "z" after "b"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'wv' }, { insert: 'z', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(delete then insert, or insert then delete: both give this)');
process.exit(show(d1) === expected ? 0 : 1);
```

Output on 14.0.0-rc.29:

```
Shape 1  observed [{"insert":"etd"}]                                           expected [{"insert":"et"},{"insert":"d","attributes":{"bold":true}}]
Shape 2  observed [{"insert":"a","attributes":{"bold":true}},{"insert":"u"}]        expected [{"insert":"au","attributes":{"bold":true}}]
Shape 3  observed [{"insert":"wvz"}]                                           expected [{"insert":"wv"},{"insert":"z","attributes":{"bold":true}}]
```

**Expected behavior**

A format over a range marks exactly the characters in that range; a character carries the attributes of the last format that covered it; and when two users edit concurrently the merged document equals the result of applying both operations in one of the two orders. In each shape both orders give the document marked "expected", and the merged document is different from it. "Both orders" means applying each edit with the character identities and anchors recorded when it was issued, not reissuing the same numeric indices against the other replica's document: in shape 3 the insert after `b` stays anchored after `b` once `b` is a tombstone, so in either order `z` is inserted after it and is bold. The deviation is always the same: characters lose formatting that the user who typed or formatted them asked for, or keep formatting that was removed.

**Relation to open issues**

#382 (overlapping bolds of the same key lose a span) and #385 (a format spreads over a concurrently inserted character) are two more shapes of the same cause: the extent of a span is decided by markers and their positions rather than by the operation that created the span. #291 and #521 look like earlier sightings. All of #382, #385 and the three shapes here reproduce on 14.0.0-rc.29 and 13.6.33. I grouped the three unreported shapes into one issue because in each a formatting marker that another edit relied on was deleted or reused by a concurrent operation; they may need separate repairs, and none was tried. #382 is the overlapping-formats face of the same marker handling. #385 additionally involves how a concurrent insertion is ordered against a format boundary, which a change to marker ownership alone need not affect.

**Environment**

* Node 26.3.1, macOS
* `@y/y` 14.0.0-rc.29; also `yjs` 13.6.33 and 13.6.31

**How this was found**

While checking Yjs text against a sequential specification of formatted text, as part of a verification project on replicated data types at IIT Madras (FP Launchpad). The specification is the one above; the list part of Y.Text passes it in every history we generated, so these are formatting results and not an artefact of a strict ordering rule. The reproductions come from a property-based testing harness, were minimised, and were checked by hand against the source; the harness was built with AI assistance.

Edited 2026-10-29: the relation to #382 and #385 was narrowed (no shared fix is claimed) and the meaning of "both orders" was stated.

---

## Comment on #382

Still present on `@y/y` 14.0.0-rc.29 and `yjs` 13.6.33. Minimal form, two concurrent bolds of overlapping ranges on `abc`, converged document has `c` plain:

```js
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'abc');
sync(d1, d2);
// concurrently:
d1.get('t').format(0, 2, { bold: true });           // user 1 bolds "ab"
d2.get('t').format(1, 2, { bold: true });           // user 2 bolds "bc"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'abc', attributes: { bold: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(both orders bold all three)');
process.exit(show(d1) === expected ? 0 : 1);
```

This is the overlapping-formats face of the marker handling in #828, in which a format's extent is decided by marker items and their positions; the shapes there and this one may need separate repairs. Details there.

---

## Comment on #385

Still present on `@y/y` 14.0.0-rc.29 and `yjs` 13.6.33. Minimal form, an italic of `a` concurrent with a plain `h` typed before it, converged document has `h` italic:

```js
import * as Y from '@y/y';
const sync = (from, to) => Y.applyUpdate(to, Y.encodeStateAsUpdate(from, Y.encodeStateVector(to)));
const show = (doc) => JSON.stringify(doc.get('t').toDelta().children.map((c) => c.format && Object.keys(c.format).length ? { insert: c.insert, attributes: c.format } : { insert: c.insert }));

const d1 = new Y.Doc({ gc: false }); d1.clientID = 1;
const d2 = new Y.Doc({ gc: false }); d2.clientID = 2;
d1.get('t').insert(0, 'a');
sync(d1, d2);
// concurrently:
d1.get('t').format(0, 1, { italic: true });         // user 1 italicises "a"
d2.get('t').insert(0, 'h');                         // user 2 types plain "h" before "a"
sync(d1, d2); sync(d2, d1);

const expected = JSON.stringify([{ insert: 'h' }, { insert: 'a', attributes: { italic: true } }]);
console.log('observed', show(d1), show(d1) === show(d2) ? '(both replicas)' : show(d2));
console.log('expected', expected, '(user 2 never formatted "h"; both orders give this)');
process.exit(show(d1) === expected ? 0 : 1);
```

With the client ids swapped the spread happens at the right boundary instead. This case involves how a concurrent insertion is ordered against a format boundary, which is related to but not the same mechanism as the marker reuse and cleanup in #828 and #382; a repair of one need not repair the other.
