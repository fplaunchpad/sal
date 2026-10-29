# Sequential specification of formatted text

The oracle (`ra-pbt/instances/yjs/spec.js` with the witness search bound to
it in `oracle.js`) is independent of Yjs: it imports no package.

## State

A state is an ordered list of characters `{ id, ch, deleted, attrs }`, where an
id is a pair `[client, clock]` and `attrs` maps attribute keys to non-null
values. The initial state is the empty list. The view of a state is its
non-deleted characters as `{ ch, attrs }`.

## Operations

- **insert** `{ id, ch, origin, rightOrigin, attrs }`. Requires that no
  character has `id`, that `origin` is null or the id of an existing character
  (deleted or not), and that `rightOrigin` is null or the id of an existing
  character at or after `origin`. Places a new visible character carrying
  exactly `attrs` at any position strictly after `origin` (or the head) and
  strictly before `rightOrigin` (or the end). This is the gap rule, the
  strong list specification of Attiya, Burckhardt, Gotsman, Morrison, Yang
  and Zawirski (PODC 2016): a character keeps its order relative to the
  characters that existed when it was issued and takes any order relative to
  concurrent insertions into the same gap. It is relational; `applyAll`
  returns every resulting state and `applyPlaced` only those consistent with
  a target view. Two deterministic rules are kept so that their refutations
  stay reproducible: the one-sided rule (`rule = 'left'`), immediately after
  `origin` as in an RGA specification, refuted by the placement pair's first
  history; and the two-sided rule (`rule = 'both'`), immediately before
  `rightOrigin` when recorded, refuted by the pair's second history.
- **delete** `{ ids }`. Requires each id to name an existing character.
  Marks each deleted. A character already deleted stays deleted, so two
  concurrent deletes of one character commute.
- **format** `{ left, right, attrs }`. Requires `left` and `right` to name
  existing characters with `left` at or before `right`. Merges `attrs` into
  every character from `left` to `right` inclusive, visible or deleted: a null
  value removes the key, any other value sets it.

A replica operation record denotes a list of these operations: an insert of
`n` characters is `n` inserts, the first after its recorded left neighbour in
the retained sequence (the nearest character to its left at issue time,
deleted or not, with format markers skipped) and each later one after its
predecessor; a delete is one delete; a format is one
format over its recorded endpoint ids.

## Choices made by this specification

These are the specification's choices, not consequences of any
implementation:

1. Insertion places the new character anywhere strictly between its recorded
   origin and its recorded right origin. Both origins are what the
   implementation records, resolved to the nearest character when the
   implementation recorded a format marker; a deleted character remains an
   anchor. Each deterministic refinement is refuted by a plain-text history
   (the placement-pair regressions).
2. Format is an identity-bounded interval: it acts on whatever lies between
   its endpoint ids when it is applied, so it also covers characters inserted
   concurrently between those endpoints.
3. Inserted text carries exactly its own attributes; it inherits nothing from
   its neighbours.

## Local meaning

`localEdit(view, request)` is the ordinary index-level edit on a view: insert
splices characters carrying exactly the requested attributes, delete removes
`[index, index + len)`, format merges attributes into exactly
`[index, index + len)`. Out-of-range requests are errors.

## Witnesses

A history is a set of events, each denoting a list of specification
operations, partially ordered by causality. A version with view `V` is
**RA-linearizable** when some linear extension of the causal order of its
events, folded from the initial state by applying each event's operations in
order, meets every precondition and yields view `V`. Such a linear extension is
a witness.

`findWitness(events, V)` decides this exactly by dynamic programming over
down-closed sets of events (at most 20), keeping for each set the distinct
states reachable through some linear extension of it. `allFinalViews(events)`
returns every view the specification admits for the history, which is what is
reported when no witness exists.
