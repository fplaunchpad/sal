# Tombstone-scanning on insert (§4.2.2) — design sketch

The Peritext paper's §4.2.2 describes a subtle refinement to `Insert`
that our current `do_` doesn't model: when inserting immediately after
a character that has adjacent tombstones, the algorithm scans past
those tombstones to pick a specific insertion point, depending on
whether any of the tombstones are anchors of active marks.

This document sketches what implementing the refinement would look
like, what would need to change, and why it's scoped as multi-session
work.

## The paper's algorithm (§4.2.2, Fig 6)

Quoting the paper:

> If the list of tombstones contains anchors for the start or end of
> several formatting operations, it is possible that no ideal
> insertion position exists. In this situation, the inserted text
> can be placed arbitrarily relative to the tombstones, and the
> worst-case outcome is that the text is formatted differently from
> what was desired.

Concretely: the paper's example inserts "frolicked" into `"fox
jumped"` after `jumped` has been tombstoned. The character `d` (end
of the link) is a tombstone. The algorithm scans tombstones at the
insertion position looking for `after`-anchors of formatting spans;
if it finds one (here, the link's end anchor), it places the
insertion AFTER that tombstone so the new text doesn't inherit the
link.

## What our current `do_` does

```lean
| (ts, (rid, app_op_t.Insert ch after)) =>
    (upd (Prod.fst s) (ts, rid) ch,
     upd (Prod.fst (Prod.snd s)) (ts, rid) after,
     Prod.fst (Prod.snd (Prod.snd s)),
     Prod.snd (Prod.snd (Prod.snd s)))
```

Four actions on four components — no inspection of the `marks` set.
The `after` parameter is used verbatim as the afters-pointer.

## What would need to change

### 1. New effect definition

Insert would need to consult the `marks` set to decide the effective
`afters` pointer:

```lean
| (ts, (rid, app_op_t.Insert ch after)) =>
    let effective_after := scan_tombstones_for_anchors s after
    (upd (Prod.fst s) (ts, rid) ch,
     upd (Prod.fst (Prod.snd s)) (ts, rid) effective_after,
     Prod.fst (Prod.snd (Prod.snd s)),
     Prod.snd (Prod.snd (Prod.snd s)))
```

Where `scan_tombstones_for_anchors` walks the chain of tombstones
reachable from `after` (via reverse-afters lookups in the full
state), finds any that are `after`-type end-anchors of marks in
state, and returns the farthest such tombstone's position.

This is computationally non-trivial: needs to traverse a reverse-
afters chain, check each for mark-anchor status, and decide
placement.

### 2. The 24 VCs need re-verification

Every RA-linearizability VC that involves two or more ops where at
least one is `Insert` would need re-proof. The existing VC proofs
rely on Insert's component-independence — it only touches chars and
afters, never marks. The new Insert reads marks, breaking that
independence.

Specifically affected VCs (rough count):
- `rc_non_comm`, `cond_comm_base` — Insert-vs-everything commutativity
- `base_2op`, `base_1op`, `lem_0op` — base cases involving Insert
- `inter_*op`, `ind_*op` — inductive cases involving Insert
- Probably 12 to 18 of the 24 VCs touch Insert directly

Each needs re-proof with the new Insert semantics.

### 3. Downstream reasoning

- `afters_reach`, `visible_lt`, `in_span_visible` — these are
  pure functions of afters + marks. With the new Insert, the
  afters pointer can DIFFER from the user-supplied `after`
  parameter. Any theorem that assumes "afters(c_new) = after"
  after `do_ Insert ch after` needs revisiting — now it's
  "afters(c_new) = scan_tombstones_for_anchors s after".
- `insert_within_span_in_span_visible` (CRDT, Ex 1 closure) —
  rests on `after_of s_post (ts, rid) c_after = true`. Under
  the new semantics, this may or may not hold depending on
  whether c_after has tombstone anchors between it and its
  predecessors. Would need a refined version.

### 4. MRDT side

MRDT's `do_` Insert adds to a `set CharRec` rather than a `map`.
The tombstone-scanning story is analogous but needs the set-of-
records encoding carefully thought through.

## Why this is multi-session

- Rework `do_`: 30-60 min.
- Re-prove ~15 VCs: each 5-30 min. Total 4-8 hours.
- Rework dependent read-side theorems (`insert_within_span_*`,
  visible_lt preservation): 1-2 hours.
- MRDT mirror: 2-4 hours.
- Total: 8-15 hours across multiple sessions.

## Interim alternative

For users who need Ex 8 fidelity (link-no-expand), the current
`in_span_visible` on the existing `do_` **already gives the right
answer** for most cases: chars inserted as direct descendants of
endId are > endId in visible-order, hence outside the span.

The edge case where `§4.2.2 really matters` is when an end-anchor's
`target` char has been tombstoned AND the user re-inserts at that
position. Without the scan, the new char might inherit the link
formatting when the paper says it shouldn't. This is a fidelity gap
but not a convergence gap — two replicas in agreement on the same
op log will still agree on the rendered document; they'll just
render it wrong per the paper.

So: this is a "UX fidelity" issue, not a "correctness" issue. That
matters for Peritext as a product, but the Lean formalization of
convergence + the paper-faithful read-side is intact either way.

## Deciding to do it

Worth tackling when:
- Building a production Peritext editor on top of this Lean spec
  that needs the §4.2.2 edge case correctly.
- Writing a paper comparing the formalization to the paper in full
  detail, and wanting every bullet checked off.

Not worth tackling for:
- "Is our Peritext convergent?" — already answered: yes.
- "Does our Peritext faithfully capture Ex 1-8?" — mostly yes
  already; this would flip one edge case of Ex 8 from "may
  disagree with paper on rare tombstone configurations" to "fully
  matches paper everywhere."
