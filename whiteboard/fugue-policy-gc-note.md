# Fugue mint-policy collection

## Enquiry

**Goal.** Identify the smallest collectable issuer-side summary that preserves
the plain Fugue generation policy after deleted EmbedRGA records disappear.

**Candidate claim.** The live sided-EmbedRGA state determines the next Fugue
`(side, parent)` choice at every live cursor anchor.

**Falsifier.** Two reachable Fugue knowledge states have the same live
coordinate map but choose different `(side, parent)` values for the same fresh
insert after the same live anchor.

**Formal oracle.** Add a concrete Lean counterexample beside
`SidedRGA_Fugue.lean`, then state the sufficient-summary theorem over the
smallest surviving candidate.

**Reality oracle.** Run the corresponding trace through
`whiteboard/litmus/embed_sided.py`, whose policy follows the
Weidner--Kleppmann tombstone-visible tree rule. Later, differentially test the
JavaScript issuer against that model.

## Initial candidate trace

Compare these worlds:

1. insert `a`; then insert fresh `y` after `a`;
2. insert `a`; insert `x` after `a`; delete `x`; then insert the same fresh
   `y` after `a`.

Immediately before `y`, both live projections contain only `a`. World 1 has no
right child of `a`, so Fugue chooses `(R, a)`. World 2 retains the dead `x` in
the policy tree, so it chooses `(L, x)`. If checked, this refutes live-state
sufficiency and makes policy metadata load-bearing.

Status: **refuted**. The Python policy model returns `(R, 1)` and `(L, 2)`
for the two worlds. Lean checks the same result in
`SidedRGA_FuguePolicyGC.lean`:

- `live_projection_equal` proves the live folds equal;
- `choose_without_dead_child` and `choose_with_dead_child` pin the two choices;
- `live_projection_does_not_determine_choose` packages the counterexample.

The same module proves `fullMintSummary_preserves_choose`: filtering out delete
events while retaining every insert record preserves every `fugueChoose` result.
This is a machine-checked sufficient summary, but it grows with all inserts and
therefore does not solve collection.

## Result boundary

Live-state-only exact Fugue minting is impossible. A bounded design must do one
of the following:

1. retain a policy summary that distinguishes the two worlds;
2. change mint decisions at a settled epoch and prove continuation-equivalence
   rather than exact decision preservation; or
3. use a different generation policy and prove its ordering guarantee.

The next enquiry tested option 2's simplest form: erase a stable dead leaf and
restart Fugue from the live state. It is also **refuted**. Starting from the
common stable state `insert 1; insert 2 after 1; delete 2`, two replicas
concurrently insert `5` and `4` after `1`. The uncollected policy makes both
new records L children of dead `2` and reads `[1,4,5]`; the restarted policy
makes them R children of `1` and reads `[1,5,4]`. Lean checks this as
`stable_dead_leaf_collection_changes_future_read`; the independent Python
model returns the same two reads.

Therefore, causal stability alone does not make Fugue policy tombstones
discardable. A collector must preserve their future ordering effect.

## Next candidate: a live-gap summary

The full insert history is sufficient but may be stronger than necessary.
At any state, a client can insert only after start or a live element. For each
such anchor, `fugueChoose` consumes two facts:

1. whether the anchor has ever had an R child; and
2. its tombstone-visible successor and that successor's chain.

Conjecture: a summary indexed by the current live gaps, with shared chains for
the referenced dead successors, is closed under insert and delete and preserves
all future Fugue choices and reads. Its cardinality would be `O(live)` even
though individual shared chains may still contain dead waypoints.

Status: **executable candidate checked; proof in progress**. The incremental
model is `whiteboard/litmus/fugue_policy_gap_check.py`. Its directed control
reproduces the stable-dead-leaf distinction: the retained-gap model agrees
with the full tree on `[1,4,5]`, while the deliberately live-only model returns
`[1,5,4]`. It also agrees with the full tree across 20 randomized runs of 60
fork/join rounds, using the true common ancestor for every ternary merge.

The Lean module now defines the exact per-anchor `LiveGap` observation and
proves, without `sorry`, that it preserves both `fugueChoose` and the chosen
parent chain. These theorems establish that the proposed fields are sufficient
at mint time. It also proves exact delete-transition congruence:
`liveGapOf_append_delete` shows that a delete leaves every policy gap
unchanged, so the implementation need only remove the deleted anchor's own
map entry.

Insert and merge congruence remain. The former Fugue G1 dependency is now
closed in this module: `succOf_schain_immediate` and its root companion prove
that `succOf`'s finite key argmax is the immediate `schainBefore` successor in
every state satisfying the strengthened reachable Fugue invariant. These
lemmas supply the ordering premise for the incremental equations
`succ[a] := x` and `succ[x] := oldSucc[a]`. The next proof must derive those
equations for the post-insert summary itself; randomized agreement is not a
substitute for that transition theorem.

The insert proof has also discharged its non-argmax fields:
`gChainOf_append_gen_new` proves that the fresh id resolves to exactly the
minted chain, and `hasRChild_append_gen_anchor` proves that the anchor's
monotone policy bit is true after every Fugue insert. The remaining insert
obligation is therefore precisely the pair of successor equations above.
As a stronger refutation check, the executable model also passed 1,000 seeds
of 30 true-LCA fork/join rounds.

The anchor-successor proof is now free of list implementation details.
`succOf_of_append_beating_candidate`, `gKeys_append_gen`,
`succCand_append_of_gKeys`, and `gKey_append_gen_old` prove the finite-argmax
update. `succOf_append_gen_anchor_of_between` reduces the exact equation
`post.succ[a] = x` to the Fugue geometry. That geometry is now discharged:
`genInsAfter_between` proves that the minted chain is after `a` and before
`old.succ[a]` in all three policy branches, using monotone-id arithmetic for
the newest-R case. Consequently `succOf_append_gen_anchor` proves the exact
first successor equation without additional premises. The inherited equation
`post.succ[x] = old.succ[a]` and merge congruence remain.

For the inherited equation, `gKey_append_gen_new` proves exact fresh-key
lookup and `succOf_append_gen_new_of_candidates` reduces the result
definitionally to
`post.succCand[x] = old.succCand[a]`. Thus the remaining insert proof is a
single candidate-set order equivalence: every old element after `a` remains
after the inserted `x`, and every element after `x` was already after `a`.

Status update: that equivalence is now proved by
`succCand_append_gen_new`, using the old argmax and the checked gap-placement
lemma. Consequently `succOf_append_gen_new` proves
`post.succ[x] = old.succ[a]`. Together with
`succOf_append_gen_anchor`, exact fresh-chain lookup, and the monotone `hasR`
equation, the insert transition's two changed gap records are discharged.
Merge congruence is now the remaining formal obligation.

Merge congruence is partially discharged. `mem_syncK_iff` proves that policy
merge is exact record union, and `hasRChild_syncK` proves that the merged
monotone bit is branchwise OR. The remaining merge theorem is successor
argmax composition: select the display-earlier of the two branch successor
witnesses (and its shared chain), with `none` as identity.
