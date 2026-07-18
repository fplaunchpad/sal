# Virtual LCAs for the rehoming RGA: the invariant stack at antichain unions

Task #90, equivalence residue, design phase. Python plus pen and paper
(`whiteboard/litmus/rehoming_vlca_check.py`); no Lean in this phase. The
question: the virtual LCA construction (recursive antichain merge, validated
for canonicity datatypes in `whiteboard/virtual-lca-note.md`) is re-probed on
the rehoming RGA, the one production instance with a reachability-anchored
invariant stack and a proof route that runs through an equivalence quotient.
Verdict in section 6: SURVIVES on every probe; `noopFeasible` is refuted at
antichain unions (again), so the Lean mirrors must take the generation
discipline route, and section 7 gives the bill.

## 1. The datatype

The rehoming RGA (Lean: `Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean`,
conditioned chain `Sal/ConditionedMRDTs/MRDT_Instances/RGA_Rehoming/`; the
flat-RGA row of the litmus matrix), component by component:

* **State.** `id -> (element, anchor)`, a finite map; `0` is the root and is
  never stored. Tombstone-free: deletion removes the record.
* **Ops.** `Ins t e pre a` (insert `e` with fresh id `t` after anchor `a`) and
  `Del t pre x` (delete `x`). `pre` is the leaf's live ancestor chain at the
  generation state, nearest first, root excluded (the recorded path).
* **do.** `Ins`: store `t -> (e, resolve s (a :: pre))`, where `resolve`
  returns the first live candidate, else `0`; on a state where `a` is live the
  path is never read. `Del`: `tgt := resolve s pre`; rehome `x`'s children to
  `tgt`; remove `x`. Total; a delete of a dead target is the identity.
* **merge (three-way).** Survivors `I = (dl & da & db) | (da - dl) | (db - dl)`
  on identities; records read from the LCA first, then the branches; each
  survivor's stored anchor is climbed up the LCA's parent chain to the nearest
  survivor (else the root).
* **rc.** `Either` everywhere; order is a read-side concern.
* **Equivalence.** `eq` (the `~=` of the quotient layer): same domain, same
  records on the domain. Observational state equality; in the model, dict
  equality. All probes compare at this finest equivalence, so nothing below
  weakens the check.
* **Honesty chain** (the conditions the RA-linearizability capstone assumes,
  `RGA_Honest_Residual.lean`): born accuracy (every op's recorded path is its
  leaf's true live chain at some causal fold of the op's visibility past,
  forced by tombstone-freedom), applicable delivery
  (`applicable = accurate /\ fresh_ts` at each apply step), Lamport-fresh
  nonzero ids, `GenDisc2C` (accuracy at the fold of the op's transitively
  closed dependency prefix, `RGA_CanonFoldOK.lean:110`), and, in the NF layer,
  `noopFeasible` (each op applicable or a no-op along an enumeration,
  `Framework/NoopFeasible.lean`).

Critical history respected throughout: the claim that `noopFeasible` could be
derived from the initial state along arbitrary enumerations was kernel-refuted
(memory 7a7ff9c): an LCA-first enumeration pre-applies a concurrent
anchor-kill below a cross-branch insert, accuracy fails there, and the insert
is not a no-op. The delta fold is instead certified by rehome-correctness
(`GenDisc2C` via the K1 route, `RGA_HEnum_Discharge.lean`). Intermediate
antichain unions are precisely event sets of this unanchored kind, so this
probe aims the refutation shape at them directly.

## 2. The virtual rule and what it must preserve

VirtualLCA(v1, v2): take the maximal common ancestors `M`; if a singleton,
done; else fold `M` in ascending rank, merging each member into an accumulator
through the recursively resolved LCA of the sub-pair, materializing scratch
nodes whose event set is the union so far. The proved merge case of the
framework consumes exactly two facts about the LCA slot: its event set is the
head intersection (`lca_events`), and its registered state is canonical for
that event set. The covering proposition (section 3 of
`virtual-lca-note.md`) re-supplies the first; the per-datatype residue is the
second, at every intermediate union `E(m_1) u ... u E(m_j)`. These sets are
unions of below-meet sets: backward closed, but neither head event sets nor
meets, so no replica ever held them. For the rehoming RGA the canonical state
of an event set `E` has an implementation-independent description:

    live(E)   = inserted ids minus deleted ids
    anchor(y) = the nearest live BIRTH ancestor of y (walk y's recorded
                birth anchors, skip dead ids, stop at the first live or 0)

because recorded paths and LCA chains are both sub-chains of the birth chain
omitting only dead ids, and deadness is monotone (no resurrection among
survivors when the LCA slot covers the intersection). This normal form is the
`birth_oracle` of the script: it never runs `do` or `merge`, so it is a
non-self-fulfilling oracle for every state-level check.

## 3. The probes

`whiteboard/litmus/rehoming_vlca_check.py`, exit 0 iff all asserted
expectations hold; an expected refutation firing is a passing assertion.

Checks, asserted at every resolution or sync:

* **C1 covering**: `E(virtual) = E(v1) & E(v2)` at every resolution.
* **C2 scratch canonicity**: every scratch state equals BOTH the datatype's
  own ts-order fold of its union event set AND the birth-forest normal form.
* **C3**: every sync result equals both oracles; final all-replica
  convergence at dict equality.
* **C4 generation discipline at unions**: for every event of every scratch
  union, accuracy holds at the fold of its dependency prefix (visibility past
  restricted to ids in the leaf's birth ancestry) and at the fold of its full
  visibility past, both taken inside the union.
* **C5 `noopFeasible` at unions**: walk two enumerations of each scratch
  union (plain ascending Lamport, and LCA-events-first then delta) and record
  every step that is neither applicable nor a no-op. Firings are counted, not
  fatal: the refuted predicate is expected to fail, and C2 must hold anyway.
* **P2 fold-order insensitivity**: at every criss-cross the antichain is also
  folded descending; the returned LCA state must be dict-equal.

The generator is honest by construction: anchors live at mint, recorded paths
are the live chain at the minting head, deletes name observed live nodes, ids
come from one global Lamport counter (so ascending ts is a causal
linearization and `fold_oracle` is a legitimate honest fold).

Directed scenarios (all expected values hand-derived in comments, never taken
from the implementation): T1 the routine two-pair criss-cross where one MCA
deletes a node whose child is inserted concurrently in the other, with a FAIL
companion (the fixed single-MCA pick `v` resurrects the deleted id 2, read
`((2,b),(4,c))` against oracle `((4,c))`; the virtual LCA does not); T2 a
nested depth-2 criss-cross with deletes at both levels (recursion depth 2
asserted); T3 the rows/L4 symmetric shape, each branch deleting a node with a
concurrent child on the other branch, then delete-heavy continuations; T4a
the directed hEnum shape at a union (one MCA holds `Del 2` at ts 3, the other
`Ins _ 2` at ts 4, so every ts-respecting enumeration of the union folds the
kill below the insert); T4b the delete variant (a delete applied where a
concurrent kill has already contracted its recorded path); T8 a directed
3-antichain (`MCA = {v, u, w}`) whose ascending fold passes through the
strict intermediate union `E(v) u E(u)` with the hEnum shape planted inside
it. Randomized: T5 open PBT (320 trials, delete-heavy mix, 3 to 5 replicas,
criss-cross gate removed); T6 targeted PBT (150 trials, each forcing the T4a
shape on a random base tree, firing asserted per trial); T7 dense PBT (120
trials, 6 replicas, sync-heavy). ST: a harness-power selftest, the climb-free
mutant merge must be caught by the canonicity assertions (it is, by T3).

## 4. Results

All checks passed; exit 0; about 0.35 s total.

* C1, C2, C3, P2: asserted at every one of the several hundred resolutions
  and scratch nodes across all runs, never failed.
* C4: full on all 590 randomized trials plus all directed tests; never
  failed. Accuracy at dependency-prefix folds survives restriction to every
  intermediate union probed.
* T5: 320/320 converged to both oracles; criss-cross in 54/320 trials,
  antichain sizes `{2: 83}`, resolution depths `{0: 74, 1: 9}`.
* T6: 150/150 trials fired the hEnum shape at the union AND converged.
* T7: 120/120 converged; antichain sizes `{2: 309, 3: 1}`, resolution
  nesting depths `{0: 230, 1: 62, 2: 13, 3: 4, 4: 1}`.
* C5 firings (expected): ts-order totals across T5/T6/T7 were
  `ins-anchor-dead` 390, `del-path-stale` 68, `ins-path-stale` 80; the
  LCA-first enumeration fired on the same scenarios (totals 381, 68, 68).
  Every firing was rehome-correct: C2 held at the very scratch nodes whose
  union folds violated `noopFeasible`.

Two observations worth pinning. First, the hEnum shape fires under EVERY
ts-respecting enumeration once a concurrent anchor-kill carries a smaller
Lamport stamp than a cross-branch insert under the killed node (T4a): at an
antichain union this is routine, not exotic (T6 forces it on every random
tree). Second, in T8 the intermediate scratch states are order-dependent
(the ascending fold's first scratch has id 2 dead and absent; the descending
fold's first scratch keeps 2 alive with different survivors), yet each is
canonical for its OWN union, and the returned LCA state is identical. So the
mirror lemma must state canonicity of each scratch for its own event set and
order-insensitivity only of the final result, never canonicity of
intermediates across fold orders.

## 5. The invariant stack at unions, component by component

Component (Lean name), verdict at unions of below-meet sets:

* Backward closure (`fullClosureRel`): union-closed, structurally (union of
  event sets of versions; each is visibility-closed).
* Finiteness, nonzero ids, nonzero delete targets (`HonCore` clauses 1-3):
  per-event, restrict to any subset; union-closed trivially.
* Born accuracy (`HonCore` clause 4): per-event and ambient-set independent
  (the op's own visibility past); union-closed for free. Confirmed by C4.
* `GenDisc2C` (recorded prefix correct at the dependency-prefix fold):
  per-event; the dependency prefix of an event lies inside any backward
  closed set containing the event, so the discipline restricts to unions by
  the existing restriction lemma (`isDepPreC_of_restrict`, consumed at
  `RGA_HEnum_Discharge.lean:148`) given predecessor-closure of the union.
  Confirmed by C4, including at the strict intermediate union of T8.
* `opOK` (`t /= 0`, `x` not in its own path, `RGA_CondSig.lean:85`):
  order-stable op-only facts; union-closed trivially.
* Applicable delivery and `noopFeasible`: STATE-DEPENDENT and FALSE at
  unions. Refuted empirically in three forms: `ins-anchor-dead` (the exact
  hEnum shape), `del-path-stale` (a delete applied while its recorded chain
  is stale after a concurrent kill of a path member; the delete is not a
  no-op, and its `resolve` still lands on the right rehome target),
  `ins-path-stale` (anchor live, recorded path stale; `resolve` stops at the
  live anchor, so the stored record is right). These predicates must not
  appear in the union-level obligations of the mirrors.

The dividing line is exactly the one the hEnum history drew: per-event
components (accuracy relative to the event's own past) are union-closed;
prefix-state components (applicability along an enumeration) are not, and
correctness at unions rests on rehome-correctness, not on applicability.

## 6. Verdict

**SURVIVES.** On every directed shape (including the delete-under-concurrent-
child sore spot, the nested depth-2 shape, the 3-antichain with a strict
intermediate union) and on 590 randomized trials with the criss-cross gate
removed, the virtual-merge execution converges across replicas, every scratch
state is canonical for its union event set at dict equality (the finest
equivalence, so a fortiori up to `~=`), and every final read matches the
datatype's own honest fold and the independent birth-forest normal form. No
countermodel was found, and the harness demonstrably catches a broken merge
(ST) and a broken resolution policy (the T1 fail companion). The
`noopFeasible` refutation reproduces at antichain unions in the predicted
LCA-first form and also under plain Lamport order; it marks a dead proof
route, not a defect of the construction.

Delimitation: this is model-level evidence at Python fidelity (map-with-
default semantics, climb with a cycle guard in place of fuel), on honest
generators only, with `~=` instantiated to state equality as in the Lean
`eq`. It does not discharge the Lean obligations; it selects the route and
predicts no surprise.

## 7. The Lean bill for the rehoming mirrors

Generic tier (owed once, from the virtual-lca-note addendum, unchanged):
`Step3V` with the `mergeVirtual` case, `mca_events_cover`, the well-founded
fold measure, and the GC closure revision. Nothing rehoming-specific there.

Rehoming-specific tier, in dependency order:

1. **Union predecessor-closure** (new, mechanical): antichain unions
   `E(m_1) u ... u E(m_j)` are `loOnA`-predecessor-closed (each member is a
   version event set; `loOnA` edges imply visibility). Feeds
   `isDepPreC_of_restrict` to restrict `GenDisc2C` to every scratch union.
2. **`rgaHonJ` at sub-pair unions** (new, medium): the join context
   (`RGA_HEnum_Discharge.lean:47`) must be presented at `(vis, U)` for each
   scratch union `U`. The witness configuration is the same real core; the
   clause `Cfg.vis a b <-> vis a b /\ a,b in U` needs the restriction
   configuration or a relaxed HonJ stated on a superset universe with
   membership side conditions. This is the analog of the mergeable queue's
   intermediate-union hook, first instance of the recorded residue.
3. **The virtual fold induction** (the genuinely new proof): scratch states
   are layer-canonical for their unions. Induction over the ascending-rank
   fold; each step instantiates the already-general delta lemma
   `rga_hEnum_discharged` (stated for arbitrary backward-closed `ev1, ev2`)
   at `ev1 := E(acc)`, `ev2 := E(m_i)`, with the inner recursion plus the
   covering proposition supplying `CanonFoldOK` at the sub-pair
   intersection. The K1/GenDisc route is forced: by section 5 a
   `noopFeasible` premise at unions would be unsatisfiable.
4. **Mirror case duplication** (mechanical but wide): the `Step3V.mergeVirtual`
   case through `RGA_Skeleton3`, the H/NF/Eq layers
   (`RGA_Instance_NF.lean`, `RGA_EqJoin_NF.lean`, `RGA_EqQuotient.lean`
   consumers), and `RGA_Honest_Residual.lean` (`HonCore` transfers unchanged:
   merges add no events and no visibility, `honCore_transfer` applies;
   `HonestDelivery` is untouched, merges consume no honesty).
5. **Statement hygiene**: canonicity is per scratch node for its own union;
   order-insensitivity is stated only for the returned LCA state (T8's
   order-dependent intermediates are the counterexample to anything
   stronger).

Estimated genuinely new content: items 1 to 3. Item 3 is the rehoming
instance of `virtualLCAState_canonical` and is where the equivalence quotient
earns its keep (merge is not `~=`-congruent in the LCA argument raw; the
quotient layer already carries the congruence kit).

## 8. How to run

    python3 whiteboard/litmus/rehoming_vlca_check.py

Exit 0 iff all asserted expectations hold (expected refutation firings are
passing assertions). Runs in well under a second; the verdict block prints
the C5 firing counts per suite.

## Addendum: errata from the mechanization pass

1. Bill items 1 and 2 cost zero: the union predecessor-closure is a
   three line closure fact inside the fold, and the mechanized
   EqJoinLemma3C_H / rgaHonJ shape already is this note's own
   alternative (the relaxed HonJ on a superset universe with
   membership side conditions).
2. Only ONE fold induction was owed, at the H layer: the Eq-quotient
   layers contain no step destructs, and the NF layer is precisely the
   refuted noopFeasible route with no production consumer at V, so its
   mirror was deliberately not built.
3. rga_hHext_discharged carried a dead reachability premise; the V
   route forced exposing a premise-free core, with the original kept
   verbatim as a wrapper.
