# Virtual LCAs: recursive merges for criss-cross configurations

Task #90, design phase. Pen-and-paper plus Python
(`whiteboard/litmus/virtual_lca_check.py`); no Lean in this phase. The Lean
bill is section 7.

## 1. Setting

The ternary execution model (`Sal/ConditionedMRDTs/Framework/ExecutionModel.lean`,
`Sal/ConditionedMRDTs/Metatheory/LCA_Lemma.lean`) runs a conditioned MRDT over a
ranked version store: `ver : Version -> Option (State x Set Op)` registers each
allocated version's state and event set `E(v)`, `parents` is a DAG with
`parents_lt : p in parents v -> p < v` (a version id is its allocation rank),
`Reaches` is ancestry, and `IsLCA parents v1 v2 vT` says `vT` reaches both heads
and dominates every common ancestor. The Merge rule (`Step3.merge`,
`LCA_Lemma.lean:471`) fires only when such a `vT` exists and is allocated; the
store invariant (`StoreInv`, `LCA_Lemma.lean:50`, with fields `parents_alloc`,
`events_mono`, `origin`) then gives `E(vT) = E(v1) /\ E(v2)`
(`lca_events_of_storeInv`; carried on configurations as the `lca_events` field,
`ExecutionModel.lean:164`).

In a criss-cross configuration the common ancestors of two heads have two or
more maximal elements, no version satisfies `IsLCA`, and Merge is disabled. The
JS runtime makes this an explicit gate (`runtime/src/lca.js`,
`CrissCrossError`), and its PBT showed the shape is routine under honest
head-sync: 592 gated sync attempts in 220 randomized trials. The extension
studied here is the git-recursive-merge move: merge the antichain of maximal
common ancestors first, recursively, and use the result as the LCA.

Write `M = MCA(v1, v2)` for the maximal common ancestors of `v1, v2` (maximal
in `Reaches`, which is a partial order by `reaches_le` and rank antisymmetry).

## 2. The rule

VirtualLCA(v1, v2):

* `M := MCA(v1, v2)`. Nonempty (the pinned root is a common ancestor); when
  the heads are incomparable every member is a strict ancestor of both.
* If `M = {m}`: return `m`. This is the existing rule; `lca_events` applies.
* Otherwise sort `M` ascending by rank (the canonical order: version ids are
  allocation ranks, so this is deterministic) as `m_1 < ... < m_k` and fold:
  `acc := m_1`; for `i = 2..k`, `acc := node(parents = [acc, m_i], state =
  mergeL (state of VirtualLCA(acc, m_i)) (state acc) (state m_i), events =
  E(acc) u E(m_i))`. Return `acc`.

The final head merge then runs the ordinary ternary merge with the returned
state in the LCA slot. The fold nodes ("scratch" nodes) exist so that the
nested `MCA` queries are well posed; nothing references them afterwards, so
they are never ancestors of real heads and cannot perturb later queries. Two
structural facts keep the recursion clean:

* `m_i` is never in the support of `acc` (the antichain members are pairwise
  incomparable), so every sub-pair is incomparable and its MCAs are proper.
* `MCA(acc_j, m_{j+1})` consists of real (allocated) versions only, and each
  of its members is a member of `MCA(m_i, m_{j+1})` for some `i <= j`: the
  common-ancestor set of the sub-pair is the union of the pairwise
  common-ancestor sets, and a maximal element of a union is maximal in any
  member set that contains it.

## 3. E(virtual) is exactly the intersection

**Proposition 1 (covering).** Let `S` be a finite nonempty set of allocated
versions and `w` an allocated version, `CA(S, w) = { x : (exists u in S,
Reaches x u) /\ Reaches x w }`, and `MCA(S, w)` its maximal elements. Under
`StoreInv`:

    Union over m in MCA(S, w) of E(m)  =  (Union over u in S of E(u)) /\ E(w).

With `S = {v1}, w = v2` this covers the head pair; with `S` the support of a
scratch node it covers every sub-pair of the recursion; with `|MCA| = 1` it
degenerates to `lca_events_of_storeInv`.

Proof. (subset) Each `m` reaches some `u in S` and reaches `w`;
`storeInv_events_mono_reaches` twice. (superset) Let `e` lie in `E(u')` for
some `u' in S` and in `E(w)`. `StoreInv.origin` gives a generator version `v0`
with `e in E(v0)` that reaches every version whose event set contains `e`, so
`v0` reaches `u'` and `w`: `v0 in CA(S, w)`. Every member `x` of `CA(S, w)`
reaches a maximal member: among the members reachable from `x` (nonempty,
finitely many, ranks bounded by `min`), take `m` of maximal rank; any strictly
Reaches-larger member would be reachable from `x` with strictly larger rank
(`reaches_le`), contradicting the choice. So `v0` reaches some
`m in MCA(S, w)`, and `events_mono` along that path puts `e in E(m)`. QED.

Since the fold unions event sets, the returned virtual node has event set
`Union E(m_i) = E(v1) /\ E(v2)`: exactly the event set the Merge rule
requires of an LCA. This sharpens the forecast in `whiteboard/runtime-gc-note.md`
section 5, which said the union "approximates the intersection from below":
the approximation is exact. Each member is strictly below the meet when
`k >= 2`; the union is the meet on the nose.

Delimitation: `origin` is load-bearing. In a model that can apply the same
event at two incomparable versions (op-based redelivery, no store-wide
timestamp freshness), the event has two incomparable birth sites, neither a
common ancestor, and the union strictly undershoots the intersection.
Countermodel: `e` applied independently at the root on both branches gives
`E(v1) /\ E(v2) = {e}` while the sole MCA is the root with `E = {}`. `Step3`
excludes this by `h_fresh_store`; the runtime by construction (an op is born
at exactly one commit). So the covering invariant the task forecast is not a
new invariant: it is `StoreInv.origin` plus `events_mono`, already carried and
maintained (`storeInv_step`, `storeInv_reachable`).

## 4. Termination and order-insensitivity

Termination is unconditional. Define the real support of a node: allocated
versions it reaches (a scratch node's support is the union of its parents').
Measure a call on `(a, b)` by the size of `support(a) u support(b)`. Every
version in any sub-pair's support lies in `CA(v1, v2)`, and `v1` itself does
not (incomparable heads), so the measure strictly drops at each nesting level;
within a level the fold index drops. Finite store, so the recursion
terminates. No configuration invariant is needed for well-definedness, only
`parents_lt` for the rank order.

Determinism is by the fixed ascending-rank fold. Order-insensitivity is a
theorem, not an obligation, for datatypes with a join lemma: canonical states
of a fixed event set are unique (`isCanonicalState_unique`,
`Sal/CRDTs/Metatheory/Merge_Linearization_Set.lean:991`), and section 5 shows
every fold order lands on a canonical state of the same union. For datatypes
without full canonicity, order-insensitivity (up to the datatype's
equivalence) is an obligation to record. Git's own recursive strategy folds in
commit-date order and is known to be order-sensitive on conflicting merges;
the rank fold plus canonicity is what removes that defect here. Empirically
(P2 below) raw states, and with them reads, were order-independent for both
tested datatypes.

## 5. The semantic obligation per datatype

The adequacy induction consumed two facts about the LCA slot: its event set is
the intersection (`lca_events`), and its registered state is canonical for
that event set (the `GoodConfig3` invariant threaded through
`goodConfig3_merge_at`, `Metatheory/Adequacy.lean:283`). The virtual
construction re-supplies both from one per-datatype hypothesis, the ternary
join lemma the framework already centers on:

`JoinLemma3` / `JoinLemma3At` (`Framework/VC_Set.lean:65` / `:81`): for
backward-closed event sets with canonical states, `mergeL` of the canonical
state of the intersection produces the canonical state of the union.

**Claim (virtual join).** If every allocated version's state is canonical for
its event set and `JoinLemma3At` holds at the configuration, then every fold
node's state is canonical for its (union) event set; in particular the
returned virtual state is canonical for `E(v1) /\ E(v2)`.

Induction over the fold. Base: the `m_i` are allocated, canonical by
hypothesis. Step: the inner LCA slot of the sub-pair `(acc, m)` is canonical
for `E(acc) /\ E(m)` by the inner recursion plus Proposition 1 applied to the
sub-pair; `acc` and `m` are canonical by induction; `JoinLemma3At` yields
canonicity at the union. Side conditions: backward closure (the two
visibility-closure hypotheses of `JoinLemma3At`) is preserved by union and
intersection, so all intermediate sets stay in the hypothesis class.
Invariance (`D.Inv`) of fold states comes from `inv_mergeL` closure. Note
`IsCanonicalState` is a property of a (configuration, event set, state)
triple, not of allocated versions, so fold states need no allocation and no
reachability to carry it.

Consequences:

* Datatypes discharging `JoinLemma3` outright (`join_lemma3_of_cd`,
  `join_lemma3_of_cd_feasible`, `Adequacy.lean:541/:979`) owe nothing new.
  The embed RGA is the model case: fold canonicity means the merged antichain
  state is the fold of the union event set, and the Python oracle check
  confirms it at every merge.
* Datatypes whose join lemma holds only in a witness class or quotient
  (`JoinLemma3AtW`, `Metatheory/WitnessClass.lean:130`; `JoinLemma3AtWC`,
  `Metatheory/WitnessCoherence.lean:136`; `JoinLemma3FAt`,
  `Metatheory/Product.lean:830`; `JoinLemma3F`, `VC_Set.lean:211`) owe a
  genuinely new condition: their witness or closure predicate must hold at
  the intermediate antichain unions `E(m_1) u ... u E(m_j)`, which are unions
  of below-meet sets and are neither head event sets nor meets. Call this the
  intermediate-union condition; it is the honest per-datatype residue of the
  extension (the mergeable queue's honest-history hook is the first instance
  to re-check).

## 6. GC: the keep set is one closure layer short

Current mechanized rule (`Metatheory/GC_Safety.lean`): `keepSet` (`:87`)
retains versions whose event sets contain some pairwise meet of prune-time
heads, and `lca_not_dropped` (`:343`) shows future exact LCAs are retained.
Under virtual LCAs this prunes exactly what the recursion reads: antichain
members sit strictly below the meet. The runtime rule (`runtime/src/gc.js`)
seeds Keep with the pairwise MCAs of the current heads (one layer) and keeps
their upward closure; that retains depth-1 needs but not the MCAs of the MCAs.

Revision. Let `mcasClosure(H)` be the least superset of the head set closed
under pairwise `MCA` (finite: ranks only decrease). Keep the upward event-set
closure of its members:

    keepSetV(C) = { v allocated : exists w in mcasClosure(heads C),
                                  E(w) subset of E(v) }  union  {0}.

This contains the old `keepSet` (any MCA of a head pair has event set inside
that pair's meet, so anything above a meet is above a closure member) and
covers every recursion read (section 2's containment of sub-pair MCAs in
real-pair MCAs, iterated, lands all reads in the closure).

Future-proofing (the `lca_not_dropped` analog): a prune-time-allocated version
that a future virtual resolution reads lies in `keepSetV`. The argument needs
one new reachability fact, the gateway lemma: after the prune point, versions
extend only current heads, and prune-time heads that are still current are
prune-time heads, so every ancestry path from a prune-time version to a
post-prune version passes through a prune-time head (or the pinned root). A
prune-time `w` in `MCA(v1', v2')` therefore reaches the future heads through
prune-time heads `h_a, h_b`, sits in `CA(h_a, h_b)`, and maximality transfers
downward (a dominating common ancestor of `(h_a, h_b)` would dominate it for
`(v1', v2')` too): `w in MCA(h_a, h_b)`, layer one of the closure. Deeper
recursion reads stay in the closure by the same containment. The gateway
lemma is an ancestry-form strengthening of the `HeadDom`/`Virgin` disjunction
(`GC_Safety.lean:190/:194`) and is the main new GC proof.

The Python T5 check demonstrates both halves on a directed nested criss-cross:
pruning by the runtime's one-layer rule kills the depth-2 reads (the sync
raises); pruning by the closure rule keeps them, still prunes a genuinely
dead interior commit, and the post-GC sync equals the no-GC control.

## 7. The Lean mechanization bill

* `Framework/ExecutionModel.lean`: an `IsMCA` predicate beside `IsLCA`; the
  well-founded fold measure (from `parentStep_wf`, `reaches_le`).
* `Metatheory/LCA_Lemma.lean`: Proposition 1 as `mca_events_cover`
  (set-support form, generalizing `lca_events_of_storeInv`); a pure recursive
  `virtualLCAState`; a new `Step3.mergeVirtual` constructor (allocating only
  the final `vm`; `storeInv_step` extends via `storeInv_merge_extend`).
  `Configuration.lca_events` is untouched (it is `IsLCA`-gated).
* `Framework/VC_Set.lean`: unchanged. The per-datatype VC surface for
  `JoinLemma3` datatypes does not move; that is the headline.
* `Metatheory/Adequacy.lean`: `virtualLCAState_canonical` (the section 5 fold
  induction from `JoinLemma3At` + `mca_events_cover`); a
  `goodConfig3_mergeVirtual_at` beside `goodConfig3_merge_at` (`:283`);
  re-thread `goodConfig3_merge` (`:521`), `ra_linearizable3_of_join`
  (`:793`), and the `JoinLemma3F` route (`goodConfig3_mergeF`, `:1232`).
* `Metatheory/HonestReach.lean`: the induction's merge case (`:65`) gains the
  sibling case; `goodConfig3_of_honest_reach` (`:52`) and
  `ra_linearizable3_of_honest_reach` (`:74`) re-thread mechanically.
* Case duplications where `Step3.merge` is destructed: `GoodConfig3H.lean`
  (`:571`), `GoodConfig3NF.lean` (`:398`), `GenericSafety.lean` (`:418`
  region), the Eq-quotient layers (`GenericEqQuotient.lean`,
  `GenericEqQuotient_H/NF.lean`); the witness-class layers owe the
  intermediate-union condition (section 5).
* `Metatheory/GC_Safety.lean`: `mcasClosure`, `keepSetV` (revising `keepSet`
  `:87`); the gateway invariant added to `GCInv` (`:202`);
  `mcaClosure_not_dropped` replacing `lca_not_dropped` (`:343`);
  `step_dropVer` (`:388`) and `gc_safety` (`:519`) restated on the widened
  LTS.

Two proofs are genuinely new: the fold induction (`virtualLCAState_canonical`)
and the gateway invariant. Everything else is case duplication.

## 8. Python verdicts (`whiteboard/litmus/virtual_lca_check.py`)

* P1: `E(virtual) = E(v1) /\ E(v2)` asserted at every resolution, never
  failed (thousands of resolutions across all runs).
* P2: ascending vs descending antichain folds produced identical raw states
  at every criss-cross sync, both datatypes.
* T1: the runtime's routine criss-cross shape converges on the embed RGA and
  the OR-set; reads equal hand-derived values and the fold oracle.
* T1F (fail companion): on a symmetric delete shape, every single-MCA pick
  resurrects one deleted element (pick `u` revives `y`, pick `v` revives
  `x`); the virtual LCA revives neither.
* T2: 500 randomized embed trials plus 300 OR-set trials, 3 to 5 replicas,
  no criss-cross gate: all converged, reads matched the full-history fold
  oracle after every merge. Criss-crosses in 113/500 and 67/300 trials.
  A denser probe (200 trials, 6 replicas, sync-heavy) hit criss-crosses in
  176/200 trials with antichain sizes `{2: 1116, 3: 10}` and resolution
  nesting depths 0 through 7 (recursion depth 8): rivalry propagates upward
  (rival joins of rival joins), so a depth-limited implementation would gate
  again; the general recursion is needed.
* T3: directed nested criss-cross exercises recursion depth 2 by hand;
  converges to the hand-derived read.
* T5: the keep-set verdicts of section 6.

## 9. What this settles and what it opens

Settled: the criss-cross gate can be lifted with no new per-datatype VC for
join-lemma datatypes; the covering invariant is the already-carried
`StoreInv.origin`; the virtual LCA's event set meets the framework requirement
exactly; termination is unconditional; the GC keep set must be reseeded by the
MCA closure. Open: the intermediate-union condition for witness-class join
lemmas (first instance: the mergeable queue's hook), and the gateway lemma's
mechanization. A candidate follow-up question: whether `keepSetV` is tight,
i.e. whether every closure member is readable by some future virtual merge
(the converse of future-proofing; T5's `c1` shows non-members can be dead, but
tightness of the closure itself is unexamined).

## Addendum: errata from the mechanization pass

1. The extension landed as a conservative NEW step relation `Step3V`
   (with `Step3V.base` embedding every old step and `mergeVirtual` the
   one new case) rather than a new constructor inside `Step3`. Forced:
   in-place widening breaks exhaustive `Step3` case analyses in
   instance files the bill omitted (`Peritext_Composed/Supplies.lean`,
   `RGA_Rehoming/RGA_Honest_Residual.lean`, `RGA_HHext_Discharge.lean`).
2. Section 7's claim that everything beyond the two new proofs is case
   duplication is wrong for the H, NF, and Eq-quotient layers: their
   merge cases consume the registered slot's layer canonicity, so each
   owes its own fold induction, and the GenDisc route additionally
   owes GenDisc at intermediate antichain unions (consistent with
   section 5, contradicting section 7's classification). These mirrors
   are the recorded residue; the production Eq-quotient capstones do
   not yet run over `Step3V`.
3. `GCInvV` extends `GCInv` (keeping the tier-1 artifact intact) and
   needed two fields beyond the gateway: `parentsExt` (prune-time
   parent lists immutable) and `store₀`; the maximality-transfer moves
   genuinely consume both. The well-founded measure landed in
   LCA_Lemma.lean, not ExecutionModel.lean (import surface).
4. `gc_safetyV` kept the headline shape of `gc_safety` unchanged; the
   gateway forced no statement change.
