# Runtime GC for the ranked version store: the keep set and the commit GC-safety theorem

Status: mechanized in `Sal/ConditionedMRDTs/Metatheory/GC_Safety.lean` (task #94).
Companion of the stability-frontier discussion at the end of this note.

## 1. Setting

The ternary execution model (`ExecutionModel.lean`, `LCA_Lemma.lean`) runs a conditioned
MRDT `D` over configurations `C` carrying two layers:

* a replica-keyed core: per-replica head state `N : Replica -> Option State`, per-replica
  observed event set `L : Replica -> Option (Set Op)`, and a causal visibility relation
  `vis`;
* a ranked version store: `ver : Version -> Option (State x Set Op)` (the version's state
  and event set; `none` means unallocated), `head : Replica -> Option Version`, and a DAG
  `parents : Version -> List Version` with `parents_lt : p in parents v -> p < v`.

Write `E(v)` for the event set registered at an allocated version `v`. The transition
system `Step3` has four rules. CreateReplica starts a fresh replica with its head at the
pinned root version `0` (which `ver_init` fixes to `(init, empty)`). Apply extends the
issuing replica's head with a fresh version. Merge, the only rule that consults a
non-head version, requires an LCA: a version `vT` with `IsLCA parents v1 v2 vT` (it
reaches both heads and dominates every common ancestor) and `ver vT = some (sT, eT)`.
The configuration invariant `lca_events` (Lemma LCA, proved from the store invariant
`StoreInv`) gives `E(vT) = E(v1) /\ E(v2)`: the LCA's event set is exactly the
intersection of the merged heads' event sets. Query reads `N r` and leaves the
configuration unchanged.

The GC question: which store entries may the runtime reclaim without changing any future
behavior? Merges arbitrarily far in the future reach back into the store for their LCA
state, so the answer is not "everything below the heads".

## 2. The keep set

Fix a configuration `C0` (the prune point) with current heads `H = { v : head r = some v
for some r }`. Define, over allocated versions:

    Keep(C0)  = { v : exists heads h1 h2 (h1 = h2 allowed),
                      E(h1) /\ E(h2)  is a subset of  E(v) }
    Keep'(C0) = Keep(C0) union {0}
    Dropped(C0) = allocated versions of C0 not in Keep'(C0)

Taking `h1 = h2` shows every allocated head is in `Keep` (its own event set contains its
self-intersection), and with it everything event-set-above any single head. The root `0`
is pinned separately: the configuration structure demands `ver 0 = some (init, empty)`
forever, and CreateReplica rebases fresh replicas there, so `0` is not reclaimable in
this model regardless of its event set.

Pruning drops the store payload only:

    prune(C0).ver v = none      if v in Dropped(C0)
    prune(C0).ver v = C0.ver v  otherwise

with `N`, `L`, `vis`, `head`, and `parents` unchanged. Retaining the DAG skeleton
(`parents`, a `Nat -> List Nat` of ids, not states) is forced, not a convenience:
restricting `parents` to `Keep` changes the `IsLCA` predicate. Removing common ancestors
makes the domination clause easier to satisfy, so new LCA triples can appear whose event
sets violate the intersection law, and the pruned structure would fail its own
`lca_events` invariant. The reclaimable payload is the states and event sets, which is
where the memory is; the skeleton stays.

## 3. The three lemmas and the theorem

Lemma 1 (monotonicity, disjunctive form). Along any `Step3` run from `C0`, every current
head `v` with `ver v = some (s, e)` satisfies one of:

* HeadDom: some prune-time head `h` has `E0(h)` a subset of `e`, or
* Virgin: the only ancestor of `v` (in the current DAG) that was allocated at prune time
  is the root `0`.

The disjunction is forced by CreateReplica: a freshly created replica's head is the root,
whose event set contains no prune-time head's event set in general, and its lineage keeps
growing from `empty` until it first merges with a HeadDom lineage, at which point it
becomes HeadDom itself. Apply preserves each disjunct (the event set grows; the ancestry
gains only the fresh version). Merge takes the HeadDom disjunct if either argument has
it, and stays Virgin if both arguments are Virgin.

Lemma 2 (intersection containment; the LCA lands in the keep set). If a future merge
fires with head versions `v1, v2` and allocated LCA `vT`, then `vT` is not in
`Dropped(C0)`. Proof sketch: if `vT` was not allocated at prune time it was never
dropped. Otherwise `E(vT) = E(v1) /\ E(v2)` by `lca_events`. If both `v1` and `v2` are
HeadDom, with witnesses `h1, h2`, then `E0(h1) /\ E0(h2)` is a subset of
`E(v1) /\ E(v2) = E(vT)`, and the store extends allocated entries unchanged, so `vT` is
in `Keep(C0)` by definition. If either side is Virgin, then `vT`, being a prune-time
allocated ancestor of that side, must be the root, which is pinned.

Lemma 3 (prune commutation, forward simulation). Write `drop(C)` for `C` with the
`Dropped(C0)` entries of `ver` removed. Every `Step3` step `C -l-> C'` in the unpruned
run is matched by `drop(C) -l-> drop(C')` with the same label. CreateReplica and Query
touch no non-head version. Apply reads only the issuing head (kept, by Lemma 1 collapsed
to the self-pair or the root) and a fresh slot (never dropped: dropped slots were
allocated at prune time and allocation is permanent). Merge reads the two heads and the
LCA state, and Lemma 2 keeps the LCA. Since pruning does not touch `N`, replica reads are
literally equal, and Query steps carry identical values.

Theorem (gc_safety). For every `Step3` run `C0 -l1-> ... -ln-> Cn`, the pruned
configuration `prune(C0)` admits the run `prune(C0) -l1-> ... -ln-> drop(Cn)` with the
same label sequence, and `drop(Cn).N = Cn.N`: every replica read at every point of the
run is unchanged. Hypothesis: `StoreInv C0` (the store invariant, which plain
reachability supplies via `storeInv_reachable`).

Scope note on the converse direction. The pruned configuration can exhibit steps the
unpruned one cannot: a freed version slot can be re-allocated, and Apply's store-wide
timestamp freshness (`h_fresh_store`) quantifies over fewer entries after pruning, so a
timestamp recorded only in a dropped version's event set becomes reusable. In reachable
configurations every allocated version sits below some current head (each version was
once its replica's head and heads only advance), so every recorded event also lives in a
head's event set and the asymmetry is unobservable; that reachability invariant is not
part of the configuration structure and the converse simulation is deliberately not
mechanized. The theorem direction that GC-safety needs (nothing is lost) is the
mechanized one.

## 4. The head-sync countermodel, worked concretely

Head-sync is the discipline that future merge arguments are current heads (or their
descendants). In this framework the Merge rule enforces it syntactically: `v1, v2` are
read off the head map. The countermodel shows the discipline is load-bearing, not
pessimism: a merge from an old interior version genuinely needs a version outside the
keep set.

The configuration `Cex` (two replicas A = 0, B = 1; events `e1 = (1,0,10)`,
`e2 = (2,0,20)`, `e3 = (3,0,30)`, `e4 = (4,1,40)`):

    version  created by                 state           events            parents
    0        root                       {}              {}                []
    1        A applies e1 at 0          {10}            {e1}              [0]
    2        A applies e2 at 1          {10,20}         {e1,e2}           [1]
    3        B merges A (LCA 0)         {10,20}         {e1,e2}           [0,2]
    4        A applies e3 at 2          {10,20,30}      {e1,e2,e3}        [2]
    5        B applies e4 at 3          {10,20,40}      {e1,e2,e4}        [3]

Heads: A at 4, B at 5. Pairwise head intersections: `E(4) /\ E(5) = {e1,e2}`, plus the
self-pairs `E(4)` and `E(5)`. Membership in `Keep`:

    v = 2, 3: {e1,e2} contains {e1,e2}          kept
    v = 4, 5: heads (self-pairs)                 kept
    v = 1: E(1) = {e1} contains no pairwise head intersection    DROPPED
    v = 0: pinned root, in Keep' by fiat         kept

So `Dropped(Cex) = {1}` and pruning is strict (the FAIL companion of the SPOT: the
pruned store genuinely returns `none` at 1 while `Cex` returns `some`).

PASS: the future head merge A |><| B has `IsLCA parents 4 5 2` (common ancestors of 4 and
5 are {0,1,2}; both 0 and 1 reach 2), and 2 is kept: the pruned configuration still
registers `ver 2 = some ({10,20}, {e1,e2})`, hand-derived, and the merge fires with
reads at both heads unchanged.

Countermodel: version 1 is an interior version (no head points at it). It satisfies
`IsLCA parents 1 5 1`: it reaches itself, it reaches 5 through 2 and 3, and it trivially
dominates the common-ancestor clause with itself as target. So a widened Merge that
accepted the interior pair `(1, 5)` (a rewound replica, a checkpoint restore, a replica
missing from the head map) would demand `ver 1`, which pruning removed. The keep set is
exactly calibrated to the head map being complete; every out-of-band way of resurrecting
an old version breaks it. That is why head-sync is a hypothesis of the metatheorem and
not pessimism.

## 5. Caveats

Criss-cross. The Merge rule fires only when a version satisfying `IsLCA` exists and is
allocated. In criss-cross configurations (two incomparable maximal common ancestors) no
such version exists, Merge is disabled there by the step relation itself, and gc_safety
is vacuously unaffected: pruning cannot break a step that could not fire. The theorem
says nothing new about such configurations.

Virtual LCA (task #90). The planned virtual-LCA extension widens the Merge rule: where no
exact LCA exists, the merge synthesizes one from the maximal common ancestors (potential
LCAs). Those versions have event sets strictly BELOW the pairwise head intersection
(their union approximates it from below), while this note's keep set retains versions
whose event sets sit ABOVE some pairwise intersection. So under the widened rule the
present `Keep` would prune away exactly the versions the virtual merge needs. The keep
set must then be revisited: it has to additionally retain the below-approximations of
each pairwise meet (at least the maximal common ancestors of every head pair). The
mechanized theorem is stated against the exact-LCA rule and its `Keep` is correct for
that rule only.

Open membership. The head set is not closed: CreateReplica adds heads at the root at any
time. This is sound for the prune-time keep set because new lineages base at the pinned
root and are covered by the Virgin disjunct of Lemma 1; no recomputation of `Keep` is
needed when replicas join. Re-pruning at a later configuration uses that configuration's
own heads.

## 6. The stability frontier: same cut, two consumers

The meet of the current heads, `E(H1) /\ ... /\ E(Hn)`, is the stable cut: the set of
events every replica has already incorporated. No future merge can ever again place a
concurrent event below the cut, which is what the stability side-conditions of the VC
line consume (facts certified at the cut stay true under all future merges; escrow-style
arguments discharge their interference obligations below it).

The keep set is the other face of the same frontier. GC retains the upward closure of the
PAIRWISE meets `E(Hi) /\ E(Hj)`: every version whose event set dominates some pairwise
meet. The global meet is the intersection of the pairwise family, so the stable cut sits
at or below every pairwise meet; versions whose event sets lie strictly below every
pairwise meet are exactly the store entries no future LCA lookup can name, and they are
what pruning reclaims. One frontier, two consumers: the stability line reads it from
below (what is settled), the garbage collector reads it from above (what must be
retained). A runtime that already tracks the stable cut for stability VCs gets the GC
retention boundary from the same bookkeeping, at pairwise rather than global
granularity.

## Addendum (from the virtual-LCA design, task #90)

Two corrections from `virtual-lca-note.md`, recorded here so this note
stays accurate.

1. The criss-cross section above forecast that the union of the
   maximal common ancestors' event sets approximates the intersection
   from below. Under the store invariants actually carried
   (`StoreInv.origin` + `events_mono`) it is EXACT: Proposition 1 of
   the virtual-LCA note (the covering proposition). The virtual LCA
   therefore has precisely the intersection event set, and the Merge
   rule's semantic requirement is met natively.

2. When virtual merges land, the keep set must grow from the pairwise
   MCAs of the heads to the FIXPOINT of the head set under pairwise
   MCA (`mcasClosure`): the one-layer seed is one closure layer short,
   machine-witnessed by a depth-2 sync raising PrunedError under the
   one-layer rule and succeeding under the closure rule (harness T5).
   The runtime's `gc.js` must switch to the closure seed in the same
   change that introduces virtual merges; until then the criss-cross
   gate makes the one-layer seed sufficient.
