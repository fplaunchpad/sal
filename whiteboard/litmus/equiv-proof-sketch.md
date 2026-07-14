# DeltaTreeV3 ≡ published tombstoned RGA: simulation proof sketch

Task #69. Companion code: `equiv_stress.py` (hostile sweeps, small-string
churn, targeted scenarios, trace minimizer, negative control); the paired
lockstep checker is `delta_tree.PairedV3RGA`. Empirical certificate at the
end. Status: **conjecture survived every attack regime (30,782 executions /
scenarios, ~10M lockstep read-equality checks, 0 divergences); sketch below,
with 8 flagged gaps/assumptions (F1–F8).**

## 0. The two objects

Shared op alphabet: `ins(x, a)` (fresh id `x`, anchor `a`; `a = 0` = front),
`del(d)`. Ids are totally ordered; `0` is reserved for the root.

**RGA** (litmus `Tombstoned`). State `σ : id ⇀ (anchor, alive)`; anchor
immutable, alive monotone-down. `read(σ)` = pre-order DFS of the birth tree
(child of its anchor), siblings in **descending id** order, emitting live
nodes only (tombstones traversed, skipped). Merge = pointwise union with AND
on alive.

**DeltaTreeV3** (`delta_tree.DeltaTreeV3`). State `(r, led)`:
`r : id ⇀ (parent, loF, hiF)` — geometric register over **live** nodes only,
fractions relative to the parent's frame; `led : id → birth parent` — the
ledger, retained for dead ids too. `read` = DFS over `r`, kids by descending
`(loF, id)`. Local `ins` carves the top slot in the anchor's headroom;
local `del` pops the record and isometrically folds the geometric children
into the dead slot; `merge` = OR-set survival + ledger-chain arbitration +
canonical re-render (never reads branch geometry except for survival).

## 1. Model assumptions (the honesty envelope)

The equivalence is a theorem about **honest executions of the version-DAG
(state-based / MRDT) model** — exactly what `pbt.py` and the churn harness
generate — not about arbitrary op soups:

- **A1 (Lamport freshness).** An `ins(x, a)` applied at origin state `s` has
  `x >` every id occurring in `s` — **including dead ids** (the ledger /
  tombstone domain), not just the live ones: chain comparisons can be
  decided at a dead coordinate. (Any causal implementation with Lamport ids
  provides this, since dead ids were also in the causal past; the harnesses
  use a global counter.)
- **A2 (anchor liveness at origin).** `a = 0` or `a ∈ read(s)` at the
  origin — clients edit against their own read.
- **A3 (delete liveness).** `d ∈ read(s)` at the origin. (Almost free:
  deletes of dead/unknown ids are no-ops in *both* designs; A3 is only
  needed for the "RGA state is a pure function of the event set" corollary.)
- **A4 (LCA honesty).** Every merge `(L, A, B)` has
  `events(L) = events(A) ∩ events(B)` (pbt's "common past ⊆ LCA"
  discipline). Two consequences are used:
  - **no-resurrection**: an id dead in `L` is dead in `A` and `B`
    (deletes are permanent, branches extend `L`);
  - **birth visibility**: an id known to both `A` and `B` is known to `L`
    (each id is born exactly once).

## 2. The relation R (an erasure map plus a cache-coherence invariant)

Define the **erasure** `E(r, led) = σ` by
`dom σ = dom led` and `σ(x) = (led(x), x ∈ dom r)`.

So the ledger + the register's *domain* literally **is** an RGA state; the
fractions are extra. The relation:

```
R((r, led), σ)  :=   σ = E(r, led)                                   (R1–R3)
                   ∧ led is birth-closed and birth-decreasing         (R-led)
                   ∧ G ∧ H                                            (geometric sanity)
                   ∧ read_v3(r) = canon(led, dom r)                   (R4, cache coherence)
```

with the components:

- **R1** `dom σ = dom led` (both record every id ever seen; neither prunes).
- **R2** birth anchors agree: `σ(x).anchor = led(x)`.
- **R3** live sets agree: `dom r = {x | σ(x).alive}`.
- **R-led** (ledger discipline) `led` is *birth-closed* (the birth parent of
  any entry is `0` or an entry — so chains never dangle) and
  *birth-decreasing* (`led(x) < x`, from A1+A2 — so chains are finite and
  the merge's `live_par` climb terminates).
- **G** (laminarity) for every geometric parent, the children's relative
  intervals are pairwise disjoint with positive width, strictly inside
  `(0, 1)`; consequently the absolute intervals form a laminar family in
  which containment = geometric ancestry.
- **H** (headroom) at every geometric parent, `max child hiF < 1` (so the
  next local carve has positive width — the invariant whose violation was
  v2's residual PBT failure).
- **R4** the geometric read equals the **canonical order**
  `canon(led, S)`: enumerate `S` in increasing **chain-lex** order, where
  `chain(x)` is the birth path `root → x` read off `led`, levels compared
  by *descending id*, and a proper prefix sorts *before* its extensions.
  (The code encodes this as Python list-lex over negated ids.)

Note on the task's candidate relation ("`led` restricted to live ∪
chain-reachable ids = the RGA tree including tombstones"): the implemented
v3 never GCs the ledger, so the *stronger* R1 (full domain equality) holds
and is what we use. The restricted form is what R1 must weaken to if a
future v3 garbage-collects ledger entries unreachable from live chains;
survival and arbitration only ever consult live chains, so the proof should
survive that weakening — but then E is no longer total on `dom σ` and R2/R3
must be re-scoped. Flagged as the GC variant (F8).

**Theorem (observational equivalence).** In every honest execution (A1–A4),
every reachable paired version satisfies `R`; in particular
`read_v3 = read_rga` at every apply, merge, and read.

## 3. The canonicality lemma (the crux, RGA side)

**Lemma 1 (canonical order).** For any RGA state σ,
`read_rga(σ) = canon(anchors(σ), live(σ))`.

*Proof.* `read_rga` is the pre-order DFS of the birth tree with siblings in
descending-id order, emitting live nodes only. Pre-order DFS of a tree whose
siblings are ordered by any per-level key enumerates *all* nodes in
lexicographic root-path order with prefixes first (a node precedes its
descendants; distinct siblings' subtrees are contiguous, ordered blocks).
Restricting an ordered enumeration to the live subset preserves order. ∎

This is rigorous. It is also the design's headline: the canonical order is a
pure function of the *identity data* (birth forest + live set), so any state
carrying that data — with tombstones (σ) or with a ledger (v3) — can realize
the same read.

## 4. The v3 read is a laminar linearization (geometry side)

**Lemma 2 (laminar read).** If `r` satisfies G (+ parents live or 0), then
`read_v3(r)` enumerates `dom r` in the order: `x` before `y` iff
`I(x) ⊃ I(y)`, or `I(x)`, `I(y)` disjoint with `I(x)` above `I(y)` — where
`I(·)` is the absolute interval (affine composition down the root path).
In particular the read is a pure function of the laminar family
`{I(x)}` — and the id tiebreak in `_kids` is dead code on reachable states
(strict disjointness ⟹ no `loF` ties).

*Proof.* Within one parent's frame, descending `loF` = descending absolute
position (same affine map, order-preserving); children's intervals are
strictly inside the parent's, so "parent first, then children top-down,
recursively" is exactly the stated laminar order. Induction on the tree. ∎

**Lemma 2′ (folds are read-invariant deletions).** A local `del d` preserves
G, H, and satisfies `read' = read − d`.

*Proof sketch.* The isometric fold re-parents `d`'s geometric children with
`I(c)` unchanged (affine composition is exact over ℚ). The family
`{I(x)} − {I(d)}` is still laminar, containment still equals the new
ancestry (children land under `d`'s old parent, whose interval contains
`I(d) ⊃ I(c)`), so by Lemma 2 the read drops exactly `d`. H at the parent:
folded children's `hiF < d`'s old `hiF ≤` old max `< 1`. ∎

## 5. Preservation of R

**(i) Local `ins(x, a)`.** RGA adds `x ↦ (a, True)`; v3 adds
`led(x) = a` and carves the top slot at `a`. R1–R3, R-led immediate
(`x > all`, `a` known). Geometry: the new slot's `loF = base + w/4 >
base = max sibling hiF`, width `w/4 > 0` (H), new `hiF = base + w/2 < 1`
(H preserved), disjoint from all siblings (G preserved). Reads: v3 emits `x`
immediately after `a` (top child, no descendants); canonically,
`chain(x) = chain(a)·x` and by **A1** `x` exceeds every id in the state, so
`x` sorts before every other extension of `chain(a)` (first coordinate) and
inherits `a`'s verdict against everything else (comparison decided at or
before `a`'s last coordinate; prefix-first puts `a` itself before `x`).
Both reads = old read with `x` inserted immediately after `a` (at the front
when `a = 0`). R4 preserved. ∎(mod F1, F2)

**(ii) Local `del(d)`.** RGA flips the flag: canonical order is defined on
ids independently of liveness, so `read' = read − d`. v3: Lemma 2′ gives
`read' = read − d`. Ledger untouched = tombstone retained (R1, R2); both
live sets drop `d` (R3). R4 preserved. ∎

**(iii) Merge `(L, A, B)` with R on all three inputs and A4.**

*Survival (R3).* v3 computes `surv = (L∩A∩B) ∪ (A∖L) ∪ (B∖L)` over register
domains; RGA takes AND of alive flags over the sources knowing the id.
Case analysis on an id `x` of the merged domain:
  1. live at `L`: both reduce to `alive_A ∧ alive_B` (R3 on inputs);
  2. known to `L` but dead there: RGA gives dead; v3 must not admit `x` via
     `A∖L` — excluded by **no-resurrection** (A4);
  3. born on the A branch: unknown to `B` by **birth visibility** (A4),
     both reduce to `alive_A`; symmetrically for B. ∎
*Ledger (R1, R2, R-led).* Union of coherent ledgers (single birth ⟹ agree
where overlapping); closure and decrease are preserved by union.
*Arbitration + render (R4, G, H).* Two lemmas:

**Lemma 3 (collapse coherence).** Let `S` = survivors, and for `x ∈ S` let
`par(x)` = the nearest **surviving** strict ancestor on `x`'s birth chain
(or 0) — what `live_par` computes (terminating by R-led). Then pre-order DFS
of the collapsed forest `(S, par)`, with each node's children sorted by
ascending `chain`, enumerates `S` in chain-lex order, i.e. equals
`canon(led', S)`.

*Proof sketch.* For `k` a collapsed child of `p`, the collapsed subtree at
`k` is exactly the cone `{y ∈ S : chain(k) ≤prefix chain(y)}` (a surviving
`y` whose chain passes through `k` has its nearest surviving ancestor at or
below `k`, inductively). Chain-lex sorts each cone contiguously with its
apex first (prefix-first), and cones of distinct siblings never interleave
(order decided at the first differing coordinate). Note collapsed *siblings*
are never prefix-comparable (a surviving prefix would be the parent), so
prefix-first is only exercised across levels, which DFS realizes
structurally. Concatenating cones in sibling order = global chain-lex sort;
induction. ∎

**Lemma 4 (render realization).** `render(p)` walks the chain-sorted kids
display-last-first, assigning `(base + w/4, base + w/2)`, `w = 1 − base`:
after `n` kids, `base = 1 − 2⁻ⁿ`. So slots are pairwise disjoint, positive
width, strictly inside `(0,1)` (G), `max hiF = 1 − 2⁻ⁿ < 1` (H), and
descending `loF` = ascending chain = display order. Hence the merged state's
read (Lemma 2) = the collapsed DFS (Lemma 3) = `canon(led', surv)` (R4). ∎

**(iv) R ⟹ read-equality.**
`read_v3 = canon(led, dom r)` (R4) `= canon(anchors(σ), live(σ))` (R1–R3)
`= read_rga(σ)` (Lemma 1). ∎

Induction over the version DAG (base: both states empty) gives the theorem.

## 6. Corollaries

- **C1 (reads are a function of the event set).** With A3, the RGA state at
  any honest version is the pointwise fold of its event set; hence the v3
  read — despite its history-dependent fractions — is a pure function of
  the event set. Convergence (pbt's CONV) is free.
- **C2 (anomaly-profile identity).** Every display-level property is shared
  *exactly*: v3 inherits precisely the published RGA's anomalies (the h/L19
  backward-run interleaving) and nothing else. Equivalence ≠ correctness
  (the RA-lin spec-limit memory applies to both equally).
- **C3.** No duplicates, OR-set survival, idle-branch identity — inherited
  from the RGA via (iv).

## 7. Flagged gaps and load-bearing assumptions

- **F1 (A1 is load-bearing, not incidental).** At a local insert, v3
  arbitrates by *recency* (top slot), the RGA by *id*. They coincide only
  because a fresh Lamport id dominates its causal past. An execution
  violating A1 is an immediate countermodel — so the Lean statement must
  carry A1 as a per-step hypothesis (HonestDelivery-style, as in the RGA
  capstone), not fold it into the datatype.
- **F2 (A2 is a hard model boundary).** Under op-based causal delivery an
  insert can arrive with a *tombstoned* anchor: the RGA displays the child;
  v3 attaches it to a nonexistent geometric parent and the node is
  unreadable until some merge rehomes it. The designs genuinely differ
  outside the state-based/version-DAG model. The theorem is about the MRDT
  model only; do not quote it for op-based RGA.
- **F3 (A4 / no-resurrection).** v3's OR-set survival vs the RGA's AND-merge
  agree *only* under honest LCAs; with a dishonest LCA, v3 resurrects where
  the RGA stays dead — a divergence, not just an anomaly. The case analysis
  in 5(iii) silently uses delete-permanence, single-birth, and knowledge
  monotonicity; each is an event-system invariant that a mechanization must
  discharge separately (the reachability/conditioning layer, not the VCs).
- **F4 (Lemma 2 is the least battle-tested step).** "DFS-by-loF = laminar
  linearization" quantifies over all reachable geometries; its hypotheses
  (strict disjointness, positive widths, strict nesting) must survive every
  operation, and v1/v2 died precisely in this layer (frame mixing; zero-
  width mints = H violations). Mitigations in v3 that the proof exploits:
  merges *never* fold (they re-render wholesale), so only *single-node*
  local folds occur; and render restores `base = 1 − 2⁻ⁿ` headroom. The
  fold-preserves-laminarity argument (Lemma 2′) should be its own
  mechanized lemma; it silently uses exactness of ℚ arithmetic.
- **F5 (exact arithmetic).** Fractions are exact (Python `Fraction`, ℚ in
  Lean). Floating point breaks G silently. Denominators grow ~4^depth
  between renders and are reset by each merge render — a perf remark, but
  also why "the ledger is the arbitration substrate" matters: no order
  decision ever reads the fractions across a merge.
- **F6 (encoding lemmas).** Chain-lex is *encoded* as Python list-lex over
  negated ids, prefix-first for free; descending-id sibling sort is encoded
  as `reverse=True`; render realizes display order by iterating
  `reversed(ks)`. Three tiny "the code realizes the abstract order" lemmas —
  historically where the bugs hid, so they belong in the mechanization
  explicitly.
- **F7 (per-level vs global order in step (i)).** The insert-position
  argument compares `chain(x)` against *all* live chains, not just siblings;
  the two-paragraph argument in 5(i) covers extensions vs non-extensions of
  `chain(a)`, but a mechanization should instead prove the reusable lemma
  "inserting a chain-maximal fresh extension of a live node's chain inserts
  immediately after it in `canon`" — stated once, used by both (i) and
  Lemma 3's cone bookkeeping.
- **F8 (statement shape for Lean; GC variant).** The clean factorization:
  `E` is a *homomorphism* of MRDT algebras on the ledger+liveness component
  (`do_ ; E = E ; do_rga`, `merge ; E = E-merge` — small case analyses,
  5(iii)a), and R4/G/H is a *cache-coherence invariant* of the geometric
  component. The delta tree is then literally "the published RGA + a
  geometric read cache", and the obligation splits as homomorphism (easy) +
  cache coherence (the content) — matching the repo's HonestReach ×
  conditioning pattern. If the ledger is ever GC'd to live-chain scope, R1
  weakens to an inclusion and E stops being total on `dom σ`; survival and
  arbitration only consult live chains, so the theorem should survive, but
  that variant is unproven and untested.

## 8. Empirical certificate (this task's runs; all via the lockstep pair)

Baseline (pre-existing, `delta_tree.py __main__`): full battery + 120 + 300
DAG PBT executions, clean. New adversarial evidence (`equiv_stress.py`,
seeds fixed and reproducible; logs in the session scratchpad):

| regime | executions | divergences |
|---|---|---|
| targeted scenarios T1–T10 (dead-interior/deep-insert, full-chain kill with root rehoming, same-anchor bursts ± double anchor-kill, del/re-ins cycles × 3 branches × all merge topologies, multi-epoch dead-ancestor stacks, tie-inheritance under dead anchor, cross-branch chain kill, stale fork + delete, front churn, fast-forward re-render after deep folds, idle-branch identity) | 12 | 0 |
| hostile DAG-PBT grid: p_del {0.4, 0.5, 0.6} × p_merge {0.4, 0.7} × shapes (4r,8rd), (6r,12rd), (8r,16rd), (10r,20rd) at ≤2 ops/turn and (4r,8rd), (6r,12rd) at ≤4; supplement (8r,16rd), (10r,20rd) at ≤4 | 29,800 | 0 (and 0 shared anomalies) |
| small-string churn (cap 6–10 live chars, 4–8 replicas, 200–500 rounds, p_merge 0.5–0.75, forced deletes over cap): ~1.01M ops, 332,141 legal LCA merges; probe: dead-ancestor depth on live birth paths up to **32**, ledger up to 304 ids vs ≤ 14 live | 970 | 0 (and 0 CONV mismatches) |
| **total** | **30,782** | **0** (~10M lockstep read-equality checks) |

Negative control (test of the test): the *refuted* v1 `DeltaTree` paired
against the RGA through the identical churn harness is caught within 3
seeds, and the delta-debug shrinker minimizes the 12-event trace to an
honest 4-event countermodel (`ins 2@0; ins 3@0 ∥ ins 4@0; merge` —
v1 reads `[3,4,2]`, RGA `[4,3,2]`). The machinery detects real divergence
and minimizes it; the clean table above is therefore evidence, not silence.
