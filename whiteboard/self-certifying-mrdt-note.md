# Self-certifying MRDTs: a runtime admission contract for the embed RGA

Task #116, phase 1 (Python adversary validation; no Lean this phase).
Companion harness: `whiteboard/litmus/rga_byzantine_check.py`.

## 1. The question and the goals

The verified embed RGA (Part II of `Sal/ConditionedMRDTs/sal-mrdts.tex`)
certifies RA-linearizability *per version* at every **honestly reachable**
configuration (`thm:embedcapstone`, `embed_ra_linearizable3`). Honesty is a
**rely**: the metatheory assumes every op was generated where its anchor
was live (`eApplicable`) and carries a real birth chain (`EHonest`). Nothing
in the state-based model forces a peer to be honest. A malicious peer can
ship any record it likes over the sync wire (`runtime/src/sync.js`).

The research question of this note is whether the rely can be turned into a
**runtime-checked contract**:

> Is there a decidable per-op predicate `A(op, declared_past)`, a function
> of the op and the DECLARED past only (never of a verifier's private
> view), such that any op passing `A` cannot make honest verifiers diverge
> or produce a non-RA-linearizable state, while structural intent
> (non-interleaving of chained runs) holds by merge geometry regardless of
> authorship?

The declared past is a set of content-addressed commit ids (hash-linked).
A verifier possessing those commits reconstructs the pre-state as the
canonical fold of that event set; because the fold is a function of the
*set* (fold canonicity, `e_fold_canon`, Theorem chain(i)), two verifiers
that possess the same commits compute the same pre-state and the same
verdict. This is what makes `A` a **certificate check** rather than a local
opinion.

The claim is falsifiable, and the harness's job is to refute it: build a
Byzantine trace that passes `A` yet breaks RA-linearizability or interleaves
a chained run. A hit is the finding; a clean sweep pins the metatheorem for
phase 2.

## 2. The three admission obligations

A self-certifying MRDT owes three properties of its admission predicate.
State them before any experiment.

**O1 (soundness).** If every op in a configuration passes `A` against its
own declared past, the assembled event set is honest in the sense the
capstone consumes: it satisfies `EHonest`, hence every reachable
configuration is RA-linearizable per version. Contrapositive: no
`A`-passing set of ops diverges between honest verifiers or reads
non-linearizably.

**O2 (no false reject / liveness).** Every op a correct replica generates
is accepted. A correct replica anchors on a live record of its own current
read and mints a fresh id; `A` must accept it. `A` must also accept
*legitimate concurrency*: a slow replica that has seen only part of history
declares a smaller past and anchors inside it. Rejecting that would be a
liveness bug, not a safety win. The stale-past case (a3 below) is exactly
this obligation made concrete.

**O3 (determinism / no private view).** `A(op, declared_past)` is a pure
function of the op plus the declared past as a set of commit ids. Any
verifier holding those commits recomputes the identical verdict. `A` never
reads a verifier's local head, wall-clock, or delivery order. This is what
lets the check be replicated without coordination and is the precondition
for a phase-2 proof that "locally checked" assembles into "globally
honest".

## 3. The admission predicate A

Model (transliterated from `epoch_diamond_check.py` and
`embed_recode_check.py`). A coordinate is a delta chain, a tuple of positive
integers. The coordinate of insert `i` anchored at `a` is
`coord(a) ++ (i - a)`, with root anchor (`a = 0`) giving `(i,)`. The display
key is `key(c) = tuple(-d for d in c)`; the read is the ascending-key sort
(an ancestor sorts before its subtree, a larger delta = newer sibling sorts
first: the RGA recency order). Delete removes the record; merge is OR-set
survival with coordinates carried unchanged, because a coordinate is a birth
constant (Theorem chain(ii)). Every insert carries its coordinate as payload
(`def:embed`, `do_`: the insert writes its carried prefix and never reads
the state), so the fold never consults a live anchor and is order
independent.

`A(op, declared_past)` reconstructs `pre = fold(declared_past)` and then:

- `ins(id, el, anchor)`:
  - **(a) phantom-anchor rejection.** `anchor` is the root, or present in
    `pre`.
  - **(b) derived coordinate.** The coordinate is recomputed,
    `coord == base(anchor) ++ (id - anchor)`, never the shipped one. A
    forged coordinate is therefore unrepresentable: the blessed record
    carries the derived coordinate, so even an accidentally admitted forge
    is harmless. The FAIL companion "trust the shipped coordinate" flips a
    read.
  - **(c) freshness.** `id` exceeds every insert id in the declared past
    (Lamport monotonicity) and is not already present (pairwise fresh).
  - **(d) applicability (`eApplicable` shape).** The anchor is a live record
    carrying exactly its coordinate. In the tombstone-free embed fold,
    present equals live, so (d) coincides with (a); the derived coordinate
    then makes the newcomer land immediately after its anchor (the adjacency
    lemma `chainBefore_snoc_iff`), so there is no separate positional check.
- `del(target)`: `target` is present and live in `pre`.

**Equivocation is out of scope, imported via the substrate.** Each
replica's ops form a signed single-writer chain with monotone,
author-tagged ids; no intra-author fork is asserted as an assumption, not
defended. Concretely the harness gives author `r`'s ops ids that are unique
across authors (`id = clock*n_rep + r`), so a signed chain can neither forge
another author's id nor fork its own. Admission still enforces the
*intra-author* Lamport monotonicity of clause (c).

## 4. The attack catalogue, with hand-worked expectations

Base document, hand-derived once: a typing run `p a b c` with coordinates
`p=(1,)`, `a=(1,1)`, `b=(1,1,2)`, `c=(1,1,2,2)`, read `[p,a,b,c]`.

- **a1 forged coordinate.** Ship `ins(9, '!', anchor=p)` with a coordinate
  forged to sort `!` last, `(1,1,2,2,1)`. Honest derived is `(1,8)`, which
  lands `!` right after `p`: `[p,!,a,b,c]`. `A` recomputes `(1,8)`, sees the
  mismatch, and **rejects** (`forged_coord`). The FAIL companion that trusts
  the shipped coordinate reads `[p,a,b,c,!]`: a flipped read.

- **a2 phantom anchor.** `ins(9, '!', anchor=5)` where id 5 was never
  created. `A` **rejects** (`phantom_anchor`): 5 is not in the reconstructed
  pre-state. The FAIL companion that accepts the phantom yields a state with
  a dangling coordinate prefix, which the RA-lin checker reports as
  non-linearizable (`dangling_anchor(9->5)`).

- **a3 stale-past anchor.** Author declares the real but partial past
  `{p,a}` (down-closed, legal) and inserts `ins(9, '!', anchor=a)` having
  really seen more. `A` checks the declared past only: `a` is live there,
  derived coordinate `(1,1,7)`. `A` **accepts**. Merged with the full
  `{p,a,b,c}`, the read is `[p,a,!,b,c]`, which equals a slow replica that
  saw only `{p,a}`, inserted `!`, and then merged. This is legitimate
  concurrency, not a breach: the merged state is RA-linearizable and equal
  to the slow-replica trace. This is the boundary O2 protects.

- **a4 run-interleave attempt.** Honest run `A B C` after root `p`; the
  adversary wants the interleaved read `[A,X,B,Y,C,Z]` with its own chained
  run `X Y Z`. Three sub-cases, all machine-checked:
  - *chained into A's subtree*: `X` anchors `A`, `Y` anchors `X`, `Z`
    anchors `Y`. The run lands as a **contiguous block** inside `A`'s
    subtree, `[p,A,X,Y,Z,B,C]`. To place anything between two members of
    `A`'s subtree the coordinate must extend `A`'s coordinate (subtree
    convexity), so a chained run occupies one contiguous span and cannot be
    woven through `B,C`.
  - *scatter*: `X` anchors `A`, `Y` anchors `B`, `Z` anchors `C`. These are
    three separate single-character inserts under three anchors, not a run;
    each is admissible (the H-M boundary), and none chains another.
  - *impossibility*: the literal `[A,X,B,Y,C,Z]` needs a chained `X Y Z` to
    be non-contiguous, which subtree convexity forbids. The interleave is
    unreachable.

- **a5 stamp rewind.** `ins(3, ...)` with 3 below the declared past's max
  insert id: `A` **rejects** (`stamp_rewind`). The FAIL companion that skips
  freshness admits a duplicate id, and two verifiers that saw the two
  same-id versions in opposite order diverge (`[p,Z,b,c]` vs `[p,a,b,c]`):
  convergence broken.

- **a6 delete resurrection.** Delete is monotone removal. After deleting
  `b`, `c` keeps coordinate `(1,1,2,2)`, still prefixed by dead `b`'s chain
  `(1,1,2)`: the retained dead timestamp, the conservation law of Part II.
  Re-minting id 4 is **rejected** (not fresh); a fresh id anchored at `a`
  gives `(1,1,7)`, never `b`'s slot `(1,1,2)`, so the dead order slot is
  unreproducible. Survivor order is preserved (delete is a sublist,
  `eUpdate_del_sublist`).

## 5. The clean split

The results factor the design's guarantees into four disjoint regimes.

**Convergence and RA-linearizability are admission-defended.** They rest on
clauses (b), (c), (d): a derived coordinate, a fresh id, a live anchor. With
those, every admitted op carries an injective birth-constant coordinate
(unique decodability, `coordOf_inj`), so the merged fold has no ties and is
order independent: two verifiers cannot diverge. Drop any of the three
clauses and a countermodel appears (a1, a2, a5 FAIL companions).

**Structural intent is unconditional.** Non-interleaving is subtree
convexity, and the mechanized statement carries no honesty hypothesis at
all:

> `thm:subtreeconvex` (`subtree_convex`). In any state `s` (no honesty, no
> reachability): if `before s t1 t2` and `before s t2 t3`, and a coordinate
> `c` prefixes both stored coordinates `pos_s(t1)` and `pos_s(t3)`, then `c`
> prefixes `pos_s(t2)`. Instantiated at an anchor's coordinate: everything
> displayed between two members of a subtree is in the subtree, so runs
> typed under distinct anchors cannot interleave. The proof is pure
> lexicographic convexity of prefix sets; **no property of the code is
> consumed**.

Because the hypothesis is "in any state", H-I needs no admission theorem: a
Byzantine author cannot interleave a chained run into an honest one even
with a maliciously chosen coordinate, because convexity is a property of the
coordinate geometry, not of how the coordinate was obtained. The harness
confirms this by checking convexity on states that carry a *rejected* op
forcibly applied. (Contrast the two-sided maximal-non-interleaving theorem
`thm:t9`, which is "no hypotheses beyond reachability and the code" for the
ordering conditions, while the FugueMax *convergence* half `thm:fmralin`
does carry a mint condition, `TagsOK` / `FMHonest`. For the one-sided embed
RGA studied here, ordering intent is fully unconditional.)

**Content is out of scope: it is moderation.** A Byzantine author can insert
a single character at any legally anchored position and delete any live id.
Both pass `A` and are not breaches (H-M boundary, demonstrated positively).
Inserting a rude word after `b`, or deleting `a`, is authoring or
moderation, not a convergence or intent violation. The contract certifies
*structure and convergence*, and deliberately does not certify *content*.

**Equivocation is imported.** The no-fork, author-tagged-id substrate is an
assumption of the signed single-writer chain, not something `A` defends. A
peer that signs two different ops at one chain position is detectable by the
signature but is outside the algebraic contract.

## 6. Results

All directed cases carry hand-derived expectations; FAIL companions
demonstrably flip a read or RA-linearizability.

| Hypothesis | Verdict |
|---|---|
| H-C convergence / RA-lin under admission | VALIDATED: no admitted trace diverges or reads non-linearizably |
| H-I structural intent (subtree convexity) | VALIDATED and UNCONDITIONAL: holds even on rejected-op states |
| H-M boundary (single char, delete live id) | demonstrated positive: admitted, RA-lin, convex, not a breach |

| Attack | Expectation | Outcome |
|---|---|---|
| a1 forged coordinate | reject (recompute) | REJECTED `forged_coord`; FAIL flips read |
| a2 phantom anchor | reject | REJECTED `phantom_anchor`; FAIL is non-RA-lin |
| a3 stale-past anchor | accept (concurrency) | ACCEPTED and safe, equals a slow-replica trace |
| a4 run interleave | impossible for a chained run | contiguous block; scatter is separate chars |
| a5 stamp rewind | reject | REJECTED `stamp_rewind`; FAIL diverges verifiers |
| a6 delete resurrection | dead slot unreproducible | REJECTED re-mint; order preserved |

Adversary search: 3500 trials, 2 to 4 replicas with one Byzantine. 98145
ops admitted, 14824 rejected. Admitted classes: honest inserts and deletes,
stale-past concurrency, chained runs, scatter, boundary edits. Rejected
classes: forged coordinate (via recompute), phantom anchor, stamp rewind,
delete-resurrection (via recompute or phantom, since the resurrected slot's
anchor may itself be dead). Zero admitted-yet-broken countermodels.
Subtree convexity holds on every merged state and on every rejected-op
state.

## 7. Phase-2 Lean theorem shapes

**The admission metatheorem (the main phase-2 target).** Let each op `o`
carry a signed commit whose declared past `P(o)` is a down-closed set of
content-addressed commit ids, and take `P(o)` to be `o`'s causal past
(`{e | C.vis e o}`, which the content-address links make down-closed and
recomputable). Then

> if `A(o, P(o))` holds for every `o` in `C.events`, then `EHonest Γ C`,

and hence `EReach Γ C` reduces to `IsRALinearizable3 C` by the existing
capstone. The **per-op half already exists**: `A(o, P(o))` is exactly
`eApplicable o (eFold (enum P(o)))` for a causal enumeration of `P(o)`, and
`thm:ehonestapp` (`eHonest_of_applicable`, `eHonest_of_genHonest`) already
discharges `EHonest` from "every event is applicable at some fold of its
issuer's causal past". The phase-2 work is the assembly, in three pieces:

1. **Causal-past enumerability from the substrate.** The content-address
   DAG makes `P(o)` well-defined, down-closed, and equal to `o`'s vis-set,
   i.e. `CausalPastEnumerable C`. This is the certificate-layer lemma; the
   Python `Store.down_close` is its executable shadow.
2. **Local checks assemble into `GenHonest` at `eApplicable`.** Each signed
   op locally passing `A` supplies the per-op `eApplicable`; the framework
   already lifts `GenHonest at eApplicable` to `EHonest`. What is owed is
   that `A`-over-the-declared-past equals `eApplicable`-over-the-issuer's-
   causal-fold, which is O3 (determinism) made into a Lean equality of
   folds (`e_fold_canon`).
3. **The no-fork import.** State the signed single-writer-chain assumption
   as a hypothesis (author-tagged unique ids, no intra-author fork); do not
   attempt to prove it. It is the boundary of the algebraic contract.

**Subtree-convex unconditionality is already discharged.** H-I needs no new
theorem: `subtree_convex` is proved over an arbitrary state with no
hypotheses, so non-interleaving of chained runs is a corollary applied to
any merged state, admitted or not. The phase-2 note only has to *cite* it in
the admission-contract statement, not re-prove it. This is the sharp
asymmetry the split predicts: convergence is admission-defended and needs
the metatheorem; intent is geometric and needs nothing.

**The GC frontier conjecture (open, stated for phase 2).** Compaction (the
re-coding and epoch protocol of `#97` / `#112`) advances a settled cut
certified by evidence that every replica has been heard from. With signed
evidence certificates, an unsafe compaction is preventable: dropping an
epoch's translation map requires the all-heard certificate, which a verifier
checks (the `AllHeardSince` half, `directed_a3` of `epoch_diamond_check`,
proved that the ack-only certificate is unsound). The residual adversary is
a **withholder**: a single replica that never ships its evidence blocks the
certificate and therefore blocks compaction. So the frontier splits into
impossibility-or-eviction: either the protocol tolerates a withholder by
never compacting past the unacked frontier (safe but not live), or it evicts
the withholder (a membership or governance action outside the algebra). The
conjecture is that no admission predicate over declared pasts can both
preserve compaction safety and force liveness against a withholder, because
liveness against a withholder requires a decision the withholder's declared
past does not contain. Cross-reference: the delivery discipline already
implies the continuation-honesty clauses, `ContOK` was 11029 checks clean in
`epoch_diamond_check`, so the compaction-side honesty obligations reuse that
certificate layer rather than a fresh one.

## 8. Files

- `whiteboard/litmus/rga_byzantine_check.py`: the embed-RGA model, `A`, the
  canonical fold, the RA-lin (loOn-fold) witness checker, the subtree
  convexity checker, the content-address certificate layer, selfchecks, the
  directed a1 to a6 attacks, and the 3500-trial adversary search. Stdlib
  only, self-contained.
- `whiteboard/self-certifying-mrdt-note.md`: this note.
