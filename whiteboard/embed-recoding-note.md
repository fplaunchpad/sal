# Re-coding the embed RGA: state-level GC by stable-prefix maps

Status: mechanized (Lean theorem names and axiom sets in §7; Python harness
verdicts in §7). Companion code: `Sal/ConditionedMRDTs/MRDT_Instances/EmbedRGA/EmbedRGA_Recoding.lean`,
`whiteboard/litmus/embed_recode_check.py`.

## 1. The datatype, natively

The embed RGA's state is the document itself: a list of records
`(id, element, coordinate)` kept strictly descending by key. A coordinate is a
bit string, the concatenation of codewords of an ordered prefix code `Γ` along
the record's birth chain: an insert op `ins e π a` issued at timestamp `t`
against anchor `a` carries the anchor's stored coordinate `π` and the fold
mints the child coordinate

    coord = π ++ Γ.enc (t - a)

(`eCoord`/`eUpdate` in `EmbedRGA.lean`; the code needs only monotonicity and
prefix-freedom, packaged as `OrderedPrefixCode`). The display key of a
coordinate maps bit `0` to symbol `1`, bit `1` to symbol `2`, and appends a
terminator `3`; the read is the descending lexicographic sort of keys, so an
ancestor (whose key ends in `3` where a descendant continues with symbols
`1`/`2`) sorts strictly before its whole subtree, and siblings sort newest
first. Deletion is pure removal. The state is canonical: any two well-formed
enumerations of one event set fold to the same list (`e_fold_canon`), and the
capstone `embed_ra_linearizable3` gives per-version RA-linearizability at
every honestly reachable configuration, parametric in `Γ`.

## 2. The epoch problem and lazy translation

Coordinates are birth constants and never shrink. A live record whose birth
chain passed through nine deleted ancestors still carries all nine dead
codewords as a prefix of its coordinate forever: tombstone-freedom removed the
dead *records*, but their *codewords* survive inside every descendant. Long
runs of editing therefore accumulate coordinate weight proportional to total
history, not to the live document. A GC epoch should re-code: assign the live
records fresh, short coordinates that induce the same display order, and let
new mints extend the fresh coordinates.

Replicas cannot switch codes in lockstep: a message minted against the old
coordinates may be in flight while the receiver has already compacted. The
model is therefore *lazy translation*: the re-map is a pure function on
coordinates, applied (a) once to the state at rest, and (b) to each incoming
record or op minted in the old code (the op's carried anchor prefix `π` is
translated; the delta codeword is not touched). No protocol round is modeled
here; §6 records what the protocol half owes.

## 3. Stable-prefix maps

Fix a set `S` of *stable* coordinates, downward closed: every proper prefix
of a member that is itself a coordinate of an ancestor record is also a
member. Downward closure is not an extra design choice but a fact about
cuts: a coordinate's proper codeword-prefixes are exactly its ancestors'
coordinates, ancestors causally precede their descendants, and any causally
downward-closed notion of "stable" (all replicas have delivered it) therefore
contains the ancestors of everything it contains.

Given a compaction `ρ : S → coordinates`, define the induced re-map on all
coordinates by factoring at the cut:

    ρ̂(c) = ρ(stab c) ++ rest c

where `stab c` is the longest prefix of `c` lying in `S` and `rest c` is the
remainder. Every coordinate at hand factors this way, again by downward
closure: walking up `c`'s birth chain, the deepest stable ancestor exists
(possibly the root, with coordinate `[]`), and everything minted below it is
unstable, so the stable part of `c` is exactly one chain prefix. The re-map
rewrites the stable part wholesale and keeps the unstable tail verbatim.

## 4. Hypotheses

The theorems are parametric in the re-map. They consume three semantic
hypotheses, to be discharged later by each concrete compaction; all three are
relativized to the coordinates *at hand* (the cut state's records and the
mints applied beyond the cut), never to all bit strings:

* **H1 (injectivity).** `ρ̂` is injective on the coordinates at hand.
* **H2 (order preservation).** `ρ̂` preserves the fold's comparator on the
  coordinates at hand: `keyLt (key (ρ̂ c)) (key (ρ̂ c')) = keyLt (key c) (key c')`,
  where `key`/`keyLt` are the terminator embedding and strict lexicographic
  order of §1. Stated as a Boolean equation, so it carries both directions.
* **H3 (extension commuting).** `ρ̂ (π ++ Γ.enc d) = ρ̂ π ++ Γ.enc d` for every
  anchor/delta pair `(π, d)` minted beyond the cut. For a genuine
  stable-prefix map this is automatic: a beyond-cut mint has
  `stab (π ++ Γ.enc d) = stab π`, so both sides equal
  `ρ(stab π) ++ rest π ++ Γ.enc d`.

Remark (H1 is free). H2 already implies H1 on its domain: if `ρ̂ c = ρ̂ c'`
with `c ≠ c'` then `key c ≠ key c'` (the key embedding is injective), so by
totality one of `keyLt (key c) (key c')`, `keyLt (key c') (key c)` is true,
yet the corresponding comparison of the equal images is reflexive and false,
contradicting H2. The Lean bundle therefore carries H2 and H3 as fields and
derives H1 (`StablePrefixMap.injOn`).

## 5. The theorem cluster

Write `ρ̂[s]` for the state with every record's coordinate re-mapped (ids and
elements untouched, list order untouched) and `ρ̂[o]` for the op with its
carried anchor prefix re-mapped (`ins e π a` becomes `ins e (ρ̂ π) a`,
deletes unchanged).

**T1 (fold congruence, parametric in the cut).** For any cut state `s` whose
record coordinates are at hand and any op sequence `τ` beyond the cut whose
mints satisfy H3 and land at hand,

    applySeq (ρ̂[s]) (map ρ̂ τ) = ρ̂[ applySeq s τ ].

Folding translated ops over the translated state is the translation of the
untranslated fold. The proof is one step lemma (insert guard is id-based and
unaffected; sorted insertion compares only keys, preserved by H2; the minted
coordinate `ρ̂ π ++ Γ.enc (t - a)` equals `ρ̂ (π ++ Γ.enc (t - a))` by H3;
delete filters by id) and an induction along `τ`. Taking `s` to be the empty
state recovers a from-scratch congruence `eFold (map ρ̂ τ) = ρ̂[eFold τ]`.

**Why T1 must be stated from the cut (a finding, mechanized).** One might
hope to state the congruence over the *whole history*: map every op ever
issued and re-fold from the initial state. That statement forces H3 at every
historical mint, including the stable ones, and H3 at every mint provably
collapses the re-map: by induction along birth chains,
`ρ̂ (coordOf Γ ch) = ρ̂ [] ++ coordOf Γ ch` for every positive chain `ch`, so
`ρ̂` is a constant-prefix prepend and compacts nothing
(`eRecode_ext_global_collapse` in the Lean file). Re-coding is inherently an
epoch operation on states, not a history rewrite; the lazy-translation,
cut-parametric formulation is not a convenience but the only nontrivial one.

**T2 (reads identical).** Under T1's hypotheses, the element sequence of the
translated fold equals the untranslated one, verbatim:

    query (applySeq (ρ̂[s]) (map ρ̂ τ)) = query (applySeq s τ).

Elements are untouched and order is preserved; compression is invisible to
every observer. The contentful half is hiding in T1: the *left-hand side
re-sorts by the new keys*, so equality of reads is exactly the statement that
the new keys induce the old order (H2 doing its job). The negative control
(§7) shows a non-order-preserving re-map genuinely changes reads.

**T3 (transport along the iso).**

* Canonicity transports: two H3-satisfying enumerations of one event set
  have equal translated folds (`eRecode_fold_canon`), by T1 plus
  `e_fold_canon`.
* Sortedness transports: the re-map of a canonical (strictly descending)
  state is canonical (`eRecode_sorted`), by H2; at honest configurations
  every registered version is such a state, so the re-coded version needs no
  re-sort (`eRecode_version_sorted`).
* The capstone's per-version statement transports: at every honestly
  reachable configuration, every version `(s, E)` has a delivery-respecting
  witness enumeration `π` with `s = eFold π`; the re-coded state `ρ̂[s]`
  equals `ρ̂[eFold π]` and reads exactly as the witness fold reads
  (`eRecode_ra_transport`).

**T3's honest strength and the gap.** The transport is at the level of
states and witnesses, not configurations. What is *not* proved: that the
re-coded history is itself an honest configuration of the same datatype. It
is not, as stated: the honesty contract `EHonest` requires every minted
coordinate to be a birth-chain coordinate whose deltas telescope to the id,
and a compacted coordinate deliberately forgets dead chain segments, so
`chain_gen` fails for it. Re-basing honesty modulo an order-embedding of
coordinates (so that the capstone can be re-invoked natively in the new
epoch) is future work and belongs with the protocol half (§6).

## 6. Deferred: the protocol half, and FugueMax

**Choosing a common cut.** The theorems are parametric in `ρ̂`; nothing here
says when all replicas can *agree* on one. The obvious criterion, "the
region below the cut is stable (delivered everywhere) and every record in it
is dead or re-coded", is not enough, and the failure is the in-flight
anchor: a replica may have minted an insert anchored under a node that is
dead in the cut region, and that op may still be in flight when the cut is
declared. Stability of the *delete* does not preclude in-flight *anchors*
under the deleted node, because anchoring needs only that the issuer had the
anchor live in its local state at issue time. What does suffice: stable
delivery of the cut region *plus visibility of all current heads*. Event
sets are causally downward closed, so if the cut's declarer has seen every
replica's current head, every op not yet declared was issued after a state
that already contained the cut region, and its anchor chain factors at the
cut, which is exactly what H3 needs. Formalizing this (a two-phase epoch
advance, or a stability oracle in the configuration layer) is the deferred
protocol half; the present theorems are its data-plane soundness argument.

**FugueMax tagged variant.** The sided/FugueMax family embeds keys inside
side *tags*; a re-map would have to rewrite coordinates occurring inside tag
payloads, not only at the record's top-level coordinate field, so the
stable-prefix factorization would need to be applied under a congruence over
the tag structure. Deferred; nothing in the present cluster depends on it.

## 7. Worked example and machine validation

**Worked compaction, unary code** (`enc d = 1^d 0`), hand-computed. History:
insert `a` at the root at `t = 1`, `b` under `a` at `t = 2`, `c` under `b`
at `t = 3`, then delete `a` and `b`. The cut state is the single live record

    c : id 3, coordinate 10 10 10   (6 bits, two dead codewords carried).

Cut: `S` = the ancestor closure of everything minted, `ρ` sends `c`'s
coordinate to `enc 1 = 10`. Re-coded state: `c : 10` (2 bits). Beyond the
cut: insert `d` under `c` at `t = 6` (delta 3) and `e` at the root at
`t = 7` (delta 7). Coordinates:

    original                        re-coded
    c : 101010            (6)      c : 10                (2)
    d : 101010 1110      (10)      d : 10 1110           (6)
    e : 11111110          (8)      e : 11111110          (8)

Keys sort descending as `e, c, d` on both sides (hand check: `e`'s key
begins `2 2`, beating `c`'s `2 1`; `c`'s key offers terminator `3` where
`d`'s continues with `2`, so `c` precedes its child). Reads identical; live
coordinate weight drops from 24 bits to 16, and the dead-chain share of
`c`/`d` (8 of their 16 bits) is gone entirely.

**Lean** (`EmbedRGA_Recoding.lean`, all payload-generic in `α`, code-generic
in `Γ`): hypothesis bundle `StablePrefixMap` (fields `f`, `Rest`, `MintAt`,
`ext` = H3, `ord` = H2; derived `injOn` = H1); step lemma `eUpdate_remap`;
**T1** `eRecode_applySeq` (cut-parametric) and `eRecode_fold`; **T2**
`eRecode_reads_identical` (and the at-rest form `eRemapSt_query`); **T3**
`eRecode_fold_canon`, `eRecode_sorted`, `eRecode_version_sorted`,
`eRecode_ra_transport`; the collapse finding `eRecode_ext_global_collapse`.
All kernel-clean: axioms within `{propext, Classical.choice, Quot.sound}` on
every headline theorem. SPOTs (namespace `SPOT`, `native_decide`, PASS +
FAIL shaped) pin the worked example: the translated continuation fold equals
the re-map of the untranslated one record for record (`t1_concrete`), reads
pinned equal to the hand value, coordinate weight pinned `16 < 24`, the
bundle exhibited inhabited on the example (`gcF`, with `t1_via_theorem`
re-deriving the pin through `eRecode_applySeq` rather than by computation),
and the FAIL companion `badMap` (injective, H3-satisfying, order-breaking:
it sends `c`'s coordinate to `enc 8`, jumping over `e`) flips the read to
`c, d, e`, pinning H2 as the load-bearing hypothesis.

**Python** (`whiteboard/litmus/embed_recode_check.py`, imports the litmus
embed model's codeword generator, modifies nothing existing): implements the
flat-coordinate model and the live-tree compaction (re-mint the live records
against their nearest live ancestors, deltas `k, k-1, ..., 1` newest first;
delta dominance holds because a beyond-cut mint's delta exceeds every
original sibling delta, hence every re-assigned one). Directed cases: the
worked example above, a sibling case, and a 200-deep delete-heavy chain.
Randomized: 500 histories (random inserts/deletes, random cut, two replicas
forked beyond the cut with concurrent ops and an OR-set merge at the end),
checking reads identical at every step, the T1 state correspondence record
for record, and the negative control (the sibling-reversing bad map changes
the read). Verdicts: **all 500 randomized states PASS** (reads identical,
T1 correspondence exact), the negative control **flips the read as
predicted** (`[3,2,1]` becomes `[1,2,3]`), and the delete-heavy chain's live
coordinate weight drops **200 bits to 1 bit** (binary code, a 200x
reduction; the worked example's unary figures reproduce as 24 to 16).

## 8. What this buys

The re-coding theorem is the missing state-level half of the entropy story:
the code `Γ` controls the per-mint cost, and the stable-prefix map controls
the accumulated dead-history cost, with reads provably invariant. Together
with the capstone's parametricity in `Γ`, an implementation may pick the
Elias-delta code for mints and any order-preserving compaction for epochs,
and every observer-visible guarantee of the datatype survives both choices.

## Addendum: findings from the runtime implementation and trace measurement

From the JS twin (runtime/src/compact.js, 33 tests incl. a 140-trial
twin PBT with 899 cross-epoch merges) and the real-trace measurement
(whiteboard/litmus/embed_compact_measure.py, josephg editing traces).

1. THE MEASURED HEADLINE. Rank-renumbering alone recovers 1.1x to 1.8x
   on real traces. The residual cost is SPINE DEPTH: typing runs mint
   delta-1 chains, and every level costs at least one bit even at
   ordinal 1. This is exactly the live-tree-shape cost the design
   predicts, and it is what spine fusion (iteration two) owns; the
   order of magnitude win lives there. History independence was
   verified exactly: staggered cuts and one from-scratch final cut
   land on bit-identical totals on every sequential trace.
2. ID-ADDRESSED CUTS BREAK AFTER EPOCH ONE: renumbered coordinates no
   longer telescope to event ids, so a cut given as event ids cannot
   be resolved by prefix sums on a re-compacted state. The cut should
   be specified as coordinates/records with downward closure (a
   settled record witnesses its whole dead ancestor chain), or carry a
   per-epoch id table. The v1 in-flight walk still uses prefix-sum
   ids, exact in the mint code; the in-flight times multi-epoch
   combination is approximated in v1.
3. DROP-FINALITY: the settled set must list deleted ids below the cut
   too; an unlisted absent id is treated as never-existing, and if it
   is actually in flight it must be declared or the compaction is
   unsound (the negative control's failure class). Implied by
   SettledAt; worth the explicit clause.
4. The v1 runtime LINEARIZES epochs per replica (compaction refused
   off the newest epoch); concurrent divergent compactions remain the
   protocol half deferred in section 6 (epoch DAG plus
   common-refinement translation).

## Addendum 2: spine fusion (iteration two), the design

Motivated by the measurement: rank-renumbering alone recovers 1.1x to
1.8x because the residual cost is spine depth (typing runs mint
delta-1 chains; every level costs at least one bit even at ordinal 1).
Fusion removes the dead levels themselves.

**The map.** A fusible spine is a maximal chain of dead nodes
d1, d2, ..., dk (k >= 1), each below the cut, each with EXACTLY ONE
child branch counting every known coordinate including in-flight ones,
and with no in-flight op anchored at any d_i (checkable: SettledAt
makes all existing concurrency visible; and no FUTURE op can anchor at
a settled dead node, which is invisible to every future minter). The
fusion collapses the spine to one level: every coordinate through the
spine rewrites from prefix(parent) ++ block(d1) ++ ... ++ block(dk) ++
rest to prefix(parent) ++ enc(ordinal of d1 in its sibling group) ++
rest. Composition with rank-renumbering is the full iteration-two map.

**Why order survives (the H2 argument).** Three comparison classes:
(1) inside the fused block: the common prefix is replaced wholesale,
relative order untouched; (2) the block against the spine head's
siblings and their subtrees: decided at the head's level by the group
ordinal, which fusion preserves (the block inherits d1's rank); (3)
the sentinel corner is vacuous: dead spine nodes have no records,
hence no keys exist at the fused-away levels, so no anchor-versus-
extension comparison is lost. In-flight coordinates through the spine
are handled by the same stable-prefix translation as any re-mapped
prefix; future mints against compacted state extend the fused
coordinates natively.

**Prediction.** Post-fusion coordinate cost approaches the code cost
of the LIVE tree shape alone: sequential typing (deep delta-1 spines,
mostly dead after edits) should collapse toward a few bits per
character, delivering the order of magnitude the renumbering pass
could not.

## Addendum 2 errata (from the implementation and re-measurement)

1. Spines should be defined with k >= 2: at k = 1 the fusion map
   degenerates to rank-renumbering, so the implementation treats it as
   the identity, neither applied nor counted.
2. The fused block rewrites to the head's GROUP CODEWORD, which is the
   ordinal when the head's group renumbers and the retained original
   delta when that group is skipped by the in-flight guard. The
   class-2 order argument is unaffected either way.
3. The implementation adds one conservative guard case: a node where a
   declared in-flight coordinate ENDS is never fused (contradictory
   caller input, since an in-flight op cannot be settled-dead).
4. Harness finding, not a fusion defect: criss-cross verdict agreement
   between compacted and control twins is NOT stable in general,
   because epoch commits perturb the subject's commit graph (a control
   fast-forward can be a subject merge); 38 divergences across 120
   trials. The v1 harness's agreement assertion survives by schedule
   luck; the fusion PBT pre-checks the gate on both twins and counts
   divergences instead.

## The measured verdict on iteration two

Fusion removed essentially everything removable: surviving dead levels
cost 3 to 76 bits per char, and the fused column equals the code cost
of the live tree shape, verified by per-level attribution that
accounts for every bit. The few-bits-per-char prediction FAILS because
that live shape is itself expensive: real traces anchor typing runs in
LIVE chains of mean depth 835 to 1468 levels at about one bit per
level, and 97 to 99.8 percent of the remaining bits are live ancestor
levels. Totals: 1.7x to 3.2x end to end (edit-heavy seph-blog1 gains
the most; mostly-surviving clownschool the least). History
independence holds three ways under fusion, and the fused display
spells endContent on every sequential trace. The next cost lever is
therefore RE-CODING LIVE RUNS (run/offset coding of live delta-1
chains, the isometric-fold/path-2 representation layer, task #73's
territory), a representation change, not a better epoch map.

## Addendum 3: the sided (Fugue) instantiation, measured

(`litmus/embed_sided_compact_measure.py`; real traces replayed through
the sided model under the Fugue policy, band-aware compaction:
renumber within each parent-band group, fusion carrying the head's
band and codeword. All gates pass: endContent 6/6 via the sided
display, reads identical 80/80 across cuts, history independence two
and three way, zero band-aware order surprises.)

1. THE NUMBERS. Sided/Fugue reductions are 1.36x to 2.90x sequential
   (1.14x to 1.26x concurrent single-cut), SYSTEMATICALLY BELOW the
   one-sided 1.69x to 3.24x. The naive expectation that the ratio is
   preserved is falsified for the reason it itself cites: adding the
   same flat per-level side cost to numerator and denominator pulls
   the quotient toward the level-count ratio, which is below the
   payload ratio.
2. WHERE SIDES PAY. The fused sided state costs about 2x the fused
   one-sided state, and the premium is entirely the flat side flag:
   the sided payload exceeds the one-sided payload by only 1.0 to 4.7
   percent (the Fugue tree is payload-equivalent to RGA's on these
   traces). 94 to 98 percent of side bits sit on LIVE ancestor levels
   that no epoch map can touch. The flag costs a flat 1.000 bit per
   level against a true side entropy of 0.19 to 0.27 bits (L-mints
   are only 3.0 to 4.6 percent under Fugue on real traces): a 4x to
   5x overpay on the side channel, load-bearing for lex band
   separation, hence recoverable only at the representation layer
   (entropy-coded sides, run-coding of live all-R chains) alongside
   the live-depth cost: both point at task #73's isometric-fold
   territory.
3. Bonus observation: with the (ts, agent) tiebreak the sided walk
   spells endContent on the concurrent traces too, with zero sibling
   ties. FugueMax with tag rewriting remains out of scope (keys inside
   tags need a tag-structure congruence).
