# The epoch protocol: merging incomparable compactions without coordination

Status: Python phase (#112 phase 1). Harness:
`whiteboard/litmus/epoch_diamond_check.py` (stdlib only, self-contained).
Companions: `whiteboard/embed-recoding-note.md` (the single-epoch and
nested multi-epoch theory), `whiteboard/litmus/embed_recode_check.py`,
`whiteboard/litmus/marks_gc_check.py` (the abstract compactor this file
transliterates), `runtime/src/replica.js` (the epoch barrier this note
proposes to remove). No Lean in this phase; section 8 states what phase 2
owes.

## 1. The question

The embed RGA compacts by epochs: at a settled cut it drops dead records,
renumbers ranks densely, fuses dead unary spines, and records the change
as a stable-prefix translation map. The mechanized theory covers one epoch
and nested chains of epochs (cuts totally ordered by inclusion). The
runtime accordingly linearizes epochs per replica and THROWS on a merge
between divergent epochs. The last open distributed question in the stack:
can replicas that compacted at INCOMPARABLE settled cuts merge without
coordination?

The key given: a settled cut is CERTIFIED. AllHeardSince evidence makes
S1 and S2 downward-closed event sets that every replica already
possesses. Unlike the retention fooling pair there is no informational
obstacle; the question is purely algebraic: do the two compactions
commute, and at what strength?

## 2. The compaction model, natively

State. A document state is a set of records, one per insert event:
`(id, element, coordinate)` plus a logical deleted set. A coordinate is a
delta chain, the tuple of timestamp differences along the record's birth
chain: insert `i` against anchor `a` mints `coord(a) ++ (i - a)`. The
display key of a coordinate is its pointwise negation; the read is the
ascending key sort (an ancestor sorts before its whole subtree, and among
siblings the larger delta, the newer record, sorts first: recency order).
Deletion is logical until compaction; the physical drop happens at the
cut.

Certificates. Events carry Lamport ids and causal dependencies (an
insert depends on its anchor's insert, a delete on its target's insert,
plus issuer order). A cut S is any downward-closed event set below every
replica's heard frontier; the intersection of the frontiers IS the
AllHeardSince certificate. Because cuts contain delete events, listing
deleted ids below the cut (drop-finality) holds by construction. The
declared set of a cut, `decl(S)`, is every insert minted before the
declaration and not in S; the all-heads-visibility half of the
certificate makes the declarer know all of them.

The compactor (one cut). From the certificate data alone:

* Kept set: records of S that are live at S, plus dead records of S that
  anchor a declared in-flight op (retention).
* Rank pass: each sibling group of the kept coordinate tree renumbers
  densely (sorted original deltas become ordinals 1..n), EXCEPT groups
  under a frozen parent: the anchor group of any declared op keeps its
  deltas verbatim (the in-flight guard; renumbering under a straggler's
  already-minted delta can flip an order).
* Fusion pass, run after ranking: a maximal chain of phantom-unary nodes
  (a node that is no kept or declared record's full coordinate and has
  exactly one child branch, counting every known coordinate including
  declared in-flight ones) of length k >= 2 keeps the head's ranked
  codeword and drops the interior levels.
* The result is a StablePrefixMap: a prefix table on the old tree's
  nodes; any coordinate at hand factors as its deepest stable prefix
  (rewritten wholesale) plus a verbatim unstable tail (the extension law
  H3). The map carries its surviving domain (the kept coordinates) and
  the dropped ids.

Composition. The residue of two compactions is the composition of their
maps. Composition on the first map's full domain is unsound under rank
reclaim (a record dead between the epochs collides with the survivor
that inherited its rank: `naive_composition_collides`); the sound
composite carries its OWN surviving domain. This note sharpens what
"carry" must mean; see section 5.

Two discipline points, load-bearing later:

* OB-map-from-certificate: the map is a function of the certificate data
  only (settled coords, settled-dead subset, declared set), never of a
  replica's private unsettled records. Two replicas that hold the same
  certificates therefore compute the SAME join map with no coordination.
* OB-anchor-live: a minter anchors only at records live in its local
  state. Since a settled delete has been heard by every replica, no op
  minted after the declarations can anchor at a settled-dead node, so
  fusion eligibility and retention are decidable from the certificate.

## 3. Goals and hypotheses, falsifiable forms first

H-D (diamond, confluence). For incomparable settled cuts S1, S2 over one
honest history: compacting at S1 and then relative-compacting at the
remainder of W = S1 union S2 (composing the two maps with the
surviving-domain fix) equals compacting once at W, and equals the
symmetric S2-first path. Tested at three separated strengths:

* s1: bit-identical states, and identical composed translation maps on
  the surviving domain;
* s2: order-isomorphic (identical live-chain key order, identical reads,
  a common refinement map between the results);
* s3: reads identical only.

The task brief expected the truth at s2 or s3 if double re-coding
differed bit-wise from single re-coding; the harness's job was to find
where it sits, not to force s1.

H-M (barrier-free merge). R1 compacts at S1, R2 at S2, both continue
editing (declared stragglers included), then merge by translating BOTH
sides into the join epoch (the W compaction): reads must equal the
never-compacted twin's merge, for all continuations, multi-epoch
included (diamonds of diamonds).

H-A3 (map drop). Once every replica has advanced past epoch e and the
pre-advance traffic has drained, no old-space record can arrive, so
dropping e's translation map changes nothing. The harness models the
certificate and asks precisely which certificate justifies the drop.

ContOK shape-check (feeds phase 2). Under the modeled delivery layer,
every generated continuation must satisfy the four ContOK clauses: fresh
ids exceed all state ids; nodup insert ids; mint-key freshness against
the state; pairwise mint-key freshness.

Countermodel candidates fired first (hand-derived expectations in the
harness comments, PASS+FAIL shaped): c1 rank reclaim across the diamond
(the naive composition must FAIL, two-sided); c2 fusion asymmetry; c3
the in-flight guard met from both sides; c4 the no-translation control
(a cross-epoch merge without translation must flip a read, justifying
the runtime's current throw).

## 4. Hand-worked directed derivations

c1, rank reclaim, two-sided. Root inserts x1=(1), x2=(2), x3=(3),
x4=(4); del x1 settles only in S2, del x3 only in S1.

* Leg A (S1 first): S1 drops x3, ranks {1,2,4} to {1,2,3}. The relative
  W cut drops x1 (now (1)) and ranks {2,3} to {1,2}. Naive composition
  on the full first domain {(1),(2),(4)}: the dropped (1) falls through
  verbatim to (1), while (2) maps to (1): COLLISION.
* Leg B (S2 first): S2 drops x1, ranks {2,3,4} to {1,2,3}. The relative
  cut drops x3 (now (2)) and ranks {1,3} to {1,2}. Naive: the dropped
  (3) falls through to (2) while (4) maps to (2): COLLISION, the
  two-sided form.
* Surviving-domain composites on both legs: x2 to (1), x4 to (2),
  injective, equal to the one-shot W map. A post-cut straggler minted at
  the root with delta 9 rides through every path verbatim (fresh deltas
  dominate ordinals) and every read equals the twin's.

c2, fusion asymmetry. A unary spine r1, r2, r3, r4 with a live leaf x
below; dels of r1, r2 settle only in S1, dels of r3, r4 only in S2.
Path A fuses the prefix (r1, r2) at epoch 1 and the rest at epoch 2;
path B keeps r1, r2 as logically-deleted records at epoch 1 and fuses
the suffix; the one-shot fuses the whole spine at once. All three land
on x = (1, 1): fusion always keeps the OUTERMOST head, so where the
spine is cut into episodes does not matter.

c3, the in-flight guard. Root group a=(1), b=(2) (dead everywhere),
c=(3); f=(5) declared in flight at S1's declaration but settled under
S2; d=(6) minted after S2's declaration, settled under S1 only. The S1
path freezes the root group (deltas verbatim), then the join cut
renumbers the frozen group once f is settled: a renumbering OF a skipped
group. The S2 path renumbers {1,3,5} immediately and meets d later. Both
paths and the one-shot end at exactly a=(1), c=(2), f=(3), d=(4): the
freeze only defers renumbering, it does not change the final ordinals,
because ordinals depend only on the final group membership.

c4, no-translation control (the required FAIL). R1 compacts (x1
dropped, x2 renumbered (2) to (1)); R2, still in epoch 0, mints y
anchored at x2 with coordinate (2,7). A raw union without translation
places y's key (-2,-7) BEFORE x2's key (-1,): the read flips from
[x2, y] to [y, x2]. Translating y's stable prefix ((2) to (1), tail
verbatim) restores the twin's read. This is the defect the runtime's
throw currently guards against, and the translation that replaces it.

A3, which certificate justifies dropping a map. Three replicas; R2
mints x in epoch 0; a cut S not containing x is declared (x is
declared in flight); ALL THREE replicas advance (ack). The ack-only
certificate ("everyone is past epoch 0") is UNSOUND: x is still in
flight and arrives at R0 after the acks, and x is old-space (its
coordinate is an epoch-0 coordinate; translating it needs the epoch-0
map). The sufficient certificate is ack PLUS AllHeardSince over the ack
frontier: every op minted before its minter's advance has been heard
everywhere. After that moment every future arrival was minted by a
replica already past epoch e, hence carries epoch >= e coordinates, and
the e-1 to e map can be discarded.

## 5. Findings from building the harness (phase-2 relevant)

1. The composite's surviving domain must be CARRIED, id-addressed, not
   computed. Two pullback recipes both fail, machine-witnessed:
   membership pullback through the first map is unsound because a
   dropped coordinate falls through verbatim and can ALIAS a kept
   epoch-1 coordinate (in c3's leg B the dropped x3 image (2) is
   exactly x4's kept epoch-1 coordinate); and intersecting with the
   second map's kept set wrongly evicts records settled only at a LATER
   constituent cut (their intermediate image is an unsettled
   coordinate, correctly translated by prefix factoring but absent from
   the intermediate kept set; five triple-cut trials caught this as a
   domain mismatch while the states stayed bit-identical). The correct
   domain is the join cut's kept id set transported to epoch-0
   coordinates. This sharpens Addendum 4's "carry the composite's own
   surviving domain": the carrying is not an optimization, it is the
   only sound definition.
2. The join map must be certificate-determined (OB-map-from-certificate
   in section 2). If each side computed its relative map from its
   private state, fusion eligibility and freezing would depend on
   unsettled records the other side has not seen, and the two sides
   would install different coordinates for shared records. With the map
   a function of (settled coords, settled-dead, declared) only, both
   sides compute the same join map from the same certificates, which is
   what "without coordination" means operationally.
3. The ack-only map-drop certificate is unsound (section 4, A3); the
   sound form needs the second, AllHeardSince-over-acks half.

## 6. Machine verdicts

Harness: `whiteboard/litmus/epoch_diamond_check.py`, exit 0.

    selfchecks   SC1 single-cut reads-identical, hand renumber   PASS
                 SC2 nested two-epoch composition, s1            PASS
                 SC3 naive composition collides (landmine),
                     surviving-domain fix passes                 PASS
    directed     c1 rank reclaim: naive COLLIDES two-sided,
                     surviving composite path-equal, s1          PASS
                 c2 fusion asymmetry: all paths fuse to (1,1)    PASS
                 c3 in-flight guard: freeze-then-renumber equals
                     renumber-once at the codeword level         PASS
                 c4 no-translation merge FLIPS the read;
                     translated merge restores it                PASS
                 A3 ack-only drop unsound; ack + all-heard sound PASS
    H-D          2400 trials (1700 incomparable pairs, 700
                 triples, 400 of the 2400 spine-heavy):
                   s1 bit-identical + composed maps equal        2400/2400
                   s2 order-isomorphic, common refinement        2400/2400
                   s3 reads identical                            2400/2400
    H-M          400 trials (2 to 4 replicas, continuations,
                 declared stragglers, mid-run joins, second
                 round of incomparable cuts on top, final join
                 vs never-compacted twin)                        400/400
    ContOK       11029 continuation checks                       0 violations
    A3           1335 post-advance mint checks                   0 old-space

Coverage probes (separate instrumented runs): the randomized batches
exercise freezing in every compaction (8558 frozen groups over 2100
maps in one 400-trial batch) and retention (683 retained dead anchors);
plain random histories rarely build fusible spines (24 fusing maps per
2100), which is why the spine-heavy chainy batch exists (217 fusing
maps, 593 fused levels, s1 400/400).

## 7. Where the diamond truth sits, and why

The truth sits at s1, bit-identical, not merely at s2 or s3. Reason:
every pass of the compactor is a pointwise function of the join cut's
final certificate data and not of the path. Dense renumbering depends
only on the final membership of each sibling group (dropping then
renumbering a renumbering lands on the same ordinals as renumbering the
final survivors once); fusion keeps the outermost head, so episodic
fusion composes to the one-shot fusion; freezing only defers a
renumbering that the join cut then performs identically (c3); and fresh
mints cannot perturb ranks because a fresh delta exceeds every original
sibling delta, hence every ordinal (the rED_fresh_dominates argument at
the join). The anticipated s1 obstruction (re-coding an already
re-coded codeword) does not arise because the map renumbers DELTAS and
re-encodes, rather than rewriting encoded bit strings; since a
codeword function is applied to identical final delta tuples, bit-level
identity for any fixed code Gamma follows from s1 at the delta level.

s1 is stronger than the runtime strictly needs (s3 would do for
observers, s2 for merge order), but it is what makes the protocol
coordination-free: the join-merge asserts coordinate AGREEMENT on
shared records (a state union, no reconciliation pass), and that assert
is H-D s1 tested in vivo at every one of the 400 H-M trials' joins.

## 8. What phase 2 owes in Lean

* The diamond lemma at s1. For certified cuts S1, S2 over an honest
  configuration, with maps defined from certificate data (the
  OB-map-from-certificate discipline as a definition):
  `relSPM (S1 -> W) .comp (spm S1) = spm W = relSPM (S2 -> W) .comp (spm S2)`
  as functions on the carried surviving domain, together with equality
  of the compacted states (not merely of reads). The nested case
  (embed-recoding-note Addendum 4) is the comparable-cuts corner.
* The join-epoch CompatOn. Instantiate CompatOn's carried domain with
  the join cut's kept set transported by record identity; add the
  negative lemma that membership pullback aliases (section 5.1), the
  incomparable-cuts analogue of `naive_composition_collides`.
* The map-drop certificate lemma. Under ack + AllHeardSince over the
  ack frontier, every later-delivered op is minted at a cutset
  containing the superseded cut, so its coordinate factors in epoch
  >= e space and dropping earlier maps preserves every fold. The
  ack-only countermodel (section 4, A3) as the kernel FAIL companion.
* The ContOK discharge. From Lamport freshness plus the certificate
  discipline: every post-cut mint satisfies the four ContOK clauses at
  every compacted state (the 11029/0 observation), generalizing
  rED_fresh_dominates to join epochs.
* The shared residue is unchanged: honesty rebasing (Addendum 5.4's
  obligation (*)) now wants to be stated once on the settled-cut
  semilattice; H-D says the rebasing target is well-defined on cuts,
  independent of the path of epochs taken to reach it.

## 9. The runtime change

`runtime/src/replica.js` currently throws on a cross-epoch merge and
documents concurrent divergent compaction as not claimed. The validated
replacement:

1. Epoch identity becomes the settled cut plus its certificate
   (coordinate-addressed cut, declared set, heard frontiers), not a
   per-replica integer; the `epochs` array of maps becomes a
   cut-indexed DAG with joins.
2. On a merge between divergent epochs U and V: form W = U union V,
   `decl(W) = (decl(U) | decl(V)) - W`; each side computes the join map
   from the shared certificate data (deterministic, no round trips),
   relative-compacts its own state to W, translates in-flight old-code
   records through the map, then merges in the join epoch. The throw
   is replaced by exactly the translation the c4 control shows is
   necessary and the H-M runs show is sufficient.
3. Editors must anchor at locally-live records only (OB-anchor-live);
   the ingest path keeps the existing dedup of deletes for
   already-dropped records.
4. Translation maps are garbage-collected per the A3 double
   certificate: everyone advanced past e AND every pre-advance mint
   heard everywhere; the ack-only shortcut is unsound.

Model limits, stated plainly: ops travel id-addressed here and each
state re-derives coordinates from its own anchor record (the H3
extension law); the coordinate-carrying wire form was validated in the
single-epoch harness (#97) and its multi-epoch soundness is exactly the
map-composition question settled above, but the JS wire format itself
is not re-modeled. The declared set is computed with harness-global
knowledge, standing in for the all-heads-visibility half of the
certificate. Deletes are modeled as pure events with no payload
metadata. None of these affect the algebraic question; they are the
protocol half's engineering surface.
