# Compression headroom in the embedded-chain RGA: exploitable invariants, and what field this is

*Companion note to `whiteboard/embed-code-design.tex` (the embedded-chain RGA,
working names `embed-tree`/`embed-code`). Status: assessment / research
directions, 2026-07-15. Nothing here is implemented or validated unless
explicitly marked as already proved in the design doc.*

## Setting

The embedded-chain RGA stores, per live node, an entropy-coded dyadic interval
whose bit string encodes the node's *birth chain* (root-to-node timestamps,
dead ancestors included). Per chain level the current code C(δ) — a flipped
Elias γ over the timestamp differential δ = x − a — costs 2⌊log₂ δ⌋ + 1 bits.
Question 1: are there invariants of the MRDT/RGA setup that license a more
compressed encoding? Question 2: what field of CS (or math) studies
entropy-coded dyadic intervals?

Short answers: (1) yes — at least five invariants with real leverage, two of
them semantics-preserving, and because the Lean capstone
`embed_ra_linearizable3` is parametric in the code Γ, some improvements are
pure plug-in work; (2) the construction decomposes into known objects
scattered across three communities that don't talk to each other — naming the
intersection is itself part of the contribution.

## What field is this?

The construction decomposes into known objects:

- **The mint is arithmetic coding.** "Encode a sequence as a nested
  subinterval of the parent's interval, width ≈ 2^(−code length)" is exactly
  the Shannon–Fano–Elias / arithmetic-coding construction (Rissanen, Pasco
  1976); the dyadic-cell ↔ prefix-code correspondence is the Kraft
  inequality. Theorem 2(ii) of the design doc — extensions nest,
  incomparables are disjoint and ordered — *is* the defining structure of an
  arithmetic coder. Field: source coding / information theory.
- **C(δ) is a flipped Elias γ** (the design doc says this); the family is
  *universal codes for the integers* (Elias 1975; Levenshtein 1968).
- **Order-preserving prefix-free codes are "alphabetic codes"** —
  Gilbert–Moore 1959, Hu–Tucker 1971 (optimal alphabetic binary trees). A
  classical, somewhat dormant corner of coding theory.
- **Engineering twin: order-preserving key encoding in databases.**
  CockroachDB's key-encoding package and FoundationDB's tuple layer solve
  precisely "encode tuples so bytewise-lex equals semantic order," including
  order-preserving varints. The design doc's carrier (parent-relative bit
  string, lexicographic comparison) is that artifact.
- **Data-structures twin: online list labeling / order maintenance**
  (Dietz–Sleator 1987; Bender et al.; Bulánek–Koucký–Saks lower bounds):
  assign labels from an ordered universe under insertion. Our regime —
  labels immutable forever, assigned coordination-free — is the hardest
  corner of that problem, and their lower-bound techniques are the right
  tools for a converse.
- **Distributed-systems home: the CRDT identifier-space literature**
  (Logoot/LSEQ/Treedoc, Weidner's position strings, fractional indexing),
  with Attiya et al. PODC'16 as the only real information-theoretic result.

No community owns the composite "coordination-free, immutable,
order-preserving, self-delimiting, entropy-bounded identifiers." That gap is
one a paper can name — something like **order coding** — and the
embedded-chain RGA is its first achievability result with a mechanized proof.

## The invariants, ranked by leverage

### I1 — Same-anchor comparison locality (already proved; design doc §2 step 1)

A chain-lex first difference always compares two entries with the *same*
birth anchor. Consequence: the per-level symbol never needs to be globally
meaningful — comparisons never cross anchors. Two exploitation modes:

- **Semantics-preserving: context-conditioned coding.** The code used at a
  level may be any deterministic function of the anchor's stored record (its
  own δ, depth, author): honesty guarantees every minter of a child of `a`
  holds `a`'s record, canonicity (Theorem 1(i)) guarantees they hold
  identical copies — so all replicas agree on the context — and I1 guarantees
  comparisons only ever happen within one fixed context. The symbol encoded
  is still δ, so sibling order is still timestamp order and the RGA-lockstep
  identity is untouched; the win is spending fewer bits where the context
  predicts δ (PPM-style modeling, legal inside the convergence proof). The
  design doc's §2 note about author-relative ids is the first special case.
- **Semantics-shifting: anchor-local naming.** δ = x − a measures the
  *global* event gap, but the race it resolves is local: two concurrent
  front-inserts in a busy document pay log(everything that happened anywhere)
  to resolve a 2-way race. Replacing δ with (per-anchor counter,
  author-relative id) makes the cost the entropy of the *actual* race —
  log R + O(1) — but sibling order is no longer timestamp order, so the
  lockstep identity with the published RGA is lost and the semantics drifts
  Fugue-ward. Falsifiable hypothesis, battery-first (per the standing
  protocol: run `whiteboard/litmus/` L1–L25 + DAG PBT on any new sequence
  design before anything else): this variant passes the battery, possibly
  with a different anomaly profile at L19-adjacent shapes.

### I2 — δ=1 unary runs

Sequential typing produces unary chains of consecutive same-author stamps;
the chain of the i-th run element is determined by (run-start chain, i). So
maximal δ=1 runs coalesce into a single record (start, length, string) with
O(1) order metadata per *run*, split on interior insert/delete. This is
Yjs's item-range trick, and it is the practical 10–100× for real text — it
attacks the fact that coordinates are Θ(depth) and sequential typing makes
depth linear (the last character of a 1000-char sequentially-typed document
carries a ~4000-bit chain; parent-relative storage already amortizes this,
runs collapse it).

### I3 — Steiner closure

After folding, co-heirs of the same dead founder each carry a copy of the
dead prefix (in the design doc's worked example, 22 and 16 both carry M(6)).
The minimal retained structure is the **Steiner tree of survivors in the
birth tree**: unary dead paths splice into edge labels, branching dead nodes
are stored once and shared. That is precisely PATRICIA/radix-trie compaction
over the coordinate strings — the isometric fold is already the unary splice
done one level at a time; what's missing is the sharing.

### I4 — Causal stability (the MRDT model's gift)

Once every replica has seen all racers at an anchor, the sibling verdict can
never be contested; a closed race can be re-coded at *rank* entropy
(log k! for k siblings) and a stable sequential region at essentially zero
order bits. This yields a two-tier state — cold rank-coded prefix + hot
entropy-coded frontier — converging to the true minimum (tree shape +
characters). It is the design doc's stated open cost item, but there is an
MRDT-specific research question inside it: op-based systems find
stability-based GC notoriously subtle (Yjs), whereas the MRDT version store
hands the merge its causal frontier and LCA — does the three-way-merge model
make stability-triggered renumbering *provably* safe where op-based cannot?
That would be a genuinely novel MRDT-vs-CRDT separation result.

### I5 — The code itself is a factor of 2 off (DONE: mechanized 2026-07-15, task #77)

The design doc's "spend bits twice" argument overstates: announcing the
length needs log L ≈ log log δ bits, not L bits. An order-preserving flip of
Elias δ (flip the γ-header of the length field; the same
across-length-class monotonicity argument goes through) costs
log δ + 2 log log δ per level instead of 2 log δ, halving the cost of large
races. Because `embed_ra_linearizable3` is parametric in Γ, this is pure
plug-in work: prove flipped-Elias-δ is an `OrderedPrefixCode` instance and
the capstone is inherited. Note this touches the abstract's
"entropy-optimal" claim — currently optimal only as Θ; the constant is
beatable. (I1's context conditioning and I2's runs, by contrast, exceed the
current `OrderedPrefixCode` interface — they need the mint signature widened
to see the anchor record.)

### Also already exploited (for completeness)

Causality δ ≥ 1 (the differential coding itself); pure-removal deletes +
OR-set survival (no delete metadata in the state); the no-tie theorem (no
tiebreak bits; the read's id tiebreak is dead code).

## The sharpened research question

The frame that unifies both questions: **the state of a replicated list is a
one-shot code of its event set, under the constraints coordination-freedom
and immutability impose; the read function is the fidelity criterion.**
Attiya et al. PODC'16 is the only known converse and it is coarse (Ω(D) for
push-based protocols). The precise question this setup makes askable:

> Given the honesty invariants, what is the conditional entropy of the sort
> verdict given the context shared at mint time — and does
> context-conditioned minting achieve it?

That is a matching upper/lower bound pair — an information theory of
replicated lists — and the unusual half is already in hand: a mechanized,
code-parametric achievability theorem. The lower bound would import
list-labeling techniques into the CRDT setting, which appears not to have
been done.

## Cheapest next experiment with real signal

I1's semantics-preserving mode: measure H(δ | anchor context) on realistic
editing traces (published keystroke corpora exist) to see how far below
2 log δ the achievable rate actually sits — before committing anything to
Lean.

## Results: the I1 measurement (2026-07-15, task #76)

Ran on real traces (`josephg/editing-traces`: the automerge-paper LaTeX
trace and seph-blog1, single-user; friendsforever and clownschool, genuine
two-user concurrent DAGs). Replay harness:
`whiteboard/litmus/entropy_measure.py` — dense Lamport time (inserts *and*
deletes tick, merges take max), anchors resolved from the live view exactly
as the datatype mints, concurrent DAGs replayed over a shared birth tree
with RGA sibling order. Correctness gate: byte-equal `endContent` on all
four traces (this also independently re-validates the embed merge order on
real collaborative editing data).

| trace | n ins | P(δ=1) | E\|C\| | E\|Eliasδ\| | H(δ) | H(δ\|author) | H(δ\|joint ctx) | run-coalesced bits/char |
|---|---|---|---|---|---|---|---|---|
| automerge-paper | 182,315 | .966 | 1.512 | 1.424 | 0.529 | 0.529 | 0.513 | 0.757 |
| seph-blog1 | 212,489 | .949 | 1.759 | 1.624 | 0.766 | 0.766 | 0.718 | 1.074 |
| friendsforever | 23,720 | .915 | 1.594 | 1.562 | 0.872 | 0.834 | 0.729 | 1.023 |
| clownschool | 22,737 | .920 | 1.417 | 1.431 | 0.773 | 0.750 | 0.694 | 0.833 |

**H1 (mixture structure): confirmed.** δ is a δ=1 continuation mass
(92–97%) plus a heavy cursor-jump tail (max δ ≈ document age, 12k–356k).
H(δ) = 0.53–0.87 bits/level against E|C| = 1.4–1.8.

**H2 (context conditioning): REFUTED as a lever.** The full mint-time
context (same-author-as-anchor × anchor-δ class) buys only **0.02–0.14
bits/level** over the unconditional entropy. The reason is structural: the
entropy is already dominated by the δ=1 mass, and the anchor's record
cannot predict whether the *minter* is about to jump — the information that
matters is in the minter's head, not the anchor's record. Verdict: **I1's
semantics-preserving mode is not worth mechanizing.** A clean negative
result; the widened-mint-signature machinery it would need is hereby
de-prioritized.

**H3 (per-level floor): confirmed, with a sharper edge.** Any per-level
prefix-free code pays ≥ 1 bit/level, so the max recoding gain at this layer
is E|C| − ~1 ≈ 0.4–0.8 bits/level — and C already gives the δ=1 mass its
1-bit optimum (C(1) = 0). Elias-δ is a **wash in practice** (±0.1
bits/level; *worse* on clownschool): it wins only at δ ≥ 32 and loses at
δ ∈ {2,3} ∪ [8,15], and real tails are thin. Its value is the *theorem*
(the constant-factor claim in the design doc §2), not measured savings.

**I2 (runs) is the real lever, as ranked.** Per-agent maximal δ=1 runs
have mean length 15–35; coalescing them (run head pays C(δ), run pays
C(len) once) cuts order cost to 0.76–1.07 bits/char — **the only mechanism
that breaks the 1-bit/level floor**, worth ~2× on these traces before even
counting the Θ(depth)-collapse effect on coordinate length.

**Calibration bonus.** Measured order metadata is ~1.5 bits/level ≈ 4.5
bits/level of coordinate (mint adds |1·C|+2) on real traces — consistent
with the design doc's "~4 bits per level sequential" and small against the
8+ bits/char the characters themselves cost. Caveats: plug-in entropy
underestimates on heavy tails; conditioning classes are coarse (finer
classes would only strengthen the H2 refutation direction marginally
before overfitting); dense-Lamport regime assumed throughout.
