# The sided embed: two-sidedness as a parameter, RGA as the all-R fragment

*Design note for the two-sided extension of the embedded-chain RGA
(work item #63, successor plan to the sibling-edge design). Written
2026-07-15 from the design-review session; self-contained. Nothing here
is implemented or validated unless marked; the battery is the judge.*

## The proposal in one paragraph

Do not build a second datatype. Parametrize the embedded-chain RGA over
a *side*: an insert names an anchor and a side, chains become sequences
of (side, timestamp) entries, and the display rule generalizes from the
prefix rule ("a prefix precedes its extensions") to the in-order rule
("L-extensions, then the node, then R-extensions"). The current datatype
is the all-R fragment, *exactly*: with side constantly R the in-order
rule degenerates to the prefix rule and R-sibling order (newest adjacent
to the node) is RGA's newest-first. RGA-equivalence is then a theorem
about a fragment (all-R executions erase to current chains, reads
commute with erasure, the existing compaction theorem finishes), and
two-sidedness kills backward interleaving (L19) because backward runs
become chains instead of sibling fans.

## Why a traversal change alone cannot work

A backward run in the current datatype is a sibling fan: every "insert
before c" anchors at c's left neighbor, so concurrent backward runs
interleave *within one sibling group*. No traversal of the same tree
un-fans a fan. The fix requires insert-before to anchor at the *right*
neighbor as an L-entry, so backward runs chain. (A cheaper hack, sibling
order grouped by author, may kill the basic L19 litmus but is not known
to reach maximal non-interleaving; if tried, battery first.)

## The marker formalization (makes in-order plain lex again)

Treat a node's own position as its chain followed by a virtual
terminator, and order the sided alphabet as

    (R,1) < (R,2) < ... < marker < ... < (L,2) < (L,1)

Two-sided comparison is then ordinary lexicographic order on
marker-terminated sided strings: no bespoke three-way prefix clause.
Check: node = p.marker vs descendant p.(R,d)... has marker > (R,d), so
the node precedes its R-extensions; marker < (L,d) so L-extensions
precede the node. The one-sided case is the same formalization with L
uninhabited, which is why the current design is untouched by the
generalization. The L side within itself is *mirrored*: among L
siblings, newer displays adjacent to the node.

## Cost accounting (probably zero extra bits)

- The current block is 1 C(delta) 01, and the leading 1 does nothing
  but keep coordinates positive; positivity survives without it (every
  block ends in 01, so a coordinate always contains a 1). Repurpose the
  leading bit as the side. The format does not grow: the one-sided
  design was already spending one bit per level to say "R".
- The L side needs an order-reversing prefix-free code; the bit
  complement of C is exactly that, at identical lengths.
- Geometry: the cell already has two unminted regions (gap quarter and
  headroom); a two-sided cell needs child room on both sides of the
  node's marker, the same real estate relabeled. The exact framing
  constants need a pencil check; expect a bit of slack to appear or
  vanish, constant either way.
- Runs absorb even the side bit (constant within a run, paid once at
  the head). Backward runs, today the entropy-heavy case (fans with
  growing delta), become delta~1 chains: the side parameter buys a
  compression on backward-heavy editing, not just a semantics.
- The op carries the side on the wire: one bit.

## Side selection is a generation discipline, not a datatype choice

If insert merely "takes a side," convergence and RA-linearizability
hold for any sides whatsoever; those proofs never consult the order's
intent. But Fugue's non-interleaving theorem depends on *which* side is
picked when inserting between a and b (right child of the left neighbor
when possible, else left child of the right neighbor). That selection
rule lives at generation time, and the framework already has a slot for
generation-time rules: honesty. So the architecture is:

- **one sided datatype, verified once, policy-free**: canonicity, birth
  constancy, no-ties (easier: the side is one more tiebreak), fold
  exactness, rc = Either commutation, ins-prefix ghost, and
  RA-linearizability via the mergeable-queue route (it needs only
  canonicity);
- **intent theorems per generation policy**: under "always R at the
  left neighbor," read-equivalence to published RGA (via erasure + the
  existing compaction theorem); under the Fugue selection rule,
  non-interleaving (two-sided convexity; a subtree is an in-order
  interval).

This is the rely-guarantee shape of the framework (rely: ops generated
per the discipline; guarantee: the ordering intent), with RGA and Fugue
as two disciplines over one kernel rather than two datatypes.

## Port / re-prove inventory (Lean)

Ports by parametricity or with one extra case: canonicity, birth
constancy, totality, fold/refold exactness, commutations,
ins_prefix_ghost, the mergeable-queue route (JoinLemma3At +
HonestReach), esorted_ext, e_fold_canon.

Genuinely new proofs: display_iff_chainBefore restated with the marker
rule; subtree_convex becomes in-order-interval convexity (true, classic,
new proof); OrderedPrefixCode gains the ordered sided alphabet as a
parameter, and each code gains its complemented L-half as a new
instance; the capstone re-derives through the parametric route.

Necessarily lost for the full datatype: the lockstep identity with
published RGA and the compaction theorem *as stated* (they survive
verbatim on the all-R fragment). The two-sided intent target is the
non-interleaving spec, not RGA-equivalence.

Touch estimate: broad but mechanical across the model layer (List Nat
to List (Side x Nat) threading, comparable to the 18-file id_mono
estimate from the del-path analysis), with proof content largely
surviving.

## Sequencing (standing protocol: countermodels are the judge)

1. **Pencil the geometry**: the marker/complement layout, the L-side
   boundary cases at the marker, the framing constants. This is where
   the surprise will be if there is one.
2. **Python sided model under the Fugue policy, full battery**:
   L1--L25 including L19 (expected to flip to clean), the credential
   family (must stay clean), DAG PBT, and lockstep of the all-R
   fragment against the current embed model (expected exact).
3. **Only then the Lean refactor**, re-deriving the one-sided instance
   from the parametric kernel rather than keeping parallel code.

## Pointers

- Prior validated two-sided work: the sibling-edge design (immutable L
  anchor + R sibling origin + spine paths; Python-validated, PDF and
  model in whiteboard/); this note's plan supersedes its encoding with
  the sided-chain formulation but its litmus results and gotchas
  (loOn, tombstone, climb-vs-expand) remain the relevant prior art.
- The litmus sweep identified two-sided immutable paths ("path-2") as
  the unique fully-clean design; this is that design, given an
  entropy-coded coordinate realization and a parametric relationship
  to the proved one-sided kernel.
- Design doc: whiteboard/embed-code-design.tex (the contract, the mint,
  the fold, the compaction theorem). Compression context:
  whiteboard/order-coding-compression-notes.md.

## Step-2 results (2026-07-15, `whiteboard/litmus/embed_sided.py`)

Every prediction above validated, first full run:

| check | result |
|---|---|
| Fugue policy, full gauntlet (L1–L25, credential family, CEs, L22–L25) | **CLEAN, including L19** |
| **L19 under Fugue** | S5 = True, out = `[50,30,10,61,41,21,1]` — backward runs became L-chains, blocks contiguous |
| L19 under all-R | S5 = False, out = `[61,50,41,30,21,10,1]` — the known one-sided fan, reproduced exactly |
| all-R fragment, rest of gauntlet | CLEAN (matches the one-sided embed's profile) |
| chain-model ~ code-model lockstep (both policies) | **EXACT** — the side-bit + C/complement carrier is faithful: unique decodability + order embedding of the sided alphabet, machine-checked |
| all-R fragment ~ current `EmbedTreeCode` | **EXACT** on every battery scenario — "RGA as the all-R fragment", machine-checked |
| DAG PBT, 120 + 300 (6 replicas, 12 rounds), all four models | CLEAN |

Model notes recorded for step 3:

- The comparison symbols carry **timestamps in the semantic model and
  deltas in the carrier** — equivalent because a marker-lex first
  difference always compares same-anchor entries (the sided form of the
  §2-step-1 argument); the lockstep is the machine check of that claim.
- The step-1 pencil outcome is embedded in the carrier: block =
  `sideBit ++ (C(δ) | complement(C(δ)))`, the side bit repurposing the
  old constant leading `1`; parsing needs no framing beyond
  prefix-freedom per side. The three-zone *interval* geometry was not
  needed for the carrier at all — the Lean model layer sorts bit-string
  keys, so the fraction realization can stay a whiteboard artifact.
- The Fugue side rule consults the grow-only policy tree (dead nodes
  included — the tombstone-visible successor), confirming side selection
  as generation-time honesty: the datatype below it never changed
  between the two policies.
