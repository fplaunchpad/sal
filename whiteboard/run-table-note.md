# The run table: a lossless representation of the embed RGA's live chains

Status: designed and machine-validated (Python harness
`whiteboard/litmus/run_table_measure.py`: directed cases, randomized PBT with
concurrent merges, and the full real-trace measurement). Lean mechanization
owed; section 10 states what the representation-iso theorem should say, given
what the implementation actually needed. Task #73.

## 1. The datatype and the measured problem

The embed RGA's state is the document itself: records `(id, element,
coordinate)` kept strictly descending by key. A coordinate is a bit string,
the concatenation of codewords of an ordered prefix code along the record's
birth chain: an insert against anchor `a` at timestamp `t` mints
`coord = coord(a) ++ enc(t - ts(a))`. The display key maps bit `0` to symbol
`1`, bit `1` to symbol `2`, and appends a terminator `3`; the read is the
descending lexicographic sort of keys, so an ancestor sorts before its whole
subtree and siblings sort newest first. In the sided (Fugue) variant each
level additionally carries a side bit, with the banded order `(R, d) <
marker < (L, d')` and the L band mirrored. Deletion is pure removal.

The state-level GC stack (rank renumbering plus spine fusion, applied at
settled cuts) removes the dead-history share of coordinate weight. What
survives it, measured on the josephg editing traces, is the live tree shape
itself: live chains of mean depth 835 to 1468 levels per coordinate at about
one bit per level. The fused chain representation costs 856 to 1471 bits per
live character one-sided and 1736 to 2988 sided, and 97 to 99.8 percent of
those bits sit on live ancestor levels that no epoch map can touch. The
sided model additionally pays a flat 1 bit per level side flag against a
true side entropy of 0.19 to 0.27 bits (L mints are 3.0 to 4.6 percent under
Fugue), a 4x to 5x overpay on the side channel. Both residues are
representation costs, not epoch costs: the answer has to be a different
encoding of the same immutable chain data, not a better epoch map. The run
table is that encoding.

## 2. Runs

Work over the kept tree: the live records plus their dead ancestors
(every other node has been removed outright; tombstone-freedom is
unchanged). Say the edge from node `p` to its child `c` is fusible when

  1. `c` is the unique kept child of `p`,
  2. `delta(c) = 1`,
  3. `side(c) = R` (vacuous in the one-sided model), and
  4. `live(c) = live(p)`.

A run is a maximal chain of fusible edges. Since fusibility is a per-edge
predicate and condition 1 gives each node at most one fusible out-edge, the
runs are a canonical partition of the kept tree into chains: a function of
the state, independent of arrival order. A table entry is one run, with
header

    (liveness flag, parent entry ref, offset in parent, side, head delta,
     length)

where members after the head implicitly have delta 1 and side R, and
liveness is uniform along the run (condition 4). Live runs carry records; a
record's address is `(run id, offset)`. Dead entries carry no records, only
the structure that live descendants' coordinates pass through. What typing
mints is exactly a fusible chain (each keystroke extends its predecessor at
delta 1, side R, live), so real documents decompose into few long runs.

The table is representation metadata over immutable chain semantics. It is
lossless in the strong sense: from the table alone one recovers every kept
node's delta (head delta from the header, 1 elsewhere), side, liveness, and
timestamp (the sum of deltas along the contracted path, pre-epoch), hence
every coordinate, hence the state. The harness gates this exactly: on every
trace, every live record's coordinate bit length and every head timestamp is
recomputed from the table and compared with the chain accounting, with zero
tolerance.

No stability gate. The renumber and fusion epoch maps consume a settled
cut (stable delivery plus visibility of all heads). The run table needs no
such hypothesis: it is an invertible re-representation of the current
state, whatever that state is, so it applies to every state, unsettled
suffixes included, and in particular to the freshly typed hot end of the
document where the depth cost is being minted. The PBT exploits this by
rebuilding the table mid-flight between merges at every event.

## 3. The tail-attachment lemma

Lemma. In the canonical table, every entry attaches at its parent entry's
last member.

Proof. Suppose entry `E` attaches at member `m` of entry `P`, and `m` is
not `P`'s tail. Then `m`'s run successor is a kept child of `m`, and `E`'s
head is another kept child of `m`, so the successor is not the unique kept
child of `m`, contradicting fusibility of the edge from `m` to its
successor. So `m` is the tail.

Three consequences. (a) The header field "offset in parent" is derivable
(always parent length minus 1); the accounting model below still counts it,
and reports it as recoverable. (b) The cross-run comparator only ever
diverges at a tail or inside a shared run, so it consults entry chains and
header fields only, and never materializes a coordinate chain (section 4).
(c) It is cheap to check: the harness asserts it on every build of every
table on every trace and every PBT state.

## 4. The comparator

Within a run, display order is offset order: member `j+1` is the R delta-1
child of member `j`, hence lies in its R subtree, hence displays after it
(one-sided: a node displays before its whole subtree).

Across runs, compare the two entry chains (root entry to the record's
entry; by the lemma, every step exits at a tail). At the first difference:

* Case A, one chain is a prefix of the other: `x`'s entry lies on `y`'s
  path, and `y` exits it at the tail. If `x` sits strictly above the tail,
  `y` is inside `x`'s R-continuation subtree, so `x` displays first. If `x`
  is the tail, then one-sided `x` displays first; sided, `y` displays first
  exactly when `y`'s branch is an L branch.
* Case B, two different branch entries hanging at the same tail: compare
  branch headers. One-sided: newest first, `(ts, agent)` descending, with
  `ts` derivable from summed deltas. Sided: L band label-ascending, then
  the node itself, then R band label-descending.

Tie-break honesty: the `(ts, agent)` concurrency tie-break is not encoded
in either representation's counted bits (the chain representation's
coordinates do not encode the agent either; the landed measurement scripts
count sibling ties and skip the bit-level display check on the concurrent
traces for exactly this reason). The run table preserves that parity: the
tie oracle rides outside the representation on both sides and is charged to
neither.

The cost of a comparison is the contracted depth: one entry per run on the
path, instead of one level per node. The measurement reports the contracted
depth distribution (mean and max runs per coordinate path) next to the
chain depth it replaces.

## 5. Mutation rules

Splits mutate the table, never the semantics: the stored chain data of
every node is immutable; only the partition into runs changes.

* Insert (local mint or delivered op), anchored at node `a`:
  if `a` is interior to its entry, split the entry after `a` (the mid-run
  split: `a`'s member suffix becomes a new entry at delta 1, side R, same
  liveness, and the old entry's attachments move to the new tail). Then
  attach the new record as a singleton entry at `a`, now a tail. Then
  coalesce: if the singleton's edge is fusible and it is the tail's unique
  attachment, it fuses into the parent entry. Coalesce-after-attach is how
  typing extends a run in O(1) table work, and how a foreign run delivered
  member by member re-coalesces into a single entry (directed case D3).
* Delete of node `x`: split to make `x` the tail of its entry. If `x`
  still has kept children, this is a liveness split: carve `x` out as a
  dead singleton (or flip its entry dead if it is already a singleton),
  moving the attachments down. If `x` is childless, it simply vanishes
  (tombstone-freedom): its entry shrinks; if the entry empties, remove it,
  drop newly unkept dead tails upward (a dead tail with no children is not
  kept), and re-coalesce the parent with a now-unique fusible child.
* Coalesce is the inverse of split, and it is not optional: without it,
  deleting a concurrent interloper leaves the two halves of the old run
  split forever, and the table drifts from the canonical partition (found
  during design, pinned by directed case D4 and the PBT's
  incremental-equals-canonical gate after every event).
* Delivery under a vanished anchor: an op can arrive whose anchor chain
  passed through nodes that vanished locally (deleted while childless). The
  op's carried coordinate contains exactly the missing levels; delivery
  re-materializes them as dead entries before attaching (directed case D5).
  This is the run-table cost of tombstone-freedom, paid with information
  the embed op already carries.
* Merge: union of event sets, i.e. deliver the other replica's events one
  by one through the two rules above.
* Epoch interplay: a renumber or fusion epoch rewrites labels (rank
  ordinals per sibling group) and collapses settled dead spines; the run
  table is then rebuilt over the compacted tree. Rebuilding is sound
  because the table is a function of the state. Renumbering lengthens live
  runs (every unary live child gets ordinal 1, so cursor-jump children that
  broke fusibility at mint time become fusible), and fusion turns each
  surviving dead spine into a single dead entry. The measurement reports
  this composed column separately.

## 6. Sides

Runs are uniformly R by the fusibility conditions, so member sides cost
nothing; the entry header carries one side bit, and L entries are the only
L data in the table. Under Fugue, L is minted only when the anchor already
has an R child (3.0 to 4.6 percent of mints on the traces). One corrected
hand-derivation is worth recording (directed case D6): an insert after node
`c` whose successor is `d` mints an L child of `d`, so it is `d`'s outgoing
edge that breaks, not `c`'s incoming one: the run keeps `d` as its tail and
the L entry attaches there; no extra fragmentation occurs at `c`.

An alternative side accounting stores the L entries as an explicit id list
(cost: number of L entries times the id width) instead of one bit per
entry; the harness reports the header-bit variant as the headline and the
measured L-entry count makes the alternative computable. Either way the
side channel collapses from one bit per live level (the flat flag of the
chain representation) to one bit per entry.

## 7. The accounting model

Applied identically to both representations; every pointer and every header
bit is counted; no hidden structure. `D` is the flipped Elias delta code of
the landed scripts; `W = ceil(log2(N_entries + 1))` is the id width, one id
space for all entries plus the root sentinel.

Chain representation, per record: the sum over its kept-chain levels of
`|D(delta_level)|`, plus one side bit per level in the sided model. This is
exactly the `prefix_bits` accounting of the landed measurement scripts;
"chain fused" is that quantity after the renumber+fusion epoch, the current
best.

Run-table representation:

    per record:      W  (run id)  +  |D(offset + 1)|
    per entry:       1 (liveness) + W (parent ref) + |D(parent_offset + 1)|
                     + |D(head delta)| + |D(length)| + 1 side bit (sided)

Totals are reported per live character, with the full component breakdown
(record ids, record offsets, and each header field separately), so every
number in section 8 is auditable back to a field. Not charged on either
side: the `(ts, agent)` tie oracle (section 4). Two fields are counted
although the canonical table makes them recoverable: the parent offset
(tail-attachment lemma) and, when records are stored grouped by run, the
per-record run id itself (it is then positional); the breakdown lets the
reader subtract them.

## 8. Measured results

josephg editing traces, replayed exactly as in the landed measurement
scripts (sequential traces single-author; concurrent traces through the
shared-birth-tree driver). All values in bits per live character under the
section 7 model. "cf" is the chain representation after its best epoch
(renumber plus fusion, the landed numbers, reproduced by this harness);
"rt" is the run table over the raw uncompacted chains, no epoch, no settled
cut; "rtc" is the run table rebuilt after the renumber+fusion epoch.

    trace                family   ch-before      cf      rt     rtc  cf/rtc
    friendsforever_flat  1-sided     1622.5   856.5   22.13   22.30   38.4x
    friendsforever_flat  sided/F     2582.0  1735.7   22.54   20.98   82.7x
    clownschool_flat     1-sided     2488.7  1471.0   22.42   22.64   65.0x
    clownschool_flat     sided/F     4058.5  2988.1   24.11   21.20  140.9x
    seph-blog1           1-sided     2974.9   917.2   26.00   23.16   39.6x
    seph-blog1           sided/F     5559.1  1919.8   27.21   24.99   76.8x
    automerge-paper      1-sided     2304.5  1279.4   23.76   23.92   53.5x
    automerge-paper      sided/F     4448.0  2583.7   25.21   24.58  105.1x
    friendsforever       1-sided     1243.2   856.5   20.92   22.30   38.4x
    friendsforever       sided/F     2189.2  1735.6   22.36   20.98   82.7x
    clownschool          1-sided     1863.1  1471.0   20.85   22.64   65.0x
    clownschool          sided/F     3421.3  2988.1   22.29   21.20  140.9x

Component attribution (the auditable breakdown; representative extremes,
full breakdowns in the harness output):

    friendsforever_flat 1-sided raw:  22.13 = rec id 12.00 + rec off 5.69
        + headers 4.45 (parent 1.82, delta 1.10, len 0.72, poff 0.66,
        flag 0.15); 3,233 entries (3,121 live runs, mean length 6.8,
        112 dead), id width 12 bits
    seph-blog1 sided raw:  27.21 = rec id 14.00 + rec off 6.79 + headers
        6.42 (incl. side 0.21); 11,933 entries (6,347 live runs, mean
        length 8.9, 5,586 dead, 5,095 L), id width 14 bits

Contracted depth (runs per coordinate path, the comparator's walk length),
against the chain depth it replaces:

    trace                family   chain lvl (fused)   rt mean/max   rtc mean/max
    friendsforever_flat  1-sided        851.5          137.6/437      43.7/189
    clownschool_flat     1-sided       1467.1          231.0/556      19.6/77
    seph-blog1           1-sided        906.4          180.8/564     126.1/380
    automerge-paper      1-sided       1266.2           94.2/337      70.1/314
    (sided runs 5 to 60 percent deeper; worst: seph-blog1 253.1/801 raw,
     196.1/615 composed)

Side cost (sided/Fugue): the chain representation pays one flat bit per
live level, 867.8 to 1494.1 bits per char after fusion; the run table pays
one bit per entry header, 0.061 to 0.174 bits per char, a 5,000x to 24,000x
collapse on that channel, and below even what an entropy-coded per-level
flag could reach (H(side) = 0.19 to 0.27 bits per level times 850 to 1500
levels). The alternative explicit L-list costs |L| times the id width
(e.g. friendsforever_flat: 1,032 L entries times 12 bits = 0.58 bits per
char), so the header bit is also the cheaper explicit form at these sizes.

Gates, all PASS:

* Display identity on all six traces, both families, raw and composed
  tables: walk order equals the chain display exactly, text equals
  endContent (including the concurrent traces under the (ts, agent) tie
  oracle).
* Pairwise comparator: 8,033 to 8,273 sampled pairs per trace per family
  per table (about 198k verdicts), all matching display positions, with
  antisymmetry checked.
* Losslessness: coordinate bit lengths and (pre-epoch) head timestamps
  reconstructed from the table alone, exact on every live record of every
  trace (21,148 to 104,852 records per trace, both families, raw and
  composed).
* Tail-attachment invariant asserted on every entry of every table built.
* PBT: 150 trials, 8,186 events, 3 replicas with random concurrent edits
  and merges; the table rebuilt and gated at 4,936 states (walk identity,
  all-pairs comparator on 294,968 pairs, incremental rules equal canonical
  rebuild after every event); exercised 872 merges, 315 mid-run splits,
  438 liveness splits, 551 coalesces, 26 vanished-anchor
  materializations, 972 unkept vanishings. Directed cases D1 to D6 all
  pass, including the no-split rival pinned to the wrong display.

## 9. Verdict and attribution

The prediction (per-record cost collapses from Theta(depth) to O(1)
amortized plus a log-sized offset, tens of bits per char, an order of
magnitude below the fused 856 to 2988) is CONFIRMED, with margin: 20.9 to
27.2 bits per char, 38x to 141x below chain-fused, 1.5 to 2 orders of
magnitude. Where the remaining bits sit:

1. The per-record run id is now the dominant cost (10 to 14 of the 21 to
   27 bits, the flat id width): the deep-chain cost did not shrink to the
   offset code, it shrank to ONE pointer. In an implementation that stores
   records grouped by run, this field is positional and free, which would
   put the total at 9 to 14 bits per char; the accounting charges it
   because the pre-registered model does.
2. The offset (Elias delta) costs 5.2 to 12.1 bits per char; headers
   amortize to 0.6 to 6.4 bits per char total.
3. The epoch stack becomes bit-wise marginal under this representation: the
   composed column beats raw by at most 2.9 bits per char (sided) and
   LOSES to raw by up to 1.8 (one-sided, where longer post-renumber runs
   make offsets dearer than the headers they save). The run table alone,
   with no settled cut at all, already delivers the collapse. What the
   epoch still buys is structure, not bits: entries drop up to 7x
   (clownschool_flat 4,029 to 573), the id width shrinks, raw 'jump'
   boundaries (cursor moves minting delta > 1) vanish entirely under
   renumbering, and the contracted depth drops up to 11.8x.
4. Honest limit: the contracted depth is tens to hundreds of runs (mean
   19.6 to 261), not O(1). The BIT cost per record is O(1) amortized plus
   the offset; the comparator's TIME is still Theta(contracted depth) per
   cross-run comparison. Collapsing comparison time further (an order
   index or skip structure over the contracted tree) is a separate,
   orthogonal layer; nothing here needs it for the metadata claim.
5. The concurrent traces cost slightly less than their flattened twins
   under the raw run table (dense-clock replay yields smaller deltas and
   longer mergeable runs), and their composed columns land on the same
   totals as the flat twins, the representation-level echo of the epoch
   map's history independence.

No design flaw surfaced: no comparison required materializing chains (the
tail-attachment lemma is why), and no split rule broke display identity.
Two deviations from the task's letter, both recorded above: dead kept
structure is grouped into dead runs under the same fusibility rule (the
task text defines runs over live nodes only; dead entries are the
structural complement and amortize dead spines), and one directed
expectation (D6) was corrected during hand-derivation, not by fitting to
the implementation: the sided L child breaks the successor's outgoing edge,
so the run keeps its tail and gains an L attachment, three entries rather
than four.

## 10. What the Lean representation-iso theorem should state

The implementation needed exactly five facts; the mechanization should be
their formalization, over the kernel embed model (payload-generic,
code-generic in Gamma), with the canonical table defined as the partition
of the kept tree into maximal fusible chains.

* T-repr (the iso). `tableOf : State -> RunTable` and
  `stateOf : RunTable -> State` with `stateOf (tableOf s) = keptData s`
  and `tableOf (stateOf T) = T` for canonical `T` (characterized by:
  maximal fusible chains, uniform liveness, tail attachment). Post-epoch
  the iso is over (labels, sides, liveness), NOT timestamps: the harness
  needed the ts-reconstruction gate switched off after renumbering,
  because rank ordinals deliberately forget time. Stating T-repr over
  timestamps would make it false after the first epoch.
* T-tail (the load-bearing lemma). Every entry of a canonical table
  attaches at its parent's last member. This is what licenses the
  comparator's two-case structure and makes the parent-offset field
  derivable; it should be proved once and consumed by T-cmp and T-walk.
* T-cmp. The two-case path comparator equals the fold's key order through
  the abstraction: `cmpTable T x y = keyLt (key (coord x)) (key (coord
  y))`, parametric in the (ts, agent) tie oracle exactly as the chain
  comparator is (neither representation encodes it).
* T-walk. The structural walk of the table equals the fold's display
  (query) sequence. T-cmp and T-walk together are the display-identity
  gate as a theorem.
* T-mut (six simulation lemmas). Each mutation rule commutes with
  canonicalization: `tableOf (do op s) = rule_op (tableOf s)` for local
  insert (split + attach + coalesce), local delete (the three liveness
  cases), delivered insert including the vanished-anchor materialization
  (which consumes the op's carried coordinate, so the rule's signature
  must take pi, not just the anchor id), delivered delete, and epoch
  rebuild. The coalesce half is not optional: without it the delete rule
  does not re-enter canonical form (D4); this is the finding a paper proof
  would most plausibly have hand-waved.
* T-epoch (composition with the recoding cluster). For a stable-prefix map
  satisfying H2/H3, `tableOf (rho[s])` is the rebuild, and T-cmp/T-walk
  for it follow from H2; no new order argument is needed. This slots into
  the existing `EmbedRGA_Recoding` theorem cluster as a client.

No stability or honest-delivery hypothesis appears anywhere except T-epoch
(which inherits the settled-cut contract from the epoch map it composes
with): T-repr, T-tail, T-cmp, T-walk and T-mut are state-level theorems
about a representation change, which is the formal content of "no
stability gate".
