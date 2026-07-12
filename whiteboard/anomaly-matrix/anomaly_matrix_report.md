# Verified anomaly-comparison matrix for sequence RDTs (task #64)

Machine-verified successor of the DRAFT table in `whiteboard/sibling-linked-proof.md` §8.
Every cell below is backed by code that ran: minimal witnesses (≤ 8 nodes) for every ✗,
PBT counts for every ✓. Harness: `scratchpad/anomaly_matrix.py` (architecture ported from
`whiteboard/sl_pbt.py`); production libraries: `scratchpad/prod/prod_witness.mjs`,
`mixed_probe.mjs`, `pos_growth.mjs`. Full logs: `scratchpad/full_matrix.log`.

Reproduce: `python3 anomaly_matrix.py` (~3 min; `--quick` for a fast pass);
`cd prod && node prod_witness.mjs && node mixed_probe.mjs && node pos_growth.mjs`.

**Corpus.** Six implementations behind one interface (`insert(x, anchor)`, `delete(x)`,
`read`, ternary `merge(L,A,B)` with the live-set rule `(A∩B)∪(A∖L)∪(B∖L)` where deletion
semantics allows). Shared multi-replica corpus: 12,000 trials (5,000 epoch-trials with
E∈{1..3} epochs + 1,000 stale-LCA trials, per timestamp mode banded/interleaved) =
25,917 merges per row; 10,000 single-replica scripts for the sequential column; 2,000
randomized trials per interleaving direction; 2,000 delete-heavy trials for the
tombstone probe. Harness validity cross-check: the TombRGA row matches the global replay
oracle on **25,917/25,917** merges (its merge is the oracle), and every row passed the
survivor-set check on every merge (`liveset_bad=0`) — the live-set rule and tombstoned
removal agree everywhere, as (M2) predicts.

## What the anomalies are

Definitions for every column, self-contained. Ops are `insert(x after a)` / `delete(x)`;
notation `x·3` = element x with timestamp 3; "displayed" = appearing in the read of some
state some replica actually held.

**a. Tombstone retention** *(cost, not misbehavior)* — after `delete(x)`, does any part of
the replica state still mention x (a grave entry, a flag, x inside surviving positions)?
*Tombstone-free* = the post-delete state is indistinguishable from one where x never
existed, given the survivors.

**b. Unbounded per-node metadata** *(cost)* — does the representation of a single live
element grow with history? Witness shape: insert a chain x₁←⌂, x₂←x₁, …, xₙ←xₙ₋₁, delete
all but xₙ; measure xₙ's stored size. Position-based designs grow O(n) here (the deleted
ancestors live on inside the position); pointer/row designs stay O(1).

**c. Sequential misbehavior** — with NO concurrency at all, a single replica's read after
plain inserts and deletes differs from what a naive list would give. The canonical
instance is the **delete-reorder anomaly**: `ins(a·1←⌂); ins(b·2←⌂); ins(c·3←a)` reads
`b a c`; `delete(a)` should give `b c`, but a design that re-sorts rehomed children by
their own timestamps gives `c b` — a delete changed the relative order of two surviving
characters on one machine.

**d. Displayed-order flip** *(pairwise display stability violation)* — some state displays
x before y, and a later or concurrent state (any replica) displays y before x. To a user:
text they have already seen in one order silently reverses. The spec "pairwise display
stability" forbids exactly this, and nothing more.

**e. Global-timeline inconsistency** *(strong list spec violation, Attiya et al. PODC'16)*
— no single total order of all elements is consistent with every read any replica ever
displayed. This can fail **without any single pair flipping** (column d clean): the
witness is a cycle through a *deleted* element's past displays — A displayed `x` before
`g`, B displayed `g` before `y`, and the merge (which no longer knows g's rank) orders
`y` before `x`. Each pairwise order is seen only once; jointly they admit no timeline.

**f. RGA-oracle divergence** — the merge's order differs from what the tombstoned RGA
(graves kept forever) would produce on the same operations. Classified against the
display log: **licensed** = every differing pair was never co-displayed by any state (the
order was decided where no observation constrains it); **violation** = a differing pair
was displayed in the oracle's direction somewhere — i.e., an actual observed order got
reversed (this also shows up in column d).

**g. Forward interleaving** — two replicas concurrently type runs at the same place, each
character anchored on that replica's *previous* character (normal typing). Anomaly: the
merge shuffles the two runs character-wise (`HeWollrldo` instead of `HelloWorld` /
`WorldHello`). Excluded = each run stays contiguous.

**h. Backward interleaving** — same, but each character is anchored at the same fixed
point (typing at the start of a line, or building text right-to-left), so each replica's
own run reads in reverse insertion order. The classically hard case: several designs that
exclude (g) still shuffle here — including the tombstoned RGA itself and production
Automerge (witnessed below).

## The matrix — minimal implementations

✓ = property holds / anomaly excluded; ✗ = anomaly witnessed. Evidence pointers →
row subsections.

| design | a tomb-free | b bounded meta | c seq=naive | d pairwise stable | e strong list | f RGA-oracle | g non-int fwd | h non-int bwd |
|---|---|---|---|---|---|---|---|---|
| TombRGA | ✗ (graves + anchors) | ✓ per-node (state grows) | ✓ 10k/10k | ✓ 12k/12k | ✓ 12k/12k | ✓ 25917/25917 (is oracle) | ✓ 6+2k | **✗ W-h** |
| FlatTF (repo, refuted) | ✓ strict, 2k/2k | ✓ flat | **✗ W-c** | **✗ 6373/12k (seq!)** | ✗ 4684/12k | ✗ 9886 VIOLATION-class | ✓ 6+2k | ✗ W-h |
| Logoot (dense pos) | ✗ copied components | ✗ grows (4→6→10) | ✓ 10k/10k | ✓ 12k/12k | ✓ 12k/12k | ✗ 13998 lic, 0 viol | **✗ W-g** | ✗ W-g′ |
| StoredPath | **✗ paths retain dead** | ✗ grows (10→20→40) | ✓ 10k/10k | ✓ 12k/12k | ✓ 12k/12k | **✓ 25917/25917 (!)** | ✓ 6+2k | ✗ W-h |
| **Shesha** | ✓ strict, 2k/2k | ✓ flat (par+sib ≤ 2) | ✓ 10k/10k | ✓ 12k/12k | ✗ 833/12k, W-I2 | ✗ 5448 lic, 0 viol | ✓ 6+2k | **✓ 6+2k (open cell answered)** |
| Fugue (minimal W-K) | ✗ (tombstones) | ✓ flat | ✓ 10k/10k | ✓ 12k/12k | ✓ 12k/12k | ✗ 14378 lic, 0 viol | ✓ 6+2k | ✓ 6+2k |

"6+2k" = 6/6 directed workloads (2 ts-modes × 3 anchor contexts) + 2,000 randomized
trials, zero failures. "lic/viol" = oracle divergences classified against the display
log: *licensed* = the divergent pair was never displayed in the oracle's direction by
any state; *violation* = a displayed order was reversed.

## Production libraries (scope addition)

Op-based/state-sync libraries driven by scenarios (no ternary merge): yjs 13.6.31,
@automerge/automerge 3.2.6, loro-crdt 1.13.6, list-positions 2.0.0 (node v26.3.1;
all installed clean via npm). Columns f is N/A (no exposed RGA-anchor semantics to
compare against; each library's intended order differs by design); b is n/m for the
first three (internals not per-node comparable from the API).

| library (algorithm) | a tomb-free | c seq=naive | d pairwise | e strong | g fwd | h bwd | mixed fwd/bwd |
|---|---|---|---|---|---|---|---|
| Yjs (YATA) | ✗ S5: 22B + 1 deleted struct vs 2B fresh | ✓ witness+200 PBT | ✓ 30/30 | ✓ 30/30 | ✓ 0/30 | ✓ 0/230 | ✓ 0/50 |
| Automerge (RGA-lineage) | ✗ S5: save *grows* on delete (188→202B; 41 changes) | ✓ witness+200 PBT | ✓ 30/30 | ✓ 30/30 | ✓ 0/30 | **✗ 30/30** `"[zFyExD]"` | ✗ 25/50 `"[zyDEFx]"` |
| Loro (Fugue-lineage) | ✗ S5: 246B after delete-all vs 81B fresh | ✓ witness+200 PBT | ✓ 30/30 | ✓ 30/30 | ✓ 0/30 | ✓ 0/30 | ✓ 0/50 |
| list-positions AbsList (Fugue ref) | state ✓ (2 chars saved) / positions ✗ (S6) | ✓ witness+200 PBT | ✓ 30/30 | ✓ 30/30 | ✓ 0/30 | ✓ 0/30 | ✓ 0/50 |

Notes: (i) index-based APIs make column c definitional — the FlatTF anchored-delete
reorder is *inexpressible* through them; the witness (`"bac"`, delete `a` → `"bc"`) and a
200-script random ins/del PBT vs a JS array still pass on all four. (ii) Production d/e
corpora are small (30 two-epoch trials with deletes + all scenario reads); treat as
smoke-level, not 12k-level. (iii) Automerge backward interleaving is **full char-level
interleaving, deterministic across 30/30 trials** — the production reproduction of our
TombRGA row's h cell. Mixed-direction splits B's run: `"[zyDEFx]"`. (iv) Yjs's
literature-known backward "splitting" did **not** occur in 230 pure-backward trials
(len 3 and 5) nor 50 mixed trials of this shape; recorded as ✓-in-these-scenarios, not
as a general theorem. (v) list-positions in AbsList mode moves *all* metadata into
positions: state after delete-all is empty (truly tombstone-free state), but S6 shows
AbsPosition size grows under backward typing (182→252→392 JSON chars at n=10/20/40;
forward flat at ~122) and survivors' positions embed deleted ancestors' waypoints —
StoredPath's trade, in production. Its List+Order mode instead parks the same metadata
in a shared Order whose waypoints persist across deletes (tombstone-analogue).

## Per-row evidence (minimal implementations)

### TombRGA
- a: chain probe — after inserting 1..12 in a chain and deleting 1..11, `mentions(state)`
  still contains [1..11] (nodes map + graveyard); 1985/2000 random delete-heavy states
  retain a deleted id. Not tombstone-free *by definition* — probe shown anyway.
- b: per-node (id, anchor, grave-bit) = 2–3 fields, flat at n=10/20/40 (state size grows,
  but that is column a's complaint).
- W-h (backward, interleaved ts): anchor a=1; A types 10,12,14 all after a; B types
  11,13,15 all after a. Merged = `[1, 15,14,13,12,11,10]` — A's chars at indices 2,4,6:
  fully interleaved (siblings sort desc-id; interleaved Lamport ids interleave runs).
  Banded ts passes; verdict ✗ (anomaly possible). Forward: subtree nesting ⟹ ✓ 6+2k.

### FlatTF (the repo's refuted flat tombstone-free RGA; cf. `AgentNotes.md`)
- W-c (found by *exhaustive* search over all scripts by length — genuinely minimal):
  `ins(1←0), ins(2←0), ins(3←1), del(1)` → got `[3,2]`, naive list wants `[2,3]`.
  This is the repo's machine-checked `tombstone_free_violates_delete_order` witness
  (b a c → del a → c b). 796/10,000 random sequential scripts fail.
- d: the same flip is *sequential* — pair (2,3) displayed both ways; 6373/12,000 trials.
- f: 9886/25,917 merges are VIOLATION-classified (a previously displayed order reversed)
  — 3-node merge witness: L: `ins(1←0), ins(2←0)`; A: `ins(3←1), del(1)`; B idle.
  A displayed `[2,1,3]` (2 before 3); merge = `[3,2]`. Contrast: every other row's
  divergences are licensed-only. Instrumentation: the nearest-merged-live anchor
  resolution never disagreed between chasing A's vs B's records (0 in 25,917 merges).
- g ✓ (nesting); h ✗ (same witness shape as TombRGA).

### Logoot (dense immutable positions, (digit,ts) pairs, base 16, boundary±1 allocator)
- b: max per-node size grows: fields 4→6→10 at chain depth 10/20/40 (both append-chains
  and front-chains); positions are immutable so deletes never shrink survivors.
- a: survivors' positions *copy neighbor components*: chain probe retains id 8 inside a
  survivor's position after 8 was deleted; 1127/2000 random states retain a deleted id.
  (Caveat: in our encoding the component ts is the element id; real Logoot components
  carry (site, clock), which equally identify the donor insertion.)
- W-g (forward, 6 nodes, both ts modes): A types 10,11,12 each after its previous; B
  types 10010,10011,10012; merged = `[1, 10, 10010, 11, 10011, 12, 10012]` — the classic
  PaPoC'19 interleaving. W-g′ backward: `[1, 12, 10012, 11, 10011, 10, 10010]`.
- d/e ✓ 12k/12k, f: divergences (13,998) all licensed — immutable positions give one
  global order forever, they just pick a *different* order than RGA (2-node witness:
  concurrent `ins(10←0)` | `ins(11←0)` → `[10,11]`, oracle `[11,10]`, never co-displayed).

### StoredPath (position = anchor's position ++ [−ts]; delete = filter)
- **f ✓ (draft said ✗): 25,917/25,917 merges equal the tombstoned-RGA oracle**, including
  the §7 I1 fooling pair, both worlds (g·2: merged `[5,10]` = oracle; g·6: `[10,5]` =
  oracle). Reason: the stored path is exactly the RGA tree ancestry, so lex-sorting paths
  *is* the tombstoned traversal restricted to live nodes; I1's impossibility does not
  apply because the state remembers the dead anchor inside the path.
- **a ✗ (draft said ✓)**: chain probe — survivor 12's path is `(−1,−2,…,−12)`; ids 1..11
  all deleted, all still present; 1541/2000 random states retain deleted ids.
- b: after-chain max path length = n exactly (10/20/40); front-chain flat at 1.
- d/e ✓ 12k/12k (immutable positions); g ✓; h ✗ (same witness as TombRGA — it *is*
  RGA order).

### Shesha (ported verbatim from `sl_pbt.py` modulo oracle globals)
Cross-check row — reproduces all known results:
- a ✓ strict: chain probe NONE retained; 0/2000 random delete-heavy states mention a
  deleted id (the §1 claim "after this line the state contains no trace of d").
- b ✓: per-node row-local representation (par entry + optional sib entry) ≤ 2, flat.
- c ✓ 10,000/10,000 (Theorem S); d ✓ **0 pairwise flips in 12,000 trials** (Theorem P).
- e ✗ (forced, §7 I2): 833/12,000 trials have a display-log cycle. Directed 5-node
  witness (I2 world 1): L: m·1←⌂, g·2←⌂; A: `ins x·5←⌂, del g, del m` (displays
  `[5,2,1]` → x<g); B: `ins y·9←g` (displays g<y). Merge = `[9,5]` (y<x). Cycle
  `x<g, g<y, y<x` = `[2, 9, 5, 2]` **through the dead node g — with zero pair flips**:
  the gap between pairwise stability and strong list is exactly memory of the dead.
- f ✗ licensed (forced, §7 I1): 5,448/25,917 divergences, **0 violations** (Theorem D
  at 12k-trial scale). Directed witness (I1 world 1): A `ins p·5←⌂` | B `ins g·2←⌂,
  ins k·10←g, del g` → merged `[10,5]`, oracle `[5,10]`, pair never co-displayed.
- g ✓ 6+2k. **h ✓ 6+2k — the draft's open cell `[?backward]` answered**: a backward run
  is always a contiguous head-run of the anchor's row, the merge places runs as blocks
  (same-slot runs stay contiguous, newest head first), so runs never interleave. Note
  the scope of the check: single merge of two concurrently-typed runs (the standard
  non-interleaving statement), 2 ts-modes × 3 anchor contexts + 2,000 randomized trials.

### Fugue (minimal Weidner–Kleppmann tree: left/right child lists, tombstoned delete)
- a ✗ (tombstones by design; probe retains [1..11]); b ✓ flat (parent, side, grave-bit).
- c ✓ 10k/10k; d/e ✓ 12k/12k; f ✗ 14,378 licensed, 0 violations (2-node witness:
  concurrent root inserts merge `[10,11]` asc-id vs oracle `[11,10]`).
- g ✓ and h ✓ (6+2k each) — matches the paper's headline; corroborated in production by
  Loro (Fugue-lineage) and list-positions (the author's reference), both 0 interleavings.
- Simplifications vs the paper: insert takes (anchor = left origin, successor computed
  from the visible read); same-side siblings sorted by id ascending. Noted, not load-
  bearing for these columns.

## Surprises vs the draft table

1. **StoredPath is RGA-oracle-faithful (draft: ✗ "different order").** 25,917/25,917
   merges, plus both I1 fooling worlds. It evades the I1 impossibility because its
   positions *retain the dead anchor chain* — which is simultaneously why…
2. **StoredPath is not strictly tombstone-free (draft: ✓).** Under the uniform
   retained-id probe, survivors' paths mention deleted ancestors (1541/2000 states).
   Together, 1+2 sharpen the trilemma memory: stored-path does not escape the
   {tombstone-free, order-fidelity, bounded-metadata} trade — it relocates graves into
   positions and pays with column b (path length = chain depth, measured 10/20/40).
   Only Shesha and FlatTF pass the *strict* no-mention probe; FlatTF pays with
   sequential soundness, Shesha with strong-list/oracle (both forced, §7).
3. **Logoot's strict tombstone-freedom is also nuanced (draft: ✓):** copied position
   components keep deleted ids reachable in 56% of delete-heavy states (encoding caveat
   noted above). Its pairwise/strong-list cells, draft-marked [L?], are now [R]:
   0 flips, 0 cycles in 12,000 trials.
4. **The backward column (new, this task) splits the field:** among minimal rows only
   Shesha and Fugue keep backward runs contiguous; TombRGA/FlatTF/StoredPath/Logoot all
   interleave under interleaved Lamport ids. In production, Automerge interleaves fully
   and deterministically (30/30, plus 25/50 mixed-direction); Yjs/Loro/list-positions
   stayed clean in all scenarios tried.
5. **FlatTF's oracle divergences are violation-classified (9,886), uniquely in the
   matrix** — every other row's divergences are 100% licensed. The three-verdict
   classifier separates "picks a different never-displayed order" (Logoot, Fugue,
   Shesha) from "reverses what a user already saw" (FlatTF) — a sharper refutation of
   the flat design than convergence-failure alone, and machine-checked at 12k scale.
6. Shesha's h-cell (the draft's only genuinely open marker) closes as ✓; TombRGA's
   draft-✓ non-interleaving cell survives only as *forward*; the h-cell for tombstoned
   RGA is ✗ — consistent with the PaPoC'19 finding, now witnessed against our own
   implementation and against production Automerge.

## What remains

- Fugue row uses a minimal reconstruction; a faithful port of the paper's exact
  createBetween (left+right origins as op payload) would harden g/h into [R]-grade
  for the *algorithm as published* (Loro + list-positions already corroborate).
- Production d/e corpora are 30-trial smoke tests; scaling them (and adding offline
  three-peer topologies to exercise stale-LCA analogues) is cheap follow-up.
- Yjs backward "splitting" (Fugue paper's counterexample shape) was not reproduced;
  finding the exact triggering scenario would settle Yjs's h-cell honestly.
- The b-column for Yjs/Automerge/Loro is n/m (API-level); byte-level growth curves per
  node would need internal inspection like the Yjs struct walk used in S5.
- Multi-epoch non-interleaving (runs continued across merges) is out of the standard
  definition and unchecked; Shesha's block placement suggests it holds per-merge only.
- Literature-recall cells now verified in-repo; the two *naming* claims of §8 (the
  delete-reorder anomaly and the pairwise-vs-strong-list separation being new) still
  need the related-work pass before print.
