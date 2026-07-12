# Related-work verification pass — Shesha §8 table [L] cells

*2026-07-12. Sources: primary PDFs (PaPoC'19, PODC'16 read in full), ar5iv HTML (Fugue, Eg-walker),
plus targeted searches. Verdicts: CONFIRMED / CORRECTED / NOT FOUND.*

## 1. Kleppmann, Gomes, Mulligan, Beresford — PaPoC 2019

**Verdict: CONFIRMED with two corrections** (no impossibility result in the paper; the paper's own
spec was later proven unsatisfiable).

Full citation: M. Kleppmann, V. B. F. Gomes, D. P. Mulligan, A. R. Beresford. *Interleaving anomalies
in collaborative text editors.* PaPoC '19, ACM, 2019. doi:10.1145/3301419.3323972.
[PDF](https://martin.kleppmann.com/papers/interleaving-papoc19.pdf) | [ACM](https://dl.acm.org/doi/10.1145/3301419.3323972)

- **What is shown to interleave** (§2): "Two published CRDTs for collaborative text editing, Logoot
  [21, 22] and LSEQ [12, 13], suffer from this problem." Cause: dense position identifiers spread
  across the same interval (Fig. 3). Confirmed by tests on open-source implementations.
- **RGA** (§2, §3): "In prior work [9, 10] we mechanically proved that another text editing CRDT,
  RGA [16], does not suffer from this problem; however, RGA can exhibit a lesser variant of the
  anomaly." §3: with sequential insertions "RGA guarantees that there will be no interleaving"; the
  *lesser anomaly* needs the user to move the cursor back (insertions anchored to the same character
  in reverse order, Fig. 4); worst case "the document is typed back to front... arbitrary
  character-level interleaving could occur." **The paper does NOT use the terms forward/backward
  interleaving — that terminology is Fugue's (2023).** Our table's "non-interleaving (fwd) ✓" for RGA
  is the correct modern rendering.
- **Spec** (§2.1): quotes Attiya et al.'s A_strong, argues it "also permits the interleaving anomaly;
  we therefore argue that it is too weak," and adds clause 1(d): for concurrent insertion sets X, Y
  into the same gap, "either all X insertions appear before all Y insertions... or vice versa, but
  they are never interleaved."
- **Impossibility: NONE in the paper.** It *proposes* a fixed RGA (4-tuples with a set e of same-anchor
  timestamps, §3.1) and only "conjecture[s] that applying this construction to RGA results in a CRDT
  without interleaving... A formal proof of this conjecture is left for future work."
- **Follow-up inverts the story** (Fugue §2.5): "That work has two serious flaws: 1. The definition of
  non-interleaving in that paper cannot be satisfied by any algorithm" (4-replica counterexample:
  X={a,c}, Y={b,d} satisfy the hypotheses but must interleave) and "2. The CRDT algorithm proposed in
  that paper... is incorrect – it does not converge" (counterexample found by Chandrassery, Fugue
  App. A.3). So the nonexistence result in this line is *about the PaPoC'19 spec itself*, proved in
  the follow-up, not by it.

## 2. Attiya, Burckhardt, Gotsman, Morrison, Yang, Zawirski — PODC 2016

**Verdict: CONFIRMED on all three sub-claims** (RGA⊨strong is exactly their Theorem 1).

Full citation: H. Attiya, S. Burckhardt, A. Gotsman, A. Morrison, H. Yang, M. Zawirski.
*Specification and Complexity of Collaborative Text Editing.* PODC '16, ACM. doi:10.1145/2933057.2933090.
[PDF](https://software.imdea.org/~gotsman/papers/editing-podc16.pdf) | [ACM](https://dl.acm.org/doi/10.1145/2933057.2933090)

- **Strong spec (Definition 7)**: A = (H, vis) ∈ A_strong iff there is a *list order*
  lo ⊆ elems(A) × elems(A) such that: (1) each event e = do(op, w) returns w = a₀...a_{n−1} where
  (a) w contains exactly the elements visible to e that have been inserted but not deleted;
  (b) "The order of the elements is consistent with the list order: ∀i, j. (i < j) ⟹ (a_i, a_j) ∈ lo";
  (c) elements are inserted at the specified position: if op = ins(a, k), then a = a_{min{k, n−1}};
  (2) "The list order lo is transitive, irreflexive and total, and thus determines the order of all
  insert operations in the execution."
- **Weak spec (Definition 8)**: same condition (1), but "lo is irreflexive and, for all events
  e = do(op, w) ∈ H, it is transitive and total on {a | a ∈ w}." I.e., lo may contain *cycles through
  deleted elements*; per the paper (§3.2, Fig. 1(b)): "at the time of the read, x is deleted from the
  list, the specification permits us to decide how to order a and b without taking into account the
  orderings involving x: a → x and x → b." (Footnote 5: "We conjecture that Jupiter satisfies the weak
  specification.")
- **RGA ⊨ strong**: §4.3, **Theorem 1**: "The protocol R^n_rga satisfies the strong list
  specification." (RGA reformulated as timestamped-insertion trees + tombstone set T; stability
  Lemma 3: adding nodes to a TI tree keeps s(A) a subsequence of s(B).) Theorem 2: RGA's own
  worst-case metadata overhead is O(D lg k) for k operations, D deletions.
- **Lower bound**: metadata overhead is the *ratio* |q|/|w| of replica-state bits to
  user-observable-list bits (Def. 11, after Burckhardt et al. POPL'14). §6, **Theorem 4**: "Let R be a
  push-based protocol that satisfies the weak or strong list specification for n ≥ 3 replicas. Then
  the worst-case metadata overhead of R over executions with D deletions is Ω(D)." Via **Theorem 5**:
  for every D ≥ 4 there is an execution α_D with D deletions whose final observable list is a *single
  element* yet some replica state must hold Ω(D) bits (information-theoretic encode/decode of a
  ⌊(D−2)/2⌋-bit string, decoded by black-box experiments on the protocol). Assumptions: *push-based*
  protocols (covers op-based and state-based, incl. their RGA; every op immediately generates a
  message), n ≥ 3, and the bound "holds even for the weak list specification and even if the network
  guarantees causal atomic broadcast"; extended to client/server (Corollary 11). **So the quantity
  that grows is the state-size/list-size ratio, linear in the number of deletions — deleted-element
  memory in the strictest sense — and it already binds the WEAK spec.**

## 3. Weidner & Kleppmann — Fugue

**Verdict: CONFIRMED (definition + tombstones), with a terminology caution.**

Full citation: M. Weidner, M. Kleppmann. *The Art of the Fugue: Minimizing Interleaving in
Collaborative Text Editing.* IEEE TPDS 36(11):2425–2437, Nov 2025 (arXiv:2305.00583, v1 2023).
[arXiv](https://arxiv.org/abs/2305.00583) | [ar5iv](https://ar5iv.labs.arxiv.org/html/2305.00583)

- **Maximal non-interleaving (Def. 4)** — three conditions: "(1) (Forward non-interleaving) If A is
  the left origin of B, and B appears earlier in the list than any other element that has A as left
  origin, then A and B are consecutive list elements. (2) If B is the right origin of A, and A appears
  later in the list than any other element that has B as right origin, then A and B are consecutive
  list elements, unless Lemma 5 below says otherwise. (3) If A and B have the same left origin and the
  same right origin, then the element with the lower ID appears earlier in the list."
  **There is no standalone "backward non-interleaving" definition**: "It is tempting to define
  'backward non-interleaving' analogously... [but] there are exceptional executions in which forward
  non-interleaving *forces* us to interleave backward insertions" (hence the Lemma 5 carve-out).
  FugueMax is proved maximally non-interleaving; plain Fugue "falls slightly short" (rare backward
  cases). Table 1 verdicts: RGA fwd ✓ / bwd interleaves; Logoot, LSEQ, Treedoc interleave in both
  directions; **WOOT interleaves forward** (refuting PaPoC'19's conjecture); Yjs fwd ✓ proven.
- **Tombstones: yes, Fugue keeps them.** §3 (delete): "All replicas then replace that node's value
  with a special value ⊥, flagging it as deleted (i.e., making it a *tombstone*)." And: "We cannot
  remove a deleted element's node entirely: it may be an ancestor to non-deleted nodes, including
  nodes inserted concurrently." Overhead figure: "about 23 bytes per character, or 13 bytes per
  character including tombstones" (Tree-Fugue).

## 4. Prior naming of "delete reorders survivors"

**Verdict: NOT FOUND.** Searches ("CRDT delete reorder", "tombstone-free RGA", "sequence CRDT without
tombstones", tombstone GC + reorder, RGA purge) surfaced no naming or study of a delete changing the
relative order of surviving elements. Near-misses, all about a *different* failure (lost anchors for
incoming ops, not survivor reordering):
- Roh et al. (JPDC 2011, original RGA) purge tombstones only when *causally stable* (the "Cemetery"),
  precisely so no concurrent op still references them — avoiding the hazard rather than naming it.
  [PDF](http://csl.skku.edu/papers/jpdc11.pdf)
- Yjs: "Yjs can't garbage collect deleted structs (tombstones) while ensuring a unique order of the
  structs" — the closest published articulation that removing tombstones jeopardizes order, still not
  a survivor-reorder anomaly. [Kevin Jahns' blog](https://blog.kevinjahns.de/are-crdts-suitable-for-shared-editing) /
  [discuss.yjs.dev](https://discuss.yjs.dev/t/garbage-collection-and-version-snapshotting/1839)
- A US patent (10545993) notes GC'd tombstones make incoming deltas unpositionable — anchor loss, not
  reordering.

## 5. Prior pairwise / observed-order-stability spec

**Verdict: NOT FOUND as a named spec — but CORRECTED positioning: Attiya+16's WEAK spec is close
prior art.** No hit for "observed order stability", "user-witnessed order", "no reordering ever
observed", or a per-user pairwise spec. However:
- **A_weak already severs order-constraints through the dead** (quote in §2 above: order a, b "without
  taking into account the orderings involving x" once x is deleted). It remains a *global* single-lo
  spec: irreflexivity + per-read totality/transitivity force even causally-unrelated reads to agree on
  co-displayed pairs. Our causal pairwise display stability quantifies only over states with a common
  causal upper bound — strictly weaker in that dimension, and (crucially) A_weak still costs Ω(D)
  (Theorem 4 covers it), so the two are provably not equivalent *if* Shesha implements ours with O(1)
  per-node metadata (see item 7 caveat).
- OT's "intention preservation" (Sun et al., TOCHI 1998) is informal and per-operation, not a pairwise
  display-order spec. PaPoC'19's clause 1(d) is a *strengthening* of strong (and unsatisfiable), not a
  weakening.

## 6. Tombstone-free sequence datatypes in practice

For positioning "Shesha retains nothing": every surveyed system retains per-deletion memory
*somewhere* — in an event log, a retained struct, or discarded-only-with-history.

- **Eg-walker** (J. Gentle, M. Kleppmann, EuroSys 2025; doi:10.1145/3689031.3696076;
  [arXiv:2409.14252](https://arxiv.org/abs/2409.14252)). Not a tombstoned *document state*, but "each
  replica stores a copy of the event graph on disk" — the full editing history, deletions included,
  immutable ("events... always represent the operation as originally generated"). Merging concurrent
  edits transiently rebuilds CRDT-like state: "we invoke the CRDT only to perform merges of concurrent
  operations, and we discard its state as soon as the merge is complete"; during replay "records in
  the sequence are not removed" (transient tombstones). Deleted-element memory is *relocated to the
  log*, retained forever.
- **Chronofold / Causal Trees** (Grishchenko & Patrakeev, PaPoC 2020;
  [arXiv:2002.09511](https://arxiv.org/abs/2002.09511)). "Both a log and a text at the same time" —
  deleted characters persist in the chronofold; only "if a history of a document is discarded
  entirely" is the text re-representable "as a single sequential insertion, with no tombstones."
- **cola** ([blog](https://nomad.foo/blog/cola), [repo](https://github.com/nomad/cola)). G-tree
  ("grow-only tree"): "deleting text only marks the corresponding run as tombstoned, but it's still
  there." Tombstoned, despite being a modern high-performance design.
- **diamond-types** ([repo](https://github.com/josephg/diamond-types)). Joseph Gentle's Rust CRDT and
  the Eg-walker reference lineage: an operation log keyed by (agent, seq) per character, history
  (including deletions) retained; document state materialized from the log.
- **Yjs** ([INTERNALS.md](https://github.com/yjs/yjs/blob/main/INTERNALS.md),
  [Liveblocks guide](https://liveblocks.io/docs/guides/why-you-cant-delete-yjs-documents)). Deletion
  keeps the Item struct as a tombstone; content may be GC'd: "when a type is deleted, all child
  elements are transformed to GC structs. A GC struct only denotes the existence of a struct and that
  it is deleted... it only stores the length of the removed content." Structs are merged/compacted,
  but *existence + id-range + position of every deletion is retained forever*; full removal is unsafe
  ("can't garbage collect deleted structs... while ensuring a unique order").

## 7. Other "spec X requires memory of the dead" lower bounds

**Verdict: NOT FOUND beyond Attiya+16.** Searches for list-CRDT metadata lower bounds, tombstone
impossibility, and space complexity found nothing list-specific after PODC'16. Adjacent: Burckhardt,
Gotsman, Yang, Zawirski, *Replicated Data Types: Specification, Verification, Optimality* (POPL 2014)
— metadata lower bounds for counters/sets/registers; Attiya+16 (§7) explicitly note that framework's
"proof strategy... would not be applicable to lists; obtaining a lower bound in this case requires a
more delicate decoding argument." Attiya+16 remains the *only* bound of the requested shape — and it
is already exactly "consistency (even weak) ⟹ Ω(#deletions) state" for push-based protocols, n ≥ 3.

## Summary table

| # | claim | verdict |
|---|---|---|
| 1a | Logoot & LSEQ interleave (PaPoC'19) | CONFIRMED |
| 1b | RGA: no interleaving for sequential insertions; "lesser" (backward) anomaly | CONFIRMED (fwd/bwd terms are Fugue's) |
| 1c | Impossibility result in PaPoC'19 | CORRECTED: none; its spec proven unsatisfiable + its fix non-convergent in Fugue §2.5 |
| 2a | Strong/weak list spec definitions | CONFIRMED (Defs. 7, 8 quoted) |
| 2b | RGA satisfies strong spec | CONFIRMED (Thm 1) |
| 2c | Metadata lower bound | CONFIRMED: overhead ratio Ω(D), D = deletions; push-based, n≥3, weak OR strong, even under causal atomic broadcast |
| 3a | Maximal non-interleaving definition | CONFIRMED (Def. 4; no standalone backward def — deliberately) |
| 3b | Fugue keeps tombstones | CONFIRMED (⊥-flag; nodes never removable) |
| 4 | Prior naming of delete-reorders-survivors | NOT FOUND (near-misses: RGA stable purge; Yjs order-uniqueness remark) |
| 5 | Prior pairwise/observed-order spec | NOT FOUND as such; A_weak is the load-bearing prior art to position against |
| 6 | Tombstone-free systems retain something | CONFIRMED for all: event graph (Eg-walker, diamond-types), log-as-text (Chronofold), tombstoned runs (cola), GC structs (Yjs) |
| 7 | Other memory-of-the-dead lower bounds | NOT FOUND beyond Attiya+16 (POPL'14 is the non-list ancestor) |

## Implications for our paper

1. **Naming the delete-reorder anomaly: survives as novel.** Nothing in the literature names or
   studies it; published designs dodge it structurally (tombstones, immutable positions, stable-only
   purge). Safe to claim, citing the near-misses above as the closest prior articulations.
2. **Pairwise-vs-strong separation: survives, but must be re-aimed at the WEAK spec.** §8's current
   note ("separation... from the strong list spec appears new") is under-claiming against the wrong
   baseline: Attiya+16 already separate weak from strong precisely on orderings-through-the-dead. The
   novel content is the *finer* separation: causal pairwise display stability is strictly weaker than
   A_weak (agreement only up to common causal upper bounds vs. global lo) and — unlike A_weak, which
   still costs Ω(D) — is implementable with zero deleted-element memory in the document state. That
   is a sharper and still-novel claim.
3. **Fooling-pair impossibilities I1/I2: survive as novel in form.** No prior identical results; kin:
   Attiya's Thm 5 encode/decode (I2 is morally a 2-world finite instance of the same "auditing through
   the dead is remembering the dead" argument — cite it as the asymptotic ancestor) and Fugue §2.5's
   4-replica unsatisfiability counterexample (precedent for spec-impossibility in this exact space).
4. **"Strictly nothing retained": survives against all surveyed systems, with one sharp threat to
   defuse.** Every competitor retains per-deletion memory (log, struct, or graves). But Attiya's Ω(D)
   binds *push-based* replicas satisfying even the weak spec; Shesha escapes only because (a) its spec
   is weaker than A_weak, and/or (b) its model (M2: ternary merge with a version store supplying LCAs)
   keeps old *versions* — the deleted-element memory Attiya proves necessary may live in the LCA
   store, not the state. A reviewer will ask this. The paper needs an explicit paragraph: "retains
   nothing" is a claim about the document state; quantify what the store retains, and check whether
   Shesha-with-store falls inside or outside Attiya's push-based class.
5. **Table cell fixes for §8**: WOOT cell is wrong — Fugue's Table 1 shows WOOT *interleaves forward*
   (PaPoC'19 only conjectured otherwise); Yjs/YATA is forward-non-interleaving (proven) but can
   interleave backward; Treedoc interleaves both ways; plain Fugue is *not* maximally non-interleaving
   (FugueMax is); RGA row (fwd ✓, strong-spec ✓, display-stability ✓ — the last derivable from Thm 1
   since strong ⟹ weak ⟹ no co-displayed pair ever reverses) is confirmed.
