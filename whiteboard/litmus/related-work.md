# Related work & novelty assessment — the delta tree paper (task #72)

*2026-07-14. Method: fresh web verification pass over the named prior-art list plus 2024–2026
literature sweeps; builds on `whiteboard/related-work-verification.md` (2026-07-12), which verified
the Attiya PODC'16, PaPoC'19, and Fugue quotes against the primary PDFs. Verdict scale per claim:
**KNOWN** (someone did it — cite them, drop the claim) / **NEAR-MISS** (nearest work named, delta
stated) / **NEW** (actively searched for a refuter and found none). All verdicts are as of today's
searches; a NEW verdict is falsifiable, not a proof of absence.*

## 0. The artifact under assessment

`delta-tree-v3` (in `delta_tree.py`, README findings 13–14): a tombstone-free replicated list for
**three-way merges with an LCA** (the MRDT model of Kaki et al., not op-based delivery). State =
(a) a tree of live nodes with parent-relative fractional ranges — reads are geometric; delete is an
*isometric fold* (the dead node's fraction is composed into its children, so survivor positions are
arithmetically unchanged and delete-order preservation is an arithmetic identity); (b) a *ledger* of
one immutable birth-parent pointer per node, retained through deletes, consulted only by merges.
Merge orders siblings by immutable birth chains (canonical order = RGA order of the birth tree
restricted to survivors) and re-renders all fractions. Validated: clean on the L1–L25 battery
(except one-sided L19, identical to RGA's own backward-interleaving) and on the randomized
version-DAG PBT (120/120, 300/300); lockstep read-equal with the tombstoned RGA on every battery
scenario and 420 random DAG executions. Headed for Lean mechanization in the Sal MRDT framework.

## 1. The landscape in one table

What each nearby system **retains** for the dead, what **arbitrates** concurrent order, and what is
**proved**:

| system | dead-element residue in working state | arbitration | proved |
|---|---|---|---|
| RGA ([Roh et al. JPDC'11](http://csl.skku.edu/papers/jpdc11.pdf)) | tombstones; purged only under causal stability ("cemetery") | timestamps on a tree | strong list spec, later ([Attiya+16 Thm 1](https://software.imdea.org/~gotsman/papers/editing-podc16.pdf)); Isabelle SEC ([Gomes et al. OOPSLA'17](https://arxiv.org/abs/1707.01747)) |
| RGASplit ([Briot/Urso/Shapiro GROUP'16](https://pages.lip6.fr/Marc.Shapiro/papers/rgasplit-group2016-11.pdf)), LogootSplit ([André et al. CollaborateCom'13](https://members.loria.fr/CIgnat/files/pdf/AndreCollabCom13.pdf)) | as base CRDT (block-wise) | as base CRDT | performance work, no new correctness |
| Causal Trees / Chronofold ([Grishchenko & Patrakeev, PaPoC'20](https://arxiv.org/abs/2002.09511)) | the log **is** the text; deleted chars persist in it | causal tree + timestamps | informal |
| WOOT, YATA/Yjs | tombstones / GC-structs (Yjs retains id-range+length of every deletion forever; ["can't garbage collect deleted structs … while ensuring a unique order"](https://blog.kevinjahns.de/are-crdts-suitable-for-shared-editing)) | origin pointers + ids | Yjs fwd non-interleaving proved in [Fugue](https://arxiv.org/abs/2305.00583) |
| Logoot/LSEQ ([interleaving: PaPoC'19](https://martin.kleppmann.com/papers/interleaving-papoc19.pdf)) | no records, **but dead uids persist inside survivors' position identifiers** | identity embedded in positions | interleave (both directions, [Fugue Table 1](https://arxiv.org/abs/2305.00583)) |
| Treedoc ([Preguiça et al. ICDCS'09](https://arxiv.org/pdf/0907.0929)) | tombstones until *flatten*; [flatten requires Paxos-commit / core-nebula consensus](http://renpar.irisa.fr/cfse8/cfse8_10.pdf) | path in a binary tree | — |
| Fugue/FugueMax ([Weidner & Kleppmann, TPDS'25](https://arxiv.org/abs/2305.00583)) | tombstones ("we cannot remove a deleted element's node entirely") | tree of ids | maximal non-interleaving (pen-and-paper); Tree-Fugue ≡ List-Fugue proved |
| Peritext ([Litt et al. CSCW'22](https://www.inkandswitch.com/peritext/)) | tombstones; "deleted character values can be forgotten, but the positions must be remembered" | base text CRDT ids | PBT only |
| Eg-walker ([Gentle & Kleppmann, EuroSys'25](https://arxiv.org/abs/2409.14252)) | **none in the document state** — but the **full event graph (deletes included) is stored on disk forever**; tombstones transient during replay | event graph replay through a transient CRDT | strong list spec, **informal proof (Appendix C)**; the shipped Yjs-variant ordering only *conjectured* maximally non-interleaving |
| fractional indexing ([Figma](https://www.figma.com/blog/realtime-editing-of-ordered-sequences/), [Wallace](https://madebyevan.com/algos/crdt-fractional-indexing/)) | none | **geometry only — known unsound**: interleaves, needs server tie-breaking | none (interleaving accepted as a non-goal) |
| position-strings / list-positions ([Weidner '23](https://mattweidner.com/2023/04/13/position-strings.html), ['24](https://mattweidner.com/2024/04/29/list-positions.html)) | dead uids persist inside survivors' paths (Fugue id space) | identity **is** the sort key (eager paths) | inherits Fugue's proofs |
| MRDT line ([Kaki et al. OOPSLA'19](https://dl.acm.org/doi/10.1145/3360580); [Peepul PLDI'22](https://dl.acm.org/doi/10.1145/3519939.3523735); [RA-lin OOPSLA'25](https://dl.acm.org/doi/10.1145/3720452)) | list merges via relational abstraction (mem, ob); no sequence-CRDT-grade ordering guarantees studied | merge function over LCA | convergence / RA-lin for queues, sets, maps, counters — **no verified sequence with interleaving/stability guarantees** |

Nothing in this table is simultaneously (a) free of per-deletion records in the working state,
(b) free of dead uids inside live identifiers, (c) free of a retained history log, and (d) clean on
display stability + convergence. That is the corner the delta tree occupies, at the price of one
birth-parent pointer per live node (dead ids surviving only as pointer *targets* reachable from
live nodes).

## 2. Claim (i) — the impossibility triangle

**Claim:** {strictly dead-free state, pairwise display stability, topology convergence}: each
pairwise combination machine-witnessed achievable, the triple conjectured impossible, with two
named failure mechanisms (fold-verdict erasure; repair non-locality).

**Verdict: NEAR-MISS — novel as stated, but it has a strong asymptotic ancestor that the paper
must cite and position against.**

- **Nearest work: [Attiya, Burckhardt, Gotsman, Morrison, Yang, Zawirski, PODC 2016](https://dl.acm.org/doi/10.1145/2933057.2933090)**
  ([PDF](https://software.imdea.org/~gotsman/papers/editing-podc16.pdf)). Their Theorem 4: any
  *push-based* protocol satisfying even the **weak** list specification (n ≥ 3, even under causal
  atomic broadcast) has worst-case metadata overhead **Ω(D)** in the number of deletions. This is
  the published form of "ordering guarantees require remembering the dead." The deltas: (1) it is
  a bit-counting asymptotic bound, not a property trichotomy — it names no mechanisms and exhibits
  no achievable-pairs frontier; (2) it binds push-based op/state protocols, **not** the MRDT
  three-way-merge model — in the MRDT model the deleted-element memory can legally live in the
  version/LCA store, which is exactly where the delta tree relocates it; (3) topology convergence
  is an *assumption* in their setting (they quantify over protocols that converge), whereas the
  triangle makes it a leg that designs demonstrably trade away (L22/L23 refuted `range-repro` and
  caught `rose`'s divergence).
- **Spec-level kin:** the PaPoC'19 non-interleaving spec was itself proved unsatisfiable in
  [Fugue §2.5](https://arxiv.org/abs/2305.00583) — precedent for impossibility results about
  sequence specs, but about a different triple of properties.
- **Folklore kin (anchor-loss, not verdict-erasure):** Yjs's
  ["can't garbage collect deleted structs while ensuring a unique order"](https://blog.kevinjahns.de/are-crdts-suitable-for-shared-editing)
  and Peritext's "the positions must be remembered to correctly order incoming changes"
  ([CSCW'22](https://www.inkandswitch.com/peritext/)) both articulate *dangling-anchor* hazards for
  incoming operations. Neither is about a **survivor pair's order verdict** being erased — the
  fold-verdict-erasure mechanism (a dead node's timestamp load-bearing for verdicts among
  survivors) and repair non-locality appear in no source found. The 2026-07-12 verification pass
  independently searched for prior naming of delete-reorders-survivors and found none.
- **No prior pick-2-of-3 formulation** for collaborative sequences was found under any phrasing
  tried (trade-off, impossibility, tombstone GC vs convergence, CAP-style).

**Sharpening required before submission (reviewer traps):**
1. **Condition the triple on baseline sequential soundness (S1) and liveness (LIVE/DUP)**,
   otherwise a trivial timestamp-sorted list (delete = remove) satisfies all three legs vacuously.
   The conjecture as the paper should state it: *no S1-sound design achieves the triple*.
2. **Define "strictly dead-free" so that Logoot is visibly not a counterexample.** Logoot/LSEQ and
   position-strings retain no dead *records*, but dead uids persist inside survivors' position
   identifiers; the ledger's pointer targets are the delta tree's analogous residue. The definition
   "no dead identifier retained anywhere — including inside live nodes' keys, spines, or pointers"
   does this work, and must be stated with that force.
3. **The conjecture is open.** Present it as a conjecture with the eight-countermodel mutation
   family as evidence. The natural proof route is an Attiya-style two-world encode/decode argument
   restricted to the MRDT model; even a restricted-model theorem would upgrade the paper's
   headline. Citing Attiya's Theorem 5 as the asymptotic ancestor of the fooling-pair technique is
   both honest and strengthening.

## 3. Claim (ii) — compaction-equivalence with tombstoned RGA

**Claim:** the design is observationally equivalent to the published tombstoned RGA (lockstep
machine-checked on the battery + 420 random DAG executions): tombstones compact to one immutable
birth-parent pointer per node without changing any read, ever.

**Verdict: NEW as a theorem statement — no prior work states or proves "RGA admits a strictly-live
compaction preserving every read." Three families of near-misses, all materially different.**

- **Eg-walker ([EuroSys'25](https://arxiv.org/abs/2409.14252)) — the closest in spirit, and the
  comparison the paper will be forced to make.** It also has a tombstone-free *document state* and
  derives ordering from durable identity data. But: "each replica stores a copy of the event graph
  on disk" — the **entire editing history including deletions, forever** ("as long as concurrent
  operations may arrive"); tombstones reappear transiently at every merge replay; and its
  correctness is an **informal Appendix-C proof** plus property testing, with the shipped ordering
  variant only "conjecture[d] to be maximally non-interleaving … we leave a detailed analysis … to
  future work." Delta: the delta tree's retained identity data is **O(live)** — one pointer per
  live node, no history, no transient tombstones — and the equivalence target is a mechanized
  (Lean) read-for-read theorem against the published RGA, not spec-compliance of a replay.
- **Causal-stability compaction ([Roh et al.'s cemetery](http://csl.skku.edu/papers/jpdc11.pdf);
  [Baquero/Almeida/Shoker, pure op-based CRDTs](https://arxiv.org/abs/1710.04469);
  [Bauwens & Gonzalez Boix MPLR'20](https://soft.vub.ac.be/~jibauwen/publications/mplr20-from-causality-to-stability-jimbauwens.pdf)).**
  Removes tombstones only *conditionally* — when the middleware certifies no concurrent operation
  can still reference them. Delta: the delta tree's compaction is **unconditional and structural**;
  no stability oracle, no protocol phase. (Causal stability remains the right citation for
  *further* compacting the ledger's dead pointer-targets — the README already notes this.)
- **Representation-equivalence proofs between tombstoned representations:**
  [Attiya+16](https://software.imdea.org/~gotsman/papers/editing-podc16.pdf) reformulate RGA as
  timestamped insertion trees; [Fugue](https://arxiv.org/abs/2305.00583) proves Tree-Fugue ≡
  List-Fugue ("they induce the same total order"). Both are equivalences between two
  tombstone-retaining representations. Delta: ours crosses the retention boundary — tombstoned ↔
  strictly-live-plus-ledger — which is precisely what no prior equivalence does.
- **Engineering kin, compression not compaction:** Automerge stores every operation at ~1
  byte/op; Yjs merges GC-structs but keeps one per deletion range forever
  ([INTERNALS.md](https://github.com/yjs/yjs/blob/main/INTERNALS.md)). These reduce the constant,
  not the asymptotic residue class.

**Honest-accounting requirement (the one serious threat):** in the MRDT model, merges are handed an
LCA, so deleted-element memory lives in the **version store**. Attiya's Ω(D) predicts the memory
must exist *somewhere*; the paper's real theorem is a **working-set separation**: reads and local
edits touch O(live) state; only merges touch the store, and only to LCA depth. State this
explicitly, quantify store retention, and note that Attiya's push-based class does not cover the
MRDT model (their §7 already says their proof strategy doesn't transfer to other models without a
"more delicate decoding argument"). A reviewer who catches the paper *implying* Ω(D) is escaped
outright will reject; a paper that *states the relocation* is making a novel and true claim.

## 4. Claim (iii) — "identity arbitrates, geometry renders"

**Claim:** merge-time ordering decisions must come only from immutable identity data; positional/
geometric data must be re-derivable rendering.

**Verdict: NEAR-MISS — the components are folklore or precedent; the crystallized law with a
machine-checked separation witness is new, but it should be framed as a design principle
*demonstrated*, not a discovery.**

Prior art fragments, each holding a piece:

- **Geometry alone cannot arbitrate (known).**
  [Figma's fractional indexing](https://www.figma.com/blog/realtime-editing-of-ordered-sequences/)
  interleaves concurrent runs and needs the server to resolve identical positions;
  [Wallace's own note](https://madebyevan.com/algos/crdt-fractional-indexing/) and the
  [PaPoC'19 anomalies paper](https://martin.kleppmann.com/papers/interleaving-papoc19.pdf) (Logoot/
  LSEQ) document the same deficit; the litmus suite's finding 3 (naive midpoint collisions) is
  Logoot's original design rationale rediscovered.
- **Identity as the spec-level arbiter (known).**
  [OpSets (Kleppmann et al. 2018, Isabelle-mechanized)](https://arxiv.org/abs/1805.04263) specifies
  list semantics from a totally ordered set of identified operations — arbitration-by-identity as
  *specification*. Fugue/position-strings make identity the *sort key itself* (eager paths); dead
  identity then lives inside every key forever.
- **When geometry is authoritative, re-rendering needs consensus (known, and the sharpest
  contrast).** Treedoc's flatten "requires a consistent state across all replicas and uses
  Paxos-Commit," with core/nebula machinery
  ([Asynchronous rebalancing of a replicated tree](http://renpar.irisa.fr/cfse8/cfse8_10.pdf)).
  The delta tree re-renders **at every merge, coordination-free**, precisely because arbitration
  was moved off geometry onto the ledger. This is the single best sentence of positioning for the
  principle: *reprojection without consensus is safe iff geometry has been demoted to a rendering.*
- **Identity durable, linear state derived (known in log form).** Eg-walker/Chronofold/Loro
  ([OpLog vs DocState](https://loro.dev/docs/concepts/event_graph_walker)) treat the event
  graph/causal tree as truth and the document as a derived cache — but the durable identity there
  is the *full history*, and there is no geometric read layer at all.

Delta: prior systems make exactly one representation authoritative (identity-keys, or the log).
The delta tree keeps **both layers live** — numeric fractions for geometric reads, a minimal
identity ledger for merge arbitration — and the claim is quantified: *one pointer per node is
enough identity* (v3 clean at 120/120, 300/300), *and any leak of arbitration into geometry is
fatal* (v1/v2 and the eight mutation-family variants, each with a machine-checked countermodel;
mechanisms named). The v2-vs-v3 separation witness is what elevates this above folklore. Framed as
a slogan alone it will draw "this is well known" from distributed-systems reviewers; framed as
*the two named mechanisms + the minimality datum*, it is defensible.

## 5. Claim (iv) — the anomaly battery + DAG PBT harness

**Claim:** ~25 provenance-carrying litmus tests + a randomized version-DAG PBT harness checking
global pairwise display stability, run over 16 designs.

**Verdict: NEAR-MISS as methodology (several precedents in adjacent forms), NEW as an artifact —
no published executable anomaly corpus for sequence RDTs exists, and no prior harness checks
global pairwise display stability at all.**

- **OT puzzle tradition (nearest ancestor in spirit).** The dOPT and TP2/false-tie puzzles drove OT
  research for a decade but were never consolidated into an executable battery;
  [Imine et al. 2003](https://inria.hal.science/inria-00071213) used the SPIKE prover to find
  counterexamples in all published transformation functions but one — machine-found anomalies,
  design-by-refutation, same genre.
- **[VeriFx (ECOOP'23)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.9/LIPIcs.ECOOP.2023.9.pdf):**
  51 CRDTs auto-verified with SMT counterexamples — but the properties are convergence/commutation,
  not a display-stability ladder; no sequence-anomaly corpus.
- **[MET (arXiv 2204.14129](https://arxiv.org/abs/2204.14129) /
  [JSEP 2024)](https://onlinelibrary.wiley.com/doi/abs/10.1002/smr.2555):** TLA+ model checking +
  trace-driven testing of replicated lists in CRDT-Redis; found real list-CRDT bugs. Closest
  published "systematic exploration finds sequence bugs" work; still convergence-oriented and
  single-implementation.
- **[Fugue's Table 1](https://arxiv.org/abs/2305.00583)** is the nearest published *designs ×
  anomalies matrix* (~10 algorithms × interleaving variants, by hand); PaPoC'19's figures are its
  ancestor. The litmus matrix generalizes this to ~25 anomalies × 16 designs, executable.
- **Engineering fuzzers** (Yjs/Automerge/diamond-types/Loro test suites; Peritext's randomized
  convergence PBT) check convergence, not stability;
  [Gentle's editing-traces](https://github.com/josephg/egwalker-paper) are performance benchmarks.
  [Jepsen/Elle's list-append](https://github.com/jepsen-io/elle) is precedent for named-anomaly
  checkers, in the transactional model.
- **The genuinely new checks:** (1) **global pairwise display stability (FLIP)** across every read
  of every replica in a random LCA-disciplined version DAG — no prior harness checks any form of
  display stability; (2) **topology convergence (CONV)** — same event set via different merge
  topologies ⟹ same read, which is what caught `rose` and `range-repro` and which op-based fuzzers
  cannot even express (they have no merge topology); (3) provenance discipline — each test cites
  the refutation or mechanized artifact it came from.

Recommendation: this is the paper's evaluation section and public artifact, not a headline claim.
As a standalone, it is a solid PaPoC/artifact-track contribution ("a litmus suite for sequence
RDTs"), and its two suite-gap stories (L17 found by proof attempt, not testing; L19 retraction)
make an honest and unusual methodology narrative.

## 6. Recommended framing and venue

**Sharpest headline (in order):**

1. **The compaction theorem (claim ii)** — *"The tombstoned RGA admits a strictly-live compaction
   in the three-way-merge model: one immutable birth-parent pointer per live element preserves
   every read, mechanized in Lean."* Crisp, checkable, unclaimed by anyone, and it converts the
   design from "yet another sequence CRDT" into a statement **about** the best-studied sequence
   CRDT. The Lean theorem `read_v3 = read_RGA†` is the deliverable that makes this citable.
2. **The triangle (claim i)** as the conceptual result: conjecture + 8 machine-checked
   countermodels + the two named mechanisms, positioned explicitly against Attiya Ω(D) (asymptotic,
   push-based) with the working-state/version-store relocation stated in the open.
3. **Identity-arbitrates-geometry-renders (claim iii)** as the design story that explains both 1
   and 2 (with the Treedoc-flatten consensus contrast as the framing device).
4. **The battery (claim iv)** as methodology + artifact.

**Venue:**

- **PL/verification venue (OOPSLA / PLDI / ECOOP / CPP for the mechanization):** the strongest fit
  *iff* the Lean equivalence theorem lands. The paper then slots into an established, refereed
  lineage — [Gomes et al. OOPSLA'17](https://arxiv.org/abs/1707.01747) (Isabelle RGA),
  [OpSets](https://arxiv.org/abs/1805.04263), [Nagar & Jagannathan CAV'19](https://arxiv.org/abs/1905.05684),
  [Liu et al. OOPSLA'20](https://dl.acm.org/doi/10.1145/3428284),
  [Peepul PLDI'22](https://dl.acm.org/doi/10.1145/3519939.3523735),
  [RA-lin OOPSLA'25](https://dl.acm.org/doi/10.1145/3720452) — and is the **first verified
  sequence MRDT with sequence-CRDT-grade ordering guarantees** (the MRDT line has none; the
  verified-CRDT line has never verified a tombstone-free sequence). This positioning is unique to
  this artifact and no competitor is close.
- **Distributed-systems venue (PaPoC as workshop-first; PODC/DISC if the triangle gets a proof;
  EuroSys only with a systems evaluation):** the triangle + battery play best here, but Eg-walker
  sets a brutal empirical bar at EuroSys, and without either a proof of the triangle or a
  performance story, a systems PC will read the paper as a design note. PaPoC (co-located with
  EuroSys) is the natural first outlet for the triangle-and-battery half while the Lean half
  matures.
- **The three-way-merge angle has an extra audience:** version control /
  [patch-theory](https://arxiv.org/abs/1311.3903) /
  [diff3](https://link.springer.com/chapter/10.1007/978-3-540-77050-3_40) people. diff3 is
  three-way sequence merge *without* identity — unstable and conflict-prone exactly where the
  delta tree is stable; a paragraph drawing that line (diff3 : delta-tree :: geometry-arbitrated :
  identity-arbitrated) situates the work for PL reviewers who know merges but not CRDTs.

## 7. Reviewer-risk checklist (defuse in the paper, not in rebuttal)

1. **"Eg-walker already has a tombstone-free document."** Answer in §3 terms: full event graph on
   disk forever + transient tombstones at every merge vs O(live) ledger, never any tombstone;
   informal proof vs mechanization. Do the memory comparison honestly (their steady-state RAM is
   also just the text).
2. **"Your tombstones are hiding in the LCA store."** Concede and quantify — the claim is the
   working-set separation, plus Attiya's model gap. Never write "escapes the Ω(D) bound."
3. **"Logoot is a dead-free stable convergent counterexample to the triangle."** Pre-empt with the
   strict definition (dead uids inside live keys count as retention) and the L7/L19 interleaving
   failures.
4. **"The triangle is a conjecture, not a theorem."** Scope the abstract's wording; the 8
   countermodels license "we conjecture, with machine-checked evidence on every mutation we or our
   reviewers proposed," nothing stronger.
5. **"Delta tree" name collision** with delta-state CRDTs
   ([Almeida/Shoker/Baquero](https://repositorio.inesctec.pt/server/api/core/bitstreams/7e87bf63-1250-409c-a416-7a29f70718ea/content))
   — in a CRDT paper the word "delta" is taken; rename before submission (e.g., *ledger tree*,
   *fold tree*, or keep "isometric fold" as the branded term).
6. **420 lockstep executions ≠ equivalence.** Until the Lean theorem is closed, phrase claim (ii)
   as "machine-checked on N executions, mechanization in progress" — the VC-trap memory applies:
   the theorem is only as strong as the statement actually proved.
7. **One-sided L19 residue.** v3 inherits RGA's backward-interleaving; FugueMax exists precisely to
   remove it. Say so, and note the equivalence theorem *explains* the residue (v3 ≡ RGA, anomalies
   included) rather than apologizing for it.

## Sources

Primary papers: [RGA (Roh et al., JPDC 2011)](http://csl.skku.edu/papers/jpdc11.pdf) ·
[Attiya et al., PODC 2016](https://software.imdea.org/~gotsman/papers/editing-podc16.pdf) ([ACM](https://dl.acm.org/doi/10.1145/2933057.2933090)) ·
[Kleppmann et al., PaPoC 2019](https://martin.kleppmann.com/papers/interleaving-papoc19.pdf) ·
[Fugue (Weidner & Kleppmann)](https://arxiv.org/abs/2305.00583) ·
[Eg-walker (Gentle & Kleppmann, EuroSys 2025)](https://arxiv.org/abs/2409.14252) ([HTML](https://arxiv.org/html/2409.14252v1), [repo](https://github.com/josephg/egwalker-paper)) ·
[Chronofold](https://arxiv.org/abs/2002.09511) ·
[Treedoc](https://arxiv.org/pdf/0907.0929) · [Treedoc rebalancing](http://renpar.irisa.fr/cfse8/cfse8_10.pdf) ·
[RGASplit (GROUP 2016)](https://pages.lip6.fr/Marc.Shapiro/papers/rgasplit-group2016-11.pdf) ·
[LogootSplit (CollaborateCom 2013)](https://members.loria.fr/CIgnat/files/pdf/AndreCollabCom13.pdf) ·
[Peritext (CSCW 2022)](https://www.inkandswitch.com/peritext/) ·
[Pure op-based CRDTs / causal stability](https://arxiv.org/abs/1710.04469) ·
[From causality to stability (MPLR 2020)](https://soft.vub.ac.be/~jibauwen/publications/mplr20-from-causality-to-stability-jimbauwens.pdf) ·
[OpSets](https://arxiv.org/abs/1805.04263) ([AFP](https://www.isa-afp.org/entries/OpSets.html)) ·
[Gomes et al., OOPSLA 2017](https://arxiv.org/abs/1707.01747) ·
[Nagar & Jagannathan, CAV 2019](https://arxiv.org/abs/1905.05684) ·
[Liu et al., OOPSLA 2020](https://dl.acm.org/doi/10.1145/3428284) ·
[Kaki et al., OOPSLA 2019](https://dl.acm.org/doi/10.1145/3360580) ([PDF](https://gowthamk.github.io/docs/mrdt.pdf)) ·
[Peepul (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523735) ([arXiv](https://arxiv.org/abs/2203.14518)) ·
[RA-linearizability (OOPSLA 2025)](https://dl.acm.org/doi/10.1145/3720452) ([arXiv](https://arxiv.org/abs/2502.19967)) ·
[VeriFx (ECOOP 2023)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.9/LIPIcs.ECOOP.2023.9.pdf) ·
[MET](https://arxiv.org/abs/2204.14129) ([JSEP 2024](https://onlinelibrary.wiley.com/doi/abs/10.1002/smr.2555)) ·
[Imine et al., 2003](https://inria.hal.science/inria-00071213) ·
[A categorical theory of patches](https://arxiv.org/abs/1311.3903) ·
[A formal investigation of diff3 (FSTTCS 2007)](https://link.springer.com/chapter/10.1007/978-3-540-77050-3_40).
Systems & blogs: [Figma ordered sequences](https://www.figma.com/blog/realtime-editing-of-ordered-sequences/) ·
[Wallace, CRDT fractional indexing](https://madebyevan.com/algos/crdt-fractional-indexing/) ·
[Weidner, position-strings](https://mattweidner.com/2023/04/13/position-strings.html) ·
[Weidner, list-positions](https://mattweidner.com/2024/04/29/list-positions.html) ·
[Weidner, text without CRDTs (2025)](https://mattweidner.com/2025/05/21/text-without-crdts.html) ·
[Yjs INTERNALS](https://github.com/yjs/yjs/blob/main/INTERNALS.md) ·
[Jahns, are CRDTs suitable for shared editing](https://blog.kevinjahns.de/are-crdts-suitable-for-shared-editing) ·
[Loro Eg-walker docs](https://loro.dev/docs/concepts/event_graph_walker) ·
[Loro rich text](https://loro.dev/blog/loro-richtext).
