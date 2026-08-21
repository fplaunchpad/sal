# Ideas in flight

Research threads on top of the verified Sal suite. The README documents what's done; this is the hallway-track tour of what's interesting.

## 1. Op-based ⇒ state-based transfer (Emulation)

We've verified 28 state-based RDTs against the 24 RA-linearizability VCs. Useful, but state-based isn't the only model people care about — many systems are op-based (think: replicas exchange operations, not states). Liittschwager et al. (ICFP'25) showed that every state-based CRDT has a canonical op-based emulation, and weak simulation transfers RA-linearizability across the two.

The plan is to mechanize that transfer in Lean. If it lands, we get RA-linearizability for *every* op-based CRDT in our suite for free, just by composing two existing proofs (Sal's bottom-up linearization + Liittschwager's emulation simulation).

**Where we are**: bridge proof (24 VCs ⇒ RA-linearizable in the state-based world) is mostly done — Apply case fully proved, Merge case at PARTIAL. Transfer machinery (weak simulation, weak trace properties) is scaffolded. Big remaining piece: the simulation proof for the canonical emulation 𝒢. Estimated 3–5 months focused.

`Sal/Emulation/` has the code. `Sal/Emulation/PLAN.md` is the live status doc.

## 2. Tree-as-primary RGA — and what it taught us about Sal

The bigger result this thread surfaced is **a framework limitation we didn't know we had**.

Every Sal RDT to date has flat-set state — sets, maps, registers. Operations are *totally defined*: Add adds, Rem removes, Set sets, regardless of the input state. Existing RGA itself is flat-set: records + tombstones, and `Add_after p` doesn't even check whether `p` is in the records, just stores the record.

We tried building RGA with a literal `inductive RGATree` instead. Same operation surface, but state is a tree of currently-live elements; `Remove` physically excises and re-parents children. Should work, right?

Three concrete failure modes against Sal's 24 VCs popped out:

**Failure 1: `cond_comm_base` fails on `(Add p, Remove p, Add p)`.**
On a state where `p` is alive:

```
LHS: σ → Add p ts1 → Remove p → Add p ts3
     root[p] → root[p[ts1]] → root[ts1] (re-parented) → root[ts1] (no-op)

RHS: σ → Remove p → Add p ts1 → Add p ts3
     root[p] → root[] → root[] → root[]
```

LHS keeps ts1; RHS doesn't. The VC requires LHS = RHS. The bug is that physical excise *destroys* the parent pointer information that flat-set RGA preserves via still-stored records + tombstones. The third op, supposed to "normalize" the asymmetry, no-ops in both orderings — it can't bridge the gap.

We tried two fixes:
- **Path-augmented ops**: each op carries the full ancestor path. Add walks the path on missing target, attaches at deepest live ancestor. Add and Remove now commute pointwise. `cond_comm_base` becomes vacuous (rc = Either everywhere).

**Failure 2 (path variant): `rc_non_comm` fails on Add-chain.** Two Adds where one's `ts` appears in the other's `path`:

```
s = root[]
op1 = Add path=[0] e1 ts1
op2 = Add path=[0, ts1] e2 ts2

LHS: ts1 added → ts2 attaches under ts1 → root[ts1[ts2]]
RHS: ts2 attaches at root (ts1 absent) → ts1 added → root[ts1, ts2] (siblings)
```

Different structural results. Path-aware `do_` makes ops state-dependent; commutation breaks on syntactically-constructible-but-causally-impossible states.

**Failure 3: `merge_idem` is *literally false* on a malformed state.** Aristotle (running on the merge proofs) found a counterexample: `s = .node 0 0 [.node 1 0 [.node 0 0 []]]`. The merge's DFS loops on duplicate ts and produces a tree larger than the input. Adding `no_dup_ts s` as a hypothesis makes it provable. Same for `merge_comm` needing `consistent_elems a b`.

Aristotle on the path variant found two more lemmas that were **outright false** without preconditions: `add_add_comm` (false when one Add's ts equals another's target) and `add_remove_diff_comm` (same root cause).

### What the failures point at

The 24 VCs all quantify universally over `s : concrete_st`. For flat-set MRDTs this is fine because every op is meaningful on every state. For structural state, "meaningful" requires preconditions: target alive, paths valid, timestamps fresh. The framework can't currently express that.

The clean fix is an **applicability-conditioned `commutes_with`** plus a re-derivation of soundness. Sketch:

```lean
def applicable (o : op_t) (s : concrete_st) : Prop  -- per-MRDT
def commutes_with (o1 o2 : op_t) :=
  ∀ s, applicable o1 s → applicable o2 s →
       applicable o2 (do_ s o1) → applicable o1 (do_ s o2) →
       do_ (do_ s o1) o2 = do_ (do_ s o2) o1
```

For flat-set MRDTs, `applicable o s = True` and the framework reduces to today's. For structural state, the applicability hypothesis excludes the syntactic-but-not-real states that break the VCs. Soundness still goes through because reachable states (which the framework's induction operates over) always satisfy applicability.

This would be a Sal-paper-level contribution.

### The pragmatic correctness path

Rather than wait for the framework refinement, we can prove tree-RGA correct *observationally*: show its visible behavior (DFS pre-order of the tree) equals flat-set RGA's read-side projection on every causally-consistent op history. Flat-set RGA is already proven RA-linearizable, so observational equivalence transfers RA-linearizability.

`Sal/MRDTs/RGA_Tree/RGA_Tree_Refinement.lean` is the proof. **Aristotle closed `read_side_equiv` end-to-end across three rounds** — kernel-checked, no sorryAx, only `propext` / `Classical.choice` / `Quot.sound` in the axiom trail. The only remaining sorry is `visible_apply_merge` (the multi-replica DAG case, deferred).

The win came in three submissions:
- Round 1: filter lemmas + Remove case (3/6 sorries).
- Round 2: corrected `visible_apply_add` for flat trees + `read_side_equiv` modulo `read_side_equiv_aux` (now 5/6).
- Round 3: closed `read_side_equiv_aux` and the headline (6/6 except merge).

Aristotle also discovered that **`visible_apply_add` and `read_side_equiv` were FALSE as stated** — even the observational equivalence theorem needs preconditions:

- **Orphan-tombstone counterexample**: `[Add(3,0,1), Remove(5), Add(5,0,2)]`. Remove(5) on a state without 5 creates a tombstone in set-RGA but no-ops on tree-RGA. The subsequent Add(5,0,2) then sees different things on each side. Tree gives `[(5,2),(3,1)]`; set gives `[(3,1)]`.

- **Sort-invariant breakage**: `[Add(10,0,1), Add(5,0,2), Add(11,5,3), Add(3,0,4), Remove(5), Add(8,0,5)]`. `remove_at` splices the removed node's children into the parent's child list, breaking the ts-desc invariant that `insert_sorted` assumes for the next Add.

Both are fixed by adding `removes_valid` (every Remove targets a previously-added ts) and `unique_ts` preconditions to the headline theorem. With those, `visible_apply_add` is closed for the flat case (`p = 0`, leaves-only); `read_side_equiv` is closed modulo a mechanical-bookkeeping aux lemma.

The story isn't "tree-RGA is wrong"; it's "the observational equivalence has the same structural-state preconditions that the 24 VCs need." Same root cause, different surface.

Aristotle also discovered the `remove_drops_target` theorem in the read-side was *wrong as stated* (commented out with explanation).

`Sal/MRDTs/RGA_Tree_Path/RGA_Tree_Path_MRDT.lean` is a parallel design point — path-aware `do_` + applicability-restricted `commutes_with`. Aristotle closed 7 sorries on this one and surfaced the false-lemma findings above.

### Where the experimental empirical evidence sits

Both variants pass extensive `#eval` property tests: commutativity (3+3), idempotence (3+4), 3-branch confluence with all pair-orderings (2+3), multi-level DAG confluence (1+2). Tested on dozens of concrete trees. Operationally correct on every case we've tried. The verification gap is at the *framework* level, not the design level.

### One-line summary

**Tree-as-primary RGA is operationally fine, but the 24-VC framework needs an applicability hypothesis to verify state-aware ops on structurally-typed state.** That's the publishable observation. The proof-engineering of refinement-to-flat-set-RGA is the corollary correctness argument — the headline `read_side_equiv` theorem is mechanized and kernel-checked, modulo the multi-replica merge case.

### Caveat on the proof's scope

`read_side_equiv` is proven for **linear histories** where Adds target only the root (`p = 0`) — flat trees. The `causal_consistent` predicate as currently defined enforces this restriction. To extend to deep trees, three pieces:
- Tighten `causal_consistent` to walk the prefix maintaining the running alive-set (currently it checks only the initial alive set).
- Generalize `visible_apply_add` from `p = 0` to general `p` (the structural induction relating tree's `find_subtree p ; insert_sorted` to set's `setRGA_children p ; mergeSort` at arbitrary depths).
- Close `visible_apply_merge` for the multi-replica merge case.

All three are well-scoped Aristotle prompts. Empirical evidence (12+10 property tests on deep trees and multi-level DAG merges) suggests they all hold; the formal proof for the constrained case demonstrates the technique works.

## 3. Mechanise the soundness meta-theorem (24 VCs ⇒ RA-linearizability) — **landed**

Landed, with a twist: the mechanization found the paper's proof **unsound as written**
(sub-history convergence is false; a reachable defeater blocks every bottom-up peel) and
several of its merge VCs false in principle for LCA-sensitive data types. The corrected
chains are end-to-end and kernel-checked, 0 sorries: `CoreVCs + JoinPeelVCs ⇒ RA-lin` and
the CD ladder in the binary world (`Sal/CRDTs/Metatheory/`), and the eight-VC delta contract
over the version DAG in the ternary world (`Sal/MRDTs/Metatheory/`), with **9 of the 12
production MRDTs discharged end-to-end**. The README documents the results; the two
paper-style notes in `docs/metatheory-note/` tell the story.

What survives of this thread as open research is exactly the conditioning question it
flagged: a **feasible update layer** (update VCs conditioned on a reachability invariant,
plus a transport lemma along canonical enumerations) — needed to host the path-carrying
tombstone-free RGA, whose commutation VCs only hold on well-formed states. That is Open
Question 4 of the MRDT note; `ROADMAP.md` has the entry points. Thread 1's transfer can now
build on a kernel-checked state-based foundation instead of a paper step.

## 4. Demote the absorber clause: a declarative spec for RA-linearizability

The linearization order's conflict disjunct carries an absorber exception: a concurrent
`rc`-ordered pair is *not* ordered when the winner is already overwritten by a later
non-commuting event of the set being linearized (Definition 2.1 of
`docs/metatheory-note/mrdt-metatheory-note.pdf`; `loOn` at
`Sal/CRDTs/Metatheory/Merge_Linearization_Set.lean:159`). The clause has always felt
strapped-on, and the feeling has a precise source: it is an **operational condition inside a
declarative spec** — a syntactic proxy ("∃ later non-commuting e₃") for the semantic
statement actually wanted ("the ordering of this pair is observationally irrelevant in every
continuation"). Two tells confirm it is proof-calibrated rather than semantics-first: it is
asymmetric (only the *winner's* absorbers cancel — exactly the swaps the convergence
induction needs), and it is anti-monotone in the event set (growing the history retracts
edges) — which is what made the paper's configuration-wide reading unsound and forced the
whole set-relativity repair.

It is not decorative. Drop it and RA-linearizability is *false* for the paper's flagship
example: in the defeater's merged version the uncancelled demands form a cycle

```
A_p —vis→ R_p —rc→ A_q —vis→ R_q —rc→ A_p
```

so no witness exists at all, while the actual merged state is perfectly sensible. The clause
implements "arbitrate live conflicts, ignore dead ones."

Why does it work beyond the OR-set? Only because **cond-comm is a per-data-type obligation
that certifies the proxy**: `cond_comm_lift` (`Merge_Linearization_Set.lean:102`; the paper's
`cond_comm_base`/`cond_comm_ind` in `App_mrdt.fsti:72,77`) says precisely that an rc-ordered
pair followed by an absorber can be swapped deep in any fold without any later non-commuting
event noticing. The pairing is a single lemma — `applySeq_swap_loOn_incomparable`
(`Merge_Linearization_Set.lean:471`) destructs "the lo-edge was cancelled" into exactly
cond-comm's premises. The definition and the VC are co-designed: the clause deletes exactly
the edges cond-comm licenses the induction to swap.

**The research question.** Reformulate the spec declaratively, in the Burckhardt-style
`(vis, ar)` tradition (POPL'14): a version linearizes iff its state is the fold of *some
total arbitration extending `rc` on surviving conflicts* — unobservable disputes become a
**quotient**, not a conjunct. Then prove: for cond-comm data types, the declarative spec is
*equivalent* to the current `lo^E` definition. That would demote the absorber clause from
definition to lemma — the add/remove family's particular realization of a clean principle —
and it would say exactly what replaces it for data types the current shape cannot express:
**joint absorption**, where a disagreement is erased by several events together with no
single `e₃` (cond-comm's premise can't even state this). Empirical footnote that sharpens
the question: across the entire discharged production catalogue, the `rc`/absorber machinery
is only ever *engaged* by add/remove-shaped conflicts — everything else is all-commuting, so
the clause is vacuous. Its generality beyond that family is untested.

**Shape of the work.** The equivalence proof sits naturally next to the convergence theorem
(`Sigma_LoOn3.lean` / `Merge_Linearization_Set.lean`): declarative ⇒ current is a linear-
extension argument; current ⇒ declarative consumes cond-comm once, at the same spot the
bubble lemma does. A counterexample data type for the joint-absorption gap (if one exists)
would be a publishable observation on its own; if none exists, that is a structure theorem
about single-event overwrite being canonical. Reviewers of the metatheory note will ask this
question; better to have the answer first.

## 5. Criss-cross merges: the model gates what git recurses

`Step3`'s Merge rule is gated on `IsLCA` (`Sal/MRDTs/Metatheory/ExecutionModel.lean:67`) — a
common ancestor *dominating every common ancestor*. Criss-cross configurations are reachable
and every version in them linearizes, but the criss-crossed heads themselves cannot merge:
the premise is unsatisfiable, so the transition doesn't exist. Inherited from the paper's
main development — and it is exactly the spot where git switches to its *recursive* strategy
(merge the maximal common ancestors into a virtual base, then merge with that). Real
replication hits criss-cross constantly, so this is the one visible gap between the model
and practice.

The metatheory looks ready for the extension: the ternary Join Lemma is stated over
backward-closed **event sets** — `σ(E₁ ∪ E₂) = mergeL(σ(E₁ ∩ E₂), σ(E₁), σ(E₂))` — and
`E₁ ∩ E₂` needs no witnessing store version. So the work reduces to (a) a virtual-LCA Merge
rule, and (b) one per-data-type question: **do the eight VCs imply the recursively computed
base equals `σ(E₁ ∩ E₂)`?** For the counter it's inclusion–exclusion once more — exact iff
the maximal common ancestors jointly cover the intersection, itself a candidate store
invariant to prove (or refute) under `StoreInv`. For the OR-set, a pointwise Boolean check.
Open Question 6 of the MRDT note. A natural first experiment: mechanize the criss-cross
counterexample, state the covering invariant, and test it against `Step3` reachability.

## 6. Conditioning is conserved: intent capstones for the flat catalogue (tombstoned RGA first)

*(2026-07-12.)* The tombstoned RGA discharges **flat** (`Inv = applicable = ⊤`,
unconditional-delta route) — sound for RA-linearizability, but under-specified for
*intent*: the headline theorem holds on executions containing an `Add_after a` whose
anchor `a` was never inserted. The record is stored, satisfies `visible`, and has no
`after_of` edge — the "list" is a partial order with a floating orphan, and RA-lin
doesn't care (the fold matches the state, orphan included). `do_` never inspects the
anchor (`RGA_MRDT.lean:98`); resolution is lazy, at read time, and heals on merge — by
design. But nothing *states* that reachable versions are orphan-free.

**The missing layer** (bounded-counter pattern: conditioning for safety, not
convergence): `Inv` = anchor-closure (every `after_id` is 0 or has a record) ∧
id-monotone anchors (`after_id < ts`, making `after_of` well-founded — the same clause
the tombstone-free RGA's `Inv` already carries) ∧ grave-closure (tombstones reference
records). `applicable` = anchor/target *visible* at the issuing state, ts fresh — the
client-checkable `GenHonest`/`AppHonest` shape. Payoff theorem, via
`version_inv_of_causal_canonical`: **at every reachable version, `visible_lt` is a
well-founded strict total order on visibles — the read is a genuine sequence.** The
datatype's name-promise as a reachability theorem, which RA-lin alone cannot state.
Nuance the framework already expresses: `applicable` holds at *generation* (anchor
visible to the issuer); at delivery only anchor-*presence* survives (concurrent
tombstoning) — and presence is all `Inv` needs.

**Why it's cheap, and why that's informative:** all three `Inv` clauses are monotone
and the merge is union, so `SafetyStep` at merges is set algebra — contrast the bounded
counter's non-monotone bound and escrow argument. Two datapoints suggest a
classification of safety obligations (monotone vs measured) and make the tombstoned RGA
the cheapest test that the `GenHonest`/`GenericSafety` abstractions generalize.

**What this says (the thesis):** conditioning has two independent jobs — rescuing
*convergence* and proving *intent* — and every sequence datatype pays it somewhere.
**Tombstone-freedom forces conditioning for convergence; tombstones only defer it to
intent.** Conditioning is conserved; a design only chooses where it bites. This is the
proof-theoretic shadow of the whiteboard trilemma
(`whiteboard/anomaly-matrix/anomaly_matrix_report.md`): where a design keeps its memory
of the dead determines where its proofs need hypotheses. The anomaly matrix measures
the trade behaviorally; the catalogue exhibits it proof-theoretically — two projections
of one fact. (Lemma V / Theorem O, `whiteboard/sibling-linked-proof.md` §5½, already
sit on this bridge: an intent-layer version invariant proved from the conditioned
hypothesis (M2).)

**Generalization:** an *intent column* for the whole catalogue — per MRDT, the
name-promise theorem as a version invariant (counter: bound ✓ done; tombstoned RGA:
total-sequence read, next and cheapest; queue, OR-set, Peritext render: to be named).
"Production catalogue complete" currently means RA-lin only; this is the second story
the same machinery can carry.

---

## How to use this file

This is the hallway-track summary. Detailed status lives in:
- `Sal/Emulation/PLAN.md` — Phase 1 plan with step-by-step status table.
- `Sal/MRDTs/RGA_Tree/PLAN.md` — Tree-RGA experiment status, proof attempts, Aristotle results.
- `Sal/MRDTs/RGA_Tree_Path/BLUEPRINT.md` — Layered hand-roll proof plan for the path variant.

When an experiment lands and merges into the main framework, move the summary to the README and remove from here.
