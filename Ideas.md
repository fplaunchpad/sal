# Ideas in flight

Two research threads on top of the verified Sal suite. The README documents what's done; this is the hallway-track tour of what's interesting.

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

## 3. Mechanise the soundness meta-theorem (24 VCs ⇒ RA-linearizability)

The 24 VCs are mechanised per RDT, but the meta-theorem that discharging them implies RA-linearizability lives only in the Neem paper. So no RDT in the suite has an end-to-end machine-checked linearizability guarantee; each rests on two legs: the mechanised VCs (Lean) and a pen-and-paper soundness proof. The idea is to mechanise that meta-theorem in Lean, giving a single kernel-checked chain from `do_` / `merge` / `rc` to RA-linearizability, with no paper step in the trust chain.

**Why now, concretely.** The path-carrying RGA (`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`) made the gap load-bearing. Its `rc_non_comm'` is the standard VC with commutation conditioned on `accurate` (op path = real ancestor chain) and `fresh_ts` (Ins id fresh, nonzero): a strictly weaker statement than Neem's unconditioned `commutes_with`. Whether the weaker VC still implies RA-linearizability cannot be settled from the mechanised VCs alone; it depends on whether the paper's soundness construction only ever invokes commutation at states where those conditions hold. A mechanised soundness turns that "probably fine" into a checked obligation. This is the same "applicability-conditioned `commutes_with` plus a re-derivation of soundness" flagged in thread 2; mechanising soundness is what makes that re-derivation rigorous instead of asserted.

**What it buys.**
- Every RDT in the suite gets a kernel-checked RA-linearizability theorem by composition (its mechanised VCs plus the mechanised meta-theorem).
- Conditioned VCs become first-class. The path-RGA `accurate` / `fresh_ts` premises and the structural-state `applicable` predicate from thread 2 can be admitted explicitly: the meta-theorem states which conditioning it tolerates, and a per-RDT reachability invariant (every reachable state satisfies the conditions) discharges the side condition. The concrete risk point to settle is `accurate` versus ancestry-change-under-delete: deletes rehome nodes, so an op's recorded path can go stale, and the proof must show commutation is only needed where paths are still accurate (or the design strengthened so they stay accurate).

**Shape of the work.** Formalise the RA-linearizability definition (a sequential order respecting visibility and `rc`, matching the abstract spec), the replicated execution model (version DAG, `do_` / `merge`), and the inductive construction that rewrites a concrete execution into linearized form using the 24 VCs. The induction runs over reachable states, which is exactly where the conditioning predicates hold, so it is also the natural place to discharge them. Source material: the Neem paper and `_references/RA-Linearizability`.

**Relationship to thread 1.** The emulation transfer assumes RA-linearizability in the state-based world and carries it to op-based. A mechanised state-based soundness gives that assumption a kernel-checked foundation, so the two compose into op-based RA-linearizability with no paper step anywhere.

---

## How to use this file

This is the hallway-track summary. Detailed status lives in:
- `Sal/Emulation/PLAN.md` — Phase 1 plan with step-by-step status table.
- `Sal/MRDTs/RGA_Tree/PLAN.md` — Tree-RGA experiment status, proof attempts, Aristotle results.
- `Sal/MRDTs/RGA_Tree_Path/BLUEPRINT.md` — Layered hand-roll proof plan for the path variant.

When an experiment lands and merges into the main framework, move the summary to the README and remove from here.
