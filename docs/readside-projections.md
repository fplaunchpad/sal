# Read-side projections: when and how

This is the methodology doc for the read-side layer in Sal. The
per-RDT crosswalks (`peritext-vs-paper.md`, `or-set-vs-paper.md`,
etc.) cite the rules; this file states them once.

## The "vacuous convergence" problem

Sal's 24 RA-linearizability VCs prove **state convergence**: two
replicas with the same set of observed ops reach the same `concrete_st`
under merge. For RDTs whose state is a flat lattice with semantically
direct read (e.g. counters, simple registers), state-convergence is
the entire correctness story.

For many interesting RDTs it is not. Consider OR-Set: its 24 VCs
prove that the underlying tag-set + tombstone-set converges under
union — but they say nothing about whether `e ∈ set` agrees on
two replicas under concurrent Add/Remove on `e`. The **headline
property** of OR-Set lives in the read-side projection, not in the
state-equivalence under merge.

The Sal paper proves convergence on 13 RDTs and stops. Read-side
projections are the methodological extension that lifts the
*semantic* claims of an RDT (lookup, query, peek-max, antichain,
visible-string, …) into Lean — orthogonal to the convergence
layer, but composing with it to give a complete correctness story.

## Why the 24 VCs already do more than CCI

The textbook state-based CRDT story — commutative, associative,
idempotent merge ("CCI") — is strictly weaker than what Sal's 24 VCs
prove, and it's worth being precise about the gap.

CCI isn't even sufficient for a counter. Take `Int` as state and
`max` as merge: CCI holds, but the structure isn't a counter. Two
concurrent `inc`s on `0` produce `max(1, 1) = 1` instead of `2`. The
lattice laws hold; the operation semantics is not modelled. To
recover a counter you need a per-replica vector, pointwise-max as
merge, and the invariant that `inc` bumps only the acting replica's
slot. CCI has no machinery to express any of that.

Sal's 24 VCs prove RA-linearizability: the merged state matches
*some* sequential application of the same ops under `rc`. This is
strictly stronger than CCI. The int+max "counter" *fails* the 24 VCs
— there is no rc-respecting linear order of `inc`s whose result
equals `max`. So the 24 VCs already rule out the kind of
pseudo-counter that CCI accepts, and that's why Tier A feels free:
the operation semantics is baked into the converged state, and the
read is just a direct projection.

The real Tier C gap, then, is not "CCI vs intent." It is that the
user-visible query is a *non-injective projection* of the state.
The 24 VCs prove `(adds, tombstones)` converges in an op-respecting
way; they say nothing about `e ∈ set`, because that predicate isn't
a state component — it is a function of one. Read-side theorems
are what re-attach the user's mental model to the projection.

| | Catches int+max-as-counter? | Captures op semantics? | Captures projected queries? |
|---|---|---|---|
| CCI lattice merge | no | no | no |
| Sal's 24 VCs (RA-lin) | yes | yes | only when read = state itself |
| 24 VCs + read-side | yes | yes | yes |

This trichotomy is the load-bearing reason the tier framework below
exists. Tier A/B sit in the middle row; Tier C needs the bottom row.

## The three tiers

The Sal suite separates RDTs by how much of their semantics the
24 VCs already cover.

### Tier A — read-side is mechanical (still written for documentation)

The 24 VCs cover everything; the read is essentially the identity
projection or a per-key direct lookup whose convergence follows
componentwise from state-convergence. The read-side and SPOT files
are still written — *absence of a read-side file would communicate
nothing about whether the read is trivial*; presence with a short
mechanical proof tells a reader "yes, this query exists, this is
its name and type, here's the convergence theorem (`rfl` or one
`rw`), and here are 2–3 SPOT scenarios pinning the headline op-vs-
read claim."

| RDT | Read |
|---|---|
| `PN_Counter` | per-replica `incs[r] − decs[r]` |
| `Increment_Only_Counter` | per-replica `state[r]` (CRDT) / scalar (MRDT) |
| `LWW_Register` | `value` field of the lex-max pair |
| `MIN_Register` / `MAX_Register` | the scalar state |
| `MAX_Map` | per-key `lookup` (zero-default) |
| `Grow_Only_Set` | `lookup e = mem e` |
| `Grow_Only_Multiset` | per-replica per-element `count_at` |
| `Grow_Only_Map` | per-key per-value `lookup k v = v ∈ state[k]` |
| `LWW_Map` | per-key `lookup k = state[k].value` |
| `Bounded_Counter` | per-replica `inc_count`, `dec_count`, `transfer_count` |
| `Shopping_Cart` | per-replica per-product `add_count`, `remove_count`, `per_replica_qty` |

**Rule of thumb**: if the read is a single arithmetic/lookup over
already-converged components, it's Tier A. Write it anyway — it
takes ~30–60 lines per RDT and pays back the next reader who has
to confirm the read-side really is "obvious."

### Tier B — read-side adds clarification, not structural verification

The 24 VCs imply state-convergence, and the read converges via a
short composition. The read-side adds documentation-quality
clarification (what is "the value" of an MVR? what is "the visible
set" of a flag?) but the underlying state is simple enough that the
clarification is essentially a definition.

| RDT | Read | Why Tier B |
|---|---|---|
| `Multi_Valued_Register` (paper / Neem F* simplified variant) | "all values ever written" | Grow-only set; sequential writes don't actually overwrite, so the read-side adds little beyond `lookup`. |
| `LWW_Element_Set` | `addTs[e] > remTs[e]` | Cross-component comparison adds a small fact not in the 24 VCs, but mechanically is just `>` on per-element max. |

Tier B is the boundary: you *can* write a read-side, the theorems
*are* honest, but the payoff is small. We do it anyway when the
RDT is well-known and the read-side helps a downstream consumer
make sense of the state shape.

### Tier C — read-side is essential

The 24 VCs prove union-commutativity on grow-only state, but the
*user-visible* semantics live in the read. Without a read-side,
you have proved that the data structure converges and *nothing
else*. These are the RDTs where the read-side is structurally
load-bearing.

| RDT | What the 24 VCs prove | What the read-side adds |
|---|---|---|
| `OR_Set` (CRDT, MRDT, Efficient MRDT) | tag-set + tombstone-set converge | "is `e` in the set?" via add-wins resolution; `add_wins_over_concurrent_remove`, `add_then_remove_extinguishes` |
| `Peritext` (CRDT, MRDT) | RGA chars + flat mark-attachment set converge | Visible-order DFS, span-membership via `in_span_visible`, paper Ex 1/2/3/5/7/8 intent theorems |
| `RGA` (CRDT, MRDT) | per-OpId chars/afters/deleted maps converge | Visible-order traversal `visible_lt`, causal-order preservation, deterministic concurrent-insert tiebreak |
| `Add_Win_Priority_Queue` (CRDT, MRDT) | (A, I, R) components converge | `lookup`, LWW innate, MCW-collapsed-to-Σ acquired, `get_max`, `inc_increases_acquired` |
| `Multi_Valued_Register` (classical, post-rewrite) | (writes, removed) converge | "concurrent writes both survive" + "sequential writes supersede" via snapshot |

For Tier C, the convergence proof is necessary but **not sufficient**.
The read-side is the proof that the converged state means what the
paper says it means.

## When is a new RDT Tier C?

Three signals, any of which strongly suggests Tier C:

1. **The user query is structurally non-trivial.** Visible string,
   peek-max, "is x in the set under add-wins", maximal antichain in
   a version DAG — anything that's not a single lookup or arithmetic
   composition.
2. **The state is "richer" than the read.** OR-Set carries every
   add-tag in history; users want to know membership. AW-CRPQ
   carries every add/inc record; users want a single priority. The
   gap between state and read is where the read-side does work.
3. **The op semantics involves observation.** `Rem` snapshots
   currently-visible tags. `inc` updates per-record counters. The
   prepare/effect split that produces grow-only state often hides
   the actual semantics in the snapshot mechanism — read-side
   theorems make it explicit.

Conversely: if the query is "extract the field" or "compute a
sum," it's Tier A. Don't add a read-side for completeness alone.

## The methodology, in three steps

For each Tier-C RDT (`docs/peritext-vs-paper.md` is the canonical
template; `or-set-vs-paper.md` is the closest minimal example):

### 1. Define the query

A `def` (often `noncomputable` because of `Classical.choose` over
the Bool-valued `set`) on `concrete_st`. Examples:

- `def lookup (s) (e) : Prop := ∃ ts, mem (e, ts) (Prod.fst s) ∧ ¬ mem (e, ts) (Prod.snd s)` (OR-Set)
- `def is_visible_value (s) (v) : Prop := ∃ ts, mem (ts, v) (Prod.fst s) ∧ ¬ mem ts (Prod.snd s)` (MVR classical)
- `def is_acquired (s) (e) (v) : Prop := ∃ l : List ..., l.Nodup ∧ ... ∧ v = (l.map _).sum` (AW-CRPQ acquired, list-witness style to sidestep `Finset`)

### 2. Prove convergence-at-the-read

**`eq s₁ s₂ → (query s₁ ↔ query s₂)`** (or `=` if the query is
function-valued and the underlying `eq` is Lean-equal).

This is the read-side analogue of merge convergence. Almost always
trivial: structural induction on the propositional `eq`, or `subst`
if the underlying `eq` is `=`. It is the *foundational* read-side
theorem that justifies talking about "the value" rather than "this
replica's value."

### 3. Prove 2–4 intent-preservation theorems

The headline claims of the paper, lifted as state-based predicates.
Recurring patterns:

- **`add_wins_over_concurrent_*`** — under premises modelling
  concurrency (the new tag is fresh in the common pre-state, OR the
  Rmv's snapshot doesn't include it), the Add survives the merge.
- **`*_then_*_extinguishes`** — under sequential premises, the
  later op overrides the earlier.
- **`*_after_*`** — applying a constructor op makes the
  characteristic predicate hold.
- **A few RDT-specific ones**: `causal_order_visible_lt` (RGA),
  `bold_expand_in_span_visible` (Peritext Ex 7), `innate_record_unique`
  (AW-CRPQ LWW), `latest_write_wins` (LWW-Element-Set).

Three to four intent theorems is usually enough; the paper's
headline claims are typically that few. The Peritext suite has more
because the paper has eight examples in §A.2.

## Step 4 (recommended) — concrete SPOTs

For each Tier-C RDT, alongside the universal read-side theorems we
keep a small **`*_SPOT.lean`** file (Small Proof-Oriented Tests):
concrete `do_`/`merge` traces over literal arguments, with the
expected read-side outcome pinned by proof. Each SPOT is named
after the headline read-side claim it exercises.

Two roles:

1. **Regression tests.** A predicate that is right on every input we
   could close universally can still go subtly wrong under a
   refactor — say, an `init_st` change or a payload-shape rework.
   SPOTs catch the breakage where it bites: on a specific 3-replica,
   4-op trace.
2. **Verified API documentation.** The same scenarios that a demo
   page or paper §X.Y example narrates, here pinned by Lean. A
   reader can trace `Add e at ts=1` then `concurrent Rem e` then
   `merge` and read off the verdict from the example, with the
   guarantee that Lean agrees.

Discharge style is one of:

- Apply the existing read-side theorem (`lookup_after_add init_st …`)
  with literal arguments — fastest, and shows the universal
  theorem firing on a specific instance.
- `refine ⟨witness, ?_, ?_⟩ <;> decide` — when the membership
  predicates `mem`/`contains` reduce on literals.
- `simp [do_, merge]; grind` — when the goal needs unfolding plus
  light arithmetic / case-splitting.

### Pitfalls (audit every SPOT for these)

These are the bugs we hit when first writing the Tier-C SPOT suite;
catch them at write-time, not at review.

**1. Match `rid`s to the paper's framing.** A read-side theorem
with a universal premise (`mark_present s m' → …`) admits witness
states with one or zero such ops — the universal becomes vacuous
and the theorem applies trivially. That's a *valid invocation* but
doesn't exercise the paper scenario.

For paper claims phrased as *"concurrent X from different
replicas"*, use distinct `rid`s on the relevant ops:
`(ts₁, 0, op₁); (ts₂, 1, op₂)`. Same `rid` is only for ops a
single replica issues sequentially. With `rc := Either` on these
RDTs, sequential `do_; do_` on different rids converges to the
same state as a literal merge of two divergent branches — that's
the standard state-based stand-in for "concurrent" used elsewhere
in Sal (see e.g. `OR_Set` CRDT's `add_wins_over_concurrent_remove`).

**2. Don't degenerate the scenario.** "Two overlapping same-type
Adds" needs *two* AddMarks of the same type with truly overlapping
spans — exhibit the overlap point as the witness `c`. "Add wins
over concurrent Remove" needs both an AddMark and a RemoveMark in
the state. If your SPOT compiles with one Add and zero Removes,
re-read the theorem name: you're probably missing structure.

**3. Inline structured-type literals.** `let m : MarkOp := ⟨…⟩`
in a tactic block blocks projection reduction (`m.startSide`,
`m.markType`) inside `simp`. Pass the literal anonymous-constructor
or tuple directly to the theorem and to every reduction call.
This bit us on Peritext SPOTs 7–9 — once the literal is inlined,
`simp` unfolds the projections and the proof goes through.

**4. Use the read-side query in the conclusion, not raw membership.**
A read-side theorem's job is to lift a paper claim into the
projected vocabulary (`is_visible_value`, `lookup`, `formatted_visible`,
…). If your theorem concludes `mem ts (Prod.snd (do_ s …)) = true`
and the docstring says "v₁ is no longer visible," it's actually
proving a *building-block* fact, not the headline. The two are
different: `ts ∈ removed` invalidates *the specific* `(ts, v₁)`
witness; `¬ is_visible_value (do_ s …) v₁` says no witness for
`v₁` survives. The latter requires extra premises (typically a
coverage premise like *"every visible witness for `v₁` in `s` has
ts ∈ O₂"* and an inequality like `v₂ ≠ v₁`) but it is the actual
paper claim.

Pattern: keep both. Name the witness-level lemma
`<theorem>_witness` (the building block), and the value-level
theorem `<theorem>_value` (the headline, in projection
vocabulary). The MVR pair `sequential_write_supersedes_witness` /
`sequential_write_supersedes_value` is the canonical example —
the witness version drops out of `simp [do_]` in two lines, the
value version takes a coverage premise and a value-inequality
premise and concludes `¬ is_visible_value …`.

If a SPOT proof has to do raw `rintro/simp/grind` to close the
negative half of a "v is no longer visible" claim, that's a sign
the read-side theorem is missing — write the value-level one.

**5. The `mark_present`-uniqueness pattern.** Read-side premises
of the form `∀ m', mark_present σ m' = true → P m'` reduce, on a
concrete state with 1–2 AddMarks, to "any present `m'` equals one
of the constructed marks". Discharge:

```lean
have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
    m' = literal₁ ∨ m' = literal₂ ∨ … := by
  intro m' h_pres
  simp [hσ, ..., mark_present, marks_of, do_, add,
        _root_.singleton, union, empty] at h_pres
  rcases m' with ⟨_, _, _, _, _, _, _⟩
  grind
```

The `rcases m'` *before* `grind` is the trick — destructuring the
structured type into fields lets `grind` collapse the
AnchorAttachment-injectivity disjunction componentwise. Without
the `rcases`, `grind` stalls on a 6-way Prop disjunction with
projection-blocked equalities.

### Concurrency encoding — two equivalent conventions

Both the readside theorems and the SPOTs use one of two conventions
for representing "concurrent":

- **Literal merge** (used by OR-Set, RGA, MVR, AW-CRPQ readsides):
  the theorem's statement contains `merge (do_ s o₁) (do_ s o₂)` (or
  `merge l (do_ l o₁) (do_ l o₂)` for MRDT) with `rid₁`, `rid₂`
  universal. The "concurrent" shape is in the theorem's form.
- **Abstract state** (used by Peritext readside): the theorem takes
  any state `s` with the relevant ops' effects already present (e.g.
  `mark_present s addOp = true ∧ mark_present s remOp = true`).
  Concurrency is implicit — such a state arises by concurrent
  application from different replicas.

Both styles are paper-faithful at the readside level. The SPOT layer
is where the concurrent shape becomes concrete: in the literal
convention by literal `merge`, and in the abstract convention by
`do_; do_` with distinct rids. Either way, the rid distinction is
how the *reader* recognises the SPOT as exercising the concurrent
case.

The Sal SPOT files live next to their read-sides:

| RDT | SPOT file |
|---|---|
| OR-Set CRDT | `Sal/CRDTs/OR_Set/OR_Set_SPOT.lean` |
| OR-Set MRDT | `Sal/MRDTs/OR_Set/OR_Set_SPOT.lean` |
| OR-Set Efficient MRDT | `Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_SPOT.lean` |
| MVR CRDT / MRDT | `Sal/{C,M}RDTs/Multi_Valued_Register/Multi_Valued_Register_SPOT.lean` |
| RGA CRDT | `Sal/CRDTs/RGA_with_tombstones/RGA_SPOT.lean` |
| RGA MRDT | `Sal/MRDTs/RGA_with_tombstones/RGA_SPOT.lean` |
| AW-CRPQ CRDT / MRDT | `Sal/{C,M}RDTs/Add_Win_Priority_Queue/Add_Win_Priority_Queue_SPOT.lean` |
| Peritext CRDT / MRDT | `Sal/{C,M}RDTs/Peritext/Peritext_SPOT.lean` |

## The snapshot-in-op-payload pattern

A recurring trick when porting an op-based CRDT whose `effect`
function reads state. The classical examples:

- **OR-Set's `Rem(e)`** — at prepare time, snapshots
  `{(e, ts) ∈ adds}`; at effect time, `tombstones := tombstones ∪ snapshot`.
- **AW-CRPQ's `Rmv(e)`** — at prepare time, snapshots
  `{(e, ts) ∈ A ∧ (e, ts) ∉ R}`; at effect time, `R := R ∪ snapshot`.
- **MVR (classical) `Write(v)`** — at prepare time, snapshots all
  currently-visible ts values; at effect time, `removed := removed ∪ snapshot, writes := writes ∪ {(ts, v)}`.

The pattern keeps `rc := Either` everywhere by making `do_` a pure
pointwise-OR on grow-only components, regardless of the op's
payload. Concurrent ops have disjoint snapshots; sequential ops
each include the prior in their snapshot. Convergence is trivial
(union of grow-only sets); the headline semantics emerges in the
read-side via the visible / not-tombstoned check.

When you see "this op needs to read state" in the paper's algorithm,
this pattern is almost always how to keep it state-based.

## Spec validation — the `in_span_boundary` cautionary tale

The first read-side predicate Claude wrote for Peritext was
`in_span_boundary`. It looked plausible from a surface reading of
§3.3. About 400 lines of theorems went through against it before KC
caught the bug: the predicate's `after_of c endId → endSide` clause
encoded the *opposite* of what §3.3 specifies.

The proofs were correct. The predicate was wrong.

This is the verification analogue of "your tests pass but the code
is wrong." More proofs don't help; **spec validation** is a
separate activity. Two complementary tools:

- **Statelet model checking (SMC)**: enumerate short executions
  (3 replicas, 4 ops). For each resulting state, check whether the
  read-side predicate agrees with a reference implementation
  (e.g. for Peritext, the TypeScript reference from the paper's
  artefact). Fast, no universal claim, catches predicate-vs-paper
  drift in minutes.
- **Reference implementation cross-check**: even without SMC, run
  the predicate by hand on the paper's small examples (Peritext §A.2,
  OR-Set §3.3.5 Spec 14, etc.) and check the verdicts match.

The keynote-notes (`docs/papoc-2026-keynote-notes.md`) discuss the
SMC angle in more depth; this doc just records the rule:

> **Validate the spec before committing proof effort to it.**

## Cross-references

| Per-RDT crosswalk | Tier | Headline read-side claim |
|---|---|---|
| [`peritext-vs-paper.md`](peritext-vs-paper.md) | C | Paper Ex 1/2/3/5/7/8 intent-preservation |
| [`rga-vs-paper.md`](rga-vs-paper.md) | C | Causal-order preservation, tombstone monotonicity, deterministic tiebreak |
| [`or-set-vs-paper.md`](or-set-vs-paper.md) | C | Add-Wins on lookup |
| [`aw-crpq-vs-paper.md`](aw-crpq-vs-paper.md) | C | Add-wins, LWW innate, `get_max` |
| [`mvr-vs-paper.md`](mvr-vs-paper.md) | C | Concurrent-writes-both-survive + sequential-supersede |
| [`lww-element-set-vs-paper.md`](lww-element-set-vs-paper.md) | B/C boundary | LWW comparison lookup |
| [`papoc-2026-keynote-notes.md`](papoc-2026-keynote-notes.md) | (methodology) | Tier framework, SMC angle, agent-human collaboration |
| [`porting-op-based-crdts.md`](porting-op-based-crdts.md) | (methodology) | Five-step recipe for porting op-based CRDTs into Sal |
