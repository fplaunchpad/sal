# Tombstone-free RGA MRDT: what we know

**Status:** a mixed finding. One approach (rehab-in-`merge`) has a structural
blocker against the 24 VCs; a second approach (static-payload splice at
`do_`) has a concrete commutativity failure; a third (dynamic-lookup splice
at `do_`) remains open and appears implementable — pursuing it separately.

**Author note:** this document records counterexamples and their exact scope
so a future attempt doesn't generalize beyond what's been shown.

## Goal

A tombstone-free RGA MRDT whose 24 RA-linearizability VCs are closed within
Sal's framework. "Tombstone-free" means `Remove` removes a character from the
state outright (not just flipping a deleted bit), so state size is bounded by
live characters instead of live + removed.

The apparent difficulty: RGA's character records carry `after_id` pointers,
and removing a character strands its children with dangling pointers. RGA
classically handles this by keeping the record as a tombstone — the record's
id stays in the state as a layout anchor even though the character is
rendered as invisible.

The proposed MRDT trick — analogous to how `OR_Set_MRDT` drops its remove-set
in favour of the LCA — is **LCA rehabilitation**: let `merge` use the LCA to
rewrite orphan `after` pointers to the nearest alive LCA-ancestor, so the
merged state has a resolvable after-chain without keeping tombstones.

## The finding

The 24 VCs cannot verify any `merge` that performs LCA-rehabilitation.

Specifically: the VC

    lem_0op : eq (merge (do_ l ol) (do_ a ol) (do_ b ol))
                 (do_ (merge l a b) ol)

fails for `ol = Remove target` under any rehab scheme whose behaviour depends
on whether `target` is in the merged domain. Below is the counterexample.

## Counterexample

Take

    concrete_st := map OpId (OpId × ℕ)
    do_ Insert ch after   at (ts, rid) := upd s (ts, rid) (after, ch)
    do_ Remove target                   := del s target
    merge l a b          := three_way_map_merge l a b
                            ; rehab_of l on the orphans

Let `l`, `a`, `b` be three copies of the same map:

    target  → (root,   ch_x)     -- some character X
    y       → (target, ch_y)     -- Y was inserted after X

Let `ol = Remove target`.

**LHS = `merge (do_ l ol) (do_ a ol) (do_ b ol)`:**

Each branch after `ol`: `{ y → (target, ch_y) }`, with `target` gone.
Three-way merge domain: `{y}`. `target ∉ merged_dom`.
Rehab scans `y → (target, ch_y)`. `target ∉ merged_dom`, so **orphan**.
Rehab rewrites: call the new after-pointer `target'` (the exact value
depends on the scheme; any non-trivial scheme produces something ≠ target).
Result: `{ y → (target', ch_y) }`.

**RHS = `do_ (merge l a b) ol`:**

Inner `merge l a b`: all three inputs have `target`. Inner merged domain
includes `target`. `y → (target, ch_y)` has `target ∈ inner_merged_dom`, so
**not an orphan**. Rehab skips it. Inner result: the same two-entry map.
Outer `do_ Remove target`: removes `target` from the domain, leaves all
other mappings untouched. Result: `{ y → (target, ch_y) }` with
`target ∉ final domain` — orphan, never rehabilitated.

**LHS ≠ RHS** as long as rehab is observable (`target' ≠ target`).

## Why the finding is structural

The LHS and RHS differ because:

- Rehab runs inside `merge`, and its orphan-detection criterion consults
  `merged.domain`.
- `do_ ol = Remove target` changes whether `target` is in the domain of the
  `merge`'s inputs, which changes `merged.domain`, which changes which
  records are tagged as orphans.
- Rehab can't re-run after the outer `do_ ol` on RHS, because rehab only
  lives inside `merge`.

The two sides of `lem_0op` can't agree on which records count as orphans
unless rehab is a no-op. Any scheme that makes rehab a no-op is either (a)
not using the LCA meaningfully, or (b) moving the work elsewhere.

Moving rehab into `do_` doesn't recover the situation: `do_` has no LCA
argument, so a `do_`-time rehab can only consult the current state. The
current state is strictly less informative than the LCA (it doesn't contain
removed characters' after-chain predecessors), so this degrades the
rehabilitation to a best-effort intra-branch splice.

The lattice-join-like merges the 24 VCs were designed around — `OR_Set_MRDT`,
`Grow_Only_Set_MRDT`, the existing `Replicated_Growable_Array_MRDT` — all
commute with `do_` on the LCA because `l` appears only through set-algebraic
operations (intersection, difference), not through structural queries on
its contents. Rehabilitation is a structural query (it reads
`(sel l x).after`), and that's exactly the operation that `do_ ol` can
invalidate on `l`.

## What this rules out and what it doesn't

**Ruled out:**

1. Any MRDT that makes `merge` rewrite orphan references via an
   LCA-derived predecessor function, while claiming all 24 VCs close.
   Blocked by `lem_0op` under `ol = Remove target`.
2. Splice-at-`do_` with a **static** predecessor payload in the Remove op.
   Blocked by Remove-Remove commutativity on chain-aligned removes.

**Not ruled out:**

- **Splice-at-`do_` with dynamic lookup.** `do_ Remove target` reads the
  current state to find `target`'s predecessor; splices and filters. No
  counterexample has been found; the approach has proof-engineering risks
  (state-reading `do_` plus `rc` arbitration for Insert/Remove corner
  cases) but no structural obstruction. **Active next step.**

- **Tombstone-free state convergence without rehab.** `Σ := set CharRec`,
  plain three-way set merge (no rehab), 24 VCs close cheaply — because this
  is exactly `OR_Set_MRDT` with `CharRec` elements. The trade-off: state is
  bounded by live characters, but rendered sequence semantics under
  concurrent insert-after/remove is NOT preserved — orphan records are
  produced and left in state. A rehabilitator at read-side could still use
  the version DAG to interpret them, but that rehabilitator is external to
  the MRDT and not verified by the 24 VCs.
- **A richer framework.** Extending Sal's VCs to a version-DAG-aware
  setting (so `merge` can consult an oracle richer than `l`, and `do_` can
  participate in rehab) would sidestep the structural obstruction here.
  That's a framework-level contribution, not a single MRDT.
- **Read-side rehab with a separate theorem.** Keep the MRDT simple
  (tombstone-free state, plain three-way set merge, 24 VCs cheap), define
  a `readSeq : Σ × VersionDAG → List ch` function that does rehab at read
  time, and prove a separate theorem

      readSeq (merge_MRDT l a b) dag = rga_canonical (merge_CRDT a_tomb b_tomb)

  relating this MRDT to the RGA CRDT on equivalent executions. The theorem
  is outside the 24 VCs; it's a one-off correspondence proof. This is
  probably the most tractable path if one wants to pursue tombstone-free
  RGA rigorously.

## Bonus: splice-at-`do_` is also blocked

A natural fallback is to move the rehabilitation work out of `merge` and into
`do_` — have `Remove target` locally splice its children's after-pointers to
`target`'s own predecessor before filtering `target` out. This keeps `merge`
a pure lattice join (like the existing RGA MRDT) and addresses intra-branch
orphans.

This approach has its own blocker: two concurrent `Remove`s along the same
after-chain don't commute at `do_` level. Take `Remove` with a statically
chosen predecessor payload (so `do_` stays computable — no `Classical.choice`):

    do_ (Remove target splice_to) s :=
      let s' := rewrite children (after = target → after = splice_to) in s
      filter s' (·.id ≠ target)

Concrete scenario: state has the chain `... ← X ← Y ← Z` (X's after = Y,
Y's after = Z), plus a child `W` of `X`. Issue two Removes:

- `Remove X` with payload `splice_to = Y` (X's parent at issue time).
- `Remove Y` with payload `splice_to = Z` (Y's parent at issue time).

**Order A (Remove X then Remove Y):**

- After Remove X: `W` rewritten to `after = Y`, X filtered. State has `(W, Y)`.
- After Remove Y: `W` rewritten to `after = Z`, Y filtered. State has `(W, Z)`.
- Final: `W → after = Z`. ✓ coherent.

**Order B (Remove Y then Remove X):**

- After Remove Y: `X` rewritten to `after = Z`, Y filtered. State has `(X, Z)`, `(W, X)`.
- After Remove X: `W` rewritten to `after = Y` (X's payload was set at issue
  to point at Y), X filtered. State has `(W, Y)`.
- Final: `W → after = Y`, but `Y` is gone from the state — dangling.

The two orderings produce different final states — but **only because the
payload was frozen at issue time**. The static-payload model is what fails
here, not splice-at-`do_` in general.

#### Mechanical confirmation via `no_rc_chain`

The static-payload failure shows up cleanly when we encode the design
in Lean and try `no_rc_chain`. Consider a set-based state with
`Remove target splice_to` as the op signature and a three-case `rc`:

- `rc(Insert o1, Remove o2) = Fst_then_snd` when `target(o2)` names
  `o1`'s id or after;
- `rc(Remove o2, Insert o1) = Snd_then_fst` symmetrically;
- `rc(Remove o2, Remove o3) = Fst_then_snd` when `splice_to(o2)`
  equals `target(o3)` (the chain case that needs arbitration — otherwise
  Remove-Remove fails to commute on chain-aligned removes).

Feeding this through `by sal` on `no_rc_chain`, grind reports:

    case grind
    target splice_to : OpId
    target_1 splice_to_1 : OpId
    target_2 splice_to_2 : OpId
    h_2 : splice_to = target_1
    h_3 : splice_to_1 = target_2
    ⊢ False

That hypothesis pair — `X.splice_to = Y.target ∧ Y.splice_to = Z.target`
— is a **legitimate** sequence of three Remove ops on a chain
`X ← Y ← Z`. `grind` correctly refuses to derive `⊢ False` because
the chain is realizable. `no_rc_chain` fails.

So under static payload there is no `rc` assignment that simultaneously
satisfies `rc_non_comm` (Remove-Remove on chains must *not* commute,
forcing `rc ≠ Either`) and `no_rc_chain` (no three-op `Fst_then_snd`
chain allowed). Arbitrating the chain as `Snd_then_fst` flips the
violation to the other direction — the VC pair is unsatisfiable
regardless of the arbitration choice.

### Dynamic-lookup splice-at-`do_` — open, likely viable

If `do_ Remove target` instead reads X's current `after` from the state at
apply time (rather than carrying it as a static op field), the same trace
commutes:

    do_ (Remove target) s :=
      if contains s target then
        let splice_to := (sel s target).after
        let s' := rewrite children (after = target → after = splice_to) in s
        filter s' (·.id ≠ target)
      else s

Under this model, Order B's `Remove X` looks up X's current `after` in the
post-`Remove Y` state — which is now `Z`, because `Remove Y` had already
spliced X. W gets rewritten to `Z`, matching Order A.

Insert-vs-Remove still has genuine non-commutativity in two specific cases
that any `rc` arbitration will need to name explicitly:

1. **Insert-id = Remove-target.** Pathological — Insert stakes id `(ts, rid)`
   while a concurrent Remove targets `(ts, rid)`. The two orderings
   disagree on whether the record exists in the final state.
2. **Insert-after = Remove-target.** Semantically meaningful — Insert's
   `after_id` is the very character being concurrently removed. Insert
   first + Remove second splices the new record to target's predecessor;
   Remove first + Insert second leaves the new record pointing at an
   absent id.

Both cases require non-`Either` `rc`. The arbitration choices are
consistent with `no_rc_chain` under checked scenarios (all three-op
chains I could construct terminate the `Fst_then_snd` chain in at most
two hops).

So dynamic-lookup splice-at-`do_` is **not** blocked by the analysis that
rules out static-payload. It is also not yet *proved* to close the 24 VCs
— it has real engineering challenges:

- `do_` reads state, which pulls in `contains`/`sel` terms throughout the
  proofs and has historically made `grind` and `simp` work harder (see
  the Peritext MRDT porting experience).
- The per-key value transform requires `iter_upd` (or equivalent),
  bringing in the map-level lemmas that haven't always played cleanly
  with `by sal`.
- `rc`'s two non-`Either` cases multiply the case analysis in the
  rcases-decomposition proof pattern.

None of these are structural obstructions; they're proof-engineering
risks. The way to resolve the question is to attempt the implementation
and report what closes.

So the precise current standing on splice-at-`do_`:

- **Static payload:** blocked by Remove-Remove commutativity on chains,
  as traced above.
- **Dynamic lookup via `map`:** architecturally hostile to Sal's
  automation. A first-pass attempt (state = `map OpId (OpId × ℕ)`,
  dynamic splice implemented as `iter_upd (fun _ v => if v.1 = target
  then (splice_to, v.2) else v)`, merge with lex-max tiebreak, `rc`
  arbitrating the two corner cases) failed to close even the simpler
  VCs via `by sal`: aesop stage-3 errored with *"goal 53 was not
  normalised"* on `rc_non_comm`, and stage-3's norm-simp exceeded its
  step budget on `cond_comm_base`, `merge_comm`, `base_2op`,
  `base_1op`, and `lem_0op`.

  The failure is not proof-engineering heaviness — it's the underlying
  design hitting a known-hostile pattern. `iter_upd` builds the
  destination `map`'s `mappings` field by composing `(fun k => f k
  (s.mappings k))` under the state's struct projection; when `f` is a
  **conditional lambda** (`if v.1 = target then … else v`), grind/simp
  must reason about pointwise function equality through the
  conditional branches, which is what the instrumented
  `@[simp, grind]` lemmas on `map` primitives don't extend to. The
  Peritext-flattening principle applies here exactly: whenever
  rewriting semantics would push a conditional lambda into a map's
  `mappings` field, the state representation is wrong for Sal, not
  the proofs.

  **What the Peritext flattening principle prescribes:** reshape Σ so
  the rewrite becomes a pointwise predicate operation on a top-level
  `set`. Concretely: `Σ := set CharRec` (top-level) with `do_ Remove`
  expressed as a set-predicate combining filter + rewrite. The hard
  part that blocks this in practice: the "rewrite" needs to know
  `target`'s predecessor, which requires lookup, which in a
  set-as-predicate representation requires either `Classical.choose`
  (reintroducing `noncomputable`/propDecidable hostility) or a helper
  that asserts uniqueness and extracts a witness. Neither is a clean
  reshape; both push the problem elsewhere. A genuinely clean
  set-based design would need a different identifier scheme that
  makes splice computable without a per-state lookup (e.g., a dense
  position space à la Logoot/LSEQ rather than RGA's after-chain).
  That's a different RDT, not a tombstone-free RGA.
- **Dynamic lookup via `set`:** open. Requires either a
  Classical.choose-based helper (with the known proof-automation
  costs) or a richer identifier scheme that makes the splice target
  computable pointwise. Neither has been attempted here.

No file has landed. The attempts were deleted rather than kept as
half-proved or architecturally-hostile work.

## Why this wasn't obvious up front

The analogy to `OR_Set_MRDT` is seductive because the state reductions look
identical: drop the auxiliary component, let the LCA do its work in `merge`.
The difference is that OR-Set's "LCA work" is pure set algebra
(`(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)`), which commutes with `do_` automatically.
RGA's "LCA work" would have to be structural (chasing after-chain), which
doesn't.

Put concisely: **tombstones carry a different kind of information in OR-Set
than in RGA.** OR-Set's tombstones encode membership history — a Boolean.
RGA's tombstones encode structural position — a graph. The LCA can replace
the former but not the latter within a pure `merge : Σ → Σ → Σ → Σ`.

## References

- `Sal/Tactic/Sal.lean` — the three-stage `by sal` tactic.
- Neem (Soundarapandian et al., OOPSLA 2025) — the op-based framework whose
  24 VCs Sal ports.
- `Sal/MRDTs/OR_Set_MRDT.lean` — the template that suggests the
  LCA-replaces-tombstone move in the first place.
- `Sal/MRDTs/Replicated_Growable_Array_MRDT.lean` — existing RGA MRDT,
  lattice-join merge, LCA vestigial. Still the honest baseline.
