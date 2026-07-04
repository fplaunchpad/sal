# End-to-end roadmap: verified SEC for the tombstone-free RGA

*2026-07-04. Companion to `CONDITIONED_METATHEORY_PLAN.md`. Names the end-to-end target and the
milestones to it, ordered by information value (test the one design-refuting step early).*

## Target theorem (T-E2E)

*For any well-formed execution of the tombstone-free RGA MRDT — replicas generating ops locally
and exchanging state via three-way `merge` — any two replicas that have received the same set of
events hold observationally-equal (`eq`) states.* Verified strong eventual consistency.

**Publishability.** Gomes et al. (OOPSLA'17, Isabelle) verified SEC for the *tombstoned* RGA. A
mechanized SEC proof for a **tombstone-free RGA with physical deletion** (deletion actually removes
state and re-anchors dependents) would be genuinely new, and the conditioned-metatheory route to it
is the framework contribution.

## What is already kernel-clean (this session)

The order layer and its hard lemmas: `general_swap` / `general_swap_bothFaithful` (the swap needs
neither operand `accurate`); `chainFaithful_doDel` and `chainFaithful_doDel_faithful` (ChainFaithful
survives a Faithful Del); the enabled-scope threading steps `chainFaithful_incompStep` /
`chainFaithful_incompFold`; the eq-convergence ENGINE (bubble/order-repair/recursion, generic over an
`EqSwap` oracle). The recurring interleaving wall is resolved (enabled-scope invariant). The
closure-indexed adequacy bridge `ra_linearizable3_of_joinC` + 9 flat MRDTs are done (prior arc).

## Milestones

**M1 — Enablement base lemma** (closes update-layer threading T1; independent of M2). Formalize the
history invariant "`recList w` is `w`'s generation-time true ancestor chain" as a reachability
predicate; prove `ChainFaithful (recList w)` at every enablement fold. Subsumes the reachable-regime
clash-Ins lemma (the Part-1 counterexample needs an inconsistent `recList`, excluded here). PBT
green (0/330). **Risk: low-medium** — one splice-style induction of the kind done twice.

**M2 — Execution model (Phase 0)** (parallel with M1). A conditioned `Configuration`: replicas,
`vis`, delivery = backward-closed sets, generation discipline (ops accurate+fresh at birth,
Lamport-monotone ids). *Derive* (not assume): distinct timestamps, `mono_alloc`,
`fresh_ts`/`NoFreshClash` at folds, existence of `loOnA`-respecting delivery enumerations
(satisfiability half already in `UpdateFeasibility_Gate`). Output: `hReady` discharged →
**unconditional update-layer convergence**. **Risk: low** — known shape, no open mathematics.

**M3 — Merge-linearization bridge** (critical path; depends on M2). Prove
`eq (merge l a b) (applySeqR (state l) π)` for a `loOnA`-respecting enumeration π of the events of
`a`,`b` beyond `l`. Decomposition: (3a) per-version event sets over the version DAG; (3b) single-sided
`merge l a l ~ a`, then compose sides via M2 order-independence; (3c) do it natively over `eq` (the
generic `Merge_Linearization_Set` induction carries 2 pre-existing Lean-`Eq` sorries; rebuild the
needed induction over `eq` rather than inherit them). Mathematical content: merge's LCA-climb
re-anchoring coincides with the fold's `resolve`-rehoming — the design's core bet, currently
supported only by the 8 PDF scenarios. **Risk: HIGH — the open research question of the roadmap.**
*Mitigation: PBT-gate it FIRST* (random version triples, mechanized merge-vs-fold `eqB`) — a
counterexample there is a decisive, cheap negative that forces a merge redesign before any proof.
[In progress: `RGA_MergeFold_PBT.lean`.]

**M4 — System induction (assembly)** (depends on M1–M3). Induct over the execution DAG: every
reachable replica state is `eq` to a fold of a `loOnA`-respecting enumeration of its delivered events
(update steps definitional; merge steps by M3 + M2). Corollary: same events ⇒ `eq` states = T-E2E.
Needs `merge`'s `eq`-congruence. **Risk: medium** — pure structure once M1–M3 exist.

**M5 (optional, framework paper only)** — `eq`-quotient σ-layer so the generic
`conditioned_convergence_on` hosts the RGA as an *instance* rather than via the bespoke `eq`-route.
Not needed for T-E2E; needed to claim "one conditioned metatheorem, RGA as an instance."

## Order of work

M1 ∥ M2 → **M3 PBT gate (do FIRST — the only step that can still refute the whole design)** → M3
proof → M4. The paper's spine is M3: if its PBT gate passes, everything else is known-shape; if it
fails, we learn it before spending months. Stage-1 (update-layer convergence, = M1+M2) plus the
enabled-scoping insight already stand alone as a publishable result; the merge bridge (M3) is the
natural second result, not a prerequisite for writing up the first.
