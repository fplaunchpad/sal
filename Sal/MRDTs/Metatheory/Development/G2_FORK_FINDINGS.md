# Gate G2 (OQ4) fork: applicability-aware `lo` vs applicability-restricted convergence

*Companion to `G2_Applicability_Aware.lean` (task #7 of `CONDITIONED_METATHEORY_PLAN.md`).
Everything below is mechanized, 0 sorries, kernel-clean
(`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`).*

## Setting

`G2_Transport_Probe.lean` refuted the naive conditioned convergence (`commutes ↦
commutesOn` inside `lo`, all other hypotheses kept) on the 2-event RGA execution `insOpE`
(insert node 1) → `delOpE` (delete node 1): the pair is never jointly applicable, so
`commutesOn` is vacuously true, the conditioned order drops the `ins → del` edge, and the
bad order `[delOpE, insOpE]` — which folds `delOpE` at `init`, where it is not applicable —
respects the order yet folds differently.

Two repairs restrict the enumerations back to the feasible ones:

- **(a)** `loOnA` = `loOnC` plus a disjunct `vis e₁ e₂ ∧ appliesDependsOn e₂ e₁`, where
  `appliesDependsOn e₂ e₁` is the RGA generation dependency: `e₁` is an Ins creating a node
  (its timestamp) that `e₂` names as Del-target / Ins-anchor (`opLeaf`) or path member
  (`opPath`).
- **(b)** `applicabilityValid π s`: every prefix-fold of `π` from `s` keeps the next op
  `applicable`. Convergence is quantified only over `applicabilityValid` enumerations.

## What was proved

### Both repairs work on the 2-event instance

| repair | keeps the edge / rejects bad order | theorem |
|---|---|---|
| (a) | `loOnA` keeps `ins → del`; `[del,ins]` does not respect `loOnA` | `loOnA_keeps_edge`, `respects_ins_del_loOnA`, `not_respects_del_ins_loOnA` |
| (b) | `[ins,del]` is valid, `[del,ins]` is not; restricted convergence HOLDS | `applicabilityValid_ins_del`, `not_applicabilityValid_del_ins`, `b_convergence_holds` |

`b_convergence_holds` is the decisive positive check for (b): on the very execution that
refuted the naive statement, the two enumerations collapse to `[insOpE, delOpE]` once
`applicabilityValid` is imposed, so the folds agree. (Interesting side note: on this
instance `applicabilityValid` alone pins the order — the `loOnC`-respects hypotheses are
never consulted.)

### Instance equivalence

`instance_equivalence`: over the permutations of `{insOpE, delOpE}`,

> respects `loOnA`  ↔  (`applicabilityValid` ∧ respects `loOnC`)

Both admit exactly `[insOpE, delOpE]`. **On the counterexample the two repairs are the same
exclusion.**

### General verdict: (b) is STRICTLY more general than (a)

`separating_inequivalence`. Take `delY = (3,0,.Del [] 1)`, a second, concurrent delete of
node 1, and the 3-event set `{insOpE, delOpE, delY}`. The order `[insOpE, delOpE, delY]`:

- **is applicability-invalid** (`not_applicabilityValid_sep`): `delY` folds at a state where
  `delOpE` has already removed node 1, so `accurate delY` fails there;
- **inverts NO generation-dependency edge** (`sep_no_backward_dep`): the sole creator
  `insOpE` is already first, and `appliesDependsOn` is identically `False` between the two
  Del's. Config-independently, whenever the base order `loOnC` admits this enumeration so
  does `loOnA` (`sep_loOnC_imp_loOnA`) — the added generation-dependency edges exclude
  nothing here.

So `(b)-admitted ⊊ (a)-admitted`: (b) rejects this infeasible order, (a) cannot. The missed
constraint is a **negative / anti-dependency** — "`delOpE` must not precede `delY`" — which
a *positive* creation-reference relation is structurally unable to express. This is exactly
the "combination dependency the VC-shaped route cannot capture" that the plan anticipated
(here at 3 events).

The provable inclusion in the other direction — `(b)-admitted ⊆ (a)-admitted`, i.e.
`applicabilityValid ⟹ no generation edge inverted` — holds because inverting `e₁ → e₂` with
`appliesDependsOn e₂ e₁` places a reference to `e₁`'s uniquely-created node before `e₁`, so
`accurate e₂` fails at that prefix. `instance_claimA` is its instance witness.

## Recommendation

Adopt **(b) `applicabilityValid` as the definition of feasibility** for the update layer's
convergence theorem; use **(a) `loOnA` as a decidable, per-MRDT *sufficient* condition** that
discharges the `applicabilityValid` obligation wherever applicability is a conjunction of
positive create-before-use references (the common RGA case: Del-target, Ins-anchor, path
membership).

Grounding:

- (a) and (b) coincide on the counterexample (`instance_equivalence`), so (a) is a faithful,
  syntactic repair there.
- (a) is provably **incomplete** (`separating_inequivalence`): a convergence theorem
  quantified by (a) still admits infeasible folds (anti-dependency / combination cases), so
  (a) cannot *be* the definition of feasibility — only a sound approximation of it.
- (b) captures all feasibility, at the cost of a semantic side-condition consumers carry;
  (a) is the tool that discharges that side-condition cheaply in the positive-dependency
  common case (`(b)-admitted ⊆ (a)-admitted` reduces "`applicabilityValid`" to "respects
  `loOnA`").

## Open subtlety surfaced (research question)

For the concurrent-delete version `{insOpE, delOpE, delY}`, **no** enumeration is
`applicabilityValid` (whichever delete runs first makes the other non-applicable), yet the
merged state is well-defined and must be linearizable by *some* order. So (b)'s strict
"applicable at every prefix" can be **unsatisfiable for genuinely reachable versions** with
redundant concurrent operations. The update layer therefore needs an applicability notion
that tolerates idempotent / absorbed re-application (e.g. "`applicable` **or** a no-op at
this state") rather than strict applicability — otherwise convergence over
`applicabilityValid` enumerations becomes vacuous exactly where two concurrent effects
collide. Settling the right relaxation (and whether it re-expands the gap with (a)) is the
natural next question.

## Build / axiom status

`lake build Sal.MRDTs.Metatheory.Development.G2_Applicability_Aware` — exit 0.
`#print axioms` on `b_convergence_holds`, `instance_equivalence`, `separating_inequivalence`,
`not_applicabilityValid_sep`, `sep_loOnC_imp_loOnA`, `loOnA_keeps_edge` all report only
`[propext, Classical.choice, Quot.sound]`.
