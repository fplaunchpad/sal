# Generic safety for conditioned MRDTs — pen-and-paper memo

Status: analysis memo, no Lean. Written before mechanization, per the standing
lesson (pen-and-paper first; when a formulation fails a worked check, record
the failure and move on).

**Verdict in one paragraph.** The naive generic safety theorem — induct along
a canonical enumeration, applying `applicable`-guarded `Inv`-preservation at
each step — is not merely hard, it is *false*: for the bounded counter,
canonical enumerations exist whose intermediate states violate `BCInv`, so no
per-prefix stability condition over arbitrary canonical witnesses can be
sound (Route A, refuted in §4.1). The repair is to shrink the witness class:
add to the configuration invariant a **causal canonical witness** (an
enumeration that additionally linearizes `vis`), whose prefixes are exactly
the causally-closed, future-free supersets of each event's causal past. Over
that witness class the stability obligation (`SafetyStep`, Route A′, §4.2) is
satisfied by the bounded counter — with a proof that is *simpler* than the
mechanized `bc_version_inv` (no vis-maximal-event counting) — and is
correctly *refused* by the queue's head-check (double-dequeue counterexample,
§4.2.3), whose conditioning is convergence-directed and owes the safety layer
nothing. Independently, the counting shape of `bc_version_inv` generalizes to
an **escrow metatheorem** (Route B, §5) that needs *no* causal witness and no
`Inv`-preservation lemma at all, but only covers datatypes whose guarded
observations are affine event-counts. Route C (strengthened honesty, §6) is
rejected: it is the same obligation relocated into a hypothesis that no
generation-time client can check and that real honest executions falsify.
Mechanize A′ as the metatheorem, B as a standalone theorem for the escrow
class; both are configuration-level (they consume `GoodConfig3`, they do not
re-run the `Step3` induction).

---

## 1. Problem statement

### 1.1 Signature and configurations

`D : ConditionedMRDTSig` (`Framework/MRDTSig.lean`) is the ternary signature:
states `D.State` with initial state `D.init` (σ₀), events
`Op D.AppOp = Timestamp × Replica × AppOp`, per-event transition
`D.update : State → Op AppOp → State`, three-way merge
`D.mergeL : State → State → State → State`, plus the conditioning split:

```
Inv        : State → Prop                 -- state-shape invariant
applicable : Op AppOp → State → Prop      -- generation-time guard
```

Folds: `applySeq D.toCRDTSig s π = π.foldl D.update s`. Commutation
(`CRDT_Signature.lean:89`):

```
D.commutes o₁ o₂ := ∀ s, D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁
```

The ternary `Configuration D` (`Framework/ExecutionModel.lean:109`) carries the
replica-keyed core (`N`, `L`, `vis` with `vis_causal`, `timestamps_distinct`,
`causal_mono`, `vis_total_same_replica`) and the ranked version store
`ver : Version → Option (D.State × Set (Op D.AppOp))`. `C.events` is the union
of the replicas' observed sets. Two structural facts the safety layer leans
on:

* `ts_unique`: distinct events have distinct timestamps;
* `vis_total_same_replica`: two distinct observed events of the same replica
  are `vis`-comparable.

### 1.2 Canonical states and the convergence metatheorem

From `Merge_Linearization_Set.lean` / `RA_Linearizability.lean`:

```
listPermOf π E  := π.Nodup ∧ ∀ a, a ∈ π ↔ a ∈ E
respects π R    := π.Pairwise (fun a b => ¬ R b a)
   -- for a before b in π: no R-edge from b back to a

loOn C ev e₁ e₂ :=
  (C.vis e₁ e₂ ∧ ¬ D.commutes e₁ e₂)
  ∨ (¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁ ∧ D.rc e₁ e₂ = Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, C.vis e₂ e₃ ∧ ¬ D.commutes e₂ e₃)

IsCanonicalState C ev s :=
  ∃ ρ, listPermOf ρ ev ∧ respects ρ (loOn C ev) ∧ applySeq D.init ρ = s
```

`GoodConfig3 C` (`Metatheory/Adequacy.lean:49`) is the reachability invariant:

```
canonical      : C.ver v = some (s, E) → IsCanonicalState (core C) E s
vis_trans      : vis transitive
vis_irrefl     : vis irreflexive
ver_events_sub : version event sets ⊆ C.events
ver_causal     : C.ver v = some (s, E) → ∀ a b, C.vis a b → b ∈ E → a ∈ E
```

Note carefully: `ver_causal` closes version event sets under **all**
`vis`-predecessors, not merely non-commuting ones — strictly stronger than
the backward-closure premises of `JoinLemma3At` (which demand only
`vis ∧ ¬commutes` closure). This full closure is load-bearing below.

`HonestReach D H hInit` (`Metatheory/HonestReach.lean`) is `Step3`-reachability
where every step leaves a configuration satisfying the contract `H`;
`goodConfig3_of_honest_reach` yields `GoodConfig3` at every honestly reachable
configuration given `JoinLemma3At` at every `H`-configuration.

### 1.3 The two safety-relevant instances

**Bounded counter** (`MRDT_Instances/BoundedCounter/BoundedCounter.lean`).
State `(incs, decs) : (ℕ → ℤ) × (ℕ → ℤ)`; `inc`/`dec` bump the issuing
replica's own slot; `rc = Either` everywhere; **all operations commute**
(`BC_all_comm`). The conditioning:

```
BCInv s          := ∀ r, 0 ≤ s.2 r ∧ s.2 r ≤ s.1 r
bcApplicable o s := match o.2.2 with
                    | inc => True
                    | dec => s.2 o.2.1 + 1 ≤ s.1 o.2.1   -- slack in OWN slots
BCHonest C       := ∀ e ∈ C.events, e.2.2 = dec →
                      ∀ π, listPermOf π {e' ∈ C.events | C.vis e' e} →
                        bcApplicable e (applySeq BC.init π)
```

`bc_version_inv` (line 429): reachable + `BCHonest` ⟹ every version state
satisfies `BCInv`. Its proof does **not** do prefix induction. It counts:
canonicity + `bc_fold_incs`/`bc_fold_decs` make fold slots equal per-replica
event counts of the enumeration (hence of the *set* — counts are
order-free); if the version has any `dec` by `r`, take the `vis`-maximal one
`ê` (same-replica decs are totally `vis`-ordered by
`vis_total_same_replica`); honesty of `ê` at its causal past — which lies
inside the version set by `ver_causal` — gives
`#dec_r(past ê) + 1 ≤ #inc_r(past ê)`; every other `r`-dec of the version is
`vis`-before `ê` hence in `past ê` (`countP_le_one_of_unique` bounds the
strays by the one event `ê` itself); and `#inc_r(past ê) ≤ #inc_r(E)`. Note
the proof never uses `bcApplicable_inv_pres`.

**Mergeable queue** (`MRDT_Instances/MergeableQueue/MergeableQueue.lean`).
State = list of `(tag, value)`, head first; `enq v` appends `(ts, v)` (guarded
against duplicate tags in `qUpdate` itself); `deq t` filters out tag `t`
wherever it sits; `rc = Either`; same-tag `enq`/`deq` do **not** commute
(`q_enq_deq_not_comm`), and neither do concurrent enqueues. `Q.Inv = ⊤`. The
guard and contract:

```
qApplicable o s := match o.2.2 with
                   | enq _ => True
                   | deq t => ∃ v, s.head? = some (t, v)      -- t is the HEAD seen
QHonest C       := every deq t has a vis-prior enq of tag t
```

`q_fold_canon`: over a well-formed enumeration (`QWf`: nodup, unique enq
tags, no deq before its enq) the fold is `qCanonList ρ` — the enqueues in
enumeration order minus the dequeued tags. `qHonest_of_applicable` bridges
the applicability discipline to `QHonest`.

### 1.4 The target

> **(Generic safety.)** If (i) `∀ e s, D.applicable e s → D.Inv s →
> D.Inv (D.update s e)`, (ii) the history is honest (`applicable e` holds at
> the fold of `e`'s causal past), and (iii) `C` is honestly reachable, then
> every version state of `C` satisfies `D.Inv`.

The naive proof takes the canonical witness ρ of a version `(s, E)` from
`GoodConfig3.canonical` and inducts along it, applying (i) at each element.
The step needs `applicable e (fold of the prefix before e)`; honesty supplies
`applicable e (fold of past(e))` where `past(e) := {e' ∈ C.events | C.vis e' e}`.
These are different sets. The per-datatype residue is a stability condition
bridging them. This memo determines what that condition can and cannot be.

---

## 2. The gap, made precise: which sets occur as prefixes

Fix `GoodConfig3 C`, a version `(s, E)` (`C.ver v = some (s, E)`), and an
enumeration ρ with `listPermOf ρ E` and `respects ρ (loOn C E)`. For `e ∈ E`
at position `k` in ρ, let `S := {ρ[0], …, ρ[k−1]}` be the prefix set before
`e`. Write `past(e) = {x ∈ C.events | C.vis x e}`; by `ver_causal`,
`e ∈ E ⟹ past(e) ⊆ E`, and `past(e)` is exactly the *E-relative* causal past
(this identification is the move `bc_version_inv` makes at `hπP_perm`).

**Lemma 1 (necessity).** Every prefix set `S` before `e` satisfies:

* (N1) `S ⊆ E \ {e}`;
* (N2) `S` is `loOn(C,E)`-backward-closed in `E`:
  `∀ x ∈ E, y ∈ S, loOn C E x y → x ∈ S`
  (an `x ∉ S` sits at position ≥ k, i.e. after `y`, and `respects` forbids the
  back-edge);
* (N3) `{x ∈ E | loOn C E x e} ⊆ S` (same argument with target `e`).

**Lemma 2 (sufficiency).** Conversely, any `S` satisfying (N1)–(N3) occurs:
filter the given ρ to `S` and to `E \ (S ∪ {e})` — sublists of a respecting
list respect — and concatenate `ρ|S ++ [e] ++ ρ|rest`. The three cross-block
back-edge families are killed exactly by (N2) (rest→S and e→S: an edge
`loOn e y` with `y ∈ S` would force `e ∈ S`) and (N3) (rest→e). So
(N1)–(N3) is an **exact** characterization; no extra existence lemma is
needed because the blocks are carved out of the witness we already hold.

**Specialization, `rc = Either`** (both safety instances; also the RGA): the
rc-arm of `loOn` is dead, so `loOn C E = visNC := vis ∧ ¬commutes`,
independent of `E`. Then, unpacking (N2)+(N3) through the transitive closure
(`downset C e` of `JoinLemma_Of_CD.lean:142` is the `visNC`-path closure of
`{e}`):

* **S must contain**: `downset C e \ {e}` — the `visNC`-*path*-predecessors
  of `e`, not just the direct ones.
* **S may additionally contain**: any `visNC`-backward-closed `S' ⊆ E` of
  events with no `visNC`-path *from* `e`. Relative to `past(e)` these extras
  split into (a) events **concurrent** with `e`, and (b) — easy to miss —
  events in `e`'s **causal future** that commute with `e`
  (`vis e x ∧ commutes e x` admits no `loOn` edge in either arm, so `x` may
  precede `e`).
* **S may omit**: all of `past(e) \ downset C e` — the *commuting* causal
  predecessors of `e`. They can float after `e`.
* **S can never contain**: `e`; any event with a `visNC`-path from `e`
  (in particular any non-commuting vis-successor).

**Micro-examples.**

* BC, `E = {a, d}` with `a = (1, r, inc)`, `d = (2, r, dec)`, `vis a d`. All
  BC ops commute, so `visNC = ∅` and *every* subset of `E \ {d}` is an
  admissible prefix before `d` — including `S = ∅`: the enumeration `[d, a]`
  is canonical (respects is vacuous).
* Queue, `E = {a = enq t, d = deq t, b = enq u}` with `vis a d`, `b`
  concurrent with both, `u ≠ t`: `loOn` has the single edge `a → d`
  (`q_enq_deq_not_comm`; `b` commutes with `d`, and concurrent enqueues get
  no edge because `rc = Either` — which is exactly why queue canonical
  states are not unique). Admissible prefixes before `d`: `{a}` and
  `{a, b}`.

**General `rc`, a caveat for later**: the rc-arm makes `loOn C E` depend on
`E` through the absorber existential (growing `E` can *delete* must-edges),
so the characterization above must be read at fixed `E`; and the joint
linearizability of `vis` with `loOn(E)` (needed in §4.2) is not automatic —
see Open Question in §7.4.

---

## 3. Interlude: what honesty can legitimately say

All three shipped contracts have the shape "`P e` at the fold of `past(e)`",
but they differ in *which* fold, and the difference is not cosmetic:

* `BCHonest` quantifies over **all** enumerations of `past(e)`. Harmless for
  BC only because BC folds are permutation-invariant (all-comm).
* `qHonest_of_applicable`'s hypothesis `hApp` also quantifies over **all**
  enumerations — and for the queue this is **unsatisfiable in mundane honest
  executions**: if `past(e)` for `e = deq t` contains two surviving enqueues
  `enq t` (vis-first) and `enq t'`, the enumeration `[enq t', enq t]` folds
  to a queue with head `t'`, and `qApplicable (deq t)` fails at it. So the
  bridge `qHonest_of_applicable` is vacuous beyond single-enqueue pasts.
  (The theorem is sound; its hypothesis is a sometimes-false substitute for
  the intended one. The proof uses only one enumeration, so the fix is
  free — see §7.3.)

The state an honest client actually checks is its replica's head state at
generation time, which — since `apply` extends `vis` by `ev × {e}` — is a
fold of a **vis-linearizing** enumeration of exactly `past(e)`. Different
causal enumerations of `past(e)` can still fold differently (queue:
concurrent enqueues in the past), and the client holds only the one its
replica materialized. Hence the honest form is existential over causal
folds. Define (this is the generic honesty this memo adopts):

```
CausalFold C E σ := ∃ ρ, listPermOf ρ E ∧ respects ρ C.vis
                        ∧ applySeq D.init ρ = σ
-- `respects ρ C.vis` = no later element is vis-before an earlier one,
--  i.e. ρ linearizes vis|E; prefixes of such ρ are exactly the
--  vis-backward-closed subsets of E.

HonestApp D C := ∀ e ∈ C.events,
  ∃ σ, CausalFold (core C) {e' ∈ C.events | C.vis e' e} σ ∧ D.applicable e σ
```

`BCHonest ⟹ HonestApp` (its ∀ covers the causal enumerations; a causal
enumeration of `past(e)` exists because `past(e) ⊆ E` is finite and `vis` is
a finite strict order). For unguarded ops (`inc`, `enq`) the witness is any
causal fold. The per-datatype stability obligations below must therefore
accept an *arbitrary* causal fold `σ_P` of `past(e)` as the honesty datum.

---

## 4. Route A: prefix stability

### 4.1 Route A as posed — REFUTED by the bounded counter

**Formulation (AppStable).** For every admissible prefix pair `(S, e)` in the
sense of §2 (S satisfying (N1)–(N3) for `e` in a closed `E`):
`applicable e σ_P → applicable e σ_S`, where `σ_P` is a (causal) fold of
`past(e)` and `σ_S` a fold of an admissible enumeration of `S`.

**Refutation (BC).** Take the honestly reachable single-replica execution
`inc` (ts 1) then `dec` (ts 2), version `E = {a, d}` as in §2's
micro-example. Honesty holds: `bcApplicable d (fold {a}) = (0 + 1 ≤ 1)` ✓.
The admissible prefix `S = ∅` (enumeration `[d, a]`, canonical since all ops
commute) demands `bcApplicable d (fold ∅) = (0 + 1 ≤ 0)` — false. So
**AppStable is false for the flagship safety instance**, and any generic
theorem parameterized on it is inapplicable to BC.

The intuition offered in the task brief — "other-replica slots don't affect
`r`'s own-slot check, so plausibly yes" — is correct about the *extras* side
(§2's "may contain") and wrong about the *omissions* side: because **all**
of BC's operations commute, `downset C d \ {d} = ∅` and the prefix may omit
`d`'s entire causal past, including the very `inc` that funds it. The failure
is not repairable by weakening the conclusion: the enumeration `[d, a]` has
intermediate state `(incs r, decs r) = (0, 1)`, which violates `BCInv`
itself. **Intermediate states of canonical enumerations genuinely violate
`Inv`; only endpoints are guaranteed.** No per-prefix condition over the
witness class "all canonical enumerations" can be sound. Recorded and moved
on.

### 4.2 Route A′: causal witnesses — the repair

The refutation pinpoints the problem as the witness class, not the induction.
If the enumeration additionally **linearizes `vis`** (i.e.
`respects ρ C.vis`), then §2 collapses to something far tamer. Prefixes of a
vis-linearization of `E` are exactly the vis-backward-closed subsets of `E`,
so the prefix `S` before `e` satisfies

```
past(e) ⊆ S ⊆ past(e) ∪ Conc_E(e),      S vis-backward-closed,
```

where `Conc_E(e) = {x ∈ E | ¬ vis x e ∧ ¬ vis e x}`: the prefix contains the
*whole* causal past (nothing floats after `e` any more) and its only slack is
concurrent events; commuting-future extras are gone. (Given `S ⊆ E`,
future-freeness `∀ x ∈ S, ¬ vis e x` already implies
`S \ past(e) ⊆ Conc_E(e)`, since `vis x e ⟹ x ∈ past(e)`.)

Two things must be paid for:

**(P1) The witness must exist and fold to the version state.** A causal
enumeration of `E` always exists (finite strict order), but its fold equals
`s` only if we can *swap* the canonical witness for a causal one. This is a
new configuration-level fact:

```
CausalCanonical C := ∀ v s E, C.ver v = some (s, E) →
  ∃ ρ, listPermOf ρ E ∧ respects ρ (core C).vis
      ∧ respects ρ (loOn (core C) E) ∧ applySeq D.init ρ = s
```

(keeping the `loOn`-respect conjunct so it strictly refines
`GoodConfig3.canonical`). Two discharge species, mirroring the join species:

* **Pointwise upgrade (all-comm ∧ rc = Either — the BC species).** Here
  `loOn = ∅`, any vis-linearization respects it, and folds are invariant
  under permutation of the (Nodup, equal-membership, hence `List.Perm`)
  enumerations because all ops commute. `GoodConfig3 → CausalCanonical` with
  no induction over reachability.
* **Witness maintenance (the queue species).** The witnesses the framework
  actually builds are already causal: the Apply case appends `e` at the end
  (`isCanonicalState_extend` uses `ρ ++ [e]`, and `e` is vis-after all of
  `ev`); the queue's join witness `ρ₀ ++ Δ₁ ++ Δ₂` is causal given causal
  inputs — a vis-edge from a `Δ₂` event `y` back into `ρ₀` or `Δ₁` (target
  `x ∈ ev₁`) gives `y ∈ ev₁` by **full** causal closure of `ev₁`
  (`ver_causal`), hence `y ∈ ev₀`, contradicting `y ∈ Δ₂`; similarly
  `Δ₁ → ρ₀`. Note this argument needs full vis-closure, which
  `JoinLemma3At`'s interface does not pass (it passes only `visNC`-closure);
  a causal variant `JoinLemma3AtC` must carry the two full-closure premises,
  which `goodConfig3_merge_at` has in scope via `ver_causal`.

**(P2) The per-datatype stability obligation**, now over causal prefixes
only, fused with `Inv`-preservation so that unconditionally-safe ops (queue
`enq`'s duplicate-guard) need no `applicable` at all:

```
SafetyStep D := ∀ (C : Configuration D), -- with GoodConfig3 C facts in scope
  ∀ (E S : Set (Op D.AppOp)) (e : Op D.AppOp) (σS σP : D.State),
    (∀ a ∈ E, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E → a ∈ E) →                 -- E vis-closed
    e ∈ E → S ⊆ E → e ∉ S →
    (∀ a b, C.vis a b → b ∈ S → a ∈ S) →                 -- S vis-closed
    (∀ x ∈ S, ¬ C.vis e x) →                             -- future-free
    (∀ x, C.vis x e → x ∈ S) →                           -- past(e) ⊆ S
    CausalFold (core C) S σS →
    CausalFold (core C) {e' ∈ C.events | C.vis e' e} σP →
    D.Inv σS → D.applicable e σP → D.Inv (D.update σS e)
```

**Theorem (generic safety, causal-witness form).** If `D.Inv D.init`,
`SafetyStep D`, and `C` satisfies `GoodConfig3 C`, `CausalCanonical C`,
`HonestApp D C`, then `∀ v s E, C.ver v = some (s, E) → D.Inv s`.

*Proof.* Take the causal witness ρ of `(s, E)`. Induct along ρ maintaining
`Inv` at every prefix fold; base `Inv D.init`. At element `e` with prefix
`ρ_S` (set `S`): `ρ_S` is a vis-linearization of `S`, so
`CausalFold (core C) S (fold ρ_S)`; `S` is vis-closed in `C.events` (closed
in `E` as a linearization prefix, and `E` itself is closed by `ver_causal`);
future-free and ⊇ `past(e)` by linearization; `e ∈ C.events` by
`ver_events_sub`, so `HonestApp` supplies `σP` with
`CausalFold past(e) σP ∧ applicable e σP`; `SafetyStep` closes the step. The
endpoint fold is `s` by the witness. ∎

Nothing about reachability appears: like `isRALinearizable3_of_good`, this is
a configuration-level theorem; `GoodConfig3`/`CausalCanonical` ride the
existing `HonestReach` machinery.

#### 4.2.1 Worked check: BC discharges `SafetyStep` (and `bc_version_inv` is reproved)

Discharge of `SafetyStep` for `BC`: for `e = (ts, r, dec)`,

1. *Extras don't touch slot `r`.* For `x ∈ S \ past(e)`: `x ∈ E ⊆ C.events`
   and `e ∈ C.events`, so if `x.rep = r` then `vis_total_same_replica` gives
   `vis x e` (then `x ∈ past(e)`, contradiction) or `vis e x` (contradicts
   future-freeness). So every extra has `rep ≠ r` and `bcUpdate` by it leaves
   both `r`-slots unchanged.
2. *Slots are order-free counts* (`bc_fold_incs`/`bc_fold_decs`): so
   `σS.1 r = #inc_r(S) = #inc_r(past e) = σP.1 r` and likewise for `.2 r` —
   for *any* causal folds `σS`, `σP` of the two sets (this absorbs the
   ∃-form of honesty: all folds of `past(e)` agree on the checked slots).
3. `bcApplicable e` reads only slot `r` of both components, so
   `applicable e σP ⟹ applicable e σS`; then `bcApplicable_inv_pres` gives
   `Inv (update σS e)`. For `e = inc`, `bcApplicable_inv_pres` alone
   suffices. ∎

`BCHonest ⟹ HonestApp` (§3); `CausalCanonical` by the pointwise upgrade
(all-comm + rc-Either); so the theorem yields `bc_version_inv`'s statement
verbatim, and `bc_value_nonneg` follows as before (sum of per-replica
slacks). **Nothing is lost, and something is gained:** the causal witness
makes the whole §5–§6 apparatus of `BoundedCounter.lean` — `exists_rel_max`,
`countP_split`, `countP_le_one_of_unique`, the stray-dec bound — collapse
into step 1 above. The vis-maximal-dec trick was exactly compensation for
the non-causal witness. (The same-replica-totality and
causal-past-inside-the-version ingredients survive, as they must; they are
now used once, generically.)

The two-event refutation of §4.1 is instructive to re-run: the causal witness
is `[a, d]` (the enumeration `[d, a]` is canonical but not causal and is
never consulted); at `d` the prefix is `S = {a} = past(d)` and the check is
the honesty datum itself.

#### 4.2.2 What the BC discharge generalizes to

The discharge used only: (i) the guard of `e` reads state components that
`update` lets only `e.rep`-issued events modify ("issuer-local
observations"), and (ii) those observations are order-free functions of the
event set ("measured", §5). Any escrow-style datatype with issuer-local,
count-valued guards (bounded PN-counter with transfers restricted to own
slots, per-replica token buckets, semaphores with per-client pools)
discharges `SafetyStep` by the same three lines. This is the reusable shape;
it should be provided as a lemma
(`safetyStep_of_issuer_local`, parametric in the observation family) rather
than re-proved per instance.

#### 4.2.3 Worked check: the queue refuses `SafetyStep` — and correctly so

Take `Inv` any predicate entailing "if `deq t` is applicable-shaped then …";
concretely test the head-check's stability. Counterexample (honestly
reachable, and *exactly* Peepul's double-dequeue caveat from the note):
`r₁` enqueues `t` (ts 1); the version is merged to `r₂`; `r₁` issues
`deq t` (ts 2; applicable: head = `t` ✓); `r₂` concurrently issues `deq t`
(ts 3; its past is `{enq t}`, head = `t` ✓; the two deqs are vis-incomparable).
`QHonest` holds; both generations were `qApplicable` at their causal pasts.
Merge: `E = {enq t, deq₁ t, deq₂ t}`. Causal witness `[enq, deq₁, deq₂]`. At
`deq₂` the prefix fold is `[]`: `qApplicable deq₂` fails (`head? = none`),
though `applicable deq₂ σP` holds (`σP = [(t,v)]`). So:

* **"t is head" is not stable** under concurrent extras — a concurrent
  same-tag dequeue removes it.
* **"t is present" is not stable either** — same counterexample. The brief's
  suggested weakening does not survive; record and move on.
* The stable consequence of the head-check is **event-level, not
  state-level**: "an `enq` of tag `t` is vis-prior" (that is `QHonest`
  itself), whose closure consequence "`enq t ∈ E` whenever `deq t ∈ E`"
  (`q_deq_enq_mem`) is precisely what the *convergence* layer consumes
  (well-formedness `QWf` of enumerations, hence `q_fold_canon`, hence the
  Join). It is not expressible as `D.Inv : State → Prop`.

And nothing is lost: the queue has no true safety property of the target
shape that fails. `qUpdate (deq t)` on a `t`-less state is a no-op (filter),
so the double-dequeue produces no `Inv`-violation — it produces the
*semantic* caveat (two deqs fold over one enq) that RA-linearizability makes
visible. State-shape invariants the queue does enjoy — `(qTags s).Nodup`,
every element traceable to an enqueue — are **unconditionally** inductive
(the duplicate guard sits inside `qUpdate`), so they discharge `SafetyStep`
without touching `applicable`. Conclusion: the queue owes the safety
metatheorem nothing; its conditioning is convergence-directed. This is a
feature of the formulation, not a gap: a stability obligation that the
double-dequeue execution satisfied would be unsound.

---

## 5. Route B: counting/abstraction — the escrow metatheorem

Generalize the *actual* `bc_version_inv` proof shape. Say `D` is **measured**
by a family of observations `obs k : D.State → ℤ` and per-op weights
`μ k : Op D.AppOp → ℕ` (`k` in some index set; for BC, `k` ranges over
`{inc, dec} × Replica`) if

* (B1) `obs k D.init = 0` and
  `∀ s e, obs k (D.update s e) = obs k s + μ k e` (affine update).

Then for *any* enumeration ρ of any `E` (Nodup + membership),
`obs k (applySeq D.init ρ) = Σ_{e ∈ E} μ k e =: M k E` — folds compute
**set** measures; enumeration-independence of the measured observations is
free, no commutativity or causal witness needed, and the ∃/∀ distinction in
honesty dissolves for guard conditions expressed in `obs`.

The **escrow safety theorem**. Suppose additionally, for each invariant
instance `i` with a consuming class `cons i` and a funding class `fund i`:

* (B2) `Inv s ⊇ ∀ i, obs (cons i) s ≤ obs (fund i) s`
  (the `0 ≤ obs (cons i) s` conjunct is free from `μ ≥ 0` + (B1));
* (B3) guard–measure link: `μ (cons i) e = 1 → applicable e σ →
  obs (cons i) σ + 1 ≤ obs (fund i) σ`, and `μ (cons i)` is `{0,1}`-valued;
* (B4) consumption seriality: any two distinct events of class `cons i` in
  `C.events` are vis-comparable (discharged for BC — and expected typically —
  by "the class is issuer-determined" + `vis_total_same_replica`; provide
  that as lemma `class_total_of_same_rep`);
* (B5) honesty: each `cons i`-event was `applicable` at a fold of its causal
  past (`HonestApp` suffices; so does `BCHonest`'s stronger form).

Then at every version `(s, E)` of a `GoodConfig3` configuration, `Inv s`.

*Proof (the `bc_version_inv` argument, verbatim at the measure level).* Fix
`i`. `obs k s = M k E` by (B1) + `canonical`. If `E` has no `cons i`-event,
`M (cons i) E = 0 ≤ M (fund i) E`. Otherwise take the vis-maximal
`cons i`-event `ê` (B4 + `vis_trans`, via the already-generic
`exists_rel_max`). Every other `cons i`-event of `E` is vis-before `ê`,
hence in `past(ê) ⊆ E` (`ver_causal`), so
`M (cons i) E ≤ M (cons i) (past ê) + 1`. Honesty + (B3) at any past-fold
(order-free by (B1)) give `M (cons i)(past ê) + 1 ≤ M (fund i)(past ê)`, and
`μ ≥ 0` gives `M (fund i)(past ê) ≤ M (fund i) E`. Chain. ∎

**Assessment.** Route B needs *neither* `CausalCanonical` *nor*
`Inv`-preservation — note `bc_version_inv` never invokes
`bcApplicable_inv_pres` — and tolerates arbitrary canonical witnesses. Its
price is the affine-update premise (B1): the state must literally count.

* BC is an instance: `obs = (·.1 r, ·.2 r)`, `μ = bcIsIncAt/bcIsDecAt`,
  (B1) = `bc_fold_incs`/`bc_fold_decs`, (B3) = `bcApplicable`'s definition,
  (B4) = same-replica classes.
* The queue is **not**: presence-of-`t` is not affine — `deq t` on a
  `t`-less state adds 0, not −1 (the filter is idempotent), so (B1) fails;
  and with the double-dequeue this is essential, not an encoding accident
  (`#enq t − #deq t` goes to −1 while the state stays at `[]`). The queue's
  analogue of "slots = counts" is the fold formula
  `q_fold_canon`/`qCanonList` — a Boolean set-abstraction whose validity
  itself requires honesty (`QWf`), i.e. it *is* the per-datatype Join-adjacent
  content, not a generic instance. Tag-uniqueness comes from `ts_unique` +
  the update guard, not from measures.

So Route B is a genuine metatheorem for the escrow class and a discharge
toolkit (its lemmas `exists_rel_max`, `countP_split`,
`countP_le_one_of_unique` are already datatype-generic in
`BoundedCounter.lean` §5 and should move to a shared file), but it is not
*the* generic safety theorem.

---

## 6. Route C: strengthened honesty — rejected

**Formulation.** `HonestStrong C := ∀ e ∈ C.events`, for every admissible
prefix set `S` for `e` (per §2, or per the causal restriction of §4.2) and
every fold `σS` of `S`: `applicable e σS`. The generic theorem then holds by
the naive induction, trivially — the stability bridge is assumed away.

**What dies: dischargeability, twice over.**

1. *No client can check it.* At generation time the issuer of `e` has seen
   exactly `past(e)`. The sets `S` range over supersets containing events
   **concurrent with `e` — including events that do not yet exist** when `e`
   is issued (and, in the unrestricted form, events causally after `e`). A
   generation-time discipline cannot constrain a fold over events from the
   future. The queue's bridge `qHonest_of_applicable` works precisely
   because the checked state *is* the causal-past fold; no analogous bridge
   can exist for `HonestStrong`. The obligation is dischargeable exactly
   when it *follows* from causal-past applicability — i.e. exactly when
   Route A′'s `AppStable` content holds — so Route C adds nothing and hides
   the real obligation inside a hypothesis.
2. *Real honest executions falsify it.* Unrestricted form: BC's `[d, a]`
   prefix `∅` (§4.1) — `HonestStrong` is false in the standard inc-then-dec
   execution. Causal-prefix form: the queue's double-dequeue (§4.2.3) —
   false in an honestly reachable execution. A metatheorem whose hypothesis
   is false wherever the datatype is interesting is the exact
   "sometimes-false substitute" failure mode this repo has already paid for
   once (GenDisc2CEq); it would even *look* dischargeable on toy runs.

**When Route C is fine**: `applicable = ⊤` (all flat instances — then it is
`HonestReach` with `H = ⊤`); guards monotone in a direction that concurrent
extension preserves (e.g. "element x was ever inserted" over a grow-only
component). Both cases are subsumed by discharging `SafetyStep` trivially.
Verdict: do not mechanize Route C as an interface; keep the implication
"HonestApp + SafetyStep ⟹ per-step applicability at causal prefixes" as an
internal lemma of the Route A′ proof, which is where that content actually
lives.

---

## 7. Verdict and mechanization plan

**Mechanize A′ as the metatheorem, B as a standalone theorem + toolkit.**
They overlap on BC (both reprove `bc_version_inv`) but neither subsumes the
other: A′ covers non-affine guards but needs `CausalCanonical`; B covers
arbitrary witnesses but needs affine observations. Both are
configuration-level.

### 7.1 New file `Metatheory/GenericSafety.lean` (Route A′)

Statements (repo notation; `C : Configuration D`, `core C` its binary core):

```
def CausalFold (C : Sal.Emulation.Configuration D.toCRDTSig)
    (E : Set (Op D.AppOp)) (σ : D.State) : Prop :=
  ∃ ρ, listPermOf ρ E ∧ respects ρ C.vis ∧ applySeq D.toCRDTSig D.init ρ = σ

def HonestApp (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, ∃ σ,
    CausalFold (Configuration.core C) {e' ∈ C.events | C.vis e' e} σ
    ∧ D.applicable e σ

def SafetyStep (D : ConditionedMRDTSig) : Prop := …  -- §4.2 (P2) verbatim

def CausalCanonical (C : Configuration D) : Prop := …  -- §4.2 (P1) verbatim

theorem version_inv_of_causal_canonical
    (hStep : SafetyStep D) {C : Configuration D}
    (hG : GoodConfig3 C) (hCC : CausalCanonical C) (hHon : HonestApp C)
    (hInit : D.Inv D.init) :
    ∀ v s E, C.ver v = some (s, E) → D.Inv s
```

Proof structure: list induction over the causal witness (snoc form, mirroring
`q_fold_canon`'s `List.reverseRecOn`), with three bookkeeping lemmas
(prefix sets of a `respects · C.vis` enumeration are vis-closed, future-free,
past-containing). No `Step3` induction; no topological-sort lemma is needed
in the main proof (the honesty witness supplies `σP`; prefixes supply `σS`).
Estimated 250–350 lines.

Discharge lemmas for `CausalCanonical`:

```
theorem causalCanonical_of_allComm_rcEither
    (hcomm : ∀ a b, D.toCRDTSig.commutes a b)
    (hrc : ∀ a b, D.toCRDTSig.rc a b = RcRes.Either)
    {C} (hG : GoodConfig3 C) : CausalCanonical C
```

needing (a) fold-invariance under `List.Perm` given all-comm (~50 lines,
adjacent-swap induction), (b) existence of a vis-linearization of a finite
set with `vis` transitive+irreflexive (~60 lines, maximal-element peel —
generalize `exists_rel_max` from total to partial by extracting a maximal
element instead; or reuse it after restricting). ~150 lines. For the queue
species: `JoinLemma3AtC` (full-closure premises, causal-witness conclusion)
plus a `goodConfigC_*` induction — **defer** (§7.2: the queue currently owes
nothing to the safety layer; build this only when a second direct-join
instance wants a nontrivial `Inv`).

### 7.2 Per-instance obligations under the plan

| Instance | Owes | Status |
|---|---|---|
| BoundedCounter | `SafetyStep BC` (§4.2.1, ~80 lines via slot-transfer), `BCHonest → HonestApp` (~20), all-comm+rc-Either (have) | replaces the bespoke §5–§6 of `BoundedCounter.lean`; keep `bc_version_inv`'s statement as a corollary |
| MergeableQueue | nothing (Inv = ⊤ ⟹ `SafetyStep` trivial); optionally fix `qHonest_of_applicable` (§7.3) | head-check stability refuted (§4.2.3) — do **not** attempt |
| RGA (tombstone-free) | out of scope here; its `Inv` feeds `commutesOn` (convergence). A safety reading (`RgaInv` at every version) would need `SafetyStep` for the positional guard — expect the same rehoming difficulties as the convergence layer; flag as open | — |
| Flat catalogue (`applicable = ⊤`) | nothing; theorem degenerates to `Inv`-preservation under all ops if a nontrivial `Inv` is ever wanted | — |

### 7.3 Repairs to existing code surfaced by this analysis

* `qHonest_of_applicable`'s `hApp` quantifies over all enumerations of the
  causal past and is unsatisfiable in executions whose deq-pasts hold two
  surviving enqueues (§3). Restate `hApp` with
  `CausalFold`-∃ (or even a single named fold); the existing proof already
  uses only one enumeration, so the change is local. `BCHonest` can stay
  (harmless for BC) but the memo recommends aligning both on `HonestApp`.

### 7.4 Route B deliverable and open questions

`Metatheory/EscrowSafety.lean`: the measured-datatype record (B1)–(B4), the
theorem of §5 (~250–350 lines; move `exists_rel_max`, `countP_split`,
`countP_le_one_of_unique` out of `BoundedCounter.lean` into it), BC instance
(~80 lines). Lower priority than A′ (it re-proves only BC today) but cheap,
and it is the discharge toolkit for the next escrow-style instance.

Open questions to record in the note's Open Questions section:

1. **General `rc`.** Does a joint `vis`-and-`loOn(E)` linearization always
   exist under `UpdateVCs`? A cycle needs at least two rc-edges separated by
   vis-paths (a single rc-edge closed by a vis-path contradicts concurrency
   via `vis_trans`; a non-commuting first vis-step is an absorber killing
   the rc-edge). `no_rc_chain` forbids adjacent rc-edges but not
   vis-separated ones. Unresolved; irrelevant for all current conditioned
   instances (`rc = Either` throughout), so `CausalCanonical` is stated as a
   hypothesis with the two discharge species rather than derived generically.
2. **Client-check honesty at the `Step3` level.** `HonestApp` is a
   configuration predicate; the honest client's actual act is checking
   `applicable e` against its head state at the `apply` step. A conditioned
   step relation (apply guarded by `applicable` at the head) would make
   `HonestApp` a *theorem* of the LTS rather than a contract — the clean
   version of the RGA's `HonestDelivery`. Natural follow-up; orthogonal to
   this memo's theorems.

---

## 8. Honest failure modes (summary of recorded refutations)

* **Route A (AppStable over all canonical prefixes): unsound for BC.**
  `E = {inc_r, dec_r}`, canonical witness `[dec, inc]`, prefix `∅`;
  moreover its intermediate state violates `BCInv`, so no weakening of the
  conclusion helps (§4.1).
* **"t is head" and "t is present" are both unstable for the queue** even
  over causal prefixes: honest concurrent double-dequeue (§4.2.3). The
  stable residue is event-level (`QHonest`), consumed by convergence, not by
  a state invariant.
* **Route C (HonestStrong): sometimes-false and client-uncheckable** — false
  in the two executions above; constrains folds over not-yet-existing
  events (§6).
* **∀-enumeration honesty (`qHonest_of_applicable.hApp`) is vacuous** beyond
  single-enqueue pasts (§3) — an existing code smell, cheap to fix.
* **Route B is not universal**: fails (B1) for the queue because `deq` is an
  idempotent filter, not a decrement (§5).
