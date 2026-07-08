# Composition of conditioned MRDTs — the binary product `D₁ ⊗ D₂`, pen-and-paper memo

Status: analysis memo, no Lean. Written before mechanization, per the standing
lesson (pen-and-paper first; when a formulation fails a worked check, record
the failure and move on). Target: Open Question 9 (`oq:compose`,
`mrdt-metatheory.tex:2012`), specialized from the map combinator to the
**binary heterogeneous product** — the combinator Peritext actually needs.

**Verdict in one paragraph.** The product composes cleanly at exactly the
boundary the factored framework predicts — `JoinLemma3At` — and the reason is
one definitional fact: cross-component pairs commute *by `rfl`*, so `loOn`
localizes, folds and configurations project field-for-field, and the glued
join witness is a plain **concatenation** (no interleaving combinatorics at
all: cross pairs carry no `loOn` edge in either direction). `UpdateVCs`,
`SafetyStepOn`, `HonestApp`, `GenHonest`, and the entire `≈`-quotient VC
bundle (`EqEquiv`/`InvPres`/`CongVC`/`InvInvVC`/`WfOpReachable`/
`EqJoinLemma3C_H`) are all componentwise, so the RGA-critical `≈`-lift is
*moderate*, not heavy — what composes is the certificate bundle, re-fed to
the one generic capstone `RA_linearizable_up_to_eq_H` at the product
parameters; the finished component *theorems* do not compose, because
reachability does not project (a genuine finding, §2.1.4). Two formulations
are **refuted** by worked checks and recorded: (i) "two component causal
witnesses re-interleave into a product causal witness" is false (4-event
cycle, realizable execution, §2.4.4) — the sound repair pins *one* side and
re-sorts the other, which suffices whenever at most one component is
rc-nontrivial/order-sensitive; (ii) "component honesty supplies product
honesty for free" needs an enumerability side condition and, under
read-coupled guards, is not a componentwise notion at all (§3). Peritext =
RGA_TF ⊗ MarkStore fits the pragmatic cut (`≈₂ = Eq`: one quotiented
component) exactly; its bill is the MarkStore's OR-set discharge, the
product-LTS relativization of the RGA's honesty supplies, and the read layer
— it re-proves nothing of the RGA engine. Estimated: ~1.5–2.5k lines of
once-only kit + ~1.5–3k of Peritext instantiation, against a from-scratch
path that is not merely larger but structurally infeasible (every RGA lemma
case-splits on op constructors; a fused op type would touch all of them).

---

## 0. Notation and reading map

`D₁, D₂ : ConditionedMRDTSig` (`Framework/MRDTSig.lean`). Events are
`Op A = Timestamp × Replica × A`; `e.1` the timestamp, `e.2.1` the replica,
`e.2.2` the payload. `distinctOps` compares timestamps, `differentReplicas`
replicas (`RA_Linearizability.lean:139`) — both read only the `(t, r)`
prefix, which the product injections preserve.

Injections and projections, used throughout:

```
ι₁ : Op A₁ → Op (A₁ ⊕ A₂),   ι₁ (t, r, o) := (t, r, inl o)     (ι₂ dual)
opl : Op (A₁ ⊕ A₂) → Option (Op A₁),
      opl (t, r, inl o) := some (t, r, o);  opl (t, r, inr _) := none
π₁ ρ := ρ.filterMap opl : List (Op (A₁⊕A₂)) → List (Op A₁)      (π₂ dual)
ev↾₁ := ι₁⁻¹ ev = {e | ι₁ e ∈ ev} : Set (Op A₁)                  (↾₂ dual)
```

`ι₁` is injective, preserves timestamp and replica, and
`opl x = some a ↔ x = ι₁ a`. Hence: `π₁` preserves `Nodup`
(filterMap along an injective partial function), `a ∈ π₁ ρ ↔ ι₁ a ∈ ρ`,
`(ev₁ ∩ ev₂)↾₁ = ev₁↾₁ ∩ ev₂↾₁`, `(ev₁ ∪ ev₂)↾₁ = ev₁↾₁ ∪ ev₂↾₁`
(preimages commute with everything), and `π₁ (ι₁ ρ¹ ++ ι₂ ρ²) = ρ¹`,
`π₂ (ι₁ ρ¹ ++ ι₂ ρ²) = ρ²` (roundtrips).

Framework objects quoted: `JoinLemma3At` (`Framework/VC_Set.lean:81` — note
its closure premises are `vis ∧ ¬commutes`-closure, "visNC", NOT full
vis-closure), `UpdateVCs` (`Framework/Sigma_LoOn3.lean:33`), `loOn`
(`Merge_Linearization_Set.lean:159`), `HonestReach`/`GenHonest`
(`Metatheory/HonestReach.lean`, `GenHonest.lean`), `CausalFold`/`HonestApp`/
`SafetyStepOn`/`CausalCanonical` (`Metatheory/GenericSafety.lean`), the
quotient bundle and capstone (`Metatheory/GenericEqQuotient*.lean`,
`GoodConfig3H.lean`), the flat identity instantiation
(`Metatheory/FlatGeneric_Bridge.lean`).

---

## 1. The combinator, precisely

### 1.1 The signature `D₁ ⊗ D₂ : ConditionedMRDTSig`

| field | definition | provenance / obligation |
|---|---|---|
| `State` | `S₁ × S₂` | — |
| `dec_state` | product of `dec_state₁`, `dec_state₂` | instance derivation |
| `init` | `(init₁, init₂)` | — |
| `AppOp` | `A₁ ⊕ A₂` | — |
| `dec_op` | sum of `dec_op₁`, `dec_op₂` | instance derivation |
| `Query` | `Q₁ ⊕ Q₂` | (Peritext extends this — §3.4, §4) |
| `Value` | `V₁ ⊕ V₂` | — |
| `update` | `upd⊗ s e := match e.2.2 with `<br>`  inl o => (D₁.update s.1 (e.1,e.2.1,o), s.2)`<br>`  inr o => (s.1, D₂.update s.2 (e.1,e.2.1,o))` | **componentwise** — everything downstream rides on this |
| `merge` | `fun a b => (D₁.merge a.1 b.1, D₂.merge a.2 b.2)` | — |
| `query` | `inl q ↦ inl (D₁.query s.1 q)`; `inr` dual | — |
| `rc` | inl/inl ↦ `rc₁` of projections; inr/inr ↦ `rc₂`; **mixed ↦ `Either`** | mixed = `Either` is forced: cross pairs commute (§1.2), so any `Fst_then_snd` would violate `rc_non_comm_directional` |
| `mergeL` | `(mergeL₁ l.1 a.1 b.1, mergeL₂ l.2 a.2 b.2)` | — |
| `merge_init_slice` | componentwise from `merge_init_slice₁/₂` | the only *law field* of the structure; `rfl` if both components' are `rfl`, else `Prod.ext` of the two |
| `Inv` | `Inv₁ s.1 ∧ Inv₂ s.2` | — |
| `applicable` | `inl o ↦ applicable₁ (t,r,o) s.1`; `inr` dual | **componentwise** in the base combinator; §3 relaxes this (read-coupling) and traces exactly what breaks |

Component obligations named per lemma below; the structure itself demands
only `merge_init_slice`, which is free.

### 1.2 Two definitional facts (the load-bearing kernel)

**(D-cross) Cross-component pairs commute by `rfl`.** For `e : Op A₁`,
`f : Op A₂` and any product state `s`:

```
upd⊗ (upd⊗ s (ι₁ e)) (ι₂ f) = (D₁.update s.1 e′, D₂.update s.2 f′)
                             = upd⊗ (upd⊗ s (ι₂ f)) (ι₁ e)
```

Both sides *reduce* to the same pair: the first update produces an explicit
pair constructor, and the second update projects `.1`/`.2` off it, so no
product-eta is even needed. Hence `commutes⊗ (ι₁ e) (ι₂ f)` (the ∀-state
`CRDTSig.commutes` — note the quantifier ranges over the FULL cartesian
product `S₁ × S₂`, including component-states never jointly reachable; that
is fine, both sides are literally equal at every point) and a fortiori
`commutesOn⊗`. In Lean: `fun s => rfl` after destructuring the two payloads.
This is the checked answer to the brief's "beware: commutes is ∀-state
equality of PRODUCT states — check it actually holds definitionally": it
does, *because* `update` is componentwise; the moment an update or a
`doW`-guard reads the other component this fact dies (§2.5.2, §3).

**(D-proj) Same-side commutation is the component's.** For `a, b : Op A₁`:

```
commutes⊗ (ι₁ a) (ι₁ b)  ↔  commutes₁ a b
```

(⇐) both sides are `(D₁.update (D₁.update s.1 a′) b′, s.2)` up to the
rewrite by `commutes₁`. (⇒) instantiate the product hypothesis at
`(s₁, D₂.init)` and take `congrArg Prod.fst`. The (⇒) direction uses that
`S₂` is inhabited — `D₂.init` always is; no `Inv` needed.

---

## 2. The once-only lemmas

### 2.1 (F1) Projection

#### 2.1.1 Folds project

```
applySeq (D₁⊗D₂) s ρ = (applySeq D₁ s.1 (π₁ ρ), applySeq D₂ s.2 (π₂ ρ))
```

for every start state `s` and mixed list `ρ`. Induction on `ρ`: an `inl`
head steps component 1 and prepends to `π₁ ρ` while `π₂ ρ` is unchanged;
`inr` dual. **No commutation is used** — this identity, not an
exchange argument, is where "interleaving order between components cannot
matter" is discharged once and for all (consumed at F4(c)). ~30 lines.

Corollaries (each a one-liner over F1): folds of `ι₁`-lists act as
`(fold₁, id)`; `qapplicable⊗`-style guards evaluated at folds read
component folds.

#### 2.1.2 The binary core projects, field for field

Define `proj₁ : Emulation.Configuration (D₁⊗D₂).toCRDTSig →
Emulation.Configuration D₁.toCRDTSig`:

```
N₁ r := (C.N r).map Prod.fst      L₁ r := (C.L r).map (·↾₁)
vis₁ a b := C.vis (ι₁ a) (ι₁ b)
```

Every structural field, checked:

| field | transfer | note |
|---|---|---|
| `dom_eq` | ✓ | `Option.map` preserves `none`-ness both ways |
| `vis_src` | ✓ | `C.vis_src` yields `r, s ∋ ι₁ a`; then `L₁ r = some (s↾₁) ∋ a` |
| `vis_tgt` | ✓ | dual |
| `vis_causal` | ✓ | membership in `s↾₁` unfolds to membership of `ι₁ ·` in `s`; apply `C.vis_causal` |
| `timestamps_distinct` | ✓ | `ι₁` injective and timestamp-preserving: `a ≠ b ⟹ ι₁ a ≠ ι₁ b`, and `(ι₁ a).1 = a.1` |
| `vis_total_same_replica` | ✓ | `ι₁` replica-preserving; product totality restricted |

Consequences: `(proj₁ C).events = (C.events)↾₁` and
`(proj₁ C).vis = C.vis ∘ (ι₁ × ι₁)`, both definitional. ~100 lines.

#### 2.1.3 The ternary `Configuration` projects too

For the contract/safety layers (F5) the ranked store must also project:

```
ver₁ v := (C.ver v).map (fun (s, E) => (s.1, E↾₁))
head₁ := C.head     parents₁ := C.parents
```

| field | transfer | note |
|---|---|---|
| `causal_mono` | ✓ | timestamps preserved by `ι₁` |
| `parents_lt` | ✓ | unchanged |
| `ver_init` | ✓ | `(init.1, ∅↾₁) = (init₁, ∅)` |
| `head_coherent` | ✓ | `map fst ∘ map (proj) = map .1 ∘ map fst`; both sides chase to `N₁`/`L₁` |
| `ver_inv` | ✓ | `Inv⊗ = Inv₁ ∧ Inv₂ ⟹ Inv₁` of the first |
| `lca_events` | ✓ | preimage commutes with `∩`; `IsLCA` reads only `parents`, unchanged |

**Answer to the brief's trap-hunt ("identify any field that does NOT
restrict cleanly"): every field restricts cleanly; the projection is total
on configurations, with no reachability hypothesis.** What does *not*
transfer is reachability itself — see next.

#### 2.1.4 Reachability does NOT project (finding, drives the architecture)

A product `Step3.apply` of an `inr` op maps under `proj₁` to: same events,
same `vis`, same replica states — but a **fresh version is allocated whose
projected `(state, event-set)` duplicates the head's**. The component LTS
has no such stutter transition (its `apply` demands a fresh event). So
`proj₁` of a `(D₁⊗D₂)`-reachable configuration is in general *not*
`D₁`-reachable. Consequences:

* Component certificates usable by the product are exactly the
  **configuration-level** ones: `JoinLemma3` (∀-configuration — covers
  projections for free, reachable or not), `JoinLemma3At` under a
  configuration-predicate contract (queue), `EqJoinLemma3C`/`_H` (stated
  over abstract `(vis, events)` — even config-free), `SafetyStepOn`,
  `UpdateVCs`, the quotient VC bundles.
* Anything a component proved only "along its own reachability" (the RGA's
  `hHon`/GenDisc *supplies*, discharged by induction over RGA-`Step3`) must
  be **re-derived over the product LTS**. This is mechanical when the
  component's maintenance lemmas are per-step over `(vis, events)` — `inr`
  steps don't change the `proj₁` of either — but it is a real cost line
  (§2.5.6, §4).

This vindicates the repo's factoring: the per-configuration join hook and
configuration-predicate contracts are precisely the composable interface.

#### 2.1.5 Canonical states and causal folds project

Given `IsCanonicalState C ev (s₁, s₂)` with witness `ρ`:
`π₁ ρ` is Nodup, enumerates `ev↾₁` (roundtrip membership), respects
`loOn (proj₁ C) (ev↾₁)` (sublist-pairwise + the F3 edge transfer below), and
folds to `s₁` (F1). Hence `IsCanonicalState (proj₁ C) (ev↾₁) s₁`; dual for
`.2`. Identically, `CausalFold C S σ ⟹ CausalFold (proj₁ C) (S↾₁) σ.1`
(a sublist of a vis-respecting list vis-respects, since `vis₁` edges are
`vis` edges). ~80 lines with F3 in hand.

### 2.2 (F3) `loOn` localization

#### 2.2.1 The edge analysis

Fix `C` (product binary core), `ev`. Unfold `loOn C ev x y`:

* **Mixed pair (`x = ι₁ a`, `y = ι₂ b` or dual): no edge, ever.**
  Arm 1 needs `¬ commutes⊗ x y` — refuted by (D-cross). Arm 2 needs
  `rc⊗ x y = Fst_then_snd` — mixed `rc` is `Either` by definition. ∎
* **Same-side pair: `loOn C ev (ι₁ a) (ι₁ b) ↔ loOn (proj₁ C) (ev↾₁) a b.`**
  Arm 1: `vis` transfers definitionally; `¬commutes` both ways by (D-proj).
  Arm 2: the `vis`-negations and `rc⊗ = rc₁` transfer definitionally. The
  **absorber existential is the hidden-falsehood spot; both directions
  checked**:
  - (↓, product absorber-freeness to component): a component absorber
    `e₃ ∈ ev↾₁` with `vis₁ b e₃ ∧ ¬commutes₁ b e₃` lifts to the product
    absorber `ι₁ e₃ ∈ ev` (contrapositive of `commutes⊗ ⟹ commutes₁`,
    (D-proj)(⇒)). ✓
  - (↑, component absorber-freeness to product): a product absorber
    `e₃′ ∈ ev` with `C.vis (ι₁ b) e₃′ ∧ ¬commutes⊗ (ι₁ b) e₃′` **must be an
    `inl` event** — if `inr`, (D-cross) refutes `¬commutes⊗` — and then
    projects to a component absorber. ✓ ← this is where cross-commutation is
    load-bearing; with read-coupled updates this direction fails first.

So: `loOn` edges of the product are same-component only, and on each
component they coincide with the component `loOn` at the restricted set.
Immediate corollaries (~60 lines total):

* `respects ρ (loOn C ev)` transfers to `respects (π₁ ρ) (loOn (proj₁ C) (ev↾₁))`
  and conversely block-wise (used in F1/F4);
* enumerations of unions split: `π₁` of an enumeration of `ev₁ ∪ ev₂`
  enumerates `ev₁↾₁ ∪ ev₂↾₁`;
* `loOn`-maximality localizes: a `loOn`-maximal element of `ev↾₁` is
  `loOn`-maximal in `ev` among `inl` events, and cross-edges never disturb it.

#### 2.2.2 `UpdateVCs` inherits (a theorem: `updateVCs_prod`)

`UpdateVCs D₁ → UpdateVCs D₂ → UpdateVCs (D₁⊗D₂)`, field by field:

* `rc_non_comm_directional`: case-split. inl/inl: both sides transfer to
  component 1's instance ((D-proj), `rc⊗ = rc₁`, `distinctOps`/
  `differentReplicas` preserved by `ι`). Mixed: LHS `¬commutes⊗` is false
  (D-cross) and RHS is false (`rc = Either` both ways) — the iff holds
  vacuously-truthfully. inr/inr dual. ✓
* `no_rc_chain`: `rc⊗ o₁ o₂ = Fst_then_snd` forces `o₁, o₂` same-side (mixed
  is `Either`); two chained edges share `o₂`, hence all three ops are one
  component's; apply that component's `no_rc_chain`. ✓
* `cond_comm_lift`: the `rc`-edge and the `¬commutes` premise force
  `e, e′, e″` into one component `i`; project the equation with F1: the
  `i`-component is exactly component `i`'s `cond_comm_lift` at `s.i` with
  the filtered `πᵢ π`; the other component folds the *same* op list on both
  sides (`e, e′, e″` don't touch it) — equal by `rfl`-chasing F1. ✓

With `updateVCs_prod`, the entire σ/`loOn` layer
(`exists_loOn_respecting_perm_u`, `convergence_on_u`,
`isCanonicalState_unique_u`, …) is available at the product for free.
`rc_non_comm`-style instance facts (e.g. "add/rem same item don't commute")
stay componentwise by (D-proj); nothing new to prove per pair class.

### 2.3 (F4) Join gluing — the heart

#### 2.3.1 Statement

> **Theorem (`joinLemma3At_prod`).** Let `C` be a binary configuration of
> `(D₁⊗D₂).toCRDTSig`. If `JoinLemma3At D₁ (proj₁ C)` and
> `JoinLemma3At D₂ (proj₂ C)`, then `JoinLemma3At (D₁⊗D₂) C`.

Contracts thread through untouched: if the component joins hold only under
configuration predicates `H₁ (proj₁ C)`, `H₂ (proj₂ C)` (queue-style), the
product join holds under the conjunction — define
`H⊗ C := H₁ (proj₁ C) ∧ H₂ (proj₂ C)` and feed
`ra_linearizable3_of_honest_reach` at `H⊗`.

#### 2.3.2 Premise projection (the visNC-closure check, done carefully)

Given the product premises at `ev₁, ev₂ ⊆ C.events`, canonical
`s₀ = (s₀¹, s₀²)` at `ev₁ ∩ ev₂`, `s₁` at `ev₁`, `s₂` at `ev₂`:

* `vis₁`-transitivity/irreflexivity: restrictions of transitive/irreflexive
  relations. ✓
* `evᵢ↾₁ ⊆ (proj₁ C).events`: preimage monotone. ✓
* **visNC-closure projects.** Claim: product visNC-closure of `ev₁` gives
  component visNC-closure of `ev₁↾₁`. Take a component edge
  `vis₁ a b ∧ ¬commutes₁ a b` with `b ∈ ev₁↾₁`. Then `C.vis (ι₁ a) (ι₁ b)`
  (definitional) and `¬commutes⊗ (ι₁ a) (ι₁ b)` ((D-proj)(⇒),
  contrapositive), and `ι₁ b ∈ ev₁`; product closure puts `ι₁ a ∈ ev₁`,
  i.e. `a ∈ ev₁↾₁`. ✓ The direction consumed is "every component NC-edge is
  a product NC-edge" — which (D-proj) makes an *iff* on same-side pairs, so
  no strength is silently lost either. The suspected hidden falsehood is
  not here: it would appear only if a same-side pair could non-commute in
  the product while commuting in the component (impossible: (D-proj)(⇐) is
  componentwise `rfl`-rewriting) or vice versa (impossible by
  (D-proj)(⇒) + `S₂` inhabited). Cross edges are irrelevant to the
  *projection* direction; they would only matter if we tried to
  *reconstruct* product closure from component closures — which the gluing
  never does.
* Canonical states project (§2.1.5), and
  `(ev₁ ∩ ev₂)↾₁ = ev₁↾₁ ∩ ev₂↾₁`. ✓

#### 2.3.3 The witness: concatenation suffices

Apply the component joins: obtain `ρ¹` with `listPermOf ρ¹ (U↾₁)`,
`respects ρ¹ (loOn (proj₁ C) (U↾₁))`,
`fold₁ ρ¹ = m₁ := mergeL₁ s₀¹ s₁¹ s₂¹`, where `U := ev₁ ∪ ev₂`; dually `ρ²`,
`m₂`. Set

```
ρ := ι₁ ρ¹ ++ ι₂ ρ²
```

*No re-interleaving is needed.* Check the three obligations from the brief:

* **(a) permutation of the union.** Membership: every `x ∈ U` is `inl` or
  `inr` and lands in the matching block (roundtrip). Nodup: each block is a
  Nodup image under an injective map; the blocks are disjoint (different
  payload tags). ✓
* **(b) respects `loOn C U`.** `List.pairwise_append`: within `ι₁ ρ¹` —
  transfer `respects ρ¹` along the same-side iff (§2.2.1) via
  `pairwise_map`; within `ι₂ ρ²` dual; **cross pairs: the required
  `¬ loOn C U y x` holds outright** — `y` is `inr`, `x` is `inl`, mixed
  pairs have no edge in either direction (§2.2.1). This is why any
  component-order-preserving interleaving works and, in particular, the
  degenerate one. ✓
* **(c) folds to the product `mergeL`.** F1:
  `fold⊗ ρ = (fold₁ (π₁ ρ), fold₂ (π₂ ρ)) = (fold₁ ρ¹, fold₂ ρ²) = (m₁, m₂)
  = mergeL⊗ s₀ s₁ s₂`. The independence of the two components' folds is F1
  itself (no exchange argument; §2.1.1). ✓

Uniqueness cross-check: with `updateVCs_prod`, `isCanonicalState_unique_u`
pins the union's canonical state, so `(m₁, m₂)` is *the* canonical state —
the gluing cannot silently disagree with a differently-built witness.

#### 2.3.4 Closure-notion parametricity

The argument above never uses *which* closure the premises carry — premise
projection (§2.3.2) works verbatim for full vis-closure
(`∀ a b, vis a b → b ∈ ev → a ∈ ev` projects the same way, dropping the
NC-conjunct), and for any `ClosurePred`-indexed `𝒞` such that
`𝒞 (C, ev) → 𝒞ᵢ (projᵢ C, ev↾ᵢ)` (an obligation per closure notion, trivial
for `fullClosure` and for `wfGenFull` with componentwise `WfOpGen`). So
state the mechanized product join **three ways from one core lemma**
(the concatenation gluing §2.3.3, which is closure-free):

* `joinLemma3At_prod` (visNC premises — feeds `goodConfig3_merge_at`);
* `joinLemma3FAt_prod` (full-closure premises — for components that need
  full closure, e.g. Enable-wins-flag-like counters; `JoinLemma3F`,
  `VC_Set.lean:211`);
* `eqJoinLemma3CH_prod` (the `≈`/H form, §2.5.4).

#### 2.3.5 Adversarial check 1: queue ⊗ flat counter

`D₁ = Q` (direct join under `QHonestCore`, `MergeableQueue.lean:445`),
`D₂ = Counter` (`mergeL l a b = a + b − l`, CD-route certificate
`JoinLemma3 Counter`).

* Counter side: `JoinLemma3 Counter` is ∀-configuration; instantiate at
  `proj₂ C` — **reachability of the projection is not needed** (§2.1.4
  matters here: `proj₂ C` is generally unreachable for `Counter`'s own LTS,
  and that is fine). ✓
* Queue side: `q_join_at (hHon : QHonestCore (proj₁ C))`. The contract is a
  configuration predicate reading `(events, vis)` — both project
  (§2.1.2). Product contract:
  `H⊗ C := QHonestCore (proj₁ (core C))`, i.e. "every `inl`-deq names a
  vis-prior `inl`-enq". Its projection *is* `QHonestCore (proj₁ core C)`
  definitionally. ✓
* Capstone shape (the mechanization demo):

  ```
  theorem qc_ra_linearizable3 {C : Configuration (Q ⊗ Counter)}
      (hReach : HonestReach (Q ⊗ Counter) H⊗ trivial C) :
      IsRALinearizable3 C
  ```

  via `ra_linearizable3_of_honest_reach` with
  `hJoinAt := fun C' h => joinLemma3At_prod (q_join_at h) ((JoinLemma3.at counterJoin) _)`.
  Worked numerically in §5.2. ✓ Nothing in the gluing reads the contract's
  content — it receives the component joins under whatever implies them.

#### 2.3.6 Adversarial check 2: an RGA-like conditioned component

Attempt `D₁ = RGA_TF` (raw signature). **The gluing has nothing to consume:
the tombstone-free RGA has no `JoinLemma3At` certificate at the raw
signature** — its merges are correct only up to `≈` (the whole point of the
quotient layer; raw canonical-state equality is false for it). Two honest
routes:

1. **Product at the quotient layer (the right one).** The RGA's citable
   certificate is the bundle `(rgaEqEquiv′, WfOpA, rgaInvPresA, rgaCongVC′,
   rgaInvInvVCA, EqJoinLemma3C_H + GenDisc/HonJ supplies)`. §2.5 shows this
   bundle composes componentwise; the product capstone is
   `RA_linearizable_up_to_eq_H` at the product parameters. Peritext takes
   this route (§4).
2. **Product of quotient signatures** `QSig(D₁) ⊗ QSig(D₂)`: type-checks
   (a `QSig` is itself a `ConditionedMRDTSig`), but the RGA's join is not
   packaged as `JoinLemma3At (QSig …)` — it is `EqJoinLemma3C_H`, consumed
   inside the `GoodConfig3H` induction with full-closure + H-discipline +
   `WfOpGen` side conditions (`wfGenFull`), which plain `JoinLemma3At`
   cannot carry. Repackaging would re-prove the H-machinery. Rejected as
   the primary route; note also §2.5.3's iso friction.

Also checked: nothing in F4 breaks when a component's join needs *full*
closure — the F-variant (§2.3.4) covers it; the consumption site
(`goodConfig3_merge_at`) derives its closure facts from `ver_causal` (full)
anyway and can weaken per component.

### 2.4 (F5) Contract and safety lifts

#### 2.4.1 `GenHonest` (∀-enumeration honesty)

For componentwise `P⊗ (ι₁ e) s := P₁ e s.1` (dual for `inr`):

* **(⇐, free direction)** `GenHonest D₁ P₁ (proj₁ C)` ∧ dual ⟹
  `GenHonest (D₁⊗D₂) P⊗ C` — given a product enumeration `π` of
  `past⊗(ι₁ e)`, `π₁ π` enumerates
  `past₁(e) = (past⊗(ι₁ e))↾₁` (the identity holds because `vis₁`,
  `events₁` are restrictions), and `P₁ e (fold₁ (π₁ π)) = P⊗ (ι₁ e) (fold π)`
  by F1. ✓
* **(⇒)** needs, for each component enumeration `π¹` of `past₁(e)`, *some*
  product enumeration extending it — i.e. **enumerability of the `inr` part
  of the past** (append it in any order). Same side condition as
  `CausalPastEnumerable` (`GenHonest.lean:64`); holds in reachable
  configurations, kept as a hypothesis per the repo convention. With it:
  `GenHonest⊗ ⟺` componentwise on projections. ✓ (The caveat from
  `GenHonest.lean` stands unchanged: the ∀-form is only appropriate for
  fold-order-insensitive `P`; the product does not worsen or improve this.)

#### 2.4.2 `HonestApp` (∃-causal-fold honesty) — composes, via pinned extension

> **Lemma (pinned extension).** Let `vis` be transitive and irreflexive on
> a finite `X = X₁ ⊎ X₂` and let `ℓ₁` enumerate `X₁` respecting `vis`.
> Then some enumeration `ρ` of `X` respects `vis` with `π₁ ρ = ℓ₁`.

*Proof.* Let `R := vis ∪ (order of ℓ₁)`. Suppose a cycle; contract maximal
`vis`-runs by transitivity into single `vis`-edges, giving an alternating
cycle whose `ℓ₁`-steps have endpoints in `X₁` — hence every contracted
`vis`-edge in the cycle also runs between `X₁`-elements. But `ℓ₁` respects
`vis|X₁` and is linear on `X₁`, so `vis a b` (`a,b ∈ X₁`) implies `a`
before `b` in `ℓ₁`; the cycle becomes a strictly position-increasing cycle
in `ℓ₁` — absurd. (A cycle with no `ℓ₁`-step is a pure `vis`-cycle —
absurd by transitivity+irreflexivity.) `R` acyclic + finite ⟹ topological
sort; its `X₁`-restriction is a linear order containing `ℓ₁`'s, hence
equals it. ∎ (~150–250 lines mechanized, list-induction inserting
`X₂`-elements.)

> **Corollary (`honestAppOn_prod`).** If `HonestAppOn D₁ A₁ (proj₁ C)`,
> `HonestAppOn D₂ A₂ (proj₂ C)`, the causal pasts' opposite-side parts are
> enumerable, and `A⊗` is componentwise, then
> `HonestAppOn (D₁⊗D₂) A⊗ C`.

For `e = ι₁ e′`: component honesty gives a causal enumeration `ρ¹` of
`past₁(e′)` whose fold satisfies `A₁`. Pin `ℓ₁ := ρ¹`, extend over
`past⊗(e)` (pinned extension; only ONE side is pinned — the other side's
enumeration is free because `A⊗ (ι₁ e′)` does not read `.2`). The resulting
`ρ` is a product causal enumeration with `π₁ ρ = ρ¹`, so
`(fold ρ).1 = fold₁ ρ¹` (F1) and `A⊗ e (fold ρ)` holds. ✓ Note the semantic
reading: the issuing replica's actual head state IS a product causal fold
of `past⊗(e)`, so at `Step3` level the honesty is client-checkable exactly
as before — the lemma is only needed to *assemble* the configuration-level
predicate from per-component ones.

#### 2.4.3 `SafetyStepOn` is componentwise

> `SafetyStepOn D₁ I₁ A₁ → SafetyStepOn D₂ I₂ A₂ →
> SafetyStepOn (D₁⊗D₂) (I₁×I₂) A⊗`.

At an `inl` step `e = ι₁ e′` with prefix data `(E, S, σS, σP)`:

* the untouched component: `(upd⊗ σS e).2 = σS.2`, so `I₂` carries over
  verbatim — the brief's "untouched component unchanged" is definitional;
* the stepped component: every hypothesis projects —
  `E↾₁ ⊆ events₁` ✓; vis-closure of `E`, `S` projects (component edges are
  product edges) ✓; `e′ ∈ E↾₁`, `S↾₁ ⊆ E↾₁`, `e′ ∉ S↾₁` ✓; future-freeness
  and `past ⊆ S` restrict (contrapositives through `ι₁`) ✓;
  `CausalFold` projects (§2.1.5) with
  `(past⊗(ι₁ e′))↾₁ = past₁(e′)` ✓; `I₁ σS.1` from `I⊗ σS`,
  `A₁ e′ σP.1 = A⊗ e σP` ✓. Apply `SafetyStepOn D₁` at `proj₁ C`
  (configuration-level — no reachability, §2.1.4 again). ∎ (~120 lines.)

#### 2.4.4 `CausalCanonical` — the naive product statement is REFUTED

**Refuted formulation**: *"component causal canonical witnesses
re-interleave into one product causal witness."* Counterexample (4 events,
fully realizable):

* `r₁` issues `c = (1, r₁, inr γ)`; `r₂` merges from `r₁` (sees `c`), then
  issues `a = (2, r₂, inl α)` — so `vis c a`;
* `r₃` issues `b = (3, r₃, inl β)`, then `d = (4, r₃, inr δ)` — so
  `vis b d`; `r₂ ∥ r₃` never sync until a final merge registers
  `E = {a, b, c, d}`.
* `vis|E = {c→a, b→d}` (transitive, irreflexive; no same-component edges:
  `a ∥ b` in component 1, `c ∥ d` in component 2).

Component-1 causal witnesses of `E↾₁ = {a, b}`: both `[a,b]` and `[b,a]`
qualify. Component-2 likewise. Pin `ℓ₁ = [a, b]` and `ℓ₂ = [d, c]` (each a
legitimate causal-canonical witness its component's `CausalCanonical` may
hand us). A joint extension needs `a<b` (ℓ₁), `d<c` (ℓ₂), `c<a` (vis),
`b<d` (vis): cycle `a<b<d<c<a`. **No product causal enumeration extends
both.** ∎ The failure is the two-sided pinning; do not patch by weakening
(house rule) — the statement as posed is wrong.

**The sound repair (one-sided pinning).**

> **Proposition (`causalCanonical_prod_of_one_sided`).** If `GoodConfig3 C`
> (its `canonical` clause feeds the untouched component's fold below) and
> `CausalCanonical (proj₁ C)` hold, and `D₂` is all-comm with
> `rc₂ ≡ Either` (product versions project by §2.1.3, so `proj₁ C` has the
> versions `CausalCanonical` speaks of), then `CausalCanonical C`.

*Proof.* For a product version `(s, E)`: take component 1's witness `ρ¹`
for `(s.1, E↾₁)` (vis₁- and `loOn₁`-respecting, folds to `s.1`). Pin it;
extend over `vis|E` (pinned extension, §2.4.2). The result `ρ` linearizes
`vis`; respects `loOn⊗ (C, E)` because all `loOn⊗` edges are `inl/inl`
(mixed dead by §2.2.1; `inr/inr` dead by all-comm + `Either` — lift of
`loOn_empty_of_all_comm_u`) and `ρ`'s `inl`-order is `ρ¹`'s. Fold: `.1`
is `fold₁ ρ¹ = s.1`; `.2` is the fold of *some* enumeration of `E↾₂`, and
all-comm makes all folds of `E↾₂` agree (`applySeq_perm_of_all_comm` via
`perm_ext_iff_of_nodup`) with the projected canonical fold `s.2`
(supplied by `GoodConfig3.canonical` at the product + §2.1.5). ∎

When **both** components are rc-nontrivial/order-sensitive, product
`CausalCanonical` inherits the open status of `oq:causalcanon` (OQ8) — and
the counterexample above shows why no interleaving-based proof can close
it. Composition is **neutral** here: it neither creates the gate (a
two-sided-nontrivial product's safety was gated per component already —
BudgetCart's `bcart_version_inv_gated` situation) nor removes it. Record in
the note as a sharpening of OQ8, not a new open question.

Both-flat and flat-⊗-conditioned specializations are free: if both
components are all-comm + rc-Either, so is the product ((D-cross),
componentwise), and `causalCanonical_of_all_comm_rc_either` applies to the
product directly.

#### 2.4.5 `CausalCanonical`/`GoodConfig3` bookkeeping

`GoodConfig3 C` (product) projects clause-wise to `GoodConfig3`-*shaped*
facts at `projᵢ C` — canonical states project (§2.1.5), `vis` facts
restrict, `ver_events_sub`/`ver_causal` restrict — everything the
component-level obligations above consume. (Not needed as a standalone
theorem; the product safety metatheorem is just
`version_inv_on_of_causal_canonical` at the product with
§2.4.2–§2.4.4 supplying its hypotheses.)

### 2.5 (F6) The ≈-lift — scoped, with the pragmatic cut

#### 2.5.1 The product bundle is componentwise

Given `(E₁, W₁, hP₁, hC₁, hA₁)` for `D₁` and `(E₂, …)` for `D₂`, define
`E⊗ := ≈₁ × ≈₂` (conjunction on components), `W⊗ (ι₁ o) s := W₁ o′ s.1`
(dual), `WfOpGen⊗ (ι₁ o) := WfOpGen₁ o′` (dual). Obligation-by-obligation:

| obligation | product discharge | genuinely mixes? |
|---|---|---|
| `EqEquiv` | product of equivalences | no |
| `InvPres.inv_init` | pair of components' | no |
| `InvPres.inv_update` | `inl` op + `W⊗ = W₁` at `.1`: component 1 steps, `Inv₂` untouched | no |
| `InvPres.inv_mergeL` | componentwise | no |
| `CongVC.update_congr` | component congruence on the stepped side, carried `≈` on the other | no |
| `CongVC.mergeL_congr` | componentwise | no |
| `CongVC.query_congr` | sum query reads one side | no (until Peritext's cross query — §3.4) |
| `InvInvVC.wf_congr` | `W⊗` reads one side; component `wf_congr` + `Inv⊗ ⟹ Invᵢ` | no |
| `InvInvVC.applicable_congr` | componentwise `applicable` | **yes under read-coupling** (§3.2) |
| `WfOpReachable` | §2.5.5 | no |
| `EqJoinLemma3C_H` | §2.5.4 gluing | no |
| `hHon` (GenDisc/HonJ supply at reachable configs) | §2.5.6 | **reachability rerun** |
| `hHext`, `hHnil`, `hBA`, `hInvCong` | componentwise via F1 | no |

#### 2.5.2 `eqCommutesOn` localizes — with the W-componentwise trap

Cross pairs: `doW⊗ W⊗ (ι₁ e) s = if W₁ e′ s.1 then (upd₁ s.1 e′, s.2) else s`
— either branch leaves `.2` at `s.2`, so the subsequent `inr` guard
`W₂ f′ (·).2` evaluates identically in both orders; four guard cases, each
side literally the same pair; `eqCommutesOn⊗ (ι₁ e) (ι₂ f)` by reflexivity
of `E⊗`. **This is the one place the quotient layer is more fragile than
the raw layer: it needs `W` componentwise** (the raw (D-cross) needed only
`update` componentwise). `W` is the runtime-guaranteed wellformedness
(timestamp freshness, id-shape) — naturally componentwise; keep it so even
under §3's read-coupled `applicable` (which `doW` never reads). Same-side:
`eqCommutesOn⊗` on `inl` pairs ⟺ `eqCommutesOn₁` (⇐ componentwise with the
carried side reflexive; ⇒ instantiate `.2 := init₂` — needs `Inv₂ init₂`,
i.e. `hP₂.inv_init`, in scope ✓). Hence `loOnEq⊗` localizes exactly as
`loOn` did (§2.2.1 rerun with `eqCommutesOn` in place of `commutes`,
absorber analysis identical).

#### 2.5.3 `QSig(D₁⊗D₂, E⊗) ≅ QSig(D₁) ⊗ QSig(D₂)` — do not chase the iso

The carriers are canonically equivalent (quotient of a product setoid ≅
product of quotients) and the lifted operations correspond under it, but
the equivalence is not a Lean `Eq` of signatures, and transporting the
capstone across a sig-iso is gratuitous engineering. **Work directly at
`QSig(D₁⊗D₂, E⊗, W⊗, …)`** and never form `QSig₁ ⊗ QSig₂`.

#### 2.5.4 `EqJoinLemma3C_H` glues (easier than F4: no configuration at all)

`EqJoinLemma3C_H` is stated over an abstract `(vis, events)` pair
(`GenericEqQuotient_H.lean:60`). Set
`H⊗ ρ := H₁ (π₁ ρ) ∧ H₂ (π₂ ρ)`,
`HonJ⊗ vis ev := HonJ₁ vis↾₁ (ev↾₁) ∧ HonJ₂ vis↾₂ (ev↾₂)`,
`GenDisc⊗ vis ev := GenDisc₁ … ∧ GenDisc₂ …` (conjunctions of projections,
by fiat — the supply obligation moves to §2.5.6). Premise projection:
`vis↾ᵢ` trans/irrefl restrict; the distinct-timestamps premise restricts
(`ι` timestamp-preserving, injective); `fullClosureRel` projects (§2.3.4);
`Inv⊗ ⟹ Invᵢ`; `IsCanonicalStateEqH` projects: the witness's `π₁` is
Nodup/enumerates/respects-`loOnEq₁` (localization §2.5.2), carries
`H₁ (π₁ ρ)` by definition of `H⊗`, and its raw fold is `.1` of the product
fold (F1) with `E⊗ ⟹ E₁` on firsts. Apply the component `≈`-joins; glue by
concatenation: `respects loOnEq⊗` as in §2.3.3(b) (mixed `loOnEq` dead),
`H⊗ (ι₁ρ¹ ++ ι₂ρ²)` holds because `πᵢ` of the concatenation is `ρⁱ`
(roundtrip), and the fold clause needs **no congruence chasing**:
`fold (ι₁ρ¹ ++ ι₂ρ²) = (fold₁ ρ¹, fold₂ ρ²)` literally (F1), then
`E⊗`-componentwise. ∎

#### 2.5.5 `WfOpReachable⊗` from components

Needed: any Nodup, distinct-ts, all-`WfOpGen⊗` product enumeration `ρ` has
`WfChain⊗ W⊗ init⊗ ρ`. Small interleaving lemma: `WfChain⊗` at each prefix
demands (for an `inl` head) `W₁` at `.1` of the prefix fold = the fold of a
*prefix of `π₁ ρ`* (F1); `WfOpReachable₁` applied to `π₁ ρ` (Nodup,
distinct-ts, `WfOpGen₁` — all restrict) yields `WfChain₁ … (π₁ ρ)`, whose
steps are exactly those demands. One induction threading both component
chains through the mixed list (~80 lines). No mixing.

#### 2.5.6 What is genuinely NOT free: the reachability-derived supplies

`RA_linearizable_up_to_eq_H`'s `hHon` premise supplies `HonJ` at every
*reachable* configuration; the RGA discharges its `GenDisc`/`HonJ` supply
by induction over its own `Step3` (born accuracy → `genDisc2C_of_born`,
HonCore induction). By §2.1.4 this does not transfer. The product needs the
same supplies re-derived **over the product LTS**: `inl`-apply steps affect
`proj₁`'s `(vis, events)` exactly as RGA-apply steps do; `inr`-apply and
all other steps leave `proj₁`'s `(vis, events)` unchanged (stutters); so if
the component's maintenance is factored as per-step lemmas on
`(vis, events)` the rerun is a skeleton with trivial stutter cases —
otherwise it means re-threading the discharge files. Honest estimate for
the RGA: 500–1500 lines depending on how step-factored
`RGA_GenDisc_Assembly`/`RGA_Honest_Residual` turn out to be. **This, not
the mathematics, is the ≈-lift's cost center.**

#### 2.5.7 Verdict and the pragmatic cut

`≈ := ≈₁ × ≈₂` does give eq-quotient data for `D₁ ⊗ D₂`, and
`IsRALinearizable3Eq` composes in the only sense that type-checks: **the
product capstone is the generic `RA_linearizable_up_to_eq_H` instantiated
at the product parameters, consuming the two component bundles through the
once-only lemmas above** — it does not (cannot) consume the finished
component capstones, which are statements about component-LTS-reachable
configurations (§2.1.4). Every bundle obligation is componentwise; the two
true cost centers are (i) the supply rerun (§2.5.6) and (ii) sheer premise
plumbing (~10 premises × projection lemmas).

**Pragmatic cut, adopted:** mechanize the product ≈-lift first for
`≈₂ = Eq`, `W₂ = ⊤`, `Inv₂ = ⊤`, `H₂ = ⊤` — one quotiented component, the
flat side entering through `FlatGeneric_Bridge`'s identity bundles
(`eqOfEq`, `WTop`, `invPresTop`, `congVCEq`, `invInvVCTop`), whose
obligations are all `rfl`/trivial. This is *all Peritext needs* (RGA-TF
quotiented, mark store flat). The general `E₁ × E₂` adds no new ideas
(the proofs are symmetric) but doubles the plumbing; defer until a second
quotiented component exists.

---

## 3. The L2 read-coupling corollary

Now let contracts read **both** components while updates stay
componentwise: e.g. `applicable⊗ (ι₂ markOp) (s₁, s₂) :=` "the mark's
anchor chars are live in `s₁`" ∧ mark-side slack, and/or
`Inv⊗` a joint predicate.

### 3.1 Convergence (F4) is untouched — verified

The gluing (§2.3.3) reads: component joins (however certified), structural
`commutes`/`rc` (functions of `update`/`rc` only — unchanged), `loOn`
localization (needs only componentwise `update` — unchanged), F1
(unchanged). Contracts enter F4 solely as the hypothesis under which the
component joins are available (`H⊗ C → JoinLemma3At Dᵢ (projᵢ C)`), and a
cross-reading `H⊗` is still a product-configuration predicate — the
implication is per-instance, its *content* never inspected. So convergence
composes under arbitrary read-coupling. ✓ (Worth stating in the note: this
is the formal sense in which "convergence composes; safety needs a
transfer lemma" from `oq:compose` is correct.)

### 3.2 The quotient layer: one new mixed obligation

`qapplicable⊗`'s lift needs `InvInvVC.applicable_congr` for the
cross-reading guard: *"anchor liveness in `s₁` is `≈₁`-invariant on
`Inv`-states"* — a genuinely mixed VC, one per cross-read observation. For
the RGA's `≈` (observational equivalence of the char sequence) liveness of
a char id is plausibly `≈`-invariant, but it is a new per-instance proof,
not a product freebie. **Keep `W⊗` componentwise regardless** (§2.5.2):
`doW` reads `W`, not `applicable`, so `eqCommutesOn`/`loOnEq` localization
survives read-coupled `applicable` untouched.

### 3.3 Safety: the cross guard is BudgetCart's situation, squared

`SafetyStepOn` with a cross-reading `A⊗`: at an `inr` mark step, the
component-2 obligation receives a guard datum about `s₁` at `σP` and must
use it at `σS` — the extras `S ∖ past(e)` are concurrent events, which may
include **component-1 deletes of the anchor**. Exactly the queue-head-check
/ `BCartSpendMono` anti-stability shape (`GenericSafety` memo §4.2.3;
`BudgetCart.lean` §10): a referential-integrity invariant
("every live mark's anchors are live chars") is falsified by an honest
concurrent delete — a two-event refutation writes itself, so **do not pose
it**. The monotone-transfer escape hatch exists only for guards reading
grow-only cross observations ("char was ever inserted") — which a
tombstone-free component deliberately does not materialize. Peritext's
design answer is structural: drop the cross invariant, resolve at read time
(§3.4/§4). Honesty bookkeeping: under read-coupling, `HonestApp⊗` is
irreducibly a product-level contract (the guard reads a product fold), but
it stays client-checkable — the issuing replica holds the product state;
the §2.4.2 composition lemma is simply not applicable (and not needed).

### 3.4 Read-time coupling is free

Extending the product's `Query` with cross-reading queries (resolution)
touches **nothing** in §2: `JoinLemma3At`, `IsRALinearizable3`,
`SafetyStepOn`, the quotient join — none read `query`. The single
obligation it adds is `CongVC.query_congr` for the new query (must be
`E⊗`-congruent: resolution must answer `≈₁`-invariantly — same flavor as
§3.2's VC). This is the precise sense in which Peritext's "no update/merge
crossing; climb at read time" design makes the coupling free.

---

## 4. The Peritext instantiation sketch

Distinguish the **existing flat Peritext**
(`MRDT_Instances/Peritext/Peritext.lean` — production mirror: grow-only
chars + tombstones + grow-only mark records, all-comm, `rc ≡ Either`,
discharged through the flat bridge) from the target composite:

```
PeritextTF := RGA_TF ⊗ MarkStore
```

— live characters via the genuine tombstone-free path-carrying RGA
(conditioned, quotiented), marks in a separate OR-set-shaped store.

**MarkStore** (component 2; `ORSetCore` if the parallel agent lands it,
else clone BudgetCart §1–§8's Finset OR-set core):

* elements: mark records `(markId = (ts, rep) of the adding op, type,
  (startId, startPath, startSide), (endId, endPath, endSide))` — endpoint
  char **ids plus their recorded paths**, read off the issuer's RGA
  component at generation time (data, not references — the store never
  dereferences them);
* ops: `addMark …` inserts the record; `remMark key` removes all live
  records of the key (production OR-set semantics, state-dependent effect);
* `mergeL l a b = (l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)`; `rc`: add-wins on same
  key, else `Either`;
* certificates owed: the OR-set route — `CoreVCs3CD + FeasibleDeltaVCs3 +
  CDVC3 ⇒ JoinLemma3C` at full closure (mirror `ORSet.lean`/BudgetCart
  §1–§8; ~500–800 lines, largely transplantable), entering the quotient at
  identity via `FlatGeneric_Bridge`.

**Read-time resolution** (the composite's own layer): a query
`resolveMarks : Query` that, per mark record, climbs each endpoint's
recorded path to the nearest **surviving** character in the RGA component
and reports the resolved span set. Queries only; no update or merge reads
across (§3.4).

**What PeritextTF owes, exactly:**

1. **MarkStore certificates** (above). *New but formulaic.*
2. **The product instantiation** at the pragmatic cut (§2.5.7):
   `RA_linearizable_up_to_eq_H` at
   `(E₁ × Eq, W₁ × ⊤, hP⊗, hC⊗, hA⊗)` with `hJoinH⊗` glued from the RGA's
   `EqJoinLemma3C_H` and the MarkStore's flat join (through
   `eqJoinH_of_joinC`-style identity entry). *Small, given the kit.*
3. **The conjoined contract**: `HonestDelivery⊗` := the RGA's
   `HonestDelivery` read through `proj₁` (born accuracy + applicable
   delivery for `inl` events) — mark ops are unguarded for convergence.
   Plus the §2.5.6 rerun: relativize the RGA's `hHon`/`hBA`/`hHext`/GenDisc
   supplies to the product LTS (stutter cases for `inr` steps). *The cost
   center: 500–1500 lines.*
4. **Mark-anchor honesty** (contract only the read layer consumes):
   recorded endpoint paths were accurate at issue — the mark-side analogue
   of born accuracy. Not needed for convergence (the records are inert
   data); needed for any semantic theorem about resolution.
5. **The read layer** (optional, if semantic theorems are wanted):
   totality of climbing (terminates at root — from the RGA component's
   path-well-foundedness invariant, an `Inv₁`-shape fact), `≈₁`-congruence
   of resolution (§3.4's `query_congr` — REQUIRED if `resolveMarks` is a
   signature query, since the capstone's `CongVC` must cover it), and
   optionally a stability/intent theorem (e.g. resolution lands within the
   original span's surviving neighborhood under honest histories). *Genuinely
   new mathematics; 300–800 lines; separable.*

**What PeritextTF does NOT owe:** any re-proof of the RGA canon engine,
skeleton, or quotient machinery (reused as a bundle); RGA↔mark commutation
(definitional, (D-cross)); a cross referential-integrity safety theorem
(§3.3 — deliberately absent, by design); MarkStore-alone safety (would be
OQ8-gated exactly as BudgetCart, composition-neutral — out of scope).

**The ≈ story**: `≈ := ≈₁ × Eq`; the capstone statement reads "every
version's class is `qmk` of `(σ₁, m)` where `σ₁` is a raw RGA fold of a
`lo`-respecting linearization up to `≈₁` and `m` is the literal OR-set
fold" — the honest composite analogue of `rga_tombstone_free_ra_linearizable3_eq`.

**Lines saved.** The RGA_TF conditioned chain is ~35 files, order 15–20k
lines, all reused. The composite's new bill: product kit ~1.5–2.5k
(§5.5) + items 1–3 ≈ 1–2.3k + optional read layer. A from-scratch composite
would rerun an RGA-style development over `PtOp = RGAOp ⊕ MarkOp`, where
every case-split in every RGA lemma acquires mark cases — not a 20%
overhead but a full re-verification; realistically it would never be done.
Composition is not merely cheaper; it is the difference between feasible
and not.

---

## 5. Worked micro-checks, verdict, mechanization plan

### 5.1 Micro-check A: flat ⊗ flat (GSet ⊗ Counter)

`GSet`: `update` inserts, `mergeL l a b = a ∪ b`. `Counter`:
`update s = s+1`, `mergeL l a b = a + b − l`. Execution: `r₀` applies
`a = (1, r₀, inl (add 7))`; `r₁` (created, empty) applies
`k = (2, r₁, inr inc)`; merge `r₀ ← r₁`. `ev₁ = {a}`, `ev₂ = {k}`, LCA
`= v₀`, `ev₁ ∩ ev₂ = ∅`.

* `s₀ = (∅, 0)`, `s₁ = ({7}, 0)`, `s₂ = (∅, 1)`;
  `mergeL⊗ = (∅∪{7}... = {7}, 0+1−0 = 1) = ({7}, 1)`.
* Component joins: GSet at `proj₁` gives witness `[a′] ↦ {7}` =
  `mergeL₁ ∅ {7} ∅` ✓; Counter at `proj₂` gives `[k′] ↦ 1` =
  `mergeL₂ 0 0 1` ✓.
* Glue: `ρ = [a, k]`; no `loOn⊗` edges at all (mixed pair);
  `fold⊗ ρ = ({7}, 1)` ✓; the reversed concatenation `[k, a]` folds
  identically — cross-commutation observed concretely. ✓

### 5.2 Micro-check B: queue ⊗ counter with a live `QHonest` constraint

Events: `e₁ = (1, r₀, inl (enq 5))`; merge `r₁ ← r₀`;
`d = (2, r₀, inl (deq 1))` (applicable at `r₀`'s head: head `= (1,5)` ✓);
`c = (3, r₁, inr inc)`; final merge with
`ev₁ = {e₁, d}` (at `r₀`), `ev₂ = {e₁, c}` (at `r₁`),
`ev₁ ∩ ev₂ = {e₁}`. `vis`: `e₁→d`, `e₁→c`; `d ∥ c`.

* Contract: `H⊗` = `QHonestCore (proj₁ ·)`; holds — `d` names `e₁`,
  vis₁-prior ✓ (`vis₁` is the restriction; both are `inl`).
* Queue side at `proj₁`: `ev₁↾₁ = {enq, deq}`, `ev₂↾₁ = {enq}`, intersection
  `{enq}`. `s₀¹ = [(1,5)]`, `s₁¹ = []`, `s₂¹ = [(1,5)]`. `q_join_at`
  witness `ρ¹ = [enq] ++ [deq] ++ [] = [enq, deq]`; Peepul merge
  `qMergeL [(1,5)] [] [(1,5)]`: survivors-in-both of the LCA — tag 1 absent
  from branch a `[]` → l-part `[]`; a-news `[]`; b-news: tag 1 ∈ tags(l) →
  filtered out → `[]`. Merge `= []` = `fold₁ ρ¹` ✓.
* Counter side at `proj₂`: `ev₁↾₂ = ∅`, `ev₂↾₂ = {inc}`; `s₀² = s₁² = 0`,
  `s₂² = 1`; `mergeL₂ 0 0 1 = 1`, witness `ρ² = [inc]` ✓.
* Glue: `ρ = [e₁, d, c]`. Edges of `loOn⊗ (ev₁∪ev₂)`: only `e₁ → d`
  (vis ∧ same-tag enq/deq non-commutation, transferred by §2.2.1); `e₁`
  precedes `d` ✓; `c` cross — unconstrained. `fold⊗ ρ = ([], 1)` and
  `mergeL⊗ ([(1,5)],0) ([],0) ([(1,5)],1) = ([], 1)` ✓. Sanity: the
  interleaving `[e₁, c, d]` also works (cross pairs edge-free) and folds
  identically. ✓
* Necessity check: delete `e₁` from the history (a dishonest `d`) and the
  queue's own join fails exactly as before — the product does not
  manufacture honesty; `H⊗` is load-bearing where `H₁` was. ✓

### 5.3 Micro-check C: the F5 refutation execution

§2.4.4's 4-event execution, checked realizable step-by-step:
`r₁: c(ts 1, inr)` → merge `r₂ ← r₁` → `r₂: a(ts 2, inl)` gives `vis c a`;
`r₃: b(ts 3, inl)` then `r₃: d(ts 4, inr)` gives `vis b d`; merge
`r₂, r₃`-heads. `vis|E` is exactly `{c→a, b→d}` (no same-replica extras
among the four beyond these; transitivity adds nothing). Pinned pair
`ℓ₁ = [a,b]`, `ℓ₂ = [d,c]` yields the cycle `a<b<d<c<a`. Refutation stands
in a reachable configuration — not an artifact of adversarial `vis`. ∎

### 5.4 Refuted / rejected formulations (recorded per house rule)

1. **Two-sided re-interleaving for `CausalCanonical`** — FALSE (§2.4.4,
   §5.3). Repair: one-sided pinning; general two-nontrivial case is OQ8,
   composition-neutral.
2. **`QSig₁ ⊗ QSig₂` as the RGA-composition route** — rejected: the RGA's
   join is not a `JoinLemma3At (QSig)` and cannot be repackaged as one
   without carrying `wfGenFull`-style side conditions the hook doesn't
   admit (§2.3.6); the sig-iso to `QSig(D⊗)` is transport friction with no
   payoff (§2.5.3).
3. **"Component capstones compose"** — category error: the finished
   theorems quantify over component-LTS reachability, which does not
   project (§2.1.4). What composes is the certificate bundle.
4. **Cross referential-integrity invariants under read-coupling** — do not
   pose (§3.3): anti-stable under honest concurrency, the queue-head/
   `BCartSpendMono` failure shape reappears verbatim.
5. **Mixed `rc ≠ Either`** — not attempted: any mixed `Fst_then_snd` is
   outright inconsistent with `rc_non_comm_directional` at the product
   (cross pairs commute), so the combinator's mixed-`Either` is forced,
   not a choice.

### 5.5 Mechanization plan

**File: `Metatheory/Product.lean`** (raw layer; no imports beyond
`GenericSafety` + `VC_Set`):

| # | obligation | est. lines |
|---|---|---|
| O1 | `prodSig D₁ D₂ : ConditionedMRDTSig`, `ι₁/ι₂/opl/opr`, simp kit (`update_inl`, `rc_mixed`, roundtrips, `merge_init_slice`) | 150 |
| O2 | `applySeq_prod` (F1, arbitrary start state) + fold corollaries | 60 |
| O3 | `commutes_cross` ((D-cross), `fun s => rfl`), `commutes_inl_iff`/`inr_iff` ((D-proj)) | 60 |
| O4 | `Configuration.proj₁/proj₂` — binary core (9 fields) + `proj_events`, `proj_vis` | 120 |
| O5 | ternary `Configuration` projection (store fields) — needed only for F5/F6 plumbing; defer if F4-only | 150 |
| O6 | `listPermOf_proj`, `respects_proj`, `loOn_prod_inl_iff`, `loOn_prod_cross` (F3 edge kit, incl. absorber both directions) | 150 |
| O7 | `updateVCs_prod` | 120 |
| O8 | `isCanonicalState_proj` (§2.1.5), `causalFold_proj` | 80 |
| O9 | `canonical_glue` (concatenation lemma §2.3.3, closure-free core) | 120 |
| O10 | `joinLemma3At_prod` + `joinLemma3FAt_prod` (+ `ClosurePred` variant) | 200 |
| O11 | demo capstone `qc_ra_linearizable3` (queue ⊗ counter, §5.2's shape) — the executable adversarial check | 80 |

**File: `Metatheory/Product_Safety.lean`**:

| # | obligation | est. |
|---|---|---|
| O12 | `exists_extension_pinned` (§2.4.2 lemma) | 200 |
| O13 | `genHonest_prod_iff` (with enumerability), `honestAppOn_prod` | 120 |
| O14 | `safetyStepOn_prod` | 120 |
| O15 | `causalCanonical_prod_of_one_sided` + a `#check`-level record of the §2.4.4 refutation (kill-test file under `Refutations/` if desired) | 150 |

**File: `Metatheory/ProductEq.lean`** (≈-lift, pragmatic cut `≈₂ = Eq`
first):

| # | obligation | est. |
|---|---|---|
| O16 | bundle products `E⊗/W⊗/hP⊗/hC⊗/hA⊗` (§2.5.1 table) | 150 |
| O17 | `eqCommutesOn_cross`, `eqCommutesOn_inl_iff`, `loOnEq` localization | 120 |
| O18 | `wfOpReachable_prod` (interleaved `WfChain`) | 80 |
| O19 | `eqJoinLemma3CH_prod` (§2.5.4) | 250 |
| O20 | product capstone: `RA_linearizable_up_to_eq_H` premise-discharge wrappers (`hHext⊗`, `hBA⊗`, `hHnil⊗`, `hInvCong⊗`; `hHon⊗` left as the instance-supplied premise) | 200 |

Totals: raw kit O1–O11 ≈ 1.3k; safety O12–O15 ≈ 0.6k; ≈-kit O16–O20 ≈
0.8k. Peritext then owes §4's items 1–5 (MarkStore ~0.5–0.8k; supply
rerun ~0.5–1.5k; read layer ~0.3–0.8k, separable). Sequencing: O1–O11 with
the demo capstone first (it exercises F1/F3/F4 end-to-end against two
already-proven components); O16–O20 next (Peritext-critical); O12–O15 last
(no current instance is blocked on them).

**Note updates owed** (when mechanized): resolve `oq:compose` for the
binary product (map combinator remains open — the indexed generalization
of this memo, with `ι_k` per key and per-key `rc`, is the natural next
step and appears to be the same proofs with `Σ`-types); sharpen
`oq:causalcanon` with §2.4.4's counterexample and the one-sided-pinning
positive result.
