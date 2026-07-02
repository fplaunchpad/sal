> **NOTE (post-reorganization):** the Lean tree was restructured after T10.7 —
> canonical results now live in `../{Sigma_LoOn3, VC_Set, Adequacy,
> MRDT_Instances}.lean`; the peel route and the impossibility results are in
> this folder. File names below refer to the pre-reorganization layout;
> **all theorem names are unchanged** and searchable in the new files.

# MRDT metatheory — the ternary lift of the σ/Join-Lemma development (DRAFT)

*Findings-draft in the style of `FINDINGS.md` (A-series continuation; numbered T1–T7 to avoid
colliding with the concurrent A10 thread). Companion code:
[`LCA_Lemma.lean`](LCA_Lemma.lean) (N1 + ternary transition system),
[`Merge_Linearization_Set3.lean`](Merge_Linearization_Set3.lean) (σ-layer reuse + ternary Join
Lemma), [`RA_Lin_Of_Join3.lean`](RA_Lin_Of_Join3.lean) (end-to-end). Status markers updated to
the mechanization outcome at the bottom.*

## T0. Headline

The corrected 2-way metatheorem (`CoreVCs + JoinPeelVCs → RA-lin`, FINDINGS A5–A9) **lifts to
the ternary MRDT setting** (three-way `merge lca a b` over a version DAG — the paper's real
Theorem 2 setting). The honest decomposition of the lift:

1. **Genuinely new, ternary-only mathematics** — (i) the LCA lemma `L(v_⊤) = L(v₁) ∩ L(v₂)`
   as a store invariant, proved from an *event-origin* (generator-version) invariant that the
   paper asserts but does not maintain (T1); (ii) the ternary 0-OP peel `mergeL (update l e)
   (update a e) (update b e) = update (mergeL l a b) e` in which **the LCA argument is
   load-bearing, not inert**: the counter MRDT satisfies the ternary law and *provably
   violates* the binary `lem_0op` (T4) — so the ternary theory strictly extends the binary
   one even on the commuting class.
2. **Mild new bookkeeping** — threading the LCA event set `E₀ = E₁ ∩ E₂` through the Join
   induction: `E₀` is *invariant* under a local peel and *shrinks in lock-step* under a shared
   peel (a shared event **is** an LCA event) (T3).
3. **Verbatim reuse** — the entire `loOn`/convergence/canonical-state layer. Machine-checked
   sense of "verbatim": the ternary configuration's replica-keyed core *is* an
   `Emulation.Configuration D.toCRDTSig` (the `Configuration.core` projection), and
   `loOn`/`IsCanonicalState`/`convergence_on` etc. are **reused as-is** over `C.core`, not
   re-proved. Ternary-ness only touches `merge`.

## T1 (= mission N1). The LCA lemma: TRUE, from an origin invariant; the criss-cross defeats *enabledness*, not the lemma

**Statement.** In any configuration whose store satisfies the invariant bundle `StoreInv`
(below), for all `v₁ v₂ v_⊤` with `IsLCA parents v₁ v₂ v_⊤` and all three versions allocated,
`E(v_⊤) = E(v₁) ∩ E(v₂)`.

**The invariant bundle** (`StoreInv`, over the raw store `ver : Version → Option (Σ × Set Op)`,
`parents : Version → List Version` with ranked parents `p < v`):

* `edges_alloc` — DAG edges only connect allocated versions;
* `events_mono` — `p ∈ parents v → E(p) ⊆ E(v)` (Apply adds, Merge unions);
* `origin` — **the load-bearing one**: every event `e` of every allocated version has an
  *origin* (the paper's "generator vertex", appendix.tex Prop. `lca`): an allocated `v₀` with
  `e ∈ E(v₀)` and `∀ w. e ∈ E(w) → Reaches v₀ w`.

**Proof of the lemma.** ⊆: `events_mono` along `Reaches` (needs `edges_alloc` to keep the path
allocated). ⊇: `e ∈ E(v₁) ∩ E(v₂)` → its origin `v₀` reaches both `v₁`, `v₂` → by LCA clause
(ii) `v₀` reaches `v_⊤` → `E(v₀) ⊆ E(v_⊤)` ∋ e. No reachability induction needed at this
point: the induction lives entirely in maintaining `StoreInv`.

**Maintenance** (the paper's silent obligation). `origin` survives Apply because the paper's
Apply rule demands the fresh timestamp be fresh across **all versions' event sets**
(`∀ e' ∈ ⋃ range(L)` — note `L` in the paper is version-indexed; the 2-way Emulation TS's
replica-indexed freshness is strictly weaker and would *not* suffice for historical versions).
The fresh event's origin is the new version itself; old events keep their origin because the
fresh version's ancestors are exactly `{itself} ∪ ancestors(parent(s))` — the two DAG-extension
lemmas (`Reaches` into a fresh node decomposes through its parents; `Reaches` between old nodes
is unchanged because a fresh node is nobody's parent). Merge: `e ∈ E₁ ∪ E₂` → origin reaches
`v₁` or `v₂` → reaches the fresh `vm` through the new edge. **Machine-checked** in
`LCA_Lemma.lean` (`lca_events_of_storeInv`, `storeInv_apply_extend`, `storeInv_merge_extend`).

**The adversarial probe (criss-cross / multiple LCAs).** In the paper's semantics the Merge
rule *requires* `v_⊤ = LCA(H(r₁), H(r₂))` and the LCA, **when it exists, is unique** (LCA
clause (ii) makes any two LCAs reach each other; acyclicity — here the rank `parents_lt` —
forces them equal; mechanized as `isLCA_unique`). The criss-cross configuration (paper Fig.
LCA: two concurrent merges of the same pair, then merge the results; `v₁, v₂` maximal common
ancestors, neither dominating) does **not** refute the lemma — it makes the merge transition
*non-enabled*: there is simply no `v_⊤` satisfying `IsLCA`. So the criss-cross costs
**completeness** (some merges are blocked), never soundness. The paper's own repair is the
potential-LCA *recursive merge* (appendix "Recursive Merge Strategy"); that refinement is out
of scope here and is precisely scoped out by taking `IsLCA` as a premise of `Step3.merge`.

**Paper-gap verdict.** Lemma LCA itself is *sound* and its appendix proof sketch is the right
argument; the gaps are (i) "there will always be a unique generator vertex for each event" is
asserted, not proved — it needs the store-wide timestamp-freshness premise and an induction
maintaining the origin invariant (the mechanization's `StoreInv.origin`); (ii) the termination
hand-wave in Prop. lca's recursive descent ("decreasing events or unvisited vertices") is
replaced here by carrying the origin as an invariant, which needs no descent at all. Both are
erratum-sized, not holes.

**Design note (vacuity split).** Phase-0 baked `lca_events` into the `Configuration` structure
as a field. This makes the end-to-end induction consume it for free, but shifts the burden to
*maintainability*: if the field were unmaintainable, `Step3.merge` targets would not exist and
the soundness theorem would be vacuously true. `LCA_Lemma.lean` therefore proves the
maintainability content standalone, over raw stores (`lca_events_of_storeInv` + the two
`storeInv_*_extend` lemmas): any Step3-shaped store extension of a `StoreInv` store yields a
store satisfying both `StoreInv` and the `lca_events` field — merges are never blocked by the
invariant.

## T2 (= mission N2). The ternary Join Lemma

    JoinLemma3 D :  for backward-closed E₁, E₂ ⊆ C.events, with
                    σ(E₁ ∩ E₂) = s₀, σ(E₁) = s₁, σ(E₂) = s₂:
                    IsCanonicalState C (E₁ ∪ E₂) (D.mergeL s₀ s₁ s₂)

stated over the *binary core* configuration (so the whole A5/A6 σ-layer applies verbatim).
`E₀ := E₁ ∩ E₂` is automatically backward-closed (intersection of backward-closed sets), and by
T1 it is exactly the LCA version's event set, whose state — by the strengthened invariant — is
`σ(E₀)`. Note what this quietly settles: the paper's Merge case needs the LCA state to be a
linearization of `L(v_⊤)` *in the ambient configuration's order*; with the canonical-state
invariant carried for **every version in the store** (not just replica heads, T5) this is free.

## T3 (= mission N3). The ternary peel identities `JoinPeelVCs3`

For `e` maximal in `loOn C (E₁ ∪ E₂)`:

* `peel_local3` (`e ∈ E₁ \ E₂`, hence `e ∉ E₀`):
  `mergeL s₀ s₁ s₂ = update (mergeL s₀ t₁ s₂) e`, `t₁ = σ(E₁∖{e})`.
  The LCA set is **invariant**: `(E₁∖{e}) ∩ E₂ = E₀` because `e ∉ E₂`. The `e ∈ E₂∖E₁` case is
  the mirror via `mergeL_comm` (commutativity in the last two arguments) + `Set.inter_comm`.
* `peel_shared3` (`e ∈ E₁ ∩ E₂ = E₀` — a shared event **is** an LCA event): peel all three:
  `mergeL s₀ s₁ s₂ = update (mergeL t₀ t₁ t₂) e`, `t₀ = σ(E₀∖{e})`, `tᵢ = σ(Eᵢ∖{e})`.
  The LCA set shrinks in lock-step: `(E₁∖{e}) ∩ (E₂∖{e}) = E₀∖{e}`.

**The sub-set closure check** (mission's flagged worry): `E₀∖{e}` must be backward-closed for
the recursive call. The Emulation lemma `closure_diff_of_max` is already stated for an
arbitrary `ev ⊆ evU` with `e` only `loOn(evU)`-maximal — instantiate `ev := E₀`, `evU := E₁ ∪
E₂`; no new lemma needed. **Caution recorded**: a union-maximal shared `e` need *not* be
`loOn(E₀)`-maximal (loOn is antitone in the set, so `E₀`'s relation has *more* rc-edges — an
absorber in `(E₁∪E₂)∖E₀` disappears), hence `s₀ = update t₀ e` is **not** available to the
induction and must not be assumed — exactly the A3/A5 lesson recurring one level up; the peel
identities are stated over `t₀` as an independent canonical state, and the per-CRDT discharge
carries the burden.

**The master induction** (`join_lemma3_of_peel : CoreVCs3 D → JoinPeelVCs3 D → JoinLemma3 D`)
is the A6 induction with the LCA threaded: measure `|l₁| + |l₂|` unchanged (the `E₀`
enumeration never enters the measure — `t₀` is produced by `isCanonicalState_exists`); empty
sides collapse via `mergeL_init : mergeL init init s = s` (+ `mergeL_comm`), using `E₁ = ∅ →
E₀ = ∅ → s₀ = init`; re-attachment is the reused `isCanonicalState_snoc`.

## T4 (= mission N4). `CoreVCs3` — and why the LCA argument is *not* inert

Fields actually consumed (audited against the induction, not copied from the 2-way bundle):

| field | form | consumer |
|---|---|---|
| `rc_non_comm_directional`, `no_rc_chain`, `cond_comm_lift` | **unchanged** (update layer) | the reused σ-machinery |
| `mergeL_comm` | `mergeL l a b = mergeL l b a` | side-2 mirror, empty-side |
| `mergeL_init` | `mergeL init init s = s` | empty-side collapse |
| `lem_0op3` | `mergeL (update l e) (update a e) (update b e) = update (mergeL l a b) e` | shared peel, commuting class |
| `merge_peel_comm3` | `mergeL (fold π₀) (update a e) (fold π₂) = update (mergeL (fold π₀) a (fold π₂)) e` when `e` commutes with `π₀ ++ π₂` | local peel, commuting class |

Decisions the mission flagged, resolved:

* **Unit law.** The induction consumes only `mergeL init init s = s`. The paper's
  `MergeIdempotence` (`mergeL l s s = s`) is **not consumed anywhere** in the corrected
  σ-induction — in the 2-way development `merge_idem` was needed only by the *old* (unsound)
  witness-list induction's both-empty case. Audit finding for the paper: on the corrected
  proof route, idempotence is not a proof obligation of Theorem 2 (it remains a sanity law).
* **Does the LCA carry `e` in the 0-OP law? YES**, and this is load-bearing:
  a union-maximal shared event lies in all three sets, so all three canonical states can end
  in it. **Separation witness — the counter MRDT** (`State = ℤ`, `update s _ = s + 1`,
  `mergeL l a b = a + b - l`): the ternary law holds identically
  (`(a+1)+(b+1)-(l+1) = (a+b-l)+1`), while the binary slice `merge a b = a + b` **violates**
  binary `lem_0op` (`(a+1)+(b+1) = a+b+2 ≠ (a+b)+1`). Machine-checked
  (`Counter_coreVCs3` / `Counter_binary_lem_0op_false`). Consequence: the ternary commuting
  class **strictly contains** RDTs the binary metatheorem provably cannot host; "CRDTs are
  MRDTs that ignore the LCA" (paper results.tex:161) is *not* an equivalence — the counter is
  an all-commuting MRDT whose RA-linearizability is only reachable through the ternary bundle.
  (This also explains architecturally why `CoreVCs3` cannot require the binary `CoreVCs` of
  the init slice, and why the σ-layer had to be re-hosted on a merge-free fragment.)

## T5 (= mission N5). End-to-end

`GoodConfig3 C` = **every allocated version** `v` (not just replica heads — LCAs are
historical) satisfies `IsCanonicalState C.core (E(v)) (state(v))`, plus: `vis`-transitivity,
`vis`-irreflexivity, per-version causal closure of `E(v)`, and `E(v) ⊆ C.events` (both needed
because historical versions are no longer any replica's set: causal closure feeds the Join
Lemma's backward-closure premises, the events-bound feeds freshness at Apply). Transitions:
CreateReplica/Query trivial (canonicality depends only on `C.vis` — `isCanonicalState_congr`);
Apply = reused `isCanonicalState_extend` for the fresh version + `congr` for all old versions
(freshness of `e` against *store* event sets via the `E(v) ⊆ C.events` clause); Merge =
`JoinLemma3`, with the LCA premises supplied by the `Step3.merge` rule and
`E(v_⊤) = E₁ ∩ E₂` by the `lca_events` field (maintainability discharged in T1). Headline:

    ra_linearizable_of_core_join3 :
      CoreVCs3 D → JoinPeelVCs3 D →
      ReachableFrom (initConfig3 D hInit) C →
      ∀ v s E, C.ver v = some (s, E) →
        ∃ π, listPermOf π E ∧ respects π (lo C.core) ∧ applySeq D.init π = s

— per **version**, which strictly subsumes the per-replica statement via `head_coherent`.

## T6. The A3 defeater lifts to the ternary setting (with one staging replica)

The 2-way ferry construction (FINDINGS A3: `E₁ = {d,a,b}`, `E₂ = {b,c,d}`, forced side-orders
ending in `b` resp. `d`, union witnesses ending in `a` or `c` only) does not immediately
replay under the unique-LCA semantics: realized naively, the final merge's two heads have
common ancestors `{v₀, v_d, v_b}` with no dominator — **no LCA, merge disabled** (the
criss-cross again). The repair is one staging replica: let `r₃` merge `{d}` (from `r₁`) then
`{b}` (from `r₂`), realizing a version `v_{E₀}` with `E(v_{E₀}) = {b,d}`; let `r₁` and `r₂`
each merge `v_{E₀}` *after* their local `rem` (preserving the A3 vis-relation: only
`vis d a`, `vis b c`). Then `LCA(v₁, v₂) = v_{E₀}` exists (all five common ancestors reach
it), `E(v_{E₀}) = {b,d} = E₁ ∩ E₂` (T1 confirmed by hand on this instance), and the defeater
state of affairs is exactly A3's: every witness of `s₁` ends in `b`, every witness of `s₂`
ends in `d`, valid union witnesses end in `a`/`c` only, and no bottom-up peel of the paper's
0/1/2-OP ternary rules produces one. Since the paper's appendix Merge case (the text A3
analyzed) *is* the ternary proof, the ternary Theorem 2 proof is broken in exactly the same
way — now witnessed by a fully LCA-legal execution. The σ-level repair is T2/T3, as in A5.

## T7. The A8 separation lifts: `CoreVCs3 ⇏ JoinPeelVCs3`

Take the A8 separator `AWSetX` and make it an MRDT by ignoring the LCA:
`mergeLX l a b := mergeX a b`. Every `CoreVCs3` field transfers: the update/rc fields are
`AWSet`'s verbatim; `mergeL_comm`/`mergeL_init` are A8's `merge_comm`/`merge_init`;
`lem_0op3` at an inert `l` *is* binary `lem_0op` (the `update l e` on the LCA slot is
discarded); `merge_peel_comm3` likewise. The A8 5-event peel-failure configuration is
unchanged (its `E₀ = ∅`, so the LCA argument is `init` and inert throughout), so `peel_local3`
fails on the same instance. Hence `∃ D, CoreVCs3 D ∧ ¬ JoinPeelVCs3 D`, and — since `mergeLX`
inherits `mergeX`'s non-associativity — the sharpened open question is the ternary (b′):

> **Open (b′₃): does `CoreVCs3 D` + associativity of the induced binary join (+ ternary
> coherence laws relating `mergeL` at different LCAs, e.g. `mergeL l a b = mergeL l' a b` for
> `l, l'` canonical over the same event set) imply `JoinPeelVCs3 D`?**

The ternary twist worth recording: for MRDTs the natural lattice axiom is not associativity of
a binary join (the counter's `mergeL init a b = a + b` *is* associative but the counter is not
a semilattice — `merge_idem` fails: `a + a ≠ a`); the right ternary analog of "lattice VCs" is
itself an open design question, and the counter shows idempotence must **not** be assumed.

## Status of the mechanization (2026-07-02): all three files **0 `sorry`, kernel-clean**

| Piece | File | Status |
|---|---|---|
| `Step3`/`labeledTS3` (ternary LTS, `IsLCA`-gated Merge, store-wide freshness), `StoreInv` (parents-alloc / events-mono / **origin**), `lca_events_of_storeInv` (**N1 proved**), `isLCA_unique`, DAG-extension lemmas, `storeInv_{apply,merge}_extend`, `storeInv_reachable`, `merged/applied_store_lca_events` (maintainability / non-vacuity of the Phase-0 `lca_events` field) | `LCA_Lemma.lean` (625 lines) | ✅ 0 `sorry` |
| `Configuration.core` (the reuse projection), `UpdateVCs` + the σ-layer re-host (13 theorems, proofs verbatim from the 2-way file), `CoreVCs3`, `JoinLemma3` (**N2**), `JoinPeelVCs3` (**N3**), `join_lemma3_of_peel` (**master induction proved**), `joinPeelVCs3_of_all_comm` / `join_lemma3_of_all_comm` (**N6**), G-Set + Counter instances, `Counter_binary_lem_0op_false` (**the ternary/binary separation**) | `Merge_Linearization_Set3.lean` (1282 lines) | ✅ 0 `sorry` |
| `IsRALinearizable3` (per-version Def-lin), `GoodConfig3` (every-version canonicality + store closure facts), per-transition preservation, **`ra_linearizable_of_core_join3`** (**N5, the ternary A9**), end-to-end corollaries for G-Set and the Counter | `RA_Lin_Of_Join3.lean` (438 lines) | ✅ 0 `sorry` |

Axiom audit: headline theorems depend only on `[propext, Classical.choice, Quot.sound]`
(no `sorryAx` — the reused Emulation lemmas are all from the 0-sorry set-relative layer).

**What remains open (honestly):** the ternary analog of the A7 `AWSet` discharge (a
non-trivial-`rc` MRDT instantiating `JoinPeelVCs3` — the pattern σ-characterization →
trichotomy → set algebra should port, with the LCA component's characterization the only
new step), and the ternary (b′₃) of T7 — **answered in T8 below**.

---

# T8. (b′₃) ANSWERED: the ternary CD route exists — with a *delta* contract, not a lattice contract

*Code: [`JoinLemma_Of_CD3.lean`](JoinLemma_Of_CD3.lean) (0 `sorry`, kernel-clean). Lifts
[`Sal/CRDTs/Metatheory/JoinLemma_Of_CD.lean`](../../CRDTs/Metatheory/JoinLemma_Of_CD.lean)
(binary route B: `CoreVCs` + `LatticeVCsPlus` + `CDVC` ⇒ RA-lin).*

## T8.1 The theorem

    join_lemma3_of_cd : CoreVCs3 D → DeltaVCs3 D → CDVC3 D → JoinLemma3 D
    ra_linearizable_of_core_delta_cd3 : … → reachable C → IsRALinearizable3 C

with

* `DeltaVCs3` — **two unconditional laws** replacing the binary lattice triple
  (`merge_assoc`, `merge_idem`, `update_inflation`):
  - `local_redistribute` : `mergeL l (mergeL m x c) y = mergeL m (mergeL l x y) c`;
  - `redistribute` : `mergeL (mergeL m x₀ c) (mergeL m x₁ c) (mergeL m x₂ c)
    = mergeL m (mergeL x₀ x₁ x₂) c`;
* `CDVC3` — the single contextual per-MRDT obligation: for `e` `loOn(U)`-maximal,
  `A = σ(U∖e)`, `B = σ(↓e∖e)`:  `mergeL B A (update B e) = update A e`.

Discharged end-to-end for the **Counter** (the whole point — it satisfies no lattice law:
`mergeL l a a = 2a − l ≠ a`) and **G-Set**; the commuting class gets `CDVC3` free
(`cdVC3_of_all_comm`, via `merge_peel_comm3` at an empty LCA fold — and, unlike the
binary `cdVC_of_all_comm`, without consuming idempotence).

## T8.2 Why no order, and why CD3 is an equation (the binary/ternary asymmetry, part 1)

The binary route runs on `x ⊑ y := merge x y = y`: the principal case splits by
antisymmetry into a *free* half (`update_inflation` + `lem_0op`-monotonicity + the
absorption IH) and the *contextual* half (`CDVC`, an inequality — "half a peel"). For the
Counter every candidate ternary order **degenerates**: `x ⊑_l y := mergeL l x y = y` is
`x = l` (reflexive only at `l`); the self-relative `x ⊑ y := mergeL x x y = y` is
*always true* (total, no antisymmetry). So the free-half mechanism is order-theoretic and
does not survive the ternary lift: `CDVC3` must be (and is) a full **equation**. It
remains downset-relative — the per-CRDT burden is one identity relating `σ(U∖e)` to the
peeled event's own causal past, not the three-set `JoinPeelVCs3` equations (binary
precedent: `CD_AWSet.lean`, ~86 vs ~197 lines).

## T8.3 Idempotence, inflation, associativity all vanish (asymmetry, part 2)

The binary proof consumed `merge_idem` in exactly one spot — collapsing the shared
`σ(↓e) ⊔ σ(↓e)` when `e` sits on both sides. Ternary-ly, that collapse is performed by
the **LCA slot of `redistribute`**: with all three components decomposed as
`mergeL B tᵢ (update B e)`, the LCA-slot copy of the delta *cancels* the branch-slot
duplicate — `(x₁+δ) + (x₂+δ) − (x₀+δ) = (x₁+x₂−x₀) + δ` on the Counter. This is the
sharpest mechanized form of the T4 nugget: **the LCA argument structurally supersedes the
semilattice contract** — idempotence is not weakened but *replaced by LCA arithmetic*.
`update_inflation` disappears with the order; no associativity law is consumed at all.

## T8.4 The four-LCA associativity analysis (why associativity was the wrong target)

The naive "relative associativity" `mergeL l (mergeL l a b) c = mergeL l a (mergeL l b c)`
(common `l`) is derivable from `local_redistribute` (at `m := l`) + `mergeL_comm`, holds
for the Counter — and is *not* the associativity of the theory: a real execution's
re-association has **four distinct LCAs**, `l_ab = σ(E_a∩E_b)`,
`l_(ab)c = σ((E_a∪E_b)∩E_c)` vs `l_bc = σ(E_b∩E_c)`, `l_a(bc) = σ(E_a∩(E_b∪E_c))`. On the
Counter (state = signed measure of the event set) both sides equal
`a+b+c − (sum of two LCA states)`, and the two LCA-sums agree only by inclusion–exclusion
over `(E_a∪E_b)∩E_c = (E_a∩E_c)∪(E_b∩E_c)`: each side's LCA-sum is
`|E_ab| + |E_ac| + |E_bc| − |E_abc|` as a signed measure. So four-LCA associativity is a
**feasible-tuple law** (canonical states over an actual configuration), not a state
equation — over four unconstrained `l`-states it is false. The induction of
`join_lemma3_of_cd` therefore avoids associativity entirely: **every merge it forms sits
at its honest LCA** (`side_decomposition3` joins `E∖e` with `↓e` at
`σ((E∖e)∩↓e) = σ(↓e∖{e}) = B`; the IH-joins sit at `σ(E₀∖e)` or `σ(E₀)`), and the only
steps *equating* two such formations are the two redistribution laws.

## T8.5 The law-space carving, and dead candidates

A candidate ternary law survives the two mandatory instance families iff:
(i) **LCA-erasure test** — erasing all LCA slots yields an ACI-consequence (the LCA-blind
family: G-Set, any CRDT-as-MRDT); (ii) **ℤ-affine balance test** — the interpretation
`mergeL l a b = a + b − l` balances (the Counter). Killed on arrival:
* the rebase/cocycle law `mergeL l a b = mergeL m (mergeL l a m) b` — Counter ✓ but
  fails (i) (a spurious `m` survives erasure);
* the delta-cancellation law `mergeL (mergeL m x c) (mergeL m a c) b = mergeL x a b` —
  Counter ✓ but fails (i) (`c` dropped);
* delta-idempotence `mergeL m (mergeL m y c) c = mergeL m y c` — passes (i) but fails
  (ii) (`y + 2(c−m)`). Consequence: `redistribute` is NOT derivable from
  `local_redistribute` (any derivation route needs one of the dead laws); both are
  primitive.

## T8.6 The honest boundary of the unconditional contract (asymmetry, part 3 — the headline)

`DeltaVCs3` holds unconditionally for the two extreme classes:
* the **group instance** — `mergeL l a b = a ⊞ (b ⊟ l)` with translation-invariant
  deltas (Counter; any state group);
* the **lattice instance** — LCA-blind `mergeL l a b = merge a b` with `merge` ACI
  (every CRDT-as-MRDT).

It does **not** hold unconditionally for genuinely LCA-sensitive, non-group MRDTs: for
the classic untagged set-MRDT `mergeL l a b = (a∩b) ∪ (a∖l) ∪ (b∖l)`,
`local_redistribute` fails on the tuple "element in `c ∩ l` only" (LHS drops it, RHS
keeps it). Such tuples are infeasible for *tagged* elements (an element introduced by `e`
cannot already inhabit an LCA that excludes `e`), so the law is plausibly true on
**feasible (canonical) tuples** — but then it is a contextual VC, not an algebraic law.
Together with T8.4 this is the sharp (b′₃) asymmetry:

> **The binary route-B contract (`LatticeVCsPlus`) is unconditional for every real
> state-based CRDT. The ternary contract is unconditional exactly on the group ⊕ lattice
> (delta-monoid) classes; for general LCA-sensitive MRDTs the delta laws themselves
> become feasibility-conditioned — the "algebraic" part of the ternary theory is
> irreducibly contextual.**

(On the two-sorted delta-monoid umbrella `mergeL l a b = a ⊞ (b ⊟ l)`:
`local_redistribute` follows from ⊞ ACI alone, but `redistribute` needs *either*
translation-invariance of `⊟` (group instance) *or* ⊞ idempotent with `⊟ = id` (lattice
instance) — the umbrella does not derive the contract uniformly, which is why `DeltaVCs3`
takes the two laws as primitive rather than postulating the two-sorted structure.)

## T8.7 Status and the next questions

| Result | Status |
|---|---|
| `DeltaVCs3`, `CDVC3`, `side_decomposition3`, `join_lemma3_of_cd` | ✅ 0 `sorry` |
| `cdVC3_of_all_comm`, `ra_linearizable3_of_join`, `ra_linearizable_of_core_delta_cd3` | ✅ 0 `sorry` |
| `Counter_deltaVCs3`, `GSet_deltaVCs3`, `Counter_joinLemma3_cd`, `GSet_joinLemma3_cd`, end-to-end `counter_ra_linearizable3_cd`, `gset_ra_linearizable3_cd` | ✅ 0 `sorry` |

**Open (b″₃):** (i) is `CDVC3` derivable from `CoreVCs3 + DeltaVCs3` (the ternary twin of
the binary open (b″))? (ii) For the LCA-sensitive non-group class: formulate the
feasible-tuple `DeltaVCs3` and drive the induction through it — **answered in T9 below**.
(iii) The delta-monoid classification: is every `DeltaVCs3`-satisfying `mergeL` a
torsor-like combination of a group part and a lattice part?

---

# T9. The real Sal MRDTs vs. the ternary contracts: the feasible route mechanized; all three production RDTs land strictly in the feasible class

*Code: [`Feasible_Delta.lean`](Feasible_Delta.lean) (the generic route, 0 `sorry`),
[`Instances_CD3.lean`](Instances_CD3.lean) (the three mirrors + class placements,
0 `sorry`). Ground truth: `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean`,
`Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_MRDT.lean`,
`Sal/MRDTs/Enable_Wins_Flag/Enable_Wins_Flag_MRDT.lean` (read-only; the discharged
objects are **faithful mirrors** — same Bool-function state carriers, same
`do_`/`merge`/`rc`; deviations documented in `Instances_CD3.lean`'s header: `decide`
normalization, kept Boolean association, `mysel`-semantics for the Enable-wins map).*

## T9.1 The feasible-tuple route ((b″₃)(ii), answered constructively)

`Feasible_Delta.lean` mechanizes the feasible contract and the generalized induction:

* **`CoreVCs3CD`** — the true *unconditional* core: the three update-layer fields +
  `mergeL_comm`. Nothing else survives at full generality (T9.3).
* **`FeasibleDeltaVCs3`** — `feasible_init`, `feasible_local_redistribute`,
  `feasible_redistribute`: the T8 laws (and the unit law!) quantified over canonical
  tuples at honest LCAs — each state is `σ` of a named backward-closed set, and every
  `mergeL` node of both trees of each law sits at the true LCA set of the sets it joins.
* **`join_lemma3_of_cd_feasible : CoreVCs3CD → FeasibleDeltaVCs3 → CDVC3 → JoinLemma3`**
  and the bridge `ra_linearizable_of_core_feasible_cd3`.
* **`feasibleDeltaVCs3_of_delta : CoreVCs3 → DeltaVCs3 → FeasibleDeltaVCs3`** — T8's
  unconditional route is a corollary (`join_lemma3_of_cd'`).

**The honest-LCA invariant survived formalization — definitionally, not as a threaded
invariant.** The feasible laws are stated over exactly the contexts the T8 induction's
call sites carry (side sets, downset, union-maximality, canonicality), and the
generalized induction consumes them with hypotheses already in scope — no new
threading, no strengthened motive. T8.4's claim ("every merge the induction forms sits
at its honest LCA") is cashed out as the three law-statements' set annotations, which
the induction supplies verbatim.

## T9.2 Class placement of the three production MRDTs (machine-checked)

| MRDT | LCA-sensitive | non-commuting | unconditional `DeltaVCs3` | class |
|---|---|---|---|---|
| OR-Set | ✅ `ORSet_lca_sensitive` | ✅ `ORSet_not_all_comm` | ❌ `ORSet_local_redistribute_false` | feasible |
| OR-Set-efficient | ✅ | ✅ | ❌ | feasible |
| Enable-wins flag | ✅ | ✅ | ❌ `EWFlag_local_redistribute_false` | feasible |
| (Counter, T8) | ✅ | all-commuting | ✅ | group |
| (G-Set, T8) | LCA-blind | all-commuting | ✅ | lattice |

All three are the **LCA-sensitive AND non-commuting** combination neither T8 instance
exercised — and none satisfies the unconditional contract: the T8.6 witnesses are
realized against the *actual* production merges (OR-Set: a tag in `c ∩ l` only;
Enable-wins: an inflated middle-LCA counter suppressing a genuine enable on one
association but not the other). The empirical (b″₃)(iii) picture is stark: **the
unconditional class = group ⊕ lattice exactly; every real LCA-sensitive MRDT examined
is strictly feasible-class.**

## T9.3 Even the unit and 0-OP laws are feasibility-bounded (why `CoreVCs3CD` is slim)

Two further machine-checked boundary facts forced the slim core:

* `EWFlag_mergeL_init_false` — the unit law `mergeL σ₀ σ₀ s = s` **fails** for the
  Enable-wins flag on the infeasible state "flag set, counter 0" (every reachable set
  flag has a positive counter). Hence `feasible_init` in the feasible bundle.
* `ORSet_merge_peel_comm3_false` — `CoreVCs3.merge_peel_comm3` **fails** for the
  OR-Set when the LCA fold already contains the peeled add's tag (infeasible: execution
  timestamps are fresh). The production OR-Set therefore does not even satisfy
  `CoreVCs3` as bundled — the CD-feasible route, needing only `CoreVCs3CD`, is the only
  route in this development that can host it.

The trajectory across A→T is monotone: binary lattice contract (unconditional for all
real CRDTs) → ternary delta contract (unconditional only for group ⊕ lattice) → real
MRDTs (only `mergeL_comm` + the update layer survive unconditionally). **The "algebra"
of MRDT merges is irreducibly execution-relative.**

## T9.4 What remains for the three end-to-end discharges (honest status)

The remaining per-RDT obligations are `FeasibleDeltaVCs3` + `CDVC3` + the update-layer
fields of `CoreVCs3CD`. The mathematical content is settled by hand (recorded so the
mechanization is scoped A7-pattern engineering):

* **σ-characterization** (one per RDT; the only substantial proofs). OR-Set:
  `(ts,x) ∈ σ(E)` iff `Add x@ts ∈ E` with **no `Rem x ∈ E` vis-after it** (concurrent
  rems lose — add-wins; the LCA plays the tombstone). Enable-wins, per replica `r`:
  counter = #Enables-by-`r` in `E`; flag iff some Enable-by-`r` has no vis-later
  Disable in `E`.
* **`CDVC3`**: `e = Add x` maximal — pure set algebra (`mergeL B A (B+t) = A+t` needs
  only tag-freshness `t ∉ B`). `e = Rem x` maximal — reduces to "every `x`-tag of
  `A = σ(U∖e)` lies in `B = σ(↓e∖e)`", by the trichotomy: a live `x`-add of `U∖e`
  cannot be concurrent with the maximal `e` (its rc-edge `e →rc a'` would be unabsorbed
  since `a'` is live, contradicting maximality) nor vis-after `e` (a vis-edge out of
  `e` contradicts maximality); hence vis-before, hence in `↓e∖e` and live there.
* **Feasible delta laws**: each side of each law is an honest-LCA join of canonical
  states, hence — by the semantic join computation the σ-characterization yields — `σ`
  of the same union; the two sides are equal because they compute the same set.
* **`cond_comm_lift`**: OR-Set — swapping `Rem x`/`Add x@ts` perturbs the state by at
  most the tag `(ts,x)`; every op preserves-or-erases the perturbation and the final
  non-commuting `e''` (= `Rem x`) erases it. Enable-wins — swapping Disable/Enable
  perturbs only replica-`rid`'s flag; counters never read flags; the final Disable
  erases it.

None of this is mechanized here (three A7-scale developments); **no end-to-end
discharge of the three is claimed**. The machine-checked results are T9.1–T9.3.

## T9.5 The Enable-wins "known-broken" sibling (report)

`Enable_Wins_Flag_MRDT_known_broken.lean` is the Sal paper's canonical counterexample
demo, kept to drive Plausible and the ProofWidgets visualizer: state = a **global**
`(Int × Bool)`; `Disable` keeps the counter; `merge_flag` is the same four-case rule
but against the single global counter. Per its own docstring, the **`inter_right_1op`
VC fails** (Plausible rediscovers a minimal failing execution) while the closed-form
laws hold — a DAG-level compositional bug. The production file repairs it by tracking
`(counter, flag)` **per replica** (a map keyed by `rid`), so "has this branch enabled
since the LCA" is answered per replica rather than against a global counter that
concurrent branches both inflate. Two flags for the record: (i) the broken file
nonetheless states `inter_right_1op := by sal` with no `sorry` — either the module is
outside the compiled roots, or `sal` closes the *stated, hypothesis-laden* form while
the semantic DAG-level property fails (consistent with the docstring; not adjudicated
here — that file builds with `maxHeartbeats 0`); (ii) in the production file,
`base_1op` is proved `by try sal` — if the module compiles, the `try` is redundant and
the proof real; if the module is outside the build roots, its VCs are unverified.
Worth a CI check either way. No RA-lin-relevant defect was found in the production
per-replica merge by hand inspection; its failure of the unconditional delta contract
(T9.2) is expected feasible-class behavior, not a bug.

---

# T10. The capstone: the OR-Set discharged END-TO-END; the forcing corner for OR-Set-efficient; the Enable-wins recipe completed on paper

*Code: [`CD3_ORSet.lean`](CD3_ORSet.lean) (885 lines, **0 `sorry`**, kernel-clean),
[`CD3_ORSetE.lean`](CD3_ORSetE.lean) (0 `sorry`). Axioms:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.*

## T10.1 OR-Set: proved end-to-end

    ORSet_ra_linearizable3 : reachable C → IsRALinearizable3 C

via `CoreVCs3CD ORSet` + `FeasibleDeltaVCs3 ORSet` + `CDVC3 ORSet` and the feasible route
(`ra_linearizable3_of_join ∘ join_lemma3_of_cd_feasible`). **The first LCA-sensitive,
non-commuting real MRDT with kernel-checked RA-linearizability.** No contract refinement
was needed for the OR-Set: the T9 bundle fit as stated.

**The σ-facts** (in lieu of a monolithic A7 characterization — three lemmas pin canonical
states down to exactly what the discharge consumes):
* `ORSet_canonical_bound` — a live tag has an adding event in the set;
* `ORSet_live_no_later_rem` — a live tag admits no same-element `Rem` vis-after its add
  (the mandatory `vis∧¬commutes` edge + tag uniqueness by timestamp distinctness);
* `ORSet_no_later_kill_live` — an add with no same-element `Rem` vis-after it is live
  (a concurrent rem's rc-edge is forced before the add exactly because it is unabsorbed).

**One-line σ-characterization**: `(ts,x) ∈ σ(F)` iff `Add x@ts ∈ F` with no `Rem x ∈ F`
vis-after it — concurrent removes lose (add-wins); the LCA plays the tombstone.

**Structural bonuses found during the discharge:**
* the OR-Set merge is pointwise `if l then a ∧ b else a ∨ b`, so
  `feasible_redistribute` holds **unconditionally** (`orMergeL_redistribute`, a
  32-case Boolean tautology) — the OR-Set fails only `local_redistribute`, and only in
  its `Rem`-corner;
* `CDVC3`'s `Add`-maximal case is pure set algebra + tag freshness; the whole
  contextual burden concentrates in the **maximal-Rem trichotomy**
  (`ORSet_rem_max_trichotomy`): a live `x`-tag of `σ(U∖e)` under a maximal `Rem x` has
  its add vis-before `e` (vis-after breaks maximality by a vis-edge; concurrency breaks
  it by an unabsorbed rc-edge — unabsorbed precisely because the tag is live) and is
  live in the punctured downset;
* `cond_comm_lift` is a pointwise perturbation transport: the `Rem x`/`Add x` swap
  changes the state at most at the fresh tag, updates are pointwise, and the final
  non-commuting op erases the difference.

## T10.2 OR-Set-efficient: the machine-checked forcing corner (bundle refinement identified, not executed)

`ORSetE_rc_non_comm_directional_false`: the production OR-Set-efficient **falsifies the
`rc_non_comm_directional` field of `UpdateVCs` as stated** — same-replica, same-element
`Add`s with distinct timestamps do not commute (the later add evicts the earlier tag)
yet `rc = Either` both ways. Not an RDT defect: same-replica events are always
vis-comparable, and the production VC carries exactly the `get_rid o1 != get_rid o2`
guard that the inherited binary field dropped. **Refinement prescription** (audited,
sound): weaken the field by a `differentReplicas` premise; the σ-machinery's only `.mp`
use (convergence's overwriter step) has the guard in scope, and the only `.mpr` use
(`loOn_empty_of_all_comm_u`) is repaired by `vis_total_same_replica` (a same-replica
rc-edge demands `∥`, impossible). All existing instances satisfy the weakened field a
fortiori. With that, the ORSetE discharge is the `CD3_ORSet` recipe with a two-killer
σ-theory (live iff no vis-later `Rem x` AND no vis-later same-`rid` `Add x`), the
eviction case of the maximal-`Add` trichotomy closed by same-replica totality. Scoped;
not mechanized.

## T10.3 Enable-wins flag: the σ-recipe completed on paper (incl. one subtle trichotomy)

σ-characterization, per key `k`: `counter = #{Enables by replica k in F}`; `flag` iff
some Enable-by-`k` in `F` has no vis-later Disable in `F`. The delta laws' counter
components are inclusion–exclusion of enable-counts over honest LCA sets (ℕ-truncation
harmless: all subtractions are along set inclusions); the flag components and
`CDVC3`-Disable reduce to a trichotomy whose subtle half is: **under a maximal Disable,
a live flag at `k` forces *every* `k`-Enable into the downset** (the `k`-Enables are
totally vis-ordered — same replica; if the last one were outside the downset it would be
concurrent with the maximal Disable and its rc-edge unabsorbed — exactly the OR-Set
argument), hence `cnt_A = cnt_B` and the production `merge_flag`'s counter comparison
`a.1 > l.1` correctly returns false. This paper-proof settles that the production
per-replica merge rule is *correct* on the corner where its known-broken global-counter
sibling fails. Mechanization: the counting machinery (`List.countP` folds) is the only
new infrastructure; scoped, not done.

## T10.4 The empirical verdict on "one bundle for all three"

The T9 feasible bundle fit the OR-Set **unchanged**. The other two shapes each expose
one boundary, in different components: ORSetE breaks the *update layer* (the
`differentReplicas` guard — an rc-arbitration question), EWFlag breaks nothing stated
but concentrates its difficulty in *counting* σ-facts the set-shaped RDTs never needed.
The contract's architecture (slim unconditional core + feasible delta laws + one CD
equation) survived contact with all three; the per-RDT σ-characterization is confirmed
as the sole expensive artifact, exactly as in the binary A7 precedent.

---

# T10.5 (capstone continued): the OR-Set-efficient discharged END-TO-END; the guard refinement is a FIDELITY RESTORATION

*Code: [`CD3_ORSetE.lean`](CD3_ORSetE.lean) (1080 lines, **0 `sorry`**, kernel-clean).*

## The guard refinement, re-framed (provenance)

The `differentReplicas` guard added to `UpdateVCs.rc_non_comm_directional` (in
`Merge_Linearization_Set3.lean`; consumers repaired: the convergence overwriter step has
the guard in scope, `loOn_empty_of_all_comm_u` now kills same-replica rc-edges by
`vis_total_same_replica`) is **exactly the paper's own F\* artifact interface form**:
`_references/neem_fstar_repo/code/interface/App_mrdt.fsti:64` requires
`distinct_ops o1 o2 /\ get_rid o1 <> get_rid o2` for
`Either? (rc o1 o2) <==> commutes_with o1 o2`, and the OR-set-efficient instance
discharges the guarded form at `code/mrdts/OR-set-efficient/App_mrdt.fst:84`. The Lean
bundle's unguarded field was a transcription drop against the artifact (harmless for
every RDT examined before ORSetE); T10.2's "refinement" is a fidelity restoration, not a
new design decision. Regression: implemented inside the ternary tree's own `UpdateVCs`
(the binary `Sal/CRDTs/Metatheory/` tree untouched, its headline theorems trivially
unaffected); the full ternary chain incl. `ORSet_ra_linearizable3` rebuilt green with
statements unchanged (dischargers gain one intro).

## The ORSetE discharge

    ORSetE_ra_linearizable3 : reachable C → IsRALinearizable3 C

via `ORSetE_coreVCs3CD` (guarded update layer: for a non-commuting pair, the eviction
disjunct of the classification contradicts the guard, leaving the rc-ordered `Rem/Add`
case) + `ORSetE_feasibleDeltaVCs3` + `ORSetE_cdVC3` + the feasible route. σ-theory =
the OR-Set's with the **two-killer** notion `orEKills` (a tag `(rid, ts, x)` dies to a
`Rem x` or to a same-replica `Add x` — eviction), and one structural simplification:
ORSetE tags carry the replica id, so **the adder is determined by its tag** — the
uniqueness plumbing needs no timestamp distinctness at all. One-line σ-characterization:
`(rid,ts,x) ∈ σ(F)` iff `Add x@(ts,rid) ∈ F` with no killer in `F` vis-after it.
Genuinely new proof content vs. the OR-Set:

* the **concurrent-eviction case is closed by same-replica totality**
  (`ORSetE_no_later_kill_live`, `ORSetE_add_max_trichotomy`): an evicting add lives at
  the same replica as the evictee, so they are never concurrent — exactly why the
  production `rc` may soundly return `Either` on add/add pairs;
* the maximal-`Add` trichotomy (absent for the plain OR-Set, where `Add`-CD was pure
  set algebra): the evicted family of a maximal `Add x @ rid` behaves like the
  `Rem`-corner, with totality replacing the rc-edge;
* `cond_comm_lift` gains an evicting-final-op case (the perturbed tag is erased by the
  final same-replica add, whose own tag differs by `distinctOps`).

`feasible_redistribute` is again unconditional (`orEMergeL_redistribute` — same Boolean
tautology; the merge formula is unchanged).

# T10.6 Enable-wins flag: the honest residual (recipe mechanization-ready; one subtlety resolved)

Not mechanized (the remaining engineering is the per-key counting layer and a
flag/counter case analysis whose corners each consume a count-(in)equality lemma —
estimated at another `CD3_ORSetE`-scale file). The recipe, now fully de-risked on paper:

* σ-facts: `cnt(σF) k = #{Enables@k in F}` (fold/`countP` induction; count equalities
  across sets via nodup-enumeration lengths, `listPermOf_length_eq`); flag-(K): a set
  flag yields an enable with no list-later disable (reverse induction), converted to
  no *vis*-later disable by respects; flag-(L): the converse via the unabsorbed
  `rc(dis,en)`-edge argument.
* **The disable-trichotomy, corrected and strengthened**: under a maximal Disable, a
  live flag at `k` forces *every* `k`-enable into the downset — new subtlety found and
  resolved: for an enable `g` vis-*before* the live witness `a`, `g`'s own rc-edge
  against `e` can be absorbed by an old disable, so the direct maximality argument
  fails; instead `g ∈ ↓e` follows by **vis-transitivity through `a`** (`g → a → e`,
  with `a ∈ ↓e` by the unabsorbed-edge argument applied to the live `a`). Enables after
  `a` reach `↓e` by the absorber-plus-liveness contradiction; enables concurrent with
  `a` are impossible (same replica `k`). Hence `cnt_A(k) = cnt_B(k)` and the production
  `merge_flag`'s comparison `a.1 > l.1` correctly returns false — **the production
  per-replica merge is correct on exactly the corner where its known-broken
  global-counter sibling fails** (`inter_right_1op`); certifying this in Lean is the
  one remaining sentence of the three-candidate program.
* CD-enable needs one strict-count fact (`flagA ∧ ¬flagB → cnt_A > cnt_B`, via a
  live-witness outside the downset); CD-disable needs the trichotomy; the feasible
  laws' counter components are inclusion–exclusion over honest LCA sets (ℕ-truncation
  safe along set inclusions).

---

# T10.7 The Enable-wins flag discharged END-TO-END — via a direct FULL-CLOSURE join; the weak-closure contracts are provably insufficient for counter-comparison merges

*Code: [`CD3_EWFlag.lean`](CD3_EWFlag.lean) (1042 lines, **0 `sorry`**, kernel-clean).
**The three-candidate program is COMPLETE**: OR-Set, OR-Set-efficient, Enable-wins flag
all carry kernel-checked end-to-end RA-linearizability.*

## The route finding (the headline of this file)

Mechanizing the T10.6 recipe exposed that `JoinLemma3`/`CDVC3`'s **weak closure**
hypotheses (backward closure under `vis ∧ ¬commutes` only) are *insufficient* for the
Enable-wins flag: same-replica Enables commute, so weak closure cannot drag an earlier
Enable into a side containing a later one — and a weak-closure-legal tuple then defeats
the production `merge_flag` (a live enable in the LCA, a dead post-LCA enable inflating
one side's counter, the killing disable only on the other side: `a.1 > l.1` reports a
spurious enable-win). Under **full causal closure** — what `GoodConfig3.ver_causal`
actually supplies for every version — the defeater is impossible (the T10.6
transitivity argument becomes a closure step). So `CD3_EWFlag.lean` defines
**`JoinLemma3F`** (full-closure join), proves it for `EWFlag` **directly** (per key:
counters by inclusion–exclusion of enable-counts over nodup enumerations; flags by a
four-corner (K)/(L) liveness analysis), and lands end-to-end through the parallel
bridge `goodConfig3_mergeF`/`ra_linearizable3_of_joinF`. Sharp asymmetry for the
theory: **set-shaped MRDTs need only commutation-closure; counter-comparison MRDTs
read global causal structure and need full causal closure** — the contracts' closure
strength is itself RDT-class-dependent.

## The certification sentence (theorem-backed)

The `fa ∧ ¬fb` corner of `EWFlag_joinLemma3F` proves
`flag(σ(F₁∪F₂)) = true ↔ cnt₁ > cnt₀` — i.e. the production per-replica
`merge_flag`'s counter comparison `a.1 > l.1` computes **exactly union-liveness of the
flag**, the DAG-compositional property whose failure (`inter_right_1op`) is the
documented bug of the known-broken global-counter sibling
(`Enable_Wins_Flag_MRDT_known_broken.lean`). **The per-replica repair is hereby
verified on exactly the corner where the sibling fails.**

## Where the counting layer actually bit vs. the estimate

Lighter than estimated: no `countP` — filter-lengths over nodup enumerations
(`ew_filter_perm` + `listPermOf_length_eq`) gave monotone/strict/equal counts and
inclusion–exclusion (`N∪ + N∩ = N₁ + N₂` via the explicit union enumeration and a
12-line `ew_filter_split`) without arithmetic pitfalls (all ℕ-subtractions guarded by
inclusion inequalities, closed by `omega`). The genuinely new cost was not counting but
the **closure-strength discovery** above — the feasible/CD contracts were left
untouched and EWFlag bypasses them; whether a full-closure variant of
`FeasibleDeltaVCs3`/`CDVC3` reunifies all three discharges under one route is the
natural next question. Also recorded: the `differentReplicas` guard is **not**
load-bearing for EWFlag (no `rc = Either` non-commuting pairs; same-replica Enables
commute).
