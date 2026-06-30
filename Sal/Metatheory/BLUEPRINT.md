# Blueprint — Mechanising the Neem soundness meta-theorem

> **Target.** A single kernel-checked Lean theorem of the shape
> `∀ MRDT ⟨Σ,σ₀,do_,merge,rc⟩, (the 24 VCs hold) → (every reachable
> execution is RA-linearizable)`, with no pen-and-paper step in the trust
> base. Each RDT then earns its RA-linearizability theorem by composing its
> mechanised VCs (already done) with this meta-theorem.
>
> **Status legend.** ✅ exists & proved · 🟡 exists, partial/`sorry` ·
> 🔨 must be built · ⚠️ design decision / paper ambiguity to settle.
>
> This is a planning artifact. Lean signatures below are *targets*, not
> compiled code. Citations `file:line` point at grounded sources (paper
> `.tex` or existing Lean); everything else is design proposal, flagged.

---

## 0. Grounding: what the paper actually proves

The meta-theorem is **Neem Theorem 2** (`_references/Neem/lemmas.tex:238`,
proof `_references/Neem/appendix.tex:377`):

> If an MRDT `D` satisfies the VCs `ψ*(BottomUp-2-OP)`,
> `ψ*(BottomUp-1-OP)`, `ψ*(BottomUp-0-OP)`, `MergeIdempotence` and
> `MergeCommutativity` (and the global side-conditions `rc-non-comm`,
> `cond-comm`, `no-rc-chain`), then `D` is RA-linearizable.

Its abstract precursor is **Theorem 1** (`lemmas.tex:139`,
proof `appendix.tex:218`), stated over the *universally-quantified*
`BottomUp-X-OP` rules (Fig. `bottom-up`, `overview.tex` P1–P4 / P1′–P4′).
Theorem 2 replaces those rules with a per-event-set *induction scheme*
(Table `tbl:vc`, `lemmas.tex:151-225`) so the rules only have to hold on
*feasible* states — which is what makes them dischargeable per RDT.

The two supporting results the soundness proof leans on:
- **RA-linearizability** def — `lin.tex:400-405` (Def. `lin`).
- **Linearization relation `lo_C`** — `lin.tex:295-305` (Def.
  `lin-relation`).
- **Convergence** (any two `lo`-respecting sequences converge) —
  `lin.tex:392` (Lemma `convergence`), needs `rc-non-comm` + `cond-comm`.
- **`lo⁺` irreflexive** — `lin.tex:316` (Lemma `irreflexive`), needs
  `rc⁺` irreflexive.
- **LCA = event-set intersection** — `lin.tex:160` (Lemma `LCA`):
  `L(v_⊤) = L(v₁) ∩ L(v₂)`. This is what lets the merge VCs be stated over
  event sets.
- **Query soundness** — `lin.tex:410` (Lemma `query`).

The merge-case induction (the only hard case) is `appendix.tex:250-368`,
with the two structural lemmas `Lemma pi1` (`appendix.tex:117-178`) and
`Lemma pi2` (`appendix.tex:180-216`).

---

## 1. The meta-theorem statement (Lean target)

### 1.1 Scope decision ⚠️ (read first)

The existing `Sal/Emulation/` development is the **2-way-merge (CRDT)**
specialisation: `CRDTSig.merge : State → State → State`
(`Sal/Emulation/CRDT_Signature.lean:76`), no LCA, no version graph. Sal's
**MRDTs** — and the RGA conditioning that motivates this thread — use
**ternary** merge `merge : State → State → State → State` with an LCA
argument (`overview.tex:36`; e.g.
`Sal/MRDTs/OR_Set/OR_Set_MRDT.lean` `merge l a b`). The paper notes
(`results.tex:161`) CRDTs are the special case "ignore the LCA argument."

**Decision.** Target the **ternary MRDT** meta-theorem (Theorem 2) as the
headline. Reasons: (i) it is what per-RDT composition needs — Sal's MRDTs
are ternary; (ii) the conditioned-VC / RGA story is an MRDT story; (iii)
CRDTs fall out by instantiating `l := σ₀` (or `l := the LCA reconstructed
as the event-set intersection`). The 2-way `Sal/Emulation/` proofs are then
*reused* — `lo`, `SatisfiesVCs`, convergence, the carving — with the LCA
state threaded through as a third merge argument.

A lighter alternative (do CRDT-only first, defer ternary) is viable as a
*milestone* but does **not** close the per-RDT MRDT obligations. See §6.

### 1.2 Signature

Generalise `CRDTSig` to carry ternary merge (new file `MRDT_Signature.lean`,
modelled on `Sal/Emulation/CRDT_Signature.lean`):

```lean
structure MRDTSig where
  State : Type
  dec_state : DecidableEq State
  init : State
  AppOp : Type
  dec_op : DecidableEq AppOp
  Query : Type
  Value : Type
  update : State → Op AppOp → State                 -- do_  : Σ × (t,r,o) → Σ
  merge  : State → State → State → State             -- merge : Σ_⊤ × Σ₁ × Σ₂ → Σ
  query  : State → Query → Value
  rc     : Op AppOp → Op AppOp → RcRes

def MRDTSig.commutes (D : MRDTSig) (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁
```

### 1.3 The headline theorem

```lean
/-- **Neem soundness meta-theorem** (paper Theorem 2, lemmas.tex:238).
    Discharging the 24 VCs (+ the implicit extras, see §2.2) makes every
    reachable configuration RA-linearizable. -/
theorem ra_linearizable_of_vcs
    (D : MRDTSig) (hVC : SatisfiesVCs D)
    {C : Configuration D}
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C
```

with `IsRALinearizable` faithful to Def. `lin` (`lin.tex:402`); cf. the
2-way form already written, `Sal/Emulation/RA_Linearizability.lean:113`:

```lean
def IsRALinearizable (C : Configuration D) : Prop :=
  ∀ (r : Replica) (s : D.State) (E : Set (Op D.AppOp)),
    C.N r = some s → C.L r = some E →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (lo C) ∧ applySeq D D.init π = s
```

Corollaries to also state (cheap once the headline lands):
- `IsRALinearizableExec` over a whole execution (`RA_Linearizability.lean:121`).
- **Query soundness** (`lin.tex:410`): the value returned by any `query`
  transition equals `query (π σ₀) q` for a `lo`-respecting `π`.

---

## 2. The 24 VCs — enumeration and grouping

### 2.1 The canonical 24 (per-RDT theorem names ⇄ paper)

These field names already exist in `SatisfiesVCs`
(`Sal/Emulation/RA_Linearizability.lean:149`) and match the per-RDT theorem
names one-for-one (e.g. `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean:132-441`).

| # | Group | Lean field / theorem | Paper origin |
|---|-------|----------------------|--------------|
| 1 | **relational** | `rc_non_comm` | `rc-non-comm`, `lin.tex:387` |
| 2 | relational | `no_rc_chain` | `no-rc-chain`, `lin.tex:492` |
| 3 | relational | `cond_comm_base` | `cond-comm` base, `lin.tex:371` |
| 4 | **semilattice** | `merge_comm` | `MergeCommutativity`, `lemmas.tex:90` |
| 5 | semilattice | `merge_idem` | `MergeIdempotence`, `lemmas.tex:90` |
| 6 | **BottomUp-2-OP** | `base_2op` | `ψ^{L_⊤^b}_base`(2op), `tbl:vc` |
| 7 | 2-OP | `ind_lca_2op` | `ψ^{L_⊤^b}_ind` |
| 8 | 2-OP | `inter_right_base_2op` | `ψ^{L_2^b}_ind1` |
| 9 | 2-OP | `inter_left_base_2op` | `ψ^{L_1^b}_ind1` |
| 10 | 2-OP | `inter_right_2op` | `ψ^{L_2^b}_ind2` |
| 11 | 2-OP | `inter_left_2op` | `ψ^{L_1^b}_ind2` |
| 12 | 2-OP | `inter_lca_2op` | `ψ^{L_⊤^a}_ind` |
| 13 | 2-OP | `ind_right_2op` | `ψ^{L_2^a}_ind` |
| 14 | 2-OP | `ind_left_2op` | `ψ^{L_1^a}_ind` |
| 15 | **BottomUp-1-OP** | `base_1op` | `ψ^{L_⊤^b}_base`(1op) |
| 16 | 1-OP | `ind_lca_1op` | `ψ^{L_⊤^b}_ind`(1op) |
| 17 | 1-OP | `inter_right_base_1op` | `ψ^{L_2^b}_ind1`(1op) |
| 18 | 1-OP | `inter_left_base_1op` | `ψ^{L_1^b}_ind1`(1op) |
| 19 | 1-OP | `inter_right_1op` | `ψ^{L_2^b}_ind2`(1op) |
| 20 | 1-OP | `inter_left_1op` | `ψ^{L_1^b}_ind2`(1op) |
| 21 | 1-OP | `inter_lca_1op` | `ψ^{L_⊤^a}_ind`(1op) |
| 22 | 1-OP | `ind_left_1op` | `ψ^{L_1^a}_ind`(1op) |
| 23 | 1-OP | `ind_right_1op` | `ψ^{L_2^a}_ind`(1op) |
| 24 | **BottomUp-0-OP** | `lem_0op` | `ψ*(BottomUp-0-OP)` collapsed |

Grouping for the proof: **(1–3)** constrain `rc` and ground the `lo`
relation + conditional commutativity; **(4–5)** the semilattice laws used at
the leaves of the merge induction; **(6–14)** linearize the local-event
carving with `rc` ordering (the `BottomUp-2-OP` rule of Fig. `bottom-up`);
**(15–23)** the visibility-forced case where one branch's tail is an LCA
event (`BottomUp-1-OP`); **(24)** pushes a shared LCA event out of merge
(`BottomUp-0-OP`).

### 2.2 The 5 *implicit* extra VCs ⚠️ (surfaced finding — promote to a result)

The mechanisation discovered the paper's 24 are **not literally sufficient**:
the soundness proof silently uses 5 more properties, now extra fields of
`SatisfiesVCs` (`RA_Linearizability.lean:157-536`):

| Field | Why the 24 don't cover it | Vacuous when |
|-------|---------------------------|--------------|
| `rc_non_comm_directional` | convergence's overwriter step needs `¬commute → rc-ordered in *some* direction`, incl. same-replica pairs; the weak `rc_non_comm` only constrains the `Either`/different-replica case | `rc = Either` always (G-Set) |
| `cond_comm_lift` | `cond_comm_base` is the 3-event base; convergence needs the lift to arbitrary intervening sequences `π` (`lin.tex` cond-comm is stated semantically) | `rc o₁ o₂ = Fst` unsatisfiable |
| `merge_init` | `merge σ₀ s = s`; init is the lattice bottom — not derivable from VCs that always apply ≥1 `update` | — (lattice axiom) |
| `merge_peel_comm` | the all-commuting carving case; `ind_right_2op` needs `rc=Fst`, which never fires when everything commutes | non-trivial `rc` |
| `shared_peel_1op` | both branches share LCA event `ol`; every single-side VC needs `distinctOps` with the other tail, which fails for `distinctOps ol ol` | trivial `rc` |

**Action.** Either (a) prove each derivable from the 24 (likely impossible
for `merge_init` and the shared-peel ones — they are genuinely extra), or
(b) admit them as named hypotheses of the meta-theorem and re-discharge per
RDT (vacuous for the 14 `rc=Either` RDTs). The honest statement carries
**29** fields. *Documenting that the published 24 are incomplete is a
standalone Sal-paper contribution.*

---

## 3. Definitions inventory — exists vs. missing

### 3.1 Execution model (the replicated datastore `S_D`)

| Object | Paper | Lean status |
|--------|-------|-------------|
| Signature `⟨Σ,σ₀,do,merge,query,rc⟩` | `overview.tex:27` | ✅ `CRDTSig` (binary merge) `CRDT_Signature.lean:67`; 🔨 `MRDTSig` (ternary) — §1.2 |
| `commutes`, `appOpsCommute` | `lin.tex:231` | ✅ `CRDT_Signature.lean:89,93` |
| Configuration `⟨N,H,L,G,vis⟩` | `lin.tex:57` | 🟡 `Configuration` `CRDT_TS.lean:39` carries `N,L,vis` + 7 invariants; **no `G` (version graph), no `H`** (replica↦state directly), **no LCA**. Adequate for 2-way; 🔨 needs `G`+LCA for ternary (see §3.4) |
| Transition rules CreateBranch/Apply/Merge/Query | `lin.tex` Fig. `sem` | 🟡 `Step` `CRDT_TS.lean:101` — binary merge rule (`merge s₁ s₂`); 🔨 ternary merge rule needs `v_⊤ = LCA(...)` and `merge (N v_⊤) s₁ s₂` |
| `initConfig`, `labeledTS`, `Execution`, `Reachable` | `lin.tex:127` | ✅ `CRDT_TS.lean:147`, `Labeled_TS.lean:38-61` |
| Config invariants (causal closure, ts-distinct, vis-total-same-replica…) | implicit in paper | ✅ `CRDT_TS.lean:43-75` — `dom_eq, vis_src, vis_tgt, vis_causal, timestamps_distinct, vis_total_same_replica` (these are exactly the "every version is causally closed" + "unique timestamps" facts the appendix uses, e.g. `appendix.tex:61,362`) |

### 3.2 RA-linearizability + `lo`

| Object | Paper | Lean status |
|--------|-------|-------------|
| `lo_C` linearization relation | `lin.tex:295` Def `lin-relation` | ✅ `lo` `RA_Linearizability.lean:88` — faithful (vis∧¬commute) ∨ (concurrent ∧ rc ∧ no-overwriter) |
| `listPermOf`, `respects` (π extends lo) | `lin.tex:119` | ✅ `RA_Linearizability.lean:96,104` |
| `IsRALinearizable` (config), `…Exec` | `lin.tex:402,403` | ✅ `RA_Linearizability.lean:113,121` |
| `applySeq` (π(σ)) | `overview.tex:196` | ✅ `RA_Linearizability.lean:25` |
| `lo⁺` irreflexive | `lin.tex:316` Lemma `irreflexive` | 🔨 not separate; currently implicit in `respects = Pairwise (¬ lo · ·)`. Needs `rc⁺` irreflexive hypothesis on `D`. |
| Convergence (Lemma `convergence`) | `lin.tex:392` | 🟡 `convergence` `Merge_Linearization.lean:609` — **closed (Path 1)** over `ev = C.events`, consuming `cond_comm_lift` + config invariants |
| Query soundness | `lin.tex:410` Lemma `query` | 🔨 not started (easy corollary) |

### 3.3 The merge-linearization carving (the proof's combinatorial core)

All in `Sal/Emulation/Merge_Linearization.lean`, currently for **2-way**
(LCA collapsed to `init`, so `L_⊤ = ev₁ ∩ ev₂`):

| Object | Paper | Lean status |
|--------|-------|-------------|
| `L_top = ev₁∩ev₂`, `L₁_local`, `L₂_local` | `lemmas.tex:42` | ✅ `Merge_Linearization.lean:77-83` |
| `L_b` (depth-1-or-2 lo-path to L_⊤) | `lemmas.tex:43` | ✅ `:93` (depth-2 essential, audited `:293`) |
| `L_a` (complement) | `lemmas.tex:46` | ✅ `:103` |
| `L_top_a / L_top_b` | `lemmas.tex:45` | ✅ `:203,211` |
| `L_b_at e_⊤` (paper's `L_i^b(e_i^⊤)`) | `lemmas.tex:108` | ✅ `:254` |
| partition lemmas (∪ = whole, ∩ = ∅) | — | ✅ `:111-242` |
| `restrictTo`, `exists_lo_maximal_in_subset` | — | ✅ `:46`, PLAN.md step "lo-maximal element existence" |
| `Lemma pi1` (no lo from L^a to L^b) | `appendix.tex:117` | 🟡 `no_lo_a_to_b` `:473`, `no_lo_top_a_to_top_b` — **closed via Aristotle** (commits `15befe8`, `d8a20dc`), carry `h_distinct`, `h_ncomm_concurrent_local_top` hyps |
| `Lemma pi2` (ordering within S₂) | `appendix.tex:180` | 🟡 `no_lo_within_L_top_a` stub `:475` |
| BottomUp rules as Lean lemmas | Fig. `bottom-up` | ✅ `bottomUp_0op/1op/2op_*` (PLAN.md step 4) |
| `merge_linearization_exists` (the ∃-witness) | `appendix.tex:250` | 🟡 strong induction; both-empty ✅ (`merge_idem`), shared-last ✅ (`lem_0op`), asymmetric ✅; **distinct-last `sorry`** (`distinct_last_case`, 4 forward-closure-blocked sub-case `sorry`s at `Merge_Linearization.lean:2681,2852,2868,2874`) |
| `ra_linearizable_of_vcs` | Theorem 2 | 🟡 Merge-case discharge `sorry` (`Merge_Linearization.lean:4308,4311`); base/Apply/Query ✅. **Bridge total = 6 real `sorry`s** (these 2 + the 4 in `merge_linearization_exists`). Note: the op-side transfer `op_RA_linearizable_of_vcs` is a separate `True` placeholder (`Transfer.lean:67`) — thread 1's concern, not this bridge |

### 3.4 Missing for the *ternary* generalisation (🔨, this thread's new build)

- `MRDTSig` ternary merge (§1.2).
- Version graph `G` + head map `H` on `Configuration`, OR — cheaper — keep
  the event-set `Configuration` and **derive** the LCA state from the merge
  rule's premises, using **Lemma LCA** (`lin.tex:160`) to characterise
  `L(v_⊤) = L(v₁) ∩ L(v₂)`. The existing `L_top = ev₁∩ev₂`
  (`Merge_Linearization.lean:77`) *already encodes the LCA event set*; what
  is missing is an LCA *state* `l` and the proof it is reachable + carries
  exactly those events. **Recommend** the lightweight route: add an LCA
  state argument to the merge `Step` rule with the side-condition
  `L_⊤ = ev₁ ∩ ev₂` (justified once, by Lemma LCA), avoiding a full DAG.
- **Potential-LCA** recursion (`lin.tex:197`) — needed only if executions
  with no direct LCA are admitted. ⚠️ Decision: restrict to executions where
  every merge has an LCA (the paper's main development assumes LCA exists;
  potential-LCAs are a refinement). Flag as a scoping boundary.
- The three BottomUp rules in **ternary** form (the binary lemmas
  generalise by carrying `l`); the per-event-set ψ induction
  (`Table tbl:vc`) for each.

---

## 4. Proof skeleton — dependency graph

Nodes are lemmas; edges are "depends on". `[VC: …]` marks which of the 24/29
a node consumes. Status flags per §0.

```
                        ra_linearizable_of_vcs            ◀── headline 🟡
                                  │  (induction on execution length, appendix.tex:222)
        ┌───────────────┬────────┼─────────────┬──────────────┐
   base/CreateBranch   Apply    Merge        Query        (Lemma query)
        ✅               ✅       🟡 ◀───────    ✅            🔨
   initConfig_RA_lin   RA_lin_  RA_lin_preserved_merge
   (lin base)          preserved (= merge_linearization_exists destructured)
                       _apply
                                  │
                          merge_linearization_exists       ◀── the hard ∃ 🟡
                  (strong induction; appendix.tex:250-368)
        ┌──────────────┬─────────┴───────────┬─────────────────┐
   both-empty      asymmetric            shared-last        distinct-last 🟡
   ✅ merge_idem   ✅ merge_init/         ✅ lem_0op         (carving induction)
   [VC5]           merge_comm [VC4,29]   [VC24]                  │
                                                  ┌─────────────┼──────────────┐
                                            outer ind on   inner ind on   inner-inner ind on
                                            |L₁^a∪L₂^a|     |L_⊤^a|         |L_b_at e_⊤|
                                            (Case 1/2,      (Base/Ind 1,    (Base/Ind 1.1,
                                             appendix:288)   appendix:295)   appendix:319)
                                                  │              │               │
                                            BottomUp-2-OP   BottomUp-0-OP   BottomUp-1/2-OP
                                            [VC6-14]        [VC24]          [VC15-23]
                                                  └──────────────┴───────────────┘
                                                                 │
                                                    re-permute via convergence
                                                    + pick lo-maximal in carving layer
                                                                 │
                ┌────────────────────────────────┬──────────────┴────────────────┐
          convergence ✅            exists_lo_maximal_in_subset ✅        Lemma pi1 / pi2
          [VC: cond_comm_lift,      (restrictTo + last element)          (no lo A→B / within)
           rc_non_comm_directional]                                      [VC: no_rc_chain,
                │                                                         cond_comm, rc_non_comm]
        applySeq_swap_lo_incomparable ✅                                   🟡 pi1 ✅, pi2 stub
        applySeq_bubble_{to_front,lo_max} ✅
```

### 4.1 Node catalogue (name · statement · deps · status · approach)

**N1 `ra_linearizable_of_vcs`** — headline. *Stmt:* §1.3. *Deps:* N2–N5.
*Status:* 🟡 (Merge stub). *Approach:* induction on `Reachable` /
`Execution` length (`appendix.tex:222`); `Relation.ReflTransGen.head_induction_on`
or convert `Reachable`→`Execution` and induct on the list. CreateBranch/Query
re-use IH unchanged; Apply appends one event; Merge = N5.

**N2 base / CreateBranch** — ✅ `initConfig_RA_lin`
(`RA_Linearizability.lean:543`), `RA_lin_preserved_createReplica` (`:564`).
Witness `π = []` for the fresh replica; IH for old ones (vis unchanged ⇒ `lo`
unchanged).

**N3 Apply** — ✅ `RA_lin_preserved_apply` (`RA_Linearizability.lean:629`),
fully closed. *Key sub-lemma* `lo_shrink_under_apply` (`:601`): the fresh
event only adds vis-edges *into* it, so `lo` can only shrink on old pairs.
Witness `π_old ++ [e]`. Faithful to `appendix.tex:237-248`.

**N4 Query** — ✅ config unchanged ⇒ `exact ih`. *Plus* 🔨 the **query
soundness** corollary (`lin.tex:410`): trivial from `IsRALinearizable` at the
queried replica.

**N5 `RA_lin_preserved_merge` / `merge_linearization_exists`** — 🟡 the
∃-witness for the merged version. *Stmt (ternary target):*
```lean
theorem merge_linearization_exists
    (hVC : SatisfiesVCs D) {C : Configuration D}
    {l s₁ s₂ : D.State} {ev_⊤ ev₁ ev₂ : Set (Op D.AppOp)} {π₁ π₂ π_⊤ : List _}
    (h_lca : ev_⊤ = ev₁ ∩ ev₂)                      -- Lemma LCA
    (hπ⊤ : listPermOf π_⊤ ev_⊤) (hl : applySeq D D.init π_⊤ = l)
    (hπ₁ : listPermOf π₁ ev₁) (hr₁ : respects π₁ (lo C)) (hs₁ : applySeq D D.init π₁ = s₁)
    (hπ₂ : listPermOf π₂ ev₂) (hr₂ : respects π₂ (lo C)) (hs₂ : applySeq D D.init π₂ = s₂)
    (… reachability/closure invariants …) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C)
       ∧ applySeq D D.init π = D.merge l s₁ s₂
```
*Deps:* N6 (carving), N7 (convergence), N8 (lo-maximal), N9 (Lemma pi1),
N10 (Lemma pi2), VCs 4–24,29. *Status:* binary version 🟡 (`distinct_last`
sorry). *Approach:* the **triple-nested induction** of `appendix.tex:288-368`
— outer on `|L₁^a∪L₂^a|`, inner on `|L_⊤^a|`, inner-inner on
`|L_b_at e_⊤|` — peeling a `lo`-maximal event from a carving layer at each
step and re-permuting the source IH-linearizations via convergence.

**N6 carving partition** — ✅ (binary) `L_top/L_a/L_b/L_top_a/L_b_at`
(`Merge_Linearization.lean:77-271`). *Generalise:* take `ev_⊤` as a parameter
(= `ev₁∩ev₂`) instead of literal intersection — already parameterised.

**N7 `convergence`** — ✅ (Path 1). *Stmt:* `Merge_Linearization.lean:609`.
*Deps:* `cond_comm_lift`, `rc_non_comm_directional`, config invariants
`timestamps_distinct`/`vis_total_same_replica`/`vis_causal`. *Approach:*
bubble-sort; swap `lo`-incomparable adjacents (`applySeq_swap_lo_incomparable`
`:422`), discharging the different-replica ¬commute case with an explicit
overwriter found via the event-set's `vis∧¬commute` forward-closure.

**N8 `exists_lo_maximal_in_subset`** — ✅. Given a `lo`-respecting perm of
`S` and nonempty `T ⊆ S`, ∃ `e∈T` with no `lo`-successor in `T`. *Approach:*
`restrictTo π T |>.getLast`. Sidesteps a separate acyclicity argument (the
IH-perm already encodes it). Feeds peel-candidate selection from `M_i^a`,
`L_⊤^a` (`appendix.tex:323,342`).

**N9 `Lemma pi1`** — 🟡 (1) ✅ `no_lo_a_to_b`, (2) ✅ `no_lo_top_a_to_top_b`.
*Stmt:* no `lo_m` edge from `L^a` to `L^b`, nor `L_⊤^a` to `L_⊤^b`
(`appendix.tex:118,158`). *Deps:* `no_rc_chain` (VC2), `cond_comm` (VC3),
`rc_non_comm` (VC1), `vis`-transitivity + causal closure. *Risk:* both
carry an extra hyp `h_ncomm_concurrent_local_top` ("concurrent cross-set
events don't commute") — vacuous for trivial-`rc`, real content otherwise;
must be discharged per RDT or derived. **`no_rc_chain` is load-bearing**
(`lin.tex:464` Fig. `no-rc-chain` shows bottom-up *fails* with an rc-chain).

**N10 `Lemma pi2`** — 🟡 stub. *Stmt:* no `lo_m` among `L_⊤^a` events; and
across the `L_i^b(e_⊤)` buckets (`appendix.tex:181,203`). *Deps:* same as N9.
*Approach:* mirror N9's case explosion on the `lo` disjuncts; the rc-rc cases
die by `no_rc_chain`, the vis cases by causal closure of `L_⊤^a`.

**N11 (ternary-new) Lemma LCA** — 🔨. *Stmt:* in a reachable config,
`L(v_⊤) = L(v₁) ∩ L(v₂)` (`lin.tex:160`). *Approach:* induction on execution;
needed to justify the `h_lca : ev_⊤ = ev₁∩ev₂` premise of N5 from the version
graph. If we adopt the lightweight model (§3.4) this becomes the *definition*
and the obligation moves to the merge `Step` rule's well-formedness.

**N12 (ternary-new) BottomUp rules ternary form** — 🔨. Re-state
`bottomUp_{0,1,2}op_*` with the LCA state `l` threaded as the first merge
arg. The binary proofs port mechanically (`l` is inert in the binary
specialisation = `init`).

---

## 5. The conditioning issue (the §3-of-Ideas crux) ⚠️

### 5.1 The gap, concretely

The mechanised RGA VC is **weaker** than Neem's. From
`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean:928`:

```lean
theorem rc_non_comm' (o1 o2 : op_t) :
  (distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2)
  → (rc o1 o2 = rc_res.Either ↔ commutes_with' o1 o2)
```
where (`:331`)
```lean
def commutes_with' (o1 o2 : op_t) : Prop :=
  ∀ s, contains s 0 = false → accurate o1 s → accurate o2 s →
       fresh_ts o1 s → fresh_ts o2 s →
       eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)
```

vs. the meta-theorem's unconditioned `D.commutes o₁ o₂ := ∀ s, do(do s o₁)o₂
= do(do s o₂)o₁` (`CRDT_Signature.lean:89`). The conditions (`:319-327`):
- `accurate o s` — the op's recorded path *is* the true ancestor chain of
  its leaf in `s`;
- `fresh_ts o s` — an `Ins` uses a nonzero id absent from `s`;
- `contains s 0 = false` — the root sentinel is never a stored key.

The meta-theorem **cannot consume `rc_non_comm'` as-is** because `lo`,
convergence, and the BottomUp rules are stated with unconditioned
`commutes`. So the meta-theorem must be re-parameterised.

### 5.2 Design: applicability-conditioned meta-theorem

Add to the signature a per-RDT **applicability** predicate and a **state
invariant** (matching `Ideas.md` §2 sketch):

```lean
structure ConditionedMRDTSig extends MRDTSig where
  applicable : Op AppOp → State → Prop     -- per-RDT (= accurate ∧ fresh_ts ∧ root-pin)
  Inv        : State → Prop                -- reachability over-approximation

/-- Conditioned commutation: only required where both ops are applicable. -/
def MRDTSig.commutesOn (D : ConditionedMRDTSig) (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.Inv s → D.applicable o₁ s → D.applicable o₂ s →
       D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁
```

For flat-set RDTs set `applicable := fun _ _ => True`, `Inv := fun _ => True`
and `commutesOn` collapses to `commutes` — the framework reduces to today's,
so the 28 existing RDTs are unaffected.

The conditioned meta-theorem then requires a **reachability invariant
package**:

```lean
structure ReachInv (D : ConditionedMRDTSig) : Prop where
  init_inv     : D.Inv D.init
  do_preserves : ∀ s o, D.Inv s → D.applicable o s → D.Inv (D.update s o)
  merge_preserves : ∀ l a b, D.Inv l → D.Inv a → D.Inv b → D.Inv (D.merge l a b)
  -- every event generated in an execution was applicable at the head it hit
  events_applicable : ∀ C, Reachable … C → ∀ e ∈ C.events, ∃ s, … ∧ D.applicable e s ∧ D.Inv s
```

`ReachInv D` is proved **once per RDT** by induction on the execution
(the `apply` rule's premises already force applicability at generation
time; `merge`/`createBranch`/`query` add no events). It discharges every
`Inv`/`applicable` side-condition the soundness induction raises.

### 5.3 Where the conditions are invoked, and why reachable states satisfy them

Every state fed to `update`/`merge` *inside the soundness induction* is the
state of some **version generated in the execution** — hence `Inv`-satisfying
by `ReachInv.do/merge_preserves`. The induction runs over reachable
configurations (`appendix.tex:222`), so this is *structurally* where the
conditioning lives. Precise invocation sites:

1. **`lo`'s own definition** consults `¬ commutes e₁ e₂`. ⚠️ Decision: define
   `lo` with `commutesOn` (the *reachable-state* commute relation), keeping
   `lo` paper-faithful *on reachable configurations*. Justified because `lo_C`
   is only ever evaluated at events of a reachable `C`.
2. **`convergence` / `applySeq_swap_lo_incomparable`** (`:422`): the
   different-replica ¬commute swap. The two events are both in `C.events`,
   both applicable, and the intermediate fold state is `Inv` — so `commutesOn`
   fires.
3. **`cond_comm_lift` / `cond_comm_base`**: the overwriter swap. Same
   discharge.
4. **`BottomUp-2-OP` premise** `e₁→rc e₂ ∨ e₁ ⇄ e₂`: the `⇄` branch needs
   `commutesOn` at the merge-argument states (all `Inv`).

So the new proof obligation is purely: thread `Inv`/`applicable` through the
existing lemmas as extra hypotheses, and discharge them from `ReachInv` at
the top. No combinatorial change to the carving.

### 5.4 The `accurate`-staleness-under-delete risk ⚠️ (the real research point)

A `Del` **rehomes** nodes: it re-parents the deleted node's children to its
parent. So an op `e`'s recorded path `p` — captured when `apply` generated
`e` — can go **stale**: at a later version where an intervening `Del`
rehomed `e`'s anchor, `p` is no longer the true ancestor chain, so
`accurate e σ` may **fail at exactly the states the soundness proof needs**.
This is why "the VCs ⟹ RA-lin" is *not* obviously inherited by the
conditioned VC.

Two resolutions; **R2 is recommended and is half-built**:

- **R1 (invocation-restriction).** Prove commutation is only *needed* at
  states where the path is still accurate. Requires showing `accurate e ·`
  is preserved along the specific `update`/`merge` transforms the induction
  uses. Delicate precisely because `Del` breaks naive preservation —
  fragile, RDT-specific.

- **R2 (path-free-on-reachable).** The file already proves `do_` **ignores
  the recorded path on accurate states**: `ins_path_free` /
  `del_path_free` (`RGA_Tombstone_Free_MRDT.lean:84` `resolve`, `:455`
  `del_path_free`, `:488` "the path-carrying `Del` equals the path-free
  `doDelPF`"). `resolve` climbs to the **nearest live ancestor**, which is
  *exactly* what `Del`'s rehoming does — so the *effective* path is stable
  under deletes by construction. Therefore the reachability invariant to
  carry is not "paths stay accurate" but **`anc_consistent s`** (the `anc`
  pointers form a valid live forest, `contains s 0 = false`). On
  `anc_consistent` states, `do_ s o = doPathFree s o`, so `commutesOn`
  reduces to commutation of the path-free ops — which holds **un**conditionally
  on anc-consistent states. The conditioning is thus discharged by a clean
  forest invariant, not by freezing paths.

  > **⚠️ Update (machine-checked, `RGA_Reachability_Invariant.lean`).** R2 holds
  > for the **`do_` layer** but **not, as stated, for `merge`**. `anc_consistent`
  > (≈ `wf s ∧ contains s 0 = false`) *is* inductive under `init_st`/`do_`
  > (Ins+Del), proved `sorry`-free (`Inv_init`/`Inv_doIns`/`Inv_doDel`;
  > `Inv_doDel` is exactly the `Del`-rehoming case). But it is **refuted under
  > `merge`**: `merge_breaks_wf` exhibits `anc_consistent` states whose merge
  > violates `wf` — the merge's fuel-bounded `climb` (fuel = node id) runs out at
  > a deleted node, leaving a survivor anchored at an absent, non-root node.
  > `wf`-preservation under `merge` additionally needs **id-monotone anchors**
  > (`anc t < t`), which is **not** a `do_`-invariant under the abstract
  > `fresh_ts` — it is a **generation-time** property of monotone timestamp
  > allocation (a Phase-0 `ReachInv`/`applicable` obligation), not a pure state
  > invariant. The conditioning the RGA composition needs is `anc_consistent`
  > **plus** id-monotone allocation.

**Recommendation.** Adopt R2, **corrected per the result above**: set
`Inv := anc_consistent` (inductive under `do_`, proved) *and* strengthen
`applicable`/`ReachInv` to enforce **monotone timestamp allocation** (anchors
id-decreasing, so `climb`'s fuel suffices and `wf` survives `merge`), then prove
`ReachInv` for RGA. This makes the RGA composition go through *and* yields the
general lesson — now with a sharper edge: **conditioned VCs are sound exactly when
the conditioning predicate is a reachable-state invariant under do_/merge**, and
the RGA merge case shows that invariant can demand a *generation-time* condition
(id-monotonicity) no pure state-shape predicate supplies — the publishable
formalisation of `Ideas.md` §2/§3.

---

## 6. Decision points (flag list for the implementer)

1. ⚠️ **Ternary vs binary merge** (§1.1). *Recommend* ternary (`MRDTSig`),
   reusing `Sal/Emulation/` binary proofs as the `l := init` specialisation.
   *Milestone fallback:* close the binary CRDT bridge first (it is ~90% done).
2. ⚠️ **LCA modelling** (§3.4). *Recommend* lightweight: event-set
   intersection via Lemma LCA, no explicit version DAG. Full `G` only if
   potential-LCA executions are in scope.
3. ⚠️ **Potential-LCAs** (`lin.tex:197`). *Recommend* out of scope v1
   (restrict to executions where every merge has an LCA).
4. ⚠️ **The 29 vs 24 VCs** (§2.2). State the honest 29-field hypothesis;
   write up the 5 extras as a paper finding.
5. ⚠️ **`lo` over `commutesOn`** (§5.3). *Recommend* yes — paper-faithful on
   reachable configs, and keeps the existing carving untouched.
6. ⚠️ **R1 vs R2 for delete-staleness** (§5.4). *Recommend* R2.
7. ⚠️ **`h_ncomm_concurrent_local_top`** (N9) and the per-RDT discharge of
   the implicit VCs — vacuous for trivial-`rc`, must be supplied for
   non-trivial RDTs.

---

## 7. Phased plan

### Phase 0 — definitions / execution model (≈2–3 wks)
- `MRDTSig` (ternary merge) + `MRDTSig.commutes` (§1.2). 🔨
- Ternary `Configuration` / `Step` merge rule with `L_⊤ = ev₁∩ev₂`
  side-condition; port the 7 config invariants. 🔨
- **Lemma LCA** N11 (or fold into the Step rule). 🔨
- `lo`, `IsRALinearizable`, `applySeq`, `respects` — ✅ port verbatim from
  `Sal/Emulation/RA_Linearizability.lean`.
- `SatisfiesVCs` ternary (29 fields) — ✅ generalise existing struct.
- *Exit:* the headline statement (§1.3) type-checks with `sorry`.

### Phase 1 — key lemmas (≈3–5 wks; reuse Emulation)
- `convergence` N7 — ✅ port (binary→ternary inert).
- `exists_lo_maximal_in_subset` N8 — ✅ port.
- carving N6 + ternary BottomUp rules N12 — 🟡/🔨.
- **Lemma pi1 N9** — 🟡 port the two Aristotle proofs; discharge/justify
  `h_ncomm_concurrent_local_top`.
- **Lemma pi2 N10** — 🔨 close the stub (mirror N9's case explosion;
  `no_rc_chain` load-bearing).
- `lo⁺` irreflexivity (from `rc⁺` irreflexive) — 🔨.
- *Exit:* all merge-induction helpers proved; only the assembly remains.

### Phase 2 — the merge induction (≈4–8 wks; the hard part)
- `merge_linearization_exists` N5 — close `distinct_last_case` via the
  paper-faithful triple-nested carving induction (`appendix.tex:288-368`),
  replacing the re-permutation-blocked sorries (forward-closure dependency,
  PLAN.md). This is the single largest risk; it is also where thread 1's
  open work directly lands the CRDT half.
- Assemble `ra_linearizable_of_vcs` N1: execution induction binding
  N2/N3/N4/N5; add **query soundness**.
- *Exit:* headline kernel-checked, **no `sorry`**, for *unconditioned* VCs.

### Phase 3 — per-RDT reachability glue + conditioned VCs (≈3–6 wks)
- `ConditionedMRDTSig` / `commutesOn` / `ReachInv` (§5.2). 🔨
- Re-thread `Inv`/`applicable` through N5/N7/N9/N10 as hypotheses
  (mechanical once Phase 2 is closed). 🔨
- **RGA glue (R2):** `anc_consistent` invariant; `ReachInv` for
  `RGA_Tombstone_Free` from `ins_path_free`/`del_path_free`; compose →
  kernel-checked RA-linearizability for RGA. 🔨 *This is the thread's
  flagship demonstration.*
- Batch the unconditioned RDTs: instantiate `SatisfiesVCs` per RDT (mostly
  the existing 24 theorems + vacuous extras) and compose with N1.
  ✅-pattern exists (`Sal/Emulation/Instances/Grow_Only_Set.lean`); consider
  a macro.
- *Exit:* every RDT carries `theorem D_ra_linearizable : … RA-linearizable`
  by composition. Move the result to `README.md`'s catalog.

**Total:** ≈3–5 months focused (matches `Sal/Emulation/PLAN.md`'s estimate
for the overlapping work). Genuine risk concentrated in Phase 2 (the merge
induction) and Phase 3's R2 delete-staleness invariant.

---

## 8. Reuse map (what Phase 0–1 inherits from `Sal/Emulation/`)

| New (Metatheory, ternary) | Source (Emulation, binary) | Effort |
|---------------------------|----------------------------|--------|
| `MRDTSig` | `CRDT_Signature.lean:67` | +1 merge arg |
| ternary `Configuration`/`Step` | `CRDT_TS.lean:39,101` | +LCA state |
| `lo`, `IsRALinearizable`, `respects`, `applySeq` | `RA_Linearizability.lean:88,113,104,25` | verbatim |
| `SatisfiesVCs` (29 fields) | `RA_Linearizability.lean:149` | +`l` in merge VCs |
| `convergence`, swaps, bubbles | `Merge_Linearization.lean:366-1000` | `l` inert |
| carving (`L_*`), `exists_lo_maximal_in_subset` | `Merge_Linearization.lean:77-310` | parameterise `ev_⊤` |
| `Lemma pi1` (both parts) | `no_lo_a_to_b`, `no_lo_top_a_to_top_b` | port |
| Apply/CreateBranch/Query cases | `RA_Linearizability.lean:543-716` | verbatim |

The binary `Sal/Emulation/` work is therefore not throwaway: it is the
`l = init` slice of this blueprint, and closing its Merge `sorry`
simultaneously advances Phase 2 here.
</content>
