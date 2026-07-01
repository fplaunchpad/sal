# Neem Soundness Meta-Theorem — Lean Mechanisation Spec

**Status of this document.** Synthesis target for the design panel. It fixes, with
citations, (1) the precise statement of Neem's soundness meta-theorem (Theorem 2),
(2) the grouped VC list (24 paper VCs + 5 mechanization-only extras), (3) the proof
skeleton as a lemma DAG, and (4) the exists-vs-missing inventory — what the binary/CRDT
Lean already proves vs. what the ternary/MRDT metatheory still needs, including the
conditioning requirement (generation-time id-monotonicity).

All `file:line` citations were re-checked against the cited sources while writing.
Paper sources: `_references/Neem/{lin.tex, lemmas.tex, appendix.tex, overview.tex}`.
Lean sources: `Sal/Emulation/{RA_Linearizability.lean, Merge_Linearization.lean,
CRDT_TS.lean, CRDT_Signature.lean}`. Blueprint: `Sal/Metatheory/BLUEPRINT.md`.

**The single most important framing fact.** The existing `Sal/Emulation/` machinery is the
**binary / CRDT specialisation**: `merge : State → State → State`
(`CRDT_Signature.lean:77`), and the LCA is folded away — carried only as a shared event
prefix `ol` on both merge arguments, or sliced to `init`. The metatheory **target** is the
**ternary / MRDT** case `merge l a b` with an explicit LCA state `l`
(paper `lin.tex:140-142`; BottomUp rules `lemmas.tex:83-96`). Theorem 2 itself is stated
over ternary `merge`. So the binary Lean is the `l := init` (and `l := shared-prefix`)
instance of the target, not the target.

---

## Part 1 — The precise statement

### 1.1 System model the statement quantifies over

A **configuration** is the 5-tuple `C = ⟨N, H, L, G, vis⟩` (`lin.tex:245`, `:402`):
`N` maps versions→states, `H` maps replicas→head-versions, `L` maps versions→event-sets,
`G` is the version graph, `vis` the visibility relation. `E_C = ⋃ range(L(C))` is the
event set (`lin.tex:245-246`). Concurrency: `e₁ ||_C e₂ ≜ ¬(e₁ →vis e₂ ∨ e₂ →vis e₁)`
(`lin.tex:117-118`). Initial `C₀ = ⟨N₀,H₀,L₀,G₀,∅⟩`: one replica `r₀` at `σ₀`, no events
(`lin.tex:127-138`). `merge` is **ternary** `merge(σ_⊤, σ₁, σ₂)`, `σ_⊤` = LCA state
(`lin.tex:140-142`, `:31-33`).

Commutativity: `e ⇄ e' ≜ ∀σ. e(e'(σ)) = e'(e(σ))`; ops commute iff all their event
instances do (`lin.tex:231-235`). `rc` is defined only over non-commuting op pairs
(`lin.tex:235-236`).

### 1.2 The linearization relation `lo_C`

(Def. *Linearization relation*, `lin.tex:295-305`; verbatim Lean port `RA_Linearizability.lean:88-92`.)
For `e₁,e₂ ∈ E_C`:

```
e₁ →lo_C e₂  ⇔  (e₁ →vis e₂  ∧  ¬(e₁ ⇄ e₂))
            ∨  (e₁ ||_C e₂  ∧  e₁ →rc e₂  ∧  ¬(∃ e₃. e₂ →vis e₃ ∧ ¬(e₂ ⇄ e₃)))
```

Disjunct 1: visible non-commuting pairs follow `vis`. Disjunct 2: concurrent non-commuting
pairs follow `rc`, **unless `e₂` is already overwritten** by a later non-commuting `e₃` (the
conditional-commutativity escape that breaks `lo`-cycles, `lin.tex:307-330`). `lo` is
deliberately **partial / non-transitive** (`lin.tex:252-254` footnote) — hence the Lean
encodes "`π` extends `lo`" elementwise as `respects π (lo C) := π.Pairwise (¬ lo C b a)`,
*not* via `List.Sorted` (`RA_Linearizability.lean:99-105`).

### 1.3 RA-linearizability (Def. `def:lin`, `lin.tex:400-405`)

Let `D` satisfy `rc-non-comm(D)` and `cond-comm(D)`. Then:
- A configuration `C = ⟨N,H,L,G,vis⟩` is **RA-linearizable** iff for every active replica
  `r ∈ range(H)` there exists a sequence `π` of all events in `L(H(r))` with
  `lo(C)|_{L(H(r))} ⊆ π` and `N(H(r)) = π(σ₀)`.
- An execution `τ ∈ ⟦S_D⟧` is RA-linearizable iff all its configurations are.
- `D` is RA-linearizable iff all its executions are.

Lean port `IsRALinearizable` (`RA_Linearizability.lean:113-117`), with
`E ↔ L(H(r))`, `applySeq init π ↔ π(σ₀)`:

```lean
def IsRALinearizable (C : Configuration D) : Prop :=
  ∀ (r : Replica) (s : D.State) (E : Set (Op D.AppOp)),
    C.N r = some s → C.L r = some E →
    ∃ π, listPermOf π E ∧ respects π (lo C) ∧ applySeq D D.init π = s
```

Lifted to executions by `IsRALinearizableExec` (`:121-124`). Note: the paper folds
`rc-non-comm`/`cond-comm` into the *premise* of Def `def:lin`; the Lean instead carries
them as hypotheses inside `SatisfiesVCs`, consumed by the bridge theorem. Existence of `π`
rests on Lemma `irreflexive` (`lin.tex:316`); state-determinacy on Lemma `convergence`
(`lin.tex:392`).

### 1.4 Theorem 2 — the soundness meta-theorem (the target)

Two forms bridge VCs → RA-linearizability. **Theorem 1** (`lemmas.tex:139-141`, proof
`appendix.tex:218`) uses the `BottomUp-X-OP` rules *universally quantified over all states
`l,a,b`*. **Theorem 2** — the target — weakens each rule to the `ψ*` VC family that only
constrains *feasible* (reachable) states. Verbatim (`lemmas.tex:238-240`, proof
`appendix.tex:377-1232`):

> **Theorem 2.** If an MRDT `D` satisfies the VCs `ψ*(BottomUp-2-OP)`,
> `ψ*(BottomUp-1-OP)`, `ψ*(BottomUp-0-OP)`, `MergeIdempotence` and `MergeCommutativity`,
> then `D` is linearizable.

Carried throughout the development as standing premises (`lemmas.tex:3`): `rc-non-comm(D)`,
`cond-comm(D)`, `no-rc-chain(D)`, with `rc⁺` irreflexive.

The **five algebraic properties** Theorem 2 builds on (`lemmas.tex:83-91`, all variables
universally quantified, ternary `merge`):

- `BottomUp-2-OP`: `e₁≠e₂ ∧ (e₁→rc e₂ ∨ e₁⇄e₂) ⊢ merge(l, e₁(a), e₂(b)) = e₂(merge(l, e₁(a), b))`.
- `BottomUp-1-OP`: `(e_⊤≠ε ∧ e₁≠e_⊤) ∨ (e_⊤=ε ∧ l=b) ⊢ merge(e_⊤(l), e₁(a), e_⊤(b)) = e₁(merge(e_⊤(l), a, e_⊤(b)))`.
- `BottomUp-0-OP`: `⊢ merge(e_⊤(l), e_⊤(a), e_⊤(b)) = e_⊤(merge(l,a,b))`.
- `MergeIdempotence`: `merge(a,a,a) = a`.
- `MergeCommutativity`: `merge(l,a,b) = merge(l,b,a)`.

The **`ψ*` transformation** (`lemmas.tex:145-236`, Table `tbl:vc` at `:151-225`) replaces
"for all states" in each `BottomUp-X-OP` by an induction scheme that traverses the
event-set partition `L_⊤^b, L_⊤^a, L_1^b, L_2^b, L_1^a, L_2^a` (`lemmas.tex:41-47`)
top-down: a base VC on `σ₀` plus inductive VCs each adding one event under preconditions
like `e_b →rc e_⊤`, `∃e. e→rc e_⊤`, `¬(e ⇄ e_b)`. Every VC is `precondition ⇒
postcondition`, all variables universally quantified (`lemmas.tex:226`).

### 1.5 The Lean bridge theorem (binary instance, the *only* end-to-end target now coded)

`ra_linearizable_of_vcs` (`Merge_Linearization.lean:4390-4407`) — re-checked signature:

```lean
theorem ra_linearizable_of_vcs
    (D : CRDTSig) (hVC : SatisfiesVCs D) (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C
```

Proof = induction on reachability (= paper's induction on execution length): `refl →
initConfig_RA_lin`; `createReplica → RA_lin_preserved_createReplica`; `apply →
RA_lin_preserved_apply`; `query → ih`; `merge → RA_lin_preserved_merge_via_witness`.
This is the **binary** `D.merge s₁ s₂` form (`CRDT_TS.lean:122-133`), not the ternary
target. Faithful Theorem-2 mechanisation requires lifting `SatisfiesVCs` and this bridge
from binary `D.merge s₁ s₂` to ternary `μ(σ_⊤, σ₁, σ₂)`.

---

## Part 2 — The grouped VC list (24 paper VCs + 5 implicit extras = 29 Lean fields)

`structure SatisfiesVCs (D : CRDTSig)` (`RA_Linearizability.lean:149-536`) has **29 fields**
— verified by enumeration. Exactly **24** are the paper's VCs; **5** are mechanization-only
extras the binary proof forced. The 24 = the standing side-conditions (`lin.tex` §3.2,
referenced `lemmas.tex:3`) + the 2 merge axioms (`lemmas.tex:90`) + the 19-VC `ψ*`
expansion of the BottomUp template (Table `tbl:vc`, `lemmas.tex:151-225`).

**Count:** 24 = 1 `rc_non_comm` + 1 `no_rc_chain` + 1 `cond_comm_base` + 2
(`merge_comm`,`merge_idem`) + 19 bottom-up (9 two-op + 9 one-op + 1 `lem_0op`).
Plus 5 extras = 29. Field line numbers re-verified by grep.

**"LCA" column legend.** Sal is binary, so ternary `merge(l,a,b)` is encoded with `l`
folded away. `yes (ol)` = step references a shared LCA event `ol`; `init` = LCA = `D.init`;
`implicit` = paper carries `l`, binary form drops it; `no` = no LCA in the step. Every
non-`no` entry marks a place where the ternary→binary collapse happens and where the MRDT
target must reinstate `l` as a first-class argument.

### Group 1 — Side conditions (the 3 standing premises, `lin.tex` §3.2 / `lemmas.tex:3`)

| Lean field @line | Paper name | Statement | Constrains | LCA |
|---|---|---|---|---|
| `rc_non_comm` @152 | rc-non-comm (`lin.tex:387-390`) | at distinct ts + different replicas, `rc = Either ⟺ commute` | rc (+do_ via `commutes`) | no |
| `no_rc_chain` @177 | no-rc-chain (`lin.tex:491-493`) | no three events form an `rc=Fst_then_snd` chain | rc | no |
| `cond_comm_base` @186 | cond-comm base (`lin.tex:351-356`) | `rc o₁ o₂=Fst_then_snd ∧ ¬(o₂⇄o₃) ⇒ o₃∘o₂∘o₁(s)=o₃∘o₁∘o₂(s)` | do_ (rc premise) | no |

### Group 2 — Merge axioms (`lemmas.tex:90`)

| Lean field @line | Paper name | Statement | Constrains | LCA |
|---|---|---|---|---|
| `merge_comm` @195 | MergeCommutativity | `merge a b = merge b a` (`merge(l,a,b)=merge(l,b,a)`) | merge | implicit |
| `merge_idem` @198 | MergeIdempotence | `merge s s = s` (`merge(a,a,a)=a`) | merge | implicit |

### Group 3 — `ψ*(BottomUp-2-OP)` (9 VCs; `L₁ᵃ,L₂ᵃ` both non-empty). `lemmas.tex:85` left

Row→`ψ*` map: `base=ψ^{L⊤b}_base`; `ind_lca=ψ^{L⊤b}_ind`; `inter_lca=ψ^{L⊤a}_ind`;
`inter_left_base/inter_left=ψ^{L1b}_{ind1,ind2}`; `inter_right_base/inter_right=ψ^{L2b}_{ind1,ind2}`;
`ind_left=ψ^{L1a}_ind`; `ind_right=ψ^{L2a}_ind` (Lean `a`↔`L₁`, `b`↔`L₂`).

| Lean field @line | `ψ*` row | Statement | LCA |
|---|---|---|---|
| `base_2op` @202 | `ψ^{L⊤b}_base` (`:163`) | on `init`: `merge(o₁·init,o₂·init)=o₁·merge(init,o₂·init)` for rc-ordered/commuting `o₂,o₁` | init |
| `ind_lca_2op` @211 | `ψ^{L⊤b}_ind` (`:169`) | lift the 2-op peel from `l` to `do l ol` (prepend shared LCA event) | yes (ol) |
| `inter_lca_2op` @299 | `ψ^{L⊤a}_ind` (`:175`) | add LCA event `ol` (`∃o. rc o ol=Fst_then_snd`) to all three args | yes (ol) |
| `inter_left_base_2op` @241 | `ψ^{L1b}_ind1` (`:182`) | interpose one `L₁ᵇ` event `ob` (rc `ob ol`) before `ol` on `a` side; base | yes (ol) |
| `inter_left_2op` @278 | `ψ^{L1b}_ind2` (`:188`) | extend `a` side by non-commuting `o` (`rc o ob≠Either ∨ rc o ol=Fst_then_snd`) | yes (ol) |
| `inter_right_base_2op` @222 | `ψ^{L2b}_ind1` (`:195`) | symmetric `b`-side base | yes (ol) |
| `inter_right_2op` @257 | `ψ^{L2b}_ind2` (`:202`) | symmetric `b`-side extension | yes (ol) |
| `ind_left_2op` @324 | `ψ^{L1a}_ind` (`:209`) | add post-LCA local `o₁'` on `a` side | no |
| `ind_right_2op` @313 | `ψ^{L2a}_ind` (`:215`) | add post-LCA local `o₂'` on `b` side | no |

### Group 4 — `ψ*(BottomUp-1-OP)` (9 VCs; one of `L₁ᵃ,L₂ᵃ` empty, last event is an LCA event). `lemmas.tex:85` right

| Lean field @line | `ψ*` row | Statement | LCA |
|---|---|---|---|
| `base_1op` @336 | `ψ^{L⊤b}_base` 1op | on `init`: `merge(o₁·init,init)=o₁·merge(init,init)` | init |
| `ind_lca_1op` @342 | `ψ^{L⊤b}_ind` 1op | lift 1-op peel from `l` to `do l ol` | yes (ol) |
| `inter_lca_1op` @405 | `ψ^{L⊤a}_ind` 1op | combine two LCA events `ol,oi` (each `∃o. rc o ·=Fst_then_snd`) on both sides | yes (ol,oi) |
| `inter_left_base_1op` @363 | `ψ^{L1b}_ind1` 1op | interpose `ob` (rc `ob ol`) before `ol` on `a` side; base | yes (ol) |
| `inter_left_1op` @389 | `ψ^{L1b}_ind2` 1op | extend `a` side by non-commuting `o` | yes (ol) |
| `inter_right_base_1op` @350 | `ψ^{L2b}_ind1` 1op | symmetric `b`-side base (conditional peel hyp) | yes (ol) |
| `inter_right_1op` @374 | `ψ^{L2b}_ind2` 1op | symmetric `b`-side extension | yes (ol) |
| `ind_left_1op` @420 | `ψ^{L1a}_ind` 1op | add local `o₁'` on `a` side while `b` side carries only LCA event `ol` | yes (ol) |
| `ind_right_1op` @429 | `ψ^{L2a}_ind` 1op | add local `o₂'` on `b` side while `a` side carries only LCA event `ol` | yes (ol) |

### Group 5 — `ψ*(BottomUp-0-OP)` (1 VC). `lemmas.tex:90` left

| Lean field @line | Paper name | Statement | LCA |
|---|---|---|---|
| `lem_0op` @439 | BottomUp-0-OP | shared LCA event peels out: `merge(ol·a,ol·b)=ol·merge(a,b)` (`merge(e⊤(l),e⊤(a),e⊤(b))=e⊤(merge(l,a,b))`) | yes (ol) |

### The 5 implicit extras (mechanization-only; NOT in the paper's 24)

Forced because the binary mechanization exposes obligations the paper leaves implicit
(lattice-bottom, the cond-comm lift, all-commuting / shared-event peel cases that the
`rc=Fst_then_snd`-gated VCs never fire on). Doc-comments pin provenance.

| Lean field @line | Origin / why needed | Statement |
|---|---|---|
| `rc_non_comm_directional` @169 | strengthens `rc_non_comm` (`lin.tex:387`); drops `differentReplicas` so the overwriter/causal-chain argument can rc-order any non-commuting pair | at distinct ts, `¬commute o₁ o₂ ⟺ rc o₁ o₂=Fst_then_snd ∨ rc o₂ o₁=Fst_then_snd` |
| `cond_comm_lift` @463 | semantic lift of `cond_comm_base` over an arbitrary intervening seq `π`; paper invokes cond-comm in convergence but never proves the lift | `rc e e'=Fst_then_snd ∧ ¬commute e' e'' ⇒ e''·(π∘e∘e')(s)=e''·(π∘e'∘e)(s)` |
| `merge_init` @480 | lattice-bottom axiom; not derivable from the 24 (which constrain merge only when both args have ≥1 update) | `merge D.init s = s` |
| `merge_peel_comm` @502 | the missing all-commuting peel; `ind_right_2op` needs `rc=Fst_then_snd`, which never fires when all events commute (e.g. G-Set). Aristotle 444d5bcd | if `e` commutes with every event of `π`: `merge(e·a, π(init))=e·merge(a, π(init))` |
| `shared_peel_1op` @532 | shared-LCA 1-op peel the 24 can't derive: single-side VCs need `distinctOps` vs. the other tail, but shared `ol` gives `distinctOps ol ol` (false). Aristotle 1fe349b4 | with `o₁≠ol`: `merge(o₁·ol·a, ol·b)=o₁·merge(ol·a, ol·b)` |

**Caveat for the ternary port.** Every `yes (ol)` / `init` / `implicit` row above is exactly
a ternary→binary collapse site. The ternary metatheorem will need these VCs re-typed with
`l` as a first-class merge argument — plus, almost certainly, analogues of the 5 extras, plus
a generation-time anchor condition with no binary analogue (Part 4.4).

---

## Part 3 — Proof skeleton as a lemma DAG

Headline = **Theorem 2** (`lemmas.tex:238` / `appendix.tex:377`); its universally-quantified
precursor = **Theorem 1** (`lemmas.tex:139` / `appendix.tex:218`). Same proof shape; Theorem
2 only replaces each `BottomUp-X-OP` *rule* by a per-event-set `ψ`-VC *induction*
(`lemmas.tex:151-236`). The merge-case proof bodies are near-verbatim between the two
(`appendix.tex:250-368` vs `409-531`).

`⚑` flags a step that invokes commutation `⇄` (or its derivatives `rc-non-comm`,
`cond-comm`) — these are exactly the sites the conditioning design must reduce from
unconditioned `commutes` to `commutesOn` (reachable-state commutation). `[VC]` marks
consumed VCs.

### Top-level DAG

```
                    ra_linearizable_of_vcs  (Thm 2, lemmas.tex:238 / appendix.tex:377)
                    │  N0: induction on |τ|  (appendix.tex:384-388)
                    │  per-config target = Def lin (lin.tex:400-405)
        ┌───────────┼─────────────┬───────────────┬──────────────┐
   N1 Base/         N2 Apply      N3 Merge         N4 Query     N5 Lemma query
   CreateBranch     π'=π·e        (the hard case)  config        (corollary,
   (appendix:231)   (appendix:237) │               unchanged     lin.tex:410)
        │            │ ⚑(lo uses⇄)  │               (appendix:370)
        └────────────┴──────────────┤
                                    ▼
              N6  merge_linearization_exists  (∃π witness for v_m)
                  TRIPLE-NESTED INDUCTION  (appendix.tex:285-368)
                  outer |L₁ᵃ∪L₂ᵃ| ▸ inner |L_⊤ᵃ| ▸ inner-inner |M₁ᵃ∪M₂ᵃ|
        ┌──────────────┬─────────────┬───────────────┬──────────────────┐
   Base Case 1     Inductive C1   Case 1.1.1      Case 1.1.2 / Case 2
   |L_⊤ᵃ|=0        |L_⊤ᵃ|>0       one side ∅      both ≠∅  ⚑ e₁‖e₂ ⇒
   l=a=b          push e_⊤ᵗᵒᵖ     tail=LCA ev      rc∨rc∨⇄
   [MergeIdem]    [BottomUp-0-OP] [BottomUp-1-OP]  [BottomUp-2-OP,MergeComm]
   appendix:295   appendix:298    appendix:322     appendix:342 ⚑
        └──────────────┴──────────────┴───────────────┘
                                    │  (well-ordering of π under lo_m)
              ┌─────────────────────┼──────────────────────┬─────────────────┐
        N7 Lemma pi1          N8 Lemma pi2          N9 lo-stable-across   N10 LCA lemma
        no lo_m Sᵢ→Sᵢ₋₁       no lo_m within S₂     versions               L(v_⊤)=L(v₁)∩L(v₂)
        (appendix:117)        (appendix:180)        (appendix:270-278)    (lin.tex:160/
        ⚑ cond-comm,          ⚑ cond-comm,          ⚑ (lo via ⇄)          appendix:6-37)
          no-rc-chain           no-rc-chain
        [no_rc_chain,         [no_rc_chain,
         rc_non_comm,          rc_non_comm]
         cond_comm]
                                    │
              ┌───────────────────┬───────────────────┬────────────────────┐
   N11 lo / Def         N12 Lemma          N13 Lemma          N14 Lemma non-comm
   lin-relation         irreflexive        convergence         (special case,
   (lin.tex:295-305)    lo⁺ irreflexive    ⚑⚑⚑ all swaps       superseded by N13)
   ⚑ uses ⇄ both        (lin.tex:316/      (lin.tex:392/       (lin.tex:238/
   disjuncts            appendix:64-73)    appendix:75-103)    appendix:39-62)
                        [rc⁺ irreflexive]  [rc_non_comm,       ⚑
                                            cond_comm]
```

### Node catalogue (statement / deps / commutation use / Lean status)

- **N0 Execution-length induction** (`appendix.tex:384-388`). Every config of every
  execution is RA-linearizable; induction on `|τ|`, base `C₀` trivial, step splits on the 4
  transition rules. Deps N1–N4. The whole proof runs over *reachable* configs — structurally
  why all conditioning lives on reachable states. **Lean:** the `induction hReach` skeleton
  in `ra_linearizable_of_vcs` (`Merge_Linearization.lean:4395-4406`), complete.

- **N1 Base / CreateBranch** (`appendix.tex:231-235`). Fork copies `L`/`N`; inherits IH
  witness. Trivial, no commutation. **Lean:** `initConfig_RA_lin` (`RA_Linearizability.lean:543`),
  `RA_lin_preserved_createReplica` (`:564`) — closed.

- **N2 Apply** (`appendix.tex:237-248`). `L'=L∪{e}`, `N'=e(N)`; witness `π'=π·e`; "extends
  lo" holds since `∀e'∈π. e'→vis e`. ⚑ minor (reads `lo`, asserts no new commute fact).
  **Lean:** `lo_shrink_under_apply` (`:601`), `RA_lin_preserved_apply` (`:629`) — closed,
  no aux hyps.

- **N3 Merge** (`appendix.tex:250-368`) → **N6**. Sets up `v_⊤=LCA(v₁,v₂)`,
  `m=merge(l,a,b)`, `L'(v_m)=L(v₁)∪L(v₂)`; reduces to N6. **Lean:**
  `RA_lin_preserved_merge_via_witness` (`Merge_Linearization.lean:4330`) — destructures the
  existential, closed; the existential itself (N6) carries the open sorries.

- **N4 Query** (`appendix.tex:370-373`). Config unchanged ⇒ IH carries. No commutation.
  **Lean:** `query → ih`.

- **N5 Lemma query** (`lin.tex:410-412` / `appendix.tex:106-112`). Corollary of Def lin at
  the queried replica. No commutation.

- **N6 merge_linearization_exists — TRIPLE-NESTED INDUCTION** (`appendix.tex:285-368`).
  *The* hard node. Carving (`lemmas.tex:41-47`): `L₁',L₂'` (local), `L₁ᵇ,L₂ᵇ` (locals forced
  lo-before an LCA event, depth ≤2), `L_⊤ᵃ` (LCA events forced after a local), `L₁ᵃ,L₂ᵃ`
  (free locals), `L_⊤ᵇ`. Target sequence `S₁=L_⊤ᵇ · S₂=(L_⊤ᵃ∪L₁ᵇ∪L₂ᵇ) · S₃=(L₁ᵃ∪L₂ᵃ)`
  (`lemmas.tex:69`). Three nested inductions:
  - outer on `|L₁ᵃ∪L₂ᵃ|` (Case1=0 `:288`, Case2=>0 `:367`);
  - inner on `|L_⊤ᵃ|`: base `|L_⊤ᵃ|=0` ⇒ `l=a=b`, **MergeIdempotence** `[merge_idem]`
    (`:295`); inductive ⇒ pull maximal LCA event via **BottomUp-0-OP** `[lem_0op]` (`:298,308`);
  - inner-inner on `|M₁ᵃ∪M₂ᵃ|` (`Mᵢᵃ=Lᵢᵇ(e_m^⊤)`): base ⇒ `π·e_m^⊤` (`:315`); one side ∅ ⇒
    **BottomUp-1-OP** `[base_1op…ind_right_1op]` (`:322`); ⚑ both ≠∅ ⇒ since `e₁‖e₂`,
    `e₁→rc e₂ ∨ e₂→rc e₁ ∨ e₁⇄e₂` (`rc_non_comm`, `:343`): `e₁→rc e₂` by
    **MergeCommutativity** `[merge_comm]`, the rest by **BottomUp-2-OP** `[base_2op…ind_right_2op]`
    (`:342`); `no-rc-chain` kills the cross-edges blocking the last peel (`:359-364`).
  Theorem-2 refinement (`appendix.tex:451-531`): each `BottomUp-X-OP` rule is itself re-proved
  by the nested `ψ`-VC induction so it need only hold on feasible states; ⚑ the
  `ψ^{Lᵢᵇ}_ind2` precondition `e_b→rc e_⊤ ∧ ¬e⇄e_b` (`lemmas.tex:189,203`) reads commutation.
  Deps N7,N8,N9,N10, VCs 4–24.
  **Lean status (binary):** 🟡. `merge_linearization_exists` (`Merge_Linearization.lean:4137`)
  closes both-empty (`merge_idem`), asymmetric-empty (`merge_init`), shared-last (`lem_0op`);
  **distinct-last** delegates to `distinct_last_case` and carries all 6 open sorries (see
  Part 4.2).

- **N7 Lemma pi1** (`lemmas.tex:71-76` / `appendix.tex:117-178`). No lo_m `L₁ᵃ∪L₂ᵃ → L₁ᵇ∪L₂ᵇ`,
  none `L_⊤ᵃ → L_⊤ᵇ` (so `S₁·S₂·S₃` extends lo_m). ⚑ rc-rc chains die by **no-rc-chain**;
  several cases close because "`e''→rc e'` would require `e,e'` to **conditionally commute**"
  (`appendix.tex:151,169`). Deps `[no_rc_chain, rc_non_comm, cond_comm]` + vis-transitivity.
  **Lean:** 🟡 `no_lo_a_to_b` (`:1622`), `no_lo_top_a_to_top_b` (`:1820`) closed via Aristotle,
  but carry extra hyp `h_ncomm_concurrent_local_top`.

- **N8 Lemma pi2** (`lemmas.tex:118-122` / `appendix.tex:180-216`). No lo_m among `L_⊤ᵃ`
  events; bucket-ordering preserved. ⚑ same machinery (`no-rc-chain`, `cond-comm` at
  `:192`). **Lean:** 🟡 stub `no_lo_within_L_top_a`.

- **N9 lo stable across versions** (`appendix.tex:270-278`).
  `∀e,e'∈Lᵢ. e→lo_i e' ⟺ e→lo_m e'`. ⚑ stated through the lo disjuncts (read `¬e⇄e'`).
  Lets IH-linearizations of `a,b` be re-used. Deps N11 + causal closure.

- **N10 LCA lemma** (`lin.tex:160-165` / `appendix.tex:6-37`). In any reachable `C`,
  `v_⊤=LCA(v₁,v₂) ⇒ L(v_⊤)=L(v₁)∩L(v₂)`. `⊇` via Prop `lca` (`appendix.tex:16-26`): every
  event has a unique generator version. This is what lets every merge VC be stated over event
  sets. No commutation. Deps graph acyclicity + generator-version well-foundedness.
  *(Ternary-critical: this LCA-event-set machinery is exactly what the binary form fakes via
  `ev₁∩ev₂` and must be rebuilt over a real version DAG — Part 4.4.)*

- **N11 lo / Def lin-relation** (`lin.tex:295-305`). ⚑⚑ The definition consults `⇄` in
  *both* disjuncts (the 2nd via the overwriter clause). Root conditioning site: under
  conditioning, `lo` must be defined with `commutesOn`, paper-faithful only on reachable
  configs (`BLUEPRINT.md:471`). **Lean:** `lo` (`RA_Linearizability.lean:88`), closed def.

- **N12 Lemma irreflexive** (`lin.tex:316-319` / `appendix.tex:64-73`). `rc⁺` irreflexive ⇒
  `lo_C⁺` irreflexive (gives existence of `π`). ⚑ uses the overwriter clause of N11.
  Deps `[rc⁺ irreflexive]`.

- **N13 Lemma convergence** (`lin.tex:392-397` / `appendix.tex:75-103`). Under
  `rc-non-comm`+`cond-comm`, any two lo_C-extending sequences give the same state (SEC).
  Adjacent-transposition bubble sort. ⚑⚑⚑ **densest commutation site:** every swap is a
  commute step — vis-flip, `rc-non-comm`-flip, and `cond-comm`-flip giving `e₁⇄^{e₃}e₂`
  (`appendix.tex:82-93`). Deps `[rc_non_comm, cond_comm]`. **Lean:** 🟡 closed (Path 1),
  `convergence` (`Merge_Linearization.lean:609`), consuming `cond_comm_lift` + config
  invariants; different-replica swap = `applySeq_swap_lo_incomparable` (`:422`).

- **N14 Lemma non-comm** (`lin.tex:238-243` / `appendix.tex:39-62`). Classical special case
  of N13 (lo total on non-commuting pairs, no conditional-commute). ⚑ Superseded by N13 once
  lo is relaxed to the irreflexive Def lin-relation; kept as intuition.

### Commutation invocation sites (the conditioning surface)

Every place the proof asserts a commutation fact, by load-bearing-ness for the
conditioned-VC redesign. Each must move from unconditioned `commutes o₁ o₂` to `commutesOn`
(commutation only on `Inv`/`applicable` reachable states, `BLUEPRINT.md:437`).

| # | Site (node) | Citation | Form | Why it matters |
|---|---|---|---|---|
| ⚑1 | `lo` definition (N11), both disjuncts incl. overwriter | `lin.tex:300-303` | `¬e₁⇄e₂` | Root: lo is evaluated at events of reachable `C`, so `commutesOn` is paper-faithful there (`BLUEPRINT.md:561`). |
| ⚑2 | convergence swaps (N13) | `appendix.tex:84-93` | `⇄`, `rc-non-comm`, `e₁⇄^{e₃}e₂` | Densest. Both swapped events in `C.events`, both applicable, fold state `Inv` ⇒ `commutesOn` fires (`BLUEPRINT.md:477`). |
| ⚑3 | cond-comm lift to interval `π` (N13,N7,N8) | `lin.tex:351-374`; `appendix.tex:151,169,192` | `o₁⇄^{o₃}o₂` | 3-event `cond_comm_base` needs lift; surfaced as extra VC `cond_comm_lift` (`BLUEPRINT.md:184`). |
| ⚑4 | BottomUp-2-OP premise `e₁→rc e₂ ∨ e₁⇄e₂` (N6) | `lemmas.tex:85`; `appendix.tex:343,515` | `e₁⇄e₂` disjunct | The `⇄` branch needs `commutesOn` at merge-argument states (all `Inv`). |
| ⚑5 | rc-non-comm trichotomy (N6) | `appendix.tex:343`; `lin.tex:387` | `¬o₁⇄o₂ ⟺ rc∨rc` | Surfaced extra VC `rc_non_comm_directional` (`BLUEPRINT.md:183`). |
| ⚑6 | `ψ^{Lᵢᵇ}_ind2` guard `¬e⇄e_b` (N6 ternary scheme) | `lemmas.tex:189,203` | `¬e⇄e_b` | Per-event-set induction reads commutation in its guard. |
| ⚑7 | lo-stability across versions (N9) | `appendix.tex:274,277` | `¬e⇄e'` | Re-uses IH `⇄` facts; preserved because vis/rc unchanged across versions. |
| ⚑8 | pi1/pi2 cond-comm cases (N7,N8) | `appendix.tex:151,169,192` | conditional commute | Rule out rc-reversal cases; need `cond_comm` at reachable states. |

---

## Part 4 — Exists-vs-missing inventory

`Sal/Emulation/` is **Phase 1** of the bridge `24 VCs ⇒ RA-linearizable`, specialised to
**binary 2-way merge** (`CRDTSig.merge : State → State → State`, `CRDT_Signature.lean:77`).
The metatheory target (ternary `merge l a b`) is **not present in this directory at all**.

### 4.1 EXISTS and proved (kernel-verified, no `sorry`)

- **Generic LTS / simulation layer (merge-arity-agnostic):** `Labeled_TS.lean`
  (`LabeledTS`, executions, `ReachableFrom`); all of `Weak_Simulation.lean` —
  `silentClosure_lift` (`:93`), `weakStep_lift` (`:112`), `isWeakExecution_lift` (`:146`),
  capstone `weakSim_sound` (`:171`). Never mention `merge`.
- **State-based TS:** `CRDT_TS.lean` — `Configuration` with 6 structural invariants
  (`:44-75`), `Step` 4 rules (`:101-140`), `initConfig` invariants discharged (`:147-168`).
- **RA-lin definitions + bridge base/create/apply:** `applySeq` (`:25`), `lo` (`:88`),
  `IsRALinearizable` (`:113`), `SatisfiesVCs` (29 fields, `:149-536`); `initConfig_RA_lin`
  (`:543`), `RA_lin_preserved_createReplica` (`:564`), `lo_shrink_under_apply` (`:601`),
  `RA_lin_preserved_apply` (`:629`) — closed, no aux hyps. Bridge skeleton
  `ra_linearizable_of_vcs` (`Merge_Linearization.lean:4390`) structurally complete.
- **Merge-case machinery (large, mostly proved):** carving layer (`Merge_Linearization.lean:77-294`),
  convergence (`applySeq_swap_*`, `convergence` `:609`), BottomUp rules (`bottomUp_0op` `:950`
  … `bottomUp_1op_top_reachable` `:1089`), `merge_init_left/right_reachable` (`:1146,1153`,
  now closed via `merge_init`; PLAN.md has drifted on these), Lemma-1 supports
  `no_lo_a_to_b` (`:1622`), `no_lo_top_a_to_top_b` (`:1820`) closed via Aristotle.
- **End-to-end smoke test:** `Instances/Grow_Only_Set.lean` — `D_satisfies_VCs : SatisfiesVCs D`
  with all 29 fields closed (14 vacuous via `rc=Either`, 11 plumbed to `Sal/CRDTs/*`).

### 4.2 PARTIAL — the 6 live sorries (all in the distinct-last-event merge sub-case)

Verified by grep. All transitively under `merge_linearization_exists`, all in the branch
`e₁=π₁.last ≠ e₂=π₂.last`:

| Line | Location | Case | Why blocked |
|---|---|---|---|
| `Merge_Linearization.lean:2681` | `distinct_last_case` 3b-i-a | `e₂∈ev₁ ∧ e₁∈ev₂`, commute(e₁,e₂), both shared | commute makes `no_rc_chain` unable to kill the rc-concurrent disjunct of `lo`; needs L^a/L^b carving |
| `:2852` | 3b-i-b rc-concurrent | `e₂∈ev₁, e₁∉ev₂` | `respects` obligation needs a *forward-closure* overwriter for `y∈ev₂`; only backward closure threaded |
| `:2868` | 3b-ii-a | `e₂∉ev₁, e₁∈ev₂` (symmetric) | same rc-concurrent obstruction |
| `:2874` | 3b-ii-b | both local, commute(e₁,e₂) | needs L^a/L^b carving (lo-max-in-L^a ⇒ globally lo-max) — not yet built |
| `:4308` | `merge_linearization_exists` distinct-last | `h_ev₁_fwd` (forward closure under `vis∧¬commute`) | derivable from `vis_causal` at top-level call but not at recursive depth |
| `:4311` | same | `h_ev₂_fwd` | same |

**Root cause** (PLAN.md §2026-04-26/27, `MERGE_DISTINCT_LAST_ANALYSIS.md`): the induction
threads only **backward** `vis∧¬commute` closure; re-permutation via `perm_ending_in_lo_max
→ convergence` needs **forward** closure. The paper's fix is the triple-nested carving
induction (N6) that sidesteps re-permutation by choosing peel candidates from `L^a`; that
block is planned but unwritten, and would delete `distinct_last_case` (~860 ln).

Other scaffolds (not real yet): `Transfer.lean:48` (`OpIsRALinearizable` body = `True`),
`Transfer.lean:67` (`op_RA_linearizable_of_vcs` proof = `trivial`), `Emulation.lean:54`
(`effectiveState` = `D.init`), `Emulation.lean:103` (`emulation_G_weak_bisim` = `True`,
the §4.2 mutual weak simulation, untouched).

**Research framing:** the 6 sorries are a *binary* proof-engineering tail (Block-6 carving),
not a ternary-blocking research question. Per the project's research-first guidance, defer
this correctness tail until the ternary conditioning design (Part 4.4) is pinned down.

### 4.3 Binary-specific vs reusable for the ternary generalisation

**Reusable essentially as-is (no merge-arity dependence):**
- Entire generic layer: `Labeled_TS.lean`, all of `Weak_Simulation.lean` (incl.
  `weakSim_sound`).
- RA-lin definitions + non-merge bridge cases: `lo`, `listPermOf`/`respects`/
  `IsRALinearizable`/`applySeq`, `initConfig_RA_lin`, `RA_lin_preserved_createReplica`,
  `lo_shrink_under_apply`, `RA_lin_preserved_apply`. Port to MRDT with only a signature retype.
- Convergence machinery (`applySeq_*`, `convergence`, `cond_comm_lift`, `cond_comm_base`,
  `no_rc_chain`): pure `update`/`rc`/`lo` reasoning, no merge.
- Carving *templates* (`L_top`, `L_a/L_b`, `L_top_a/b`, `perm_ending_in_lo_max`, closure
  lemmas): reusable as templates but **their meaning changes** — binary `L_top = ev₁∩ev₂`;
  ternary "top" = the **LCA's event set**, not the intersection.

**Binary-specific (must be re-typed / re-proved with an `l` slot):**
- `CRDTSig.merge : State → State → State` (`CRDT_Signature.lean:77`) → ternary `State →
  State → State → State`.
- All merge-equation VC fields of `SatisfiesVCs` — every Group 2–5 field, plus the extras
  `merge_init`, `merge_peel_comm`, `shared_peel_1op`. Each is written `D.merge a b` with the
  LCA sliced to `init` or carried as a shared `ol` prefix. The names `ind_lca_*`,
  `inter_lca_*` and the docstrings ("For 2-way-merge CRDTs `l` collapses",
  `Merge_Linearization.lean:964`; "though with `l → init`", `:1008`) literally encode the LCA
  induction — they are ternary-shaped in spirit.
- All BottomUp rules (`bottomUp_0op` … `bottomUp_2op_reachable`): the paper's ternary
  template `merge(e_⊤(l), e₁(a), e_⊤(b))` at `l := init`.
- `CRDT_TS.Step.merge` (`CRDT_TS.lean:122-133`): `D.merge s₁ s₂` with **no LCA lookup** —
  ternary needs the config to expose the LCA state of `(r₁,r₂)`.
- `Emulation.lean`/`Op_Based_TS.lean`/`Transfer.lean`: `canonicalG` produces a *binary*
  `CRDTSig` (`merge := a ∪ b`, `Emulation.lean:75`); the whole Transfer composition targets
  the binary `SatisfiesVCs`.

**What slices in as `l := init` (the binary directory *is* the `l=init` instance):**
`ind_lca_2op`/`ind_lca_1op` (`RA_Linearizability.lean:211,342`) are the *only* fields already
universally quantified over an LCA-like `l : D.State` — they port with the smallest delta.
`bottomUp_2op_init_left`/`bottomUp_2op_reachable` are the `l:=init` specialisations
(`Merge_Linearization.lean:1008`). The **shared-event peel** path — `lem_0op` (`:439`),
`shared_peel_1op` (`:532`), `merge_peel_shared` (`:1989`), and the shared-last-event branch of
`merge_linearization_exists` — is the closest the binary proof gets to a real LCA (common
prefix `ol` on both args); in the ternary lift "shared prefix" generalises to "the LCA `l`",
making this branch the natural seed for the ternary inner induction.

### 4.4 What must be NEWLY BUILT, and the conditioning requirement

**Must be newly built (no binary analogue):**
1. **`MRDTSig`** — `merge : State → State → State → State` (l,a,b), replacing `CRDTSig`
   (`CRDT_Signature.lean:67`). `init`/`AppOp`/`update`/`query`/`rc`/`commutes` carry over.
2. **LCA / version-graph layer** — a new `Configuration` tracking a **version DAG /
   generation order**, not just per-replica `(state, event-set)`. The Merge step must compute
   the LCA state of `(r₁,r₂)` from the graph and pass it as `l`. This realises N10 (the LCA
   lemma) honestly instead of faking `L_top = ev₁∩ev₂`. Genuinely new structural component.
3. **Ternary bottom-up rules** — `merge(l, e₁(a), e₂(b))` with non-trivial `l`. The carving
   `L_top` re-anchored to the LCA's event set; the inner LCA-induction (`ind_lca_*`,
   `inter_lca_*`) becomes load-bearing rather than a degenerate slice.
4. **Ternary VC re-statement** — every merge-equation field with the `l` slot, plus likely
   new analogues of the 5 mechanization extras.
5. **Ternary `Step.merge`** + the LCA-aware closure invariants the merge-linearization
   induction needs.

**The conditioning requirement — generation-time id-monotonicity (the research crux).**
The binary `SatisfiesVCs` is purely **state-shape** (predicates on `D.State`). The ternary
`MRDTSig` conditioning must additionally carry **generation-time** invariants — properties of
*how* a state was produced, not of its shape. This is forced by a machine-checked finding,
not a conjecture:

- For RGA the soundness proof's commutation facts hold only **conditionally**:
  `commutes_with'` requires `accurate ∧ fresh_ts ∧ contains s 0 = false`
  (`RGA_Tombstone_Free_MRDT.lean:331`), and `accurate` can go **stale** under an intervening
  `Del`-rehoming.
- The machine-checked result (`Sal/MRDTs/RGA_Tombstone_Free/RGA_Reachability_Invariant.lean`):
  the natural forest invariant `anc_consistent` is **inductive under `do_` but refuted under
  `merge`** *unless anchors are id-monotone* — a **generation-time `applicable` condition,
  not a state-shape predicate**.
- Therefore the conditioning redesign must (a) replace unconditioned `commutes` by
  `commutesOn` (commutation only on `Inv`/applicable reachable states, `BLUEPRINT.md:437`) at
  every ⚑ site of Part 3, and (b) at sites **⚑2 (convergence) and ⚑4 (BottomUp-2-OP)** —
  where commutation fires at *merged* states — additionally carry the id-monotone allocation
  property as a generation-time invariant. The version-graph layer (new-build item 2) exists
  precisely to *state* such generation-time invariants; this is the component with no binary
  counterpart.

### 4.5 Bottom line

The reusable fraction is large but is exactly the **merge-independent** scaffolding (generic
LTS, weak-simulation transfer, `lo`/RA-lin definitions, base/create/apply bridge cases,
convergence, carving templates). Everything touching `merge` — the signature, ~22 of the 29
VC fields, the bottom-up rules, the TS merge step, `canonicalG` — is the `l := init` binary
specialisation and must be re-typed to ternary `merge l a b`. The ternary version
**additionally** needs a version-graph / generation-time layer with no binary analogue,
driven by the RGA non-inductiveness finding. The 6 open binary sorries are a binary
proof-engineering tail (Block-6 carving), not a ternary blocker — defer per research-first
guidance until the conditioning design (carrying generation-time id-monotonicity) is pinned
down.

---

## Citation index

- **Thm 2:** `_references/Neem/lemmas.tex:238-240`; proof `_references/Neem/appendix.tex:377-389`.
  **Thm 1:** `lemmas.tex:139-141`; proof `appendix.tex:218`.
- **BottomUp rules / axioms:** `lemmas.tex:83-96`. **`ψ*` VC table:** `lemmas.tex:151-225`
  (rows 163/169/175/182/188/195/202/209/215). **Carving:** `lemmas.tex:41-47`; sequence
  shape `:69`. **pi1:** `lemmas.tex:71-76`. **pi2:** `lemmas.tex:118-122`.
- **RA-lin Def:** `lin.tex:400-405`. **`lo_C` Def:** `lin.tex:295-305`. **Side conditions:**
  cond-comm `lin.tex:351-374`, rc-non-comm `:387-390`, no-rc-chain `:491-493`. **LCA lemma:**
  `lin.tex:160-165`. **irreflexive:** `lin.tex:316-319`. **convergence:** `lin.tex:392-397`.
  **query:** `lin.tex:410-412`. **non-comm:** `lin.tex:238-243`. **Abstract-spec intent:**
  `overview.tex:170`, `lin.tex:214-224,414`.
- **Appendix proof anchors:** LCA `appendix.tex:6-37`, non-comm `:39-62`, irreflexive
  `:64-73`, convergence `:75-103`, query `:106-112`, pi1 `:117-178`, pi2 `:180-216`, Thm 1
  exec-induction `:218-374`, merge case `:250-368`, Thm 2 `ψ`-VC induction `:377-531`,
  lo-stability `:270-278`.
- **Lean:** `lo`/`IsRALinearizable` `Sal/Emulation/RA_Linearizability.lean:88-117`;
  `SatisfiesVCs` (29 fields) `:149-536`; base/apply `:543,564,601,629`. Bridge
  `ra_linearizable_of_vcs` `Sal/Emulation/Merge_Linearization.lean:4390-4407`;
  `merge_linearization_exists` `:4137`; `distinct_last_case` sorries `:2681,2852,2868,2874`;
  forward-closure sorries `:4308,4311`; convergence `:609`; swap `:422`; carving `:77-294`.
  Binary merge step `Sal/Emulation/CRDT_TS.lean:122-133`; signature
  `Sal/Emulation/CRDT_Signature.lean:67-77`. `canonicalG` `Sal/Emulation/Emulation.lean:75`.
- **Conditioning / RGA hazard:** `Sal/Metatheory/BLUEPRINT.md` (node catalogue §4.1,
  commutation sites §5.3, RGA hazard §5.4, `:184,437,471,477,488-544,561`); RGA conditional
  commute `Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean:331`; non-inductiveness
  finding `Sal/MRDTs/RGA_Tombstone_Free/RGA_Reachability_Invariant.lean`.
