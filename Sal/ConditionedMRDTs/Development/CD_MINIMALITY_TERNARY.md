# CD-minimality (ternary): `CDVC3` is an INDEPENDENT rule of the VC bundle 🔬

Mission: settle Open Question `oq:cd` in the **ternary** (three-way merge)
direction — is the causal-delta bound `CDVC3` *derivable* from `CoreVCs3 +
DeltaVCs3` (plus the unconditional delta laws), or an *independent* VC of the
framework's bundle? This feeds `oq:proglogic`, whose program logic wants a
minimal, independent rule basis.

**Verdict: `CDVC3` is INDEPENDENT — not derivable. The bundle is minimal at
`CDVC3` and cannot be reduced.** Established by a machine-checked countermodel
(kernel-clean), together with the ternary exactness theorem that reframes
derivability as the metatheorem question itself.

Mechanized artifact: `Sal/ConditionedMRDTs/Refutations/CD_Not_Derivable_Ternary.lean`.

---

## 0. Exact statements (from `Framework/VC_Set.lean`)

Over a `D : ConditionedMRDTSig` (fields: `State`, `init`, `update`, ternary
`mergeL l a b`, binary `merge`, `rc`; with `merge_init_slice : mergeL init a b
= merge a b`). Write `Op D.AppOp` for events, `C` for a `Configuration
D.toCRDTSig`, `σ(E)` for the canonical state `IsCanonicalState C E ·`, `↓e =
downset C e` for the `vis∧¬commutes` past of `e`, `loOn C U` for the
set-relative linearization order.

**`CoreVCs3 D`** (five fields):
- `update_core : UpdateVCs D.toCRDTSig` — three update-layer fields
  (`rc_non_comm_directional`, `no_rc_chain`, `cond_comm_lift`). *No merge
  content, no inflation.*
- `mergeL_comm : ∀ l a b, mergeL l a b = mergeL l b a`
- `mergeL_init : ∀ s, mergeL init init s = s`
- `lem_0op3 : ∀ l a b e, mergeL (update l e)(update a e)(update b e) =
  update (mergeL l a b) e`
- `merge_peel_comm3 : ∀ a e π₀ π₂, (∀ x∈π₀, commutes e x) → (∀ x∈π₂, commutes
  e x) → mergeL (applySeq init π₀)(update a e)(applySeq init π₂) =
  update (mergeL (applySeq init π₀) a (applySeq init π₂)) e`

**`DeltaVCs3 D`** (two fields, the *unconditional* on-ramp — group ⊕ lattice
classes):
- `redistribute : ∀ m x₀ x₁ x₂ c, mergeL (mergeL m x₀ c)(mergeL m x₁ c)(mergeL
  m x₂ c) = mergeL m (mergeL x₀ x₁ x₂) c`
- `local_redistribute : ∀ l m x c y, mergeL l (mergeL m x c) y = mergeL m
  (mergeL l x y) c`

*Neither `CoreVCs3` nor `DeltaVCs3` contains an inflation axiom.* This is the
crux (see §4).

**`CDVC3 D`** (the goal — an EQUATION, not an `⊑`-inequality): for `e`
`loOn(U)`-maximal in a weakly-closed `U`, `A = σ(U∖e)`, `B = σ(↓e∖e)`,

```
    mergeL B A (update B e) = update A e.
```

Consumed by `Adequacy.join_lemma3_of_cd : CoreVCs3 D → DeltaVCs3 D → CDVC3 D →
JoinLemma3 D`, and thence RA-linearizability (`ra_linearizable_of_core_delta_cd3`).

---

## 1. The binary partial result, recapped (`Sal/CRDTs/Metatheory/`)

The binary (lattice / CRDT) case is the launch point. There the merge is an
LCA-blind lattice join `merge a b` and the analogue bound is the inequality
`CDVC : update A e ⊑ A ⊔ update B e` (`JoinLemma_Of_CD.lean:226`). Mechanized
in `CD_Exact.lean` (finding A12):

- `cdVC_of_joinLemma : CoreVCs D → LatticeVCsPlus D → JoinLemma D → CDVC D`.
  The principal instance `(U∖e, ↓e)` of the Join Lemma *is* `CDVC` — and it
  needs `merge_idem` to turn the resulting equation into the `⊑`-inequality.
- `joinLemma_iff_cdVC` — under `CoreVCs + LatticeVCsPlus`, `CDVC ↔ JoinLemma`.
- `cdVC_weakest` — no strictly weaker bridge VC exists.

The residual question **(b″)** — is `CDVC` derivable from `CoreVCs +
LatticeVCsPlus` alone? — is *equivalent* to the unconditional metatheorem, and
is **open** but sharply characterized (`A12_DRAFT.md`):

- **Positive attack circular at two case shapes** (§2 of `A12_DRAFT.md`): the
  mutual induction closes every peel step except (i) `e ∥ x` with `rc x e =
  Fst` (`x` before `e`, `e` absorber-free), and (ii) `commutes(e,x)` with `x`
  rc/vis-entangled in `↓e`; unwinding either with `lem_0op` reproduces the
  size-`n` goal verbatim.
- **Countermodel space narrowed** (§3 of `A12_DRAFT.md`): a forcing dichotomy
  (`rc_non_comm_directional` + `cond_comm_lift` + inflationarity, or
  `merge_peel_comm`) transports the read content into `A` before `e` fires in
  every *powerset* case; the one surviving habitat is **non-atomic lattice
  states**.

Crucially, the binary ladder is:

```
CoreVCs                        ✗ (A8, AWSetX — associativity separator)
CoreVCs + LatticeVCs (ACI)     ✗ (A10, AWSetF — inflation separator, reachably non-RA-lin)
CoreVCs + LatticeVCsPlus       ? open (b″) ≡ CDVC; narrowed to non-atomic lattices
CoreVCs + LatticeVCsPlus + CDVC ✅ end-to-end
```

The A10 separator **`AWSetF`** (`Assoc_CounterModel.lean`,
`coreVCs_lattice_insufficient`) is the key fact I lift: it is a bona-fide
bounded join-semilattice satisfying every `CoreVCs` field, whose update is
**deflationary** (`AWSetF_update_not_inflationary`: a `rem` decreases the last-op
flag), on which `JoinLemma` and `peel_local` FAIL on a two-event reachable
configuration `flagConfig`. Binary (b″) stays open only because
`LatticeVCsPlus` *adds inflation back*.

---

## 2. Ternary exactness (mechanized, kernel-clean)

Lift of `CD_Exact.lean` to the ternary bundle. In
`CD_Not_Derivable_Ternary.lean`:

```
cdVC3_of_joinLemma3 : CoreVCs3 D → JoinLemma3 D → CDVC3 D
joinLemma3_iff_cdVC3 : CoreVCs3 D → DeltaVCs3 D → (JoinLemma3 D ↔ CDVC3 D)
cdVC3_weakest        : CoreVCs3 D → (X → JoinLemma3 D) → (X → CDVC3 D)
```

`cdVC3_of_joinLemma3` runs the Join Lemma on the principal pair `(U∖e, ↓e)`:
its honest LCA set is `(U∖e) ∩ ↓e = ↓e∖{e}` (state `B`), branch states `A`
and `σ(↓e) = update B e` (free peel), union `(U∖e) ∪ ↓e = U`. The Join Lemma
delivers `IsCanonicalState C U (mergeL B A (update B e))`; `update A e` is
canonical for `U` too; **uniqueness of canonical states**
(`isCanonicalState_unique_u`, needing only `UpdateVCs`) equates them — exactly
`CDVC3`.

> **Sharpest structural finding.** The ternary backward direction needs **no
> idempotence and no delta law** — only `CoreVCs3` (in fact only the
> `update_core`/`UpdateVCs` fragment for uniqueness). The binary
> `cdVC_of_joinLemma` had to spend `merge_idem` converting the equation into
> the `⊑`-inequality; the ternary `CDVC3` is *already* the equation the
> uniqueness lemma produces. The ternary exactness is therefore *cleaner and
> stronger*: `CDVC3` is the exact Skolemization of the union-level Join, with a
> tighter hypothesis than binary.

**Consequence.** "Is `CDVC3` derivable from `CoreVCs3 + DeltaVCs3`?" is
*equivalent* to "Does `CoreVCs3 + DeltaVCs3 ⇒ JoinLemma3`?" (via
`joinLemma3_iff_cdVC3`), and any hypothesis sufficient to close the metatheorem
already implies `CDVC3` (`cdVC3_weakest`). No strictly weaker bridge VC exists.

---

## 3. The derivation attempt — where it is circular

Given exactness, the direct-derivation attempt is: prove `JoinLemma3` from
`CoreVCs3 + DeltaVCs3` by strong induction on `|U|`, and see whether `CDVC3` is
avoidable. The framework's own induction `join_lemma3_of_cd`
(`Adequacy.lean:541`) shows *exactly* where `CDVC3` is consumed and why it is
irreducible:

- `side_decomposition3` reduces every side `E ∋ e` to `σ(E) = mergeL B σ(E∖e)
  (update B e)`. For `E ⊊ U` this is discharged by the **IH at `|E| < n`** (a
  smaller Join instance). For `E = U` — the principal peel — there is no
  smaller instance, and the step *is* `CDVC3` verbatim (`Adequacy.lean:461–471`,
  the `E = U` branch literally invokes `hCD`).
- The combine step (`Adequacy.lean:602–754`) then feeds this through
  `redistribute`/`local_redistribute` to reassemble the union.

So the ternary induction is a **fixed point at the principal peel `E = U`**:
the only thing that closes it is `CDVC3(U, e)` itself. This is the ternary
analogue of the binary "principal case" circularity — and it is *cleaner* than
binary's two-shape circularity, because the ternary equation is monolithic (no
`⊑`-halves to attack separately). A non-circular derivation would need a genuinely
new principle producing `mergeL B A (update B e) = update A e` for a maximal
`e` from the core+delta equations alone — and §4 shows no such principle exists
(there is a countermodel).

**Do not** mistake `join_lemma3_of_cd` for a derivation of `CDVC3`: it
*consumes* `CDVC3` to produce `JoinLemma3`. The exactness converse
(`cdVC3_of_joinLemma3`) is the honest, non-circular implication; it produces
`CDVC3` *from* `JoinLemma3`, not from thin air.

---

## 4. The countermodel (the result) — `AWSetF3`

**The independence-forcing observation.** `DeltaVCs3` (redistribute +
local_redistribute) constrains only `mergeL`; it says **nothing about
`update`**, in particular nothing about inflation `s ⊑ update s e`. The
ternary `CDVC3`-equation `mergeL B A (update B e) = update A e`, read on an
LCA-blind lattice join `mergeL l a b = a ⊔ b`, unfolds to

```
    A ⊔ update B e = update A e.
```

Its `⊒`-half `update A e ⊑ A ⊔ update B e` is the binary `CDVC` (holds broadly);
its `⊑`-half `A ⊔ update B e ⊑ update A e` demands `A ⊑ update A e` — **exactly
the inflation** that binary `LatticeVCsPlus` supplies as a separate axiom and
that `DeltaVCs3` omits. So the ternary `CDVC3` silently packs inflation, and
the inflation-free `DeltaVCs3` cannot back it. The binary A10 separator
`AWSetF` was built precisely to violate inflation — so it lifts to a ternary
`CDVC3` countermodel.

**Construction (`AWSetF3`).** The LCA-blind ternary lift of `AWSetF`:
- `State = AWFState = AWState × Bool` — add-wins set skeleton × a last-op flag
  (`add ↦ true`, `rem ↦ false`, `init.flag = false`);
- `update = awfUpdate`, `rc = awRc` (`rc rem add = Fst`), `init` as `AWSetF`;
- ternary `mergeL l a b := awfMerge a b` — the pairwise semilattice join,
  **dropping the LCA slot `l`**; `merge_init_slice` holds by `rfl`;
- `Inv`, `applicable` trivially `True`.

Then (all in the artifact, each field reduces to an `AWSetF` core lemma):

- **`CoreVCs3 AWSetF3` (`AWSetF3_coreVCs3`).**
  - `update_core := UpdateVCs.of_core AWSetF_coreVCs` (binary core, slimmed);
  - `mergeL_comm/init`, `lem_0op3` drop the LCA slot to `AWSetF_merge_comm`/
    `AWSetF_merge_init`/`AWSetF_lem_0op`;
  - **`merge_peel_comm3`** at the branch slot IS `AWSetF_merge_peel_comm a e π₂`
    — the LCA-slot fold `π₀` is dropped, so its commuting hypothesis is unused.
    (This is the one field to check adversarially — it holds because
    `AWSetF`'s restricted 1-op peel over a *commuting* context is proven, and
    the ternary shape asks for no more.)
- **`DeltaVCs3 AWSetF3` (`AWSetF3_deltaVCs3`).** Pure ACI of `awfMerge`:
  `redistribute` = `(x₁⊔c)⊔(x₂⊔c) = (x₁⊔x₂)⊔c` (idempotence collapses the
  duplicate `c`), `local_redistribute` = `(x⊔c)⊔y = (x⊔y)⊔c`
  (right-commutativity). Proved from `AWSetF_merge_assoc/comm/idem`.
- **`¬ CDVC3 AWSetF3` (`AWSetF3_not_cdVC3`).** On `AWSetF`'s reachable
  `flagConfig` (replica 0: `{aF=add, eF=rem}` with `vis aF eF`; replica 1:
  `{aF}`), take `U = {aF, eF}`, `e = eF`, `A = B = σ({aF}) = sF₂` (both `U∖e`
  and `↓eF∖{eF}` equal `{aF}`). All `CDVC3` contextual hypotheses hold
  (transitive/irreflexive `vis`, `U ⊆ events`, weak closure, `eF ∈ U`, `eF`
  `loOn(U)`-maximal, and the two canonical-state facts — `↓eF = {aF,eF}` via
  `downset_vis`). The equation fails **on the flag**:

  ```
  mergeL B A (update B eF)  flag = A.flag ∨ (update B eF).flag = true ∨ false = true
  update A eF               flag = awFlag eF                          = false
  ```

  `true ≠ false`, closed by `decide` on the Boolean component. This is the
  binary `AWSetF_not_joinLemma`/`peel_local` failure, transported to the
  `CDVC3`-equation via the LCA-blind lift.

**Adversarial self-check (the standing trap).** The countermodel is faithful
on all counts: (a) it does *not* quietly fail a Core/Delta clause — every
`CoreVCs3` field is discharged by an `AWSetF` lemma and both `DeltaVCs3` fields
by ACI, all machine-checked; (b) the falsifying instance is a genuine
`CDVC3` instance — every contextual hypothesis is proved, and `A`, `B` are
*honest canonical states* of `U∖e` and `↓e∖e` (not free states), so the
"quietly fails a hypothesis" trap is excluded; (c) `¬commutes(aF,eF)` and the
`vis`-edge make `↓eF∖{eF} = {aF}` nonempty — this is a real non-commuting
maximal event, not the degenerate all-commuting case (`cdVC3_of_all_comm`)
where `B = init`. The specific failing instance is
`mergeL sF₂ sF₂ (update sF₂ eF) ≠ update sF₂ eF`.

By the exactness (§2), `¬ CDVC3 AWSetF3` also yields `¬ JoinLemma3 AWSetF3`
(`coreDelta3_not_joinLemma3`): `CoreVCs3 + DeltaVCs3` do NOT imply the ternary
Join Lemma.

---

## 5. Verdict and consequences

**`CDVC3` is INDEPENDENT (not derivable) — the ternary VC bundle is minimal at
`CDVC3`.** Unlike the binary (b″), which is *open* (narrowed to non-atomic
lattices), the ternary question is **CLOSED with a countermodel**: the ternary
`CDVC3`-equation packs the inflation half that `DeltaVCs3` — unlike binary
`LatticeVCsPlus` — does not carry, and the LCA-blind lift of the A10 inflation
separator `AWSetF` exhibits the gap.

- **VC count.** The canonical route `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3 ⇒
  JoinLemma3 ⇒ RA-lin` (eight VCs) cannot be shortened by dropping `CDVC3`:
  `CDVC3` is load-bearing and independent of the core + unconditional-delta
  laws. Any attempt to remove it must instead prove `CoreVCs3 + DeltaVCs3 ⇒
  JoinLemma3`, which `coreDelta3_not_joinLemma3` refutes.
- **`oq:proglogic` (minimal, independent rule basis).** The causal-delta rule
  is a *genuine independent axiom* of the would-be program logic, not a derived
  lemma — it must appear as a primitive proof obligation (a per-datatype
  side-condition), exactly as the framework already treats it. The rule basis
  is minimal at `CDVC3`.
- **Contrast with binary.** Binary (b″) stays open because `LatticeVCsPlus`
  re-adds inflation, closing the gap that would otherwise be a countermodel.
  The ternary bundle's honest omission of an inflation axiom from `DeltaVCs3`
  is what makes ternary CD-derivability *refutable* where binary is merely
  narrowed. (Whether a would-be "`DeltaVCs3 + inflation`" ternary variant
  reopens the non-atomic-lattice question is the natural ternary analogue of
  binary (b″), and is left open — but it is a *different, stronger* bundle than
  the one the framework ships.)

---

## Artifacts

| File | Content | `sorry` |
|---|---|---|
| `Refutations/CD_Not_Derivable_Ternary.lean` | `cdvc3_not_derivable_from_core_delta`, `coreDelta3_not_joinLemma3` (countermodel `AWSetF3`); `cdVC3_of_joinLemma3`, `joinLemma3_iff_cdVC3`, `cdVC3_weakest` (exactness) | 0 |

Axiom audit: `#print axioms cdvc3_not_derivable_from_core_delta` and
`#print axioms cdVC3_of_joinLemma3` both report exactly
`[propext, Classical.choice, Quot.sound]` — fully kernel-clean. (The `decide`
calls on the finite Boolean/op-inequality goals reduced without introducing
`Lean.ofReduceBool`.) Build: 0 `sorry`, 0 errors.
