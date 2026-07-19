# SMT discharge of the flat-MRDT verification conditions (task #99 / #49)

**Goal.** Make the flat-MRDT VCs *push-button*: a new flat instance should need
zero hand proof to be certified RA-linearizable. This directory is a
**translation-validation** layer. The Lean metatheory
(`Sal/ConditionedMRDTs/**`) stays the source of truth; per instance, we discharge
by SMT the eight VCs that the flat capstone `flat_ra_linearizable3_eq`
(`Metatheory/FlatGeneric_Bridge.lean`) consumes.

**Solver.** z3 4.16.0 (Python bindings; `import z3`). No shelling out. Per-query
timeout 10 s. `cvc5` was not present on the box; z3 alone closes every
non-boundary query in < 10 ms.

## 1. What the capstone actually needs

`flat_ra_linearizable3_eq` needs three things of a flat MRDT `D`
(`Inv = applicable = ⊤`): `hInvT`, `hAppT` (both trivial for a flat instance),
and `JoinLemma3C D (fullClosure)`. Every production instance supplies the Join
Lemma through `ConditionedContract.ofVCs` from **eight** verification conditions
(`Framework/VC_Set.lean`, `Framework/Sigma_LoOn3.lean`):

| # | VC | shape | source struct |
|---|----|-------|---------------|
| 1 | `rc_non_comm_directional` | `∀o₁o₂. distinct∧diffrep → (¬commutes ↔ rc-edge)` | `UpdateVCs` |
| 2 | `no_rc_chain`             | `∀o₁o₂o₃. ¬(rc o₁o₂=Fst ∧ rc o₂o₃=Fst)` | `UpdateVCs` |
| 3 | `cond_comm_lift`          | rc/commute law across an `applySeq` fold | `UpdateVCs` |
| 4 | `mergeL_comm`             | `∀l a b. mergeL l a b = mergeL l b a` | `CoreVCs3CD` |
| 5 | `feasible_init`           | `⟵ mergeL_init : mergeL init init s = s` | `FeasibleDeltaVCs3` |
| 6 | `feasible_local_redist`   | `⟵ local_redistribute` (unconditional) | `FeasibleDeltaVCs3` |
| 7 | `feasible_redistribute`   | `⟵ redistribute` (unconditional) | `FeasibleDeltaVCs3` |
| 8 | `CDVC3`                   | ternary causal-delta bound | `CDVC3` |

The Feasible* laws are *configuration-conditioned* in Lean (canonical states at
honest LCAs). The reduction lemmas in `Metatheory/Adequacy.lean` discharge them
from **unconditional algebraic** laws, which is what we translate to SMT:

* `feasibleDeltaVCs3_of_delta` : `mergeL_init` ⟹ 5, `local_redistribute` ⟹ 6,
  `redistribute` ⟹ 7 (the `DeltaVCs3` group/lattice on-ramp).
* `cdVC3_of_all_comm` : `all_comm` (`∀o₁o₂. commutes`) ⟹ 8 (commuting class).

So the SMT target per instance is the unconditional bundle
`{rc_non_comm_directional, no_rc_chain, cond_comm_lift, mergeL_comm, mergeL_init,
local_redistribute, redistribute, all_comm}`. Each **implies** the corresponding
Lean VC; discharging it push-button certifies the VC. Where the unconditional
law is *strictly stronger* than the conditioned VC (ORSet, below), an SMT `sat`
is not a refutation of the instance — it is the triage boundary.

Base facts used (`Framework/Base/CRDT_Signature.lean`,
`CRDTs/Metatheory/RA_Linearizability.lean`): `Op = (ts:ℕ, rep:ℕ, appop)`;
`commutes o₁ o₂ := ∀s. do o₂ (do o₁ s) = do o₁ (do o₂ s)`;
`distinctOps := ts₁≠ts₂`; `differentReplicas := rep₁≠rep₂`;
`RcRes = {Fst_then_snd, Snd_then_fst, Either}` (encoded as `0,1,2`).

## 2. The DSL (`vcgen.py`)

A flat MRDT signature is a `MRDT` dataclass of Z3 terms:

```
MRDT(name, new_state, init, AppOp, new_app, update, mergeL, rc,
     rc_is_either=False, PointSort=None, select=None, new_point=None,
     cell_sort=None)
```

* **State sorts** are built from `Int` (Counter/PN), a lex `WithBot` datatype
  (LWW), Z3 arrays `Array(K,V)` as *sets/maps* (GSet: `Set Int`; ORSet:
  `Set Tag`; remove-wins set: `Elem → RPair`).
* **AppOp** is a Z3 algebraic datatype (`inc`; `add e | rem e`; `write v`), so
  the "finite op cases" are literal constructors.
* **`update`, `mergeL`, `rc`** are Z3 terms; `rc` returns the `RcRes` int enum.
* For **set/map states** the instance exposes `PointSort`, `select(s,p)` and
  `cell_sort`, enabling the *pointwise* encoding below.

## 3. Translation of each VC to an SMT query

We prove a VC by asserting its **negation** and checking `unsat` (= valid). All
universally-quantified variables (states, ops, and the `∀s` inside `commutes`)
become **free symbolic constants** — quantifier-free — except where a nested `∀`
survives the negation.

* **VCs 4–7 (merge laws), `mergeL_init`** — plain equations over symbolic
  states. QF. For array/set states we check **pointwise**: `select(lhs,p) ≠
  select(rhs,p)` for a fresh symbolic point `p` (exactly the `funext t; cases`
  shape of the Lean proofs), which sidesteps extensional array reasoning over
  `Lambda`-defined merges.
* **VC 2 `no_rc_chain`** — `rc` is a concrete datatype-case function; QF.
* **VC 1 `rc_non_comm_directional`** — split into two arms:
  * *underspec* (`¬commutes → rc-edge`, contrapositive): all-universal, so
    `∀o₁o₂ (state). rc-no-edge → commute`. **QF**.
  * *overspec* (`rc-edge → ¬commutes`): negation is `∃o₁o₂. edge ∧ ∀s. commute`,
    a genuine `∀s`. Encoded with **one quantifier**. For set-states, `commutes`
    is quantified over `(cell:Bool/Cell, point)` instead of a whole array (sound
    by update-locality), which z3 closes instantly.
* **VC 3 `cond_comm_lift`** — the fold VC.
  * `rc ≡ Either` instances: the premise `rc e e' = Fst` is unsatisfiable ⇒
    vacuous. **QF**.
  * otherwise (ORSet): sound **pointwise-fold abstraction**. Since `update` is
    pointwise, `applySeq S π` at point `p` depends only on `S` at `p`; model it
    as `Lambda([p], foldp(select(S,p), p))` with `foldp` a *free* uninterpreted
    function. `unsat` then means the law holds for **every** pointwise fold,
    hence for the real `applySeq`. Sound over-approximation; the side-condition
    (`update` is pointwise) is discharged separately as `update_pointwise`.
* **VC 8 `CDVC3`** — via the `all_comm` sufficient condition: `∃o₁o₂(state).
  ¬commute`. QF; `unsat` ⇒ all ops commute ⇒ `cdVC3_of_all_comm` fires.

## 4. Decidability triage

| VC | fragment | notes |
|----|----------|-------|
| `mergeL_comm`, `mergeL_init`, `redistribute`, `local_redistribute` | **QF** (LIA / QF-array-pointwise) | plain merge equations; the sweet spot |
| `no_rc_chain` | **QF** (datatype cases) | `rc` concrete |
| `rc_non_comm_directional` underspec | **QF** | all-universal |
| `rc_non_comm_directional` overspec | **1 quantifier** (`∀s`, or `∀cell,point`) | z3/MBQI closes it |
| `cond_comm_lift` (Either) | **QF** | premise unsat |
| `cond_comm_lift` (ORSet) | **QF + uninterpreted fold** | pointwise-fold abstraction; needs `update_pointwise` |
| `CDVC3` via `all_comm` | **QF** | fails (sat) for genuinely non-commuting ORSet |

No triggers were needed. The only genuine quantifier is the `∀s`/`∀cell,point`
of the overspec arm; everything else is quantifier-free.

## 5. Soundness story / trust gap

This is **translation validation**, not a verified translator. The trust gap is
exactly the fidelity of the Python/Z3 `MRDT` term to the Lean `ConditionedMRDTSig`:

1. **DSL vs Lean definitions.** `update`/`mergeL`/`rc`/`init` are hand-mirrored
   from the `.lean` instance files. A transcription error is undetected by SMT.
   *Mitigation:* the calibration (§6) pins each instance against its Lean
   ground truth — every true VC must come back `unsat` and each mutation `sat`.
2. **Unconditional ⟹ conditioned.** We check the stronger unconditional laws
   (`DeltaVCs3`, `all_comm`). `unsat` soundly certifies the Lean VC. `sat` does
   **not** refute the instance if the conditioning saves it (ORSet). We label
   such cells rather than call them bugs.
3. **Fold abstraction.** `cond_comm_lift` for non-Either instances trusts that
   `update` is pointwise; this is itself SMT-checked (`update_pointwise`).
4. **Arithmetic domain.** Timestamps are `ℕ` in Lean but `Int` in Z3; the
   register/GC designs use an explicit `WithBot` least element so the laws hold
   for all `Int`, not only non-negative ones (no hidden `ts ≥ 0` assumption).

Results, the matrix, and the #49 verdict continue in the second half of this
file.

## 6. Calibration matrix (ground truth = the Lean discharge)

Four calibration shapes span the space: **Counter/PN** (numeric group),
**GSet** (set lattice), **ORSet** (instance-set with kill sets, non-commuting),
**LWW** (timestamp lex order). `U` = `unsat` (VC valid), `S` = `sat`
(countermodel), `·` = n/a. All times < 3 ms unless noted.

| instance | rc_dir | no_rc_chain | cond_lift | mergeL_comm | feas_init | local_redist | redist | CDVC3 | matches Lean? |
|----------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---|
| Counter  | U | U | U | U | U | U | U | U | **yes** (all VCs Lean-proved) |
| PN       | U | U | U | U | U | U | U | U | **yes** |
| GSet     | U | U | U | U | U | U | U | U | **yes** |
| LWW      | U | U | U | U | U | U | U | U | **yes** |
| ORSet    | U | U | U | U | U | **S\*** | U | **S\*** | 6/8 push-button; 2 boundary |

`S*` = the two ORSet VCs that are **configuration-conditioned in Lean**
(`ORSet_feasibleDeltaVCs3.feasible_local_redistribute` uses `ORSet_canonical_bound`
tag-freshness; `ORSet_cdVC3` uses the maximal-Rem trichotomy). Their unconditional
over-approximation is genuinely false, so SMT returns `sat` — **not** a
mismatch with Lean but a precise identification of the two VCs that required
hand proof. Everything else, including ORSet's non-vacuous `cond_comm_lift` (via
the fold abstraction) and both arms of `rc_non_comm_directional`, is push-button.

**Mutation tests** (deliberately broken; every one caught with a model):

| mutation | VC that flips to SAT | countermodel (readable) |
|----------|----------------------|-------------------------|
| Counter, drop `−l` (`mergeL=a+b`) | `redistribute` | `c=1`: merge double-counts the shared delta |
| PN, `max`-merge instead of `a+b−l` | `feasible_init` | `s=−1`: `max(0,0)=0≠−1` |
| GSet, `mergeL=a` (project) | `mergeL_comm`, `feasible_init` | `a={0}, b={}`: `a≠b` under swap |
| LWW, arbitrate on ts only, tie→first | `mergeL_comm` (+3 more) | `a=w(0,4,5), b=w(0,6,7)`: equal ts, picks first |
| ORSet, drop `¬l` on b-term | `mergeL_comm`, `local_redist` | `l=⊤,a=⊤,b=⊥`: removed tag revives asymmetrically |

## 7. The #49 success metric — remove-wins set with LCA-GC'd rem-records

**v1 (literal spec, `instances/rwset.py`).** State = a set of tags `(ts,elem)`
each with two bits `.a`/`.r`; `add`/`rem` stake bits (both monotone ⇒
`all_comm` ⇒ CDVC3 push-button); `mergeL` unions adds and applies the **LCA-GC
rule**: drop a rem-record that is *in the LCA `l`* and *superseded* (a strictly
later add exists for the element).

Push-button run: **6/8 UNSAT**, but `feasible_redistribute` **and**
`feasible_local_redistribute` come back **SAT**. The loop's finding: the
LCA-conditioned supersession-drop is *order-sensitive* — whether a rem is GC'd
depends on adds introduced by the very delta being redistributed — so `mergeL`
is **not a convergent semilattice** and the delta laws fail *unconditionally*.
Countermodel (`redistribute`): `c` carries an add `(1,2)` and a rem; extracting
the shared delta `c` before vs after the merge drops the rem in one order only.

**Repair the loop forces (`instances/rwset_compact.py`).** Normalise the
rem-records to the **per-element maximum timestamp** (the fully-GC'd normal
form: a rem superseded by a higher one for the same element is *intrinsically*
absent), and likewise adds. `mergeL` becomes a product of two `max`-semilattices,
**LCA-blind**, so the delta laws hold **unconditionally**. Semantics preserved
exactly: `e` present iff `maxAdd(e) > maxRem(e)` (strict ⇒ remove-wins on ties;
a strictly-later add resurrects).

**Verdict: all eight VCs of the compacted design discharge push-button (all
UNSAT), zero hand proof.** The LCA-GC is realised as the `max` compaction, which
is *safer* than LCA-conditioned dropping (a join never loses information).

**Two kill-tests, both refuted with countermodels:**

| kill | intent | VC refuted | countermodel |
|------|--------|-----------|--------------|
| `RwSet(eager-GC)` | drop the LCA guard: GC rems *not* covered by the LCA | `feasible_init` **SAT** | `s` has rem `(0,2)`+add `(1,2)`; `mergeL init init s` drops the rem ⇒ `≠ s` |
| `RwSet(add-wins-tie)` | asymmetric add-wins lean: an add suppresses the *peer's* rem only | `mergeL_comm` **SAT** | `a={add(1,2),rem}`, `b=∅`: `mergeL l a b ≠ mergeL l b a` |
| `RwSetC(min-rem)` | compacted analogue: `min` the rem-ts (loses a higher remove) | `feasible_init` **SAT** | `s=(⊥, rem@2)`; `min(⊥,2)=⊥` drops the remove |

(The eager-GC / add-wins variants also drive the quantified dominance queries to
the 10 s **timeout** on the redistribute arms — reported honestly, not counted
as a discharge; both kills are already refuted on the cheap VCs above.)

## 8. Solver, versions, timing

* **z3** 4.16.0, Python bindings. Per-query timeout **10 000 ms**.
* Full campaign (`run.py`): 5 calibration + 5 mutations + 2×#49 + 3 kills,
  **wall ≈ 30 s** — of which ~30 s is three honest 10 s timeouts on the hard
  quantified-dominance kill queries. Every push-button (UNSAT) query is
  < 10 ms; every clean SAT countermodel is < 150 ms.

## 9. Files and how to run

```
smt/
  NOTE.md            this file
  vcgen.py           the DSL (MRDT dataclass) + the 8 VC encoders + solver harness
  run.py             one command: runs everything, prints the matrix, writes JSON
  instances/
    numeric.py       Counter, PN (+ mutations)
    gset.py          G-Set (+ mutation)
    orset.py         OR-Set, non-commuting (+ mutation)
    lww.py           LWW register (+ mutation)
    rwset.py         #49 v1: set + LCA-GC (+ 2 kills)
    rwset_compact.py #49 repair: per-element max-ts (+ 1 kill)
  results/results.json   full matrix (instance × VC × result × time)
```

Run: `python3 smt/run.py` (needs `z3-solver`; `pip3 install --user z3-solver`).

## 10. Recommendation for a Lean-side integration (future soundness bridge)

Two routes to close the trust gap of §5:

* **A. Verified translation** (`MRDTSig → SMT-LIB` reflected in Lean, proved
  meaning-preserving). Highest assurance, but a large mechanization: it must
  internalise the semantics of `update`/`mergeL`/`rc` and of the array/datatype
  theories. Overkill given how few instance shapes exist.
* **B. Certificate replay** (recommended). Keep the Lean VC statements as the
  spec; have the SMT layer emit, per instance, an **UNSAT certificate** (z3
  proof / an explicit witness term) and replay it with a Lean tactic
  (`polyrith`/`omega` for LIA merge laws, `decide` on the finite datatype/Bool
  cases, `Finset` extensionality for the pointwise set laws). Most of the eight
  VCs already close in Lean by `omega` / `cases … <;> rfl` (see the `bor_*`
  kernel in `MRDT_Instances/Common.lean` and the Counter `omega` discharges), so
  the SMT layer is best used as an **oracle that finds the discharge and its
  countermodels**, with a thin Lean tactic re-proving the UNSAT cells natively.

Concretely: wire the SMT layer as a *pre-flight* for new flat instances — it
(i) tells the author instantly which VCs hold and which need conditioning
(the ORSet-style boundary), and (ii) produces the countermodel when a design is
broken (the #49 loop). The residual hand proof shrinks to exactly the
config-conditioned cells the triage flags — which for the whole commuting class,
and for the repaired #49 design, is **empty**.
