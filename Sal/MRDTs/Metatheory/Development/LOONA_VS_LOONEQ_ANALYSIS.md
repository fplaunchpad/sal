# loOnA vs loOnEq — pen-and-paper analysis

*Grounded in the actual definitions, not memory. Corrects an error I made reasoning from memory.*

## The two orders, after `rc ≡ Either`

Both order **only vis-comparable pairs**. Since the RGA's `rc ≡ Either`, the `loOnC` (rc-tiebreak)
disjunct is empty in both, so they reduce to `vis ∧ [predicate]`:

- **`loOnA(e₁,e₂)  ⟺  vis(e₁,e₂) ∧ appliesDependsOn(e₂,e₁)`**
  (`G2_Applicability_Aware.lean:216`; reduce because `loOnC` empty)
- **`loOnEq(e₁,e₂) ⟺  vis(e₁,e₂) ∧ ¬eqCommutesOn(e₁,e₂)`**
  (`GenericEqQuotient.lean:425` + `loOnEqQ_reduce`, `RGA_ConvergenceEq.lean:463`)

The predicates:

- **`appliesDependsOn(e₂,e₁)`** (`:210`): `e₁` is an **Ins** creating node `t` (= its own timestamp),
  and `e₂` **names `t`** — as its anchor/target (`opLeaf`) OR anywhere in its recorded path (`opPath`).
  Purely **syntactic** (reads payloads). **A `Del` is never a source**: `appliesDependsOn _ (Del…) = False`.
- **`¬eqCommutesOn(e₁,e₂)`**: reordering `e₁,e₂` observably changes the state (up to `≈`), at some `Inv` state.
  **Semantic.**

So: **loOnA = "e₂ syntactically mentions a node e₁ created"; loOnEq = "the order observably matters."**

## The error I made from memory (corrected)

I claimed: in `[Ins b; Ins a@b; Del b; Ins @a]`, the rehoming delete `Del b` orders before the dependent
`Ins @a` under `loOnA` (because "`Ins @a`'s applicability depends on `Del b`"), and that `loOnEq` misses it.

**Wrong.** `appliesDependsOn(Ins@a, Del b)` has a **`Del` as source** ⇒ `False`. So `loOnA` does **NOT**
order `Del b` before `Ins @a`. And `Del b`, `Ins @a` **eq-commute** (when `a` is live, `do_` resolves to the
live anchor `a` and ignores the path; rehoming preserves `a`'s node's placement — verified by `do_` traces),
so `loOnEq` doesn't order them either. **Both orders leave `(Del b, Ins @a)` unordered — they AGREE here.**

## Where they genuinely differ

- **`loOnA ⊋ loOnEq` (on genuine ops):** `e₂`'s recorded path **names a deep ancestor** `t` (= `e₁`'s node)
  that is **not** `e₂`'s effective anchor (a nearer node is live), so ordering `e₁,e₂` doesn't change the
  result. `loOnA` orders them (syntactic mention); `loOnEq` doesn't (they commute).
- **`loOnEq ⊋ loOnA` (needs non-genuine ops):** observable non-commutation **without** a syntactic mention —
  requires a junk/fabricated path (`RGA_OrderBridge` j-witness). Empty on honest ops.

They coincide on every "obvious" pair: `Ins a / Del a` and `Ins a / Ins @a` both *mention* AND *don't commute*
(`anchorIns_not_eqCommutesOn`). Hence **incomparable** (`RGA_OrderBridge`), but the split is narrow.

## The load-bearing insight: neither order is what excludes the bad interleaving

On the decisive execution `E = {Ins b, Ins a@b, Del b, Ins e [] a}` (call them `e_b,e_a,e_del,e_o`), BOTH
orders have exactly the edges `e_b→e_a, e_a→e_o, e_b→e_del` and leave `(e_del,e_o)` unordered. So **both admit**
the interleaving `π = [e_b, e_a, e_o, e_del]`, where `e_o` is applied at the prefix-state `{b, a@b}` — at which
its recorded path `[]` (claiming `a` under root) is **inaccurate** (`anc a = b ≠ 0`).

What excludes `π` is **`noopFeasible`** (`UpdateFeasibility_Gate.lean:100`): at that prefix `e_o` is neither
`applicable` (accuracy fails) **nor** a no-op (it changes the state), so `noopFeasible` fails on `π`.

**So the feasibility notion is `[order] + noopFeasible`, and `noopFeasible` = "applicable-or-no-op at every
prefix" is the load-bearing per-prefix-accuracy guarantee — built directly on the `applicable` field.**
The order only needs to keep the genuinely-non-commuting edges (both `loOnA` and `loOnEq` do; plain `loOnC`
drops the `Ins→Del` edge, which is why `loOnC + noopFeasible` diverges — `UpdateFeasibility_Gate`).

## Consequence for the two routes

- **`loOnA` vs `loOnEq` is second-order** — they agree on the decisive cases; `noopFeasible` / `applicable`
  is what does the work. `UpdateFeasibility_Gate` already proves **`loOnA + noopFeasible`** convergent-and-
  satisfiable on both decisive cases.
- **`GenDisc2CEq` was the wrong condition.** It demands accuracy at a **reordered dependency-prefix fold**
  (`accurate o (applySeqR init_st d)`), which is *stronger* than `noopFeasible` (applicable-or-no-op at the
  *delivery* prefix) and can **fail** for genuine executions — e.g. `e_o`'s dependency prefix is `{e_b,e_a}`
  (state `{b, a@b}`) where `e_o` is inaccurate, so `GenDisc2CEq` is **false** for `E`, even though the honest
  delivery order is `noopFeasible` and `E` converges. My `loOnEq`/`GenDisc2CEq` arc built a stronger,
  sometimes-false substitute for the framework's `applicable + noopFeasible`.

## Verdict / right target

Instantiate the RGA over **`loOnA + noopFeasible`** (the already-proven notion), with **`applicable` as the
standing genuineness condition** — no separate `GenDisc2CEq` to state or discharge. The `applicable`-or-no-op
delivery discipline *is* the honest condition, and it is a first-class part of the extended MRDT definition.

## What of the proofs done so far is reusable (most of it)

- **Order-agnostic canonical machinery** — `canon_fold`, `CanonMatch`, `eq_of_canonMatch2`
  (`RGA_CanonConvergence`): parametric in the order/start-state; reusable verbatim.
- **Merge machinery** — branch canon, `birthAnc`, `canonBirthBridge` (`RGA_BranchCanon`,
  `RGA_HinFilterEq`, `RGA_MergeFoldChain`); `merge_fold_convergence_eq` is order-parametric.
- **Framework threading** — `EqJoinLemma3C` carrying a *datatype-supplied* discipline + `GDSupply`
  (`GenericEqQuotient`, Task A): reusable; just instantiate the discipline as `noopFeasible`/`applicable`
  instead of `GenDisc2CEq`.
- **Standing findings** — `DepComp` refutation, `loOnA`/`loOnEq` incomparability, `UpdateFeasibility_Gate`'s
  verdict.

The part to **re-base**: `RGA_update_convergence_eq`'s `GenDisc2CEq` premise and the `loOnEq`-specific
wrapping → onto `loOnA + noopFeasible` / `applicable`. The convergence *engine* (canon_fold) stays; only the
premise it consumes changes to the honest `applicable`-based one.

---

## Addendum — sharpened after grounding in the framework (why `GenDisc2CEq` is un-dischargeable, and the fix)

Reading `GenericEqQuotient` (`IsCanonicalStateEq`, `EqJoinLemma3C`, `GDSupply`) and `RGA_CanonConvergence`
(`CanonFoldOK`/`ChainOK`) pins down the exact architectural reason the compacted verdict above is right, and
sharpens *where* the change lands.

### The engine is a strictly-sufficient (incomplete) condition, and that is the whole story

The convergence engine `canon_fold` requires **`CanonFoldOK`** — per event, `ChainOK` (the live-filtered
recorded chain is a genuine ancestor path) at its **actual** fold prefix. This is *stronger than true
convergence*. On the decisive honest set `E = {Ins b, Ins a@b, Del b, Ins e [] a}` (`e_b,e_a,e_del,e_o`):

- `e_del` (`Del b`) and `e_o` (`Ins e [] a`) **`≈`-commute** (`resolve` short-circuits at the live anchor `a`),
  so `loOnEq` drops the edge even though `vis(e_del,e_o)` holds causally. Hence the interleaving
  `π = [e_b, e_a, e_o, e_del]` **respects `loOnEq`** but reverses a commuting causal edge.
- At `π`'s prefix `{b, a@b}`, `e_o`'s honest empty path is inaccurate (`anc a = b ≠ 0`), so `ChainOK` FAILS —
  `CanonFoldOK` fails on `π`. Yet `π` and the honest `[e_b,e_a,e_del,e_o]` **both fold to `{a@0, n@a}`** (they
  converge, by commutativity). So the engine cannot certify a *true* convergence.

`GenDisc2CEq` (accuracy at the reordered `loOnEq`-dependency prefix) is FALSE for exactly this `E` — which is
now revealed as **correct, forced behaviour**: under a `loOnEq`-*only* linearization discipline the engine
genuinely cannot handle `E`, so any canon_fold-based premise MUST exclude it. `GenDisc2CEq` is therefore not a
*defective* condition — it is an *un-dischargeable* one: honest generation cannot prove it, because honest
executions realise `E`. Leaving it assumed means the RGA result silently excludes honest runs.

### The fix restricts the canonical-state witness, not the order

`IsCanonicalStateEq E W vis ev s := ∃ ρ, listPermOf ρ ev ∧ respects ρ (loOnEq …) ∧ eqv (applySeq init ρ) s`
is **existential** in the witnessing enumeration `ρ`. The honest fix is to constrain that witness:

> add **`noopFeasible D ρ D.init`** to the witness (applicable-or-no-op at every prefix).

This restricts canonical states to **born-applicable (causal-honest) linearizations** — a *subset* of
`loOnEq`-respecting ones, so the convergence claim is only *weakened*, and it stays SOUND for
RA-linearizability (whose linearizations must extend `vis` anyway). The bad interleaving `π` is excluded
(`e_o` is neither applicable nor a no-op at `{b, a@b}`), and every honest execution is covered because
`applicable`-at-generation transports along causal delivery (the born-applicable property). `GenDisc` is then
**deleted**, not re-instantiated (this reverses the Task A threading of `GDSupply`).

The born-applicable *existence* side is already in the repo: `ConditionedExecutionModel.exists_loOnA_noopFeasible_enum`
+ `noopFeasible_of_prefixApp`.

### The mathematically load-bearing step is certified (kernel-clean)

The engine's per-step obligation follows from `applicable` at the **actual** prefix **with no transport** —
the `chainOK_transport`/`anc_transport` machinery of `canonStepOK_of_genR` (whose only job was to carry
accuracy from a *dependency* prefix to the actual one) simply collapses. Proved in
`RGA_NoopFeasible_CanonFold.lean` (axioms ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`):

- `chainOK_of_accurate_ins` : `accurate (Ins …) s → ChainOK s (a :: p)` (accuracy makes the chain fully live).
- `delOK_of_accurate_del`  : `accurate (Del …) s → DelOK s p x` (`resolve` of an accurate path = stored anchor).
- `chainOK_of_appOrNoop_ins` / `delOK_of_appOrNoop_del` : lifted to `applicable ∨ no-op` — the no-op `Ins` is
  impossible under freshness, the no-op `Del` leaves its target absent so `DelOK` is vacuous. The two no-op
  branches `noopFeasible` admits are discharged.

### Remaining surgery (the invasive part, a decision for KC)

1. **Generic** (`GenericEqQuotient`): add `noopFeasible` to `IsCanonicalStateEq`'s witness; drop the `GenDisc`
   parameter from `EqJoinLemma3C` / `GDSupply` / `wfGenFull` / `RA_linearizable_up_to_eq`. Ripples into
   `isCanonicalState_qsig_iff` (the guarded-to-raw bridge must now also carry `noopFeasible`, from
   execution-model reachability — the born-applicable discharge).
2. **RGA**: `canonFoldOK_of_noopFeasible` (assemble §2 above with the freshness/id-uniqueness inputs
   `canonStepOK_of_genR` already uses from `C.distinctTs`); re-state `RGA_update_convergence_eq` and the merge
   bridge to consume the `noopFeasible` witness.
3. **Reachability**: supply `noopFeasible` witnesses for the execution's canonical states from
   `applicable`-at-generation (born-applicable).

Item 1 touches the 16k-line generic framework's core definition — the last-20% engineering the post-mortem
([[vc-modification-displaces-difficulty]]) warns about. The *research question is answered* and the crux is
kernel-certified; items 1–3 are mechanization debt, not new research.
