# Neem soundness metatheory — Phase-0 findings

*Status snapshot after the Phase-0 build-out and the merge-induction probe. Companion
to [`BLUEPRINT.md`](BLUEPRINT.md) (the plan), [`PHASE0_PLAN.md`](PHASE0_PLAN.md) (the
design), [`SOUNDNESS_SPEC.md`](SOUNDNESS_SPEC.md) (the spec). This file records **what
was learned building it**.*

Verification legend: **✅ verified** = independently rebuilt / re-read and confirmed;
**🔬 probe** = reported by the diagnosis agent, internally consistent and corroborated
by a verified adjacent fact, but not re-derived here; **❓ author** = a claim about the
Neem paper that the paper's authors are best placed to adjudicate.

## 1. Headline

Phase-0 is **fully scaffolded and machine-checked**, and the entire soundness
meta-theorem is now reduced to **a single hard obstruction**: the binary
merge-linearization induction. Everything else — the ternary signature, the execution
model, the ternary→binary VC reduction, and the conditioning gate — is proved. The
one blocker is not a grind; it needs a **redesign plus resolution of one paper
sub-case**.

## 2. What is proved (the scaffolding) ✅

| Piece | File | Status |
|---|---|---|
| `MRDTSig extends CRDTSig` + `mergeL`/`merge_init_slice`, `ConditionedMRDTSig`, `commutesOn`, ternary `lo`; collapse-to-binary lemmas; G-Set instance | [`MRDTSig.lean`](MRDTSig.lean) | ✅ 0 `sorry`, kernel-clean |
| Ternary `Configuration` (replica-keyed core + ranked version store `ver`/`head`/`parents`/`parents_lt`), `IsLCA`, `Reaches` well-founded, `initConfig` invariants | [`ExecutionModel.lean`](ExecutionModel.lean) | ✅ 0 `sorry`, kernel-clean |
| `SatisfiesVCsT` (29-field ternary VC bundle) + reuse contract `satisfiesVCs_of_T : SatisfiesVCsT D → SatisfiesVCs D.toCRDTSig`; G-Set witness | [`VCs.lean`](VCs.lean) | ✅ 0 `sorry`, kernel-clean |
| Conditioning gate: `RgaInv ∧ id_mono` a reachable invariant under monotone allocation; `Inv_merge` closed under `id_mono l` | [`../MRDTs/RGA_Tombstone_Free/RGA_Reachability_Invariant.lean`](../MRDTs/RGA_Tombstone_Free/RGA_Reachability_Invariant.lean) | ✅ 0 `sorry`, kernel-clean |

Two structural facts this establishes:
- **The ternary case reduces to the binary case.** `satisfiesVCs_of_T` (`VCs.lean:382`)
  collapses every ternary merge VC at `l := init` to its binary form via
  `merge_init_slice`. So **any fix to the binary soundness bridge lifts to the ternary
  meta-theorem automatically.**
- **The conditioning keystone holds for the RGA.** *A conditioned VC is sound iff its
  conditioning predicate is a reachable invariant under `do_`/`merge`* is a proved
  theorem for the RGA merge, with the generation-time `id_mono` (from monotone
  timestamp allocation) as the sole extra premise, hosted on the ranked-version store.

## 3. The single blocker: the binary merge-linearization induction

`merge_linearization_exists` (`Sal/Emulation/Merge_Linearization.lean:4137`) carries 6
open `sorry`s. The probe closed **0 of 6** and diagnosed a **single root cause**.

### Root cause 🔬
The induction is strong induction on `|π₁|+|π₂|`, peeling the **last element of one
input list** and appending it at the witness's **global tail** (`π_ih ++ [e₁]`). For
`respects (π_ih ++ [e₁]) (lo C)` the peeled event must be **globally `lo`-maximal in
`ev₁ ∪ ev₂`** — but last-of-`π₁` is only maximal within `ev₁`. In the **commuting**
tail sub-case (`e₁ ⇄ e₂`, Case 3b), a local `e₁ ∈ ev₁\ev₂` can retain a real `lo`-edge
to a foreign `e₂`-side event, and nothing in scope rules it out. Consequence: sorry
`:2852` is a leaf goal `⊢ False` from a **satisfiable** context (a model exists) — i.e.
unprovable as the proof is structured, not merely unproved.

### The two forward-closure sorries are FALSE ✅ (verified here)
`Merge_Linearization.lean:4308` and `:4311` ask to prove
```
∀ a b, C.vis a b → ¬ D.commutes a b → a ∈ ev → b ∈ ev    -- "forward"/upward closure
```
and the comment at `:4302` claims these "follow from `Configuration.vis_causal`."
**This is a direction error.** `Configuration.vis_causal` (`Sal/Emulation/CRDT_TS.lean:56`)
is `vis a b → s b → s a` — *backward/downward* closure ("observed the effect ⇒ observed
the cause"). Upward closure is the opposite and is **genuinely false**: a replica can
produce `a` without ever observing a later `b` made at a replica it has not merged. So
`:4308/:4311` must be **deleted, not discharged** — and since Case 3a of
`distinct_last_case` consumes them (to fake "shared event `e₂` is `lo`-max in `ev₁`" by
re-permuting `π₁`), even the "provable" Case 3a is unsound as written and must be rewritten.

### Per-sorry map 🔬
| sorry | sub-case | classification |
|---|---|---|
| `:2681` | 3b-i-a, both tails shared | mechanization dead-end (needs carving; no append works) |
| `:2852` | 3b-i-b, local `e₁`, `e₁⇄e₂` | dead-end; satisfiable `⊢ False` |
| `:2868` | 3b-ii-a | dead-end (symmetric to 2852) |
| `:2874` | 3b-ii-b, both local | dead-end (needs carving) |
| `:4308` / `:4311` | top-level forward closure | **false** — delete, forces Case-3a rewrite |

## 4. The paper sub-case ❓ (for the authors)

The probe traces the obstruction to `_references/Neem/appendix.tex`, **Case 1.1.2**.
The paper rules out the `rc`-successor case with *"since `e₂ →rc e₁`, this case is not
possible due to no-rc-chain."* But it **folds the commuting sub-case `e₁ ⇄ e₂` into the
same case, where `e₂ →rc e₁` does not hold** — so the cited `no-rc-chain` justification
does not literally cover the commuting sub-case. The probe judges this a genuine
under-specification, **likely patchable** because the `M₂ᵃ` events are `lo`-constrained
below the top event, but not discharged as written; the existing Lean carving lemmas do
not cover the `L₁_local → L₂_local` `rc`-edge.

**Open question for the Neem authors:** is Case 1.1.2's commuting sub-case a real gap in
the write-up, or is there an argument (perhaps using the `M₂ᵃ`-below-top constraint) that
the probe and the Lean port both missed? This answer sets the redesign direction. It is a
proof-write-up question, **not** a claim that the theorem is false — the RGA/CRDTs are
correct and the meta-theorem is very likely still true.

## 5. The redesign path (three items, none pure effort) 🔬

1. **Carving-based peel.** Replace the `|π₁|+|π₂|` peel-last measure with a peel over the
   `L^a/L^b` carving, choosing a *globally* `lo`-maximal event (the existing but unwired
   `L_a`/`L_b`/`L_top_a`/`L_top_b`, `no_lo_a_to_b` `:1622`, `no_lo_top_a_to_top_b` `:1820`,
   `perm_ending_in_lo_max` `:1504`, `exists_lo_maximal_in_subset`, `convergence` are the
   material to wire together).
2. **A vis-transitivity reachability invariant on `Configuration`.** `no_lo_a_to_b` needs
   `h_vis_trans` (vis transitivity, true only for reachable configs) which is **not
   currently a field of `Configuration`**; add and maintain it (`Step`-preservation), plus
   thread `h_ncomm_concurrent_local_top`.
3. **Close the Case 1.1.2 commuting sub-case** (§4) — rule out `e₁ →rc e` for
   `e ∈ M₂ᵃ\{e₂}` when `e₁ ⇄ e₂`.

`S6` (the ternary merge induction) is the ternary twin of this same induction, so it is
blocked on the same redesign; by `satisfiesVCs_of_T`, fixing the binary case lifts.

## 6. Assessment

Mechanization did what mechanization is for: it converted "the paper has a proof" into a
**precise, verified diagnosis** of exactly where and why the soundness argument breaks,
with two `sorry`s proven false and a concrete three-item path forward. The near-term
completion risk is real (this is a research problem, not a grind), but the research value
is high: a mechanization surfacing a likely gap in a published OOPSLA proof, with the fix
localized to one induction and one sub-case.
