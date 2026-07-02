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
one blocker is not a grind; after the redesign attempt it **reduces to a single
well-posed lemma** — convergence over backward-closed reachable replica event sets
(§5). The paper sub-case that looked like a gap is **resolved**: a missed argument,
machine-checked (§4).

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
*(Line numbers are post-redesign-attempt: the two building-block lemmas added +135
lines, shifting the sorries. All 6 remain open, and §5 shows they all reduce to a
single convergence lemma.)*
| sorry | sub-case | classification |
|---|---|---|
| `:2816` | 3b-i-a, both tails shared | reduces to convergence-over-`ev₁` (§5) |
| `:2987` | 3b-i-b, local `e₁`, `e₁⇄e₂` | satisfiable `⊢ False`; reduces to convergence-over-`ev₁` |
| `:3003` | 3b-ii-a | reduces to convergence-over-`ev₁` |
| `:3009` | 3b-ii-b, both local | reduces to convergence-over-`ev₁` |
| `:4443` / `:4446` | top-level forward closure | **false** (upward closure); *load-bearing* for the re-permutation, so cannot be deleted until the convergence lemma exists |

## 4. The paper sub-case — RESOLVED ✅ (machine-checked: missed argument, not a gap)

`_references/Neem/appendix.tex` **Case 1.1.2** rules out the `rc`-successor case with
*"since `e₂ →rc e₁`, not possible by no-rc-chain,"* but folds in the commuting sub-case
`e₁ ⇄ e₂`, where `e₂ →rc e₁` does not hold — so the cited `no-rc-chain` step does not
literally cover it. **A valid argument nonetheless exists, now mechanized** as
`no_lo_of_concurrent_to_L_b` (`Merge_Linearization.lean:1926`, **depends on no axioms at
all**):
- `e₁ ∥ e` (concurrent) by **backward** causal closure (`vis_causal`) — they are local to
  different replicas;
- so `lo e₁ e` can only be the rc disjunct: `rc(e₁,e)=Fst` ∧ `e` has no overwriter;
- but `e ∈ M₂ᵃ` has a first `lo`-hop `e →lo w` toward the top, which is either **vis**
  (⇒ `w` overwrites `e`, contradicting no-overwriter) or **rc** (⇒ `rc(e₁,e)=Fst ∧
  rc(e,w)=Fst` violates no-rc-chain).

Either way the edge cannot exist. This is the `M₂ᵃ`-below-top patch, needing **no
vis-transitivity**.

**Verdict for the Neem authors:** the theorem holds and the sub-case is soundly patchable;
the write-up is *incomplete* for the commuting sub-case (the cited no-rc-chain step doesn't
literally apply there), not *wrong* — an erratum-sized fix, exactly the argument above.

## 5. The redesign path — updated status 🔬

1. **Carving-based peel — selection half DONE, state-equation half is the blocker.**
   The global-`lo`-max *selection* is verified: `lo_max_of_L_a_is_global`
   (`Merge_Linearization.lean:1996`, `[propext, Classical.choice, Quot.sound]`) shows the
   `L_a`-maximal event is `lo`-maximal in the whole `ev_top ∪ ev_local`, composing the
   existing `no_lo_a_to_b`/`no_lo_top_a_to_top_b`/`exists_lo_maximal_in_subset`. But
   *using* it — peeling that event off `s₁` — requires re-permuting `π₁` (via
   `perm_ending_in_lo_max`), whose state equality routes through **`convergence` over the
   replica set `ev₁`** (item 2).
2. **~~vis-transitivity invariant~~ → the real blocker: convergence over backward-closed
   reachable sets.** *(Corrected from the original diagnosis.)* The Lean `convergence`
   lemma requires `ev₁` to be **forward/overwriter-closed** — provably false for a replica
   set even in reachable configs (the same forward closure as the false sorries
   `:4443/:4446`, which are therefore *load-bearing* for the re-permutation and cannot be
   deleted yet). `convergence` over `ev₁` is *true* (merge is convergent); its current
   proof route just demands overwriters the set doesn't contain. **The single remaining
   blocker is a convergence lemma valid over merely backward-closed reachable replica
   sets** (or a reachability invariant supplying the missing overwriters). vis-transitivity
   is carried as a hypothesis inside `lo_max_of_L_a_is_global` and is *not* the crux.
3. **Case 1.1.2 commuting sub-case — DONE** (§4, `no_lo_of_concurrent_to_L_b`, zero axioms).

`S6` (the ternary merge induction) is the ternary twin, blocked on the same convergence
lemma; by `satisfiesVCs_of_T`, closing the binary case lifts.

## 6. Assessment

The redesign attempt (a) **cleared the paper** — Case 1.1.2 is a missed argument, patched
with a zero-axiom lemma, not a real gap; (b) **validated half the redesign** — the carving
global-`lo`-max selection composes and is verified; and (c) **reduced the entire remaining
obstruction to one named, well-posed lemma**: convergence over backward-closed reachable
replica event sets. The theorem is true, the paper is fine, and "will it come through?" is
now the bounded question *"can we prove that convergence lemma?"* — a far sharper target
than the original architectural dead-end. Two verified additive lemmas
(`no_lo_of_concurrent_to_L_b`, `lo_max_of_L_a_is_global`) are the corrected building blocks.
