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

---

# ADDENDUM (2026-07-02, worktree `metatheory-merge-linearization`): the target lemma of §5 is FALSE; the paper has a second, deeper gap

*Independent parallel attempt. Verification legend as above. Code:
[`../Emulation/Merge_Linearization_Set.lean`](../Emulation/Merge_Linearization_Set.lean)
(0 `sorry`, kernel-clean, committed on this branch).*

## A1. The §5 blocker lemma is false ✅ (counter-model)

§5 concluded the sole blocker was *"a convergence lemma valid over merely
backward-closed reachable replica sets"* and asserted *"`convergence` over `ev₁`
is true."* **It is not.** Counter-model, built from the paper's own flagship
OR-set (add-wins, `rem →rc add`, all 24 VCs satisfiable):

- Replica A: `e = add_k` then `e₃ = rem_k` (so `vis e e₃`, `¬commute e e₃`).
- Replica B: `y = rem_k`, concurrent with both; B merges A's state *between*
  `e` and `e₃`, so B's replica set is `ev_B = {y, e}` — backward-closed.
- In the final configuration `C` (which contains `e₃`), the rc-edge
  `y →lo e` is **cancelled by the global absorber `e₃`** (`lo`'s overwriter
  existential ranges over all of `C.events`). So *both* `[y, e]` and `[e, y]`
  respect `lo C` — but they fold to different states (`{k}` vs `∅`).

Convergence over backward-closed replica sets w.r.t. `lo C` is therefore
unprovable — the merge-linearization induction cannot be closed on the §5
plan. **Machine-checked** ✅ in
[`../Emulation/Convergence_CounterModel.lean`](../Emulation/Convergence_CounterModel.lean)
(0 `sorry`): `convergence_over_backward_closed_subsets_false` exhibits the
model (`AWSet`, with the full convergence toolkit proved for it, including
`cond_comm_lift`), the 3-event configuration, and the two `lo C`-respecting
enumerations with different folds; `loOn_keeps_the_edge` demonstrates the A2
repair on the same instance; `AWSet_shared_peel_1op_false` additionally shows
the `shared_peel_1op` crutch VC of `SatisfiesVCs` is false for the paper's
own OR-set skeleton — the current bundle excludes exactly the RDTs with
non-trivial `rc`.

## A2. The fix for A1 — set-relative `lo`, machine-checked ✅

The absorber existential must range over the *version's own event set*:

    loOn C ev e₁ e₂ ⟺ (vis e₁ e₂ ∧ ¬⇄) ∨ (∥ ∧ rc = Fst ∧ ¬∃ e₃ ∈ ev. vis e₂ e₃ ∧ ¬⇄)

In the counter-model, `loOn C ev_B` *keeps* `y → e`, so only the fold-correct
`[y, e]` respects it. `lo C ⊆ loOn C ev` pointwise, so a `loOn`-respecting
witness still meets the paper's Def-lin obligation. `loOn C ev` depends only
on `vis/rc/⇄` restricted to `ev` — a stable per-version invariant.

**This matches the paper's own implicit usage**: appendix.tex's Merge case
(line ~271) works with per-version `lo_i` whose absorber clause is
`∃ e'' ∈ L(v_i)`, and asserts *"`lo` between two events should remain the same
in all versions"* (`lo_i ⟺ lo_m`). The **⟹ direction of that stability claim
is false** — a shared event can gain an absorber from the *other* branch's
local events (that is exactly A1) — while the ⟸ direction is `loOn`
monotonicity. New machine-checked layer (all 0-sorry):

| Result | Content |
|---|---|
| `convergence_on` | two `loOn C ev`-respecting perms of `ev` fold equal — **no closure hypotheses at all**: each failed `loOn`-edge hands the bubble-sort argument an absorber *inside `ev`* |
| `exists_loOn_maximal`, `exists_loOn_respecting_perm` | `loOn C T` is acyclic on `T` (`no_rc_chain` + absorber-kill + `vis` trans/irrefl), so maximal elements and respecting enumerations exist |
| `perm_ending_in_loOn_max` | re-permute a witness to end in any `loOn`-max element, state-preserving |
| `normalize_peel_tail` | after peeling a tail `t`, re-sort the front to respect the *shrunken-set* relation `loOn C (ev∖{t})`, fold-preserving (the lost absorber is `t` itself, still applied last) |

## A3. The deeper gap: the paper's re-permutation step is unsound, and a reachable configuration defeats *every* bottom-up peel ✅ (semantic analysis) / ❓ (for the authors)

The paper's Merge case repeatedly argues (appendix.tex:323, 343): *"since
`lo` ordering between events remains the same in all versions, and since
versions v₁, v₂ were already linearizable, there would exist sequences
leading to the states … such that e_i would appear at the end."* This
conflates *"an `lo`-extension ending in `e_i` exists"* (true, permutation-level)
with *"a **witness with the same fold** ending in `e_i` exists"* (requires
convergence over the version's event set — which by A1 is **false** for the
paper's global-absorber `lo`). Concrete reachable defeater, 4 events on one
OR-set key, 3 replicas (`t(b) ≠ t(d)` arbitrary):

- r1: `d = add_k`, then `a = rem_k` (`vis d a`); r2: `b = add_k`, then
  `c = rem_k` (`vis b c`).
- r3 pulls `{d}` from r1 early; r1 pulls `{b}` from r2 before `c`; r2 pulls
  `{d}` from r3 after `c`. Result: `ev₁ = {d,a,b}`, `ev₂ = {b,c,d}`,
  `s₁ = {b}`-tag-only, `s₂ = {d}`-tag-only, `merge s₁ s₂ = ∅`.
- Version-local orders are forced: `loOn(ev₁)` mandates `d→a` (vis) and
  `a→b` (rc-edge alive: `b`'s only absorber `c ∉ ev₁`); `loOn(ev₂)` mandates
  `b→c`, `c→d`. So **every witness of `s₁` ends in `b`; every witness of
  `s₂` ends in `d`.**
- Merged-set edges: `loOn(ev₁∪ev₂) = {b→c, d→a}` (both rc-edges die — the
  absorbers are now inside). Valid final witnesses end in `a` or `c` only;
  e.g. `[b,c,d,a]` folds to `∅ = merge s₁ s₂` ✓ (the *theorem* holds here).
- But **no bottom-up peel can produce it**: `a`,`c` are globally appendable
  yet *un-endable in their own sides* (`a→b`, `c→d` are mandatory locally);
  `b`,`d` are endable in their sides yet *not appendable* (`b→c`, `d→a` are
  vis-edges, alive in every relation). Peeling `a` would need
  `merge s₁ s₂ = a(merge s₁' s₂)` with `s₁ = a(s₁')` — but `s₁ = {b}` has
  **no** decomposition with `a` last (fold-wrong; only `[d,a,b]`-class works).
  The `L^a/L^b` carving classifies `a ∈ L₁^a` and the paper *would* peel it
  via the quoted false step. The 0-OP/1-OP/2-OP rules all fail here (checked
  against every disponible Lean form: `lem_0op` needs both sides to end in
  the shared event; `merge_peel_shared` needs the peeled event strictly
  local; `bottomUp_2op_reachable` needs strict rc + distinctness that shared
  tails violate).

**Consequences.**

1. The flat distinct-last induction (current `distinct_last_case`) *and* the
   carving-based redesign of §5 are both structurally incapable of closing
   the Merge case: sorries `:2816/:2987/:3003/:3009` protect sub-cases that
   contain this configuration. The two "false forward-closure" sorries
   `:4443/:4446` are unfixable as diagnosed in §3.
2. The paper's proof of Theorems 1–2 has a hole **strictly deeper than the
   Case 1.1.2 erratum of §4**: the side-witness re-permutation step. The
   theorem itself *may* still be true (it holds semantically on the
   defeater), but a new proof idea is required, not a patch.
3. Candidate repairs (open research question, for the authors and for us):
   - **Merge associativity as an explicit VC.** `s₁` in the defeater is
     itself a merge; with associativity+commutativity of `merge`, the merge
     tree can be re-associated so that peels always happen at *segment*
     boundaries (per-replica op runs), where "side ends in `e`" is real.
     All practical CRDTs/MRDTs have associative merges; the 24 VCs do not
     imply it.
   - **Provenance/segment-aware induction**: strengthen the RA-lin invariant
     to remember the merge tree (each replica state = join of per-replica
     op-sequence prefixes), and induct on segments rather than single
     events. This is the direction the tombstone-free RGA work already
     pioneers (path-carrying ghost state).
   - Determine whether the 24 VCs alone are *insufficient* — i.e. exhibit a
     VC-satisfying `D` and a reachable configuration violating RA-lin. The
     defeater's shape is the place to look: the VCs pin `merge` down only on
     update-shaped arguments, and nothing forces
     `merge s₁ s₂ = fold [b,c,d,a]` for adversarial `D`.

## A4. Status of this branch

- `Merge_Linearization_Set.lean`: the A2 layer, complete and kernel-clean.
- The 6 sorries of `Merge_Linearization.lean` are **not closable as posed**
  (A1/A3); the correct next milestones are (i) the Lean counter-model of A1,
  (ii) the associativity-VC or segment-induction redesign of the Merge case,
  (iii) only then the ternary S6 lift.

## A5. The repair, scoped: canonical states, the Join Lemma, and why "just add associativity" is not enough ✅ (partially machine-checked)

`convergence_on` makes every finite event set denote a **unique state** —
the fold of any `loOn C ev`-respecting enumeration. New machine-checked
layer (`Merge_Linearization_Set.lean` §6, 0 sorry):

| Result | Content |
|---|---|
| `IsCanonicalState` + `_unique`/`_exists`/`_lo_witness` | σ(ev) well-defined; canonical witnesses satisfy the paper's Def-lin |
| `isCanonicalState_peel` | σ(ev) = update σ(ev∖{e}) e for any `loOn(ev)`-max `e` — the *sound* replacement for the paper's broken re-permutation step |
| `isCanonicalState_extend` | the Apply case at the σ-level |
| `JoinLemma` (statement) + `merge_linearization_of_join` | **the entire merge case reduces to**: σ(ev₁∪ev₂) = merge σ(ev₁) σ(ev₂) for backward-closed sets |

So the metatheorem is now: *strengthened RA-lin invariant = "every replica
holds the canonical state of its event set"*; Apply = `_extend`; Merge =
**Join Lemma**. Witness lists are gone from the induction.

**Status of the Join Lemma.** Its natural induction peels a
`loOn(ev₁∪ev₂)`-maximal `e` (exists, ✅) and needs the contextual identity
`merge σ(ev₁) σ(ev₂) = update (merge σ(ev₁∖e) σ(ev₂)) e` (local case; 0-OP
`lem_0op` covers the shared case when `e` is both-sides-max). Checked by
hand on `AWSet` *including the A3 defeater*: the identity is **true** under
exactly the available hypotheses — `e` `loOn(∪)`-max forces every
non-commuting `x ∈ ev₂∖ev₁` to be either `vis`-ordered against `e`
(excluded by backward closure) or absorbed *inside `ev₂`* (the absorber is
`vis`-after `x`, so backward closure of `ev₂` traps it there). Note the A3
defeater is no obstacle at the σ-level: `merge s₁ s₂ = update (merge
σ({d,b}) σ(ev₂)) a` holds even though `s₁ ≠ update σ({d,b}) a` — the merge
supplies the absorber that the side lacks.

**Why no unconditional VC captures the peel.** The candidate
`∀ a b e₁ e₂, (rc(e₂,e₁)=Fst ∨ e₁⇄e₂) → merge (update a e₁) (update b e₂) =
update (merge a (update b e₂)) e₁` is **false for the two-key OR-set**:
`e₁ = rem_k`, `e₂ = add_j` (`j ≠ k`, they commute — premise satisfied),
`b` holding a live `k`-add that `a` never saw: the RHS `rem_k` kills `b`'s
`k`-add, the LHS cannot. The saving condition is contextual
(`e₁` `loOn(∪)`-maximal ⟹ `b`'s non-commuting content is absorbed), not
equational. Consequence: **merge associativity alone does not discharge the
Join Lemma** — assoc/inflation/monotonicity (the lattice VCs) give the easy
`⊑`-direction, but the peel needs a *contextual* induction threading
`loOn`-maximality and backward closure down to `cond_comm`-style leaf VCs.

**The sharpened open problem** (was: "prove the §5 convergence lemma" —
false; now): *prove `JoinLemma D` from `SatisfiesVCs D` (+ lattice VCs:
merge associativity, update inflationarity/monotonicity), by induction on
`|ev₁ ∪ ev₂|` peeling `loOn`-maximal events, with the contextual peel
identity derived from `cond_comm_lift` + backward closure.* Everything
around it is proved; a counter-model to *this* statement would show the
paper's theorem needs stronger hypotheses than its 24 VCs even up to
lattice axioms.
