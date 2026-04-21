# New CRDTs (work-in-progress sandbox)

State-based CRDTs added on top of the paper's 13 benchmarks, following the same `⟨Σ, σ₀, do, merge, rc⟩` signature and the 24 RA-linearizability VCs. Files live here until they've either (a) been fully verified and are worth promoting to `CRDTs/SAL/`, or (b) been declared out of scope.

All files are on branch `wip/more-crdts`. None are referenced from the main build, so they don't affect the paper-reported numbers.

## Status

| File | VCs closed | sorried | Notes |
|---|---:|---:|---|
| `MAX_Register_CRDT.lean` | 24 | 0 | Single `ℕ` state; `do_`/`merge` both = `max`. Clean. |
| `MIN_Register_CRDT.lean` | 24 | 0 | Dual of MAX. Degenerate on `ℕ` with `init_st = 0` but still a valid CRDT; all VCs are lattice facts. |
| `LWW_Register_CRDT.lean` | 24 | 0 | State `ℕ × ℕ` (ts, value). `do_`/`merge` both use a shared `lex_max` function — this unification is what makes it verify (earlier attempts with strict `>` in `do_` and tie-break in `merge` failed `lem_0op`). |
| `Priority_Queue_Insert_Only_CRDT.lean` | 24 | 0 | Insert-only (no state-based Pop). State: `map (prio × rid × ts) elem`. |
| `Grow_Only_Set_CRDT.lean` | 24 | 0 | `set ℕ` with `add`/`union`. CRDT counterpart of the existing `Grow_Only_Set_MRDT`. |
| `Grow_Only_Multiset_CRDT.lean` | 24 | 0 | `map (rid × eid) Int`; element multiplicity is the sum across replicas. |
| `MAX_Map_CRDT.lean` | 21 | 3 | `map ℕ ℕ` with per-key max. `ind_lca_2op`, `ind_left_2op`, `ind_left_1op` fail with aesop "proof reconstruction" errors. |
| `Shopping_Cart_CRDT.lean` | 18 | 6 | `map (rid × pid) Int × map (rid × pid) Int` (per-(replica, product) PN counters). `rc_non_comm` closed with a direct PN-Counter-style proof; 6 `ind/lem` VCs remain sorried. |
| `LWW_Element_Set_CRDT.lean` | 18 | 6 | `map ℕ ℕ × map ℕ ℕ` (add timestamps, remove timestamps). Same pattern as Shopping Cart — `rc_non_comm` closed directly; 6 remain sorried. |
| `LWW_Map_CRDT.lean` | 17 | 7 | `map ℕ (ℕ × ℕ)` with `lex_max` per key. The lex_max case analysis defeats grind even on `rc_non_comm`. |
| `Add_Win_Priority_Queue_CRDT.lean` | 17 | 7 | State-based adaptation of Zhang et al. (Internetware 2023) Add-Win CRPQ. 3-component state `(A : map (ℕ×ℕ) ℕ, I : set (ℕ×ℕ×ℤ), R : set (ℕ×ℕ))` with state-dependent `Rmv` (observes current `A`). Same 7-VC family as LWW-Map fails on the 3-component unfolding. |

## What worked

- **The paper's template is a good fit.** Copying the 24-VC shape from `MAX_Register_CRDT.lean` and only changing state/op/do_/merge/eq is enough for most CRDTs.
- **`sal`'s DG stage closes most VCs on its own.** 6 out of 10 files verify all 24 VCs without any hand-written proof.
- **Direct proofs in the style of the paper's PN_Counter** (intro; simp [commutes_with]; rcases on each op; `grind +ring`) close `rc_non_comm` when `sal` fails on two-map state types.
- **Unified `lex_max` rather than `do_ strict / merge tie-break`** is load-bearing for LWW-Register — the two needed to agree on arbitrary state pairs.

## What didn't

- **Pair-valued maps (`map ℕ (ℕ × ℕ)`) stress sal.** LWW-Map hits aesop's `norm_simp` step budget on 7 VCs. Splitting into two parallel `map ℕ ℕ`s (as in `LWW_Element_Set_CRDT`, `Shopping_Cart_CRDT`) helps slightly but the same 6 `ind/lem` VCs still blow up.
- **`lex_max` with 3 nested `if-then-else` is harder than pointwise `max`.** The `rc_non_comm` direct proof that worked for Shopping Cart (two-map `Int` state with `+1`) didn't work for LWW-Map (single-map pair state with `lex_max`).
- **MAX-Map's failures are a different mode** — aesop internal "proof reconstruction" errors rather than norm-simp blow-up. These may need a different fix than the norm-simp cases.

## Next steps (not attempted here)

- For the 6 consistently-failing VCs (`ind_lca_2op`, `ind_left_2op`, `ind_lca_1op`, `ind_left_1op`, `ind_right_1op`, `lem_0op` across LWW-family files): port the `lemma_merge_do_comm`-style intermediate-lemma pattern from `PN_Counter_CRDT.lean` (the paper discharged those with Aristotle-generated proofs).
- Zhang, Ouyang, Huang, Ma 2023's CRPQ: a state-based adaptation (Add-Win) is now in `Add_Win_Priority_Queue_CRDT.lean`. The paper is op-based (prepare/effect); our adaptation transposes it to Sal's state-based `⟨Σ, σ₀, do, merge, rc⟩` model. The per-add-record accumulation from the paper's `inc` is simplified to per-element; see the file's docstring for what is and isn't preserved.
- Shapiro 2011's 2P2P-Graph — vertices and edges each as 2P-sets. Skipped as too similar to the existing `TwoPhase_Set_CRDT`.
- Byzantine-tolerant / Merkle-search-tree / JSON CRDTs (from crdt.tech) — require metadata beyond the paper's state-based model.
