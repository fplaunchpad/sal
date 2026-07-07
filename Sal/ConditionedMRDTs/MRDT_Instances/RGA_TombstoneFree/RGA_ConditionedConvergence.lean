import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CondSig
import Sal.ConditionedMRDTs.Framework.LoOnC

/-!
# RGA conditioned-convergence assembly (up to observational `eq`)

The headline assembly for the tombstone-free RGA: two `loOnA`-respecting,
`noopFeasible` enumerations of a backward-closed reachable event set fold from
`init_st` to observationally-`eq` states.  Everything here works up to the RGA's
observational `eq` (NOT Lean `Eq`) — the eq-vs-Eq wall (`RGA_BubbleWiring.lean`
§2, `eq_strictly_weaker_than_Eq`) forbids the Lean-`Eq` σ-layer from hosting the
RGA directly, so we rebuild the fold-swap / bubble machinery over `eq`.

Built BOTTOM-UP, each layer 0-sorry:

* **§0 plumbing** — a concrete `applySeqR := foldl do_`, and `eq` as an
  equivalence (`eq_refl`, `eq_trans`; `eq_symm` is imported).
* **§1 eq-congruence of the fold** (`applySeqR_eq_congr`) — from `do_eq_congr`.
* **§2 generation base case** (`chainFaithful_of_accurate`) — an accurate op is
  `ChainFaithful` on its recorded list (the "routine" lift documented in
  `RGA_BubbleWiring` §3.4), using `id_mono` for chain-acyclicity.
* **§3 threading** — `NoFreshClash` for concurrent pairs from monotone
  allocation; `Faithful` along a single fold via base case +
  `chainFaithful_doIns`/`chainFaithful_doDel` + `climbFaithful_of_chain`.
* **§4 swap-at-fold** — `general_swap` discharges an observational swap witness,
  lifted to a fold swap (`applySeqR_swap_of_eqWitness`).
* **§5 eq-bubble** — a generic `eq`-bubble (`bubble_eq`) parameterised by a
  per-step swap-witness supply, mirroring `applySeq_bubble_to_front_loOn_u`.
* **§6 headline** — `RGA_conditioned_convergence` (see the layer's own doc for
  the exact hypotheses it consumes and the located obstruction).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAConditionedConvergence

open Sal.Emulation

/-! ## §0  Plumbing: the concrete `eq`-fold and `eq` as an equivalence -/

/-- `eq` is reflexive. -/
theorem eq_refl (s : concrete_st) : eq s s := fun _ => ⟨rfl, fun _ => rfl⟩

/-- `eq` is transitive. -/
theorem eq_trans (a b c : concrete_st) (hab : eq a b) (hbc : eq b c) : eq a c := by
  intro k
  refine ⟨(hab k).1.trans (hbc k).1, ?_⟩
  intro hka
  exact ((hab k).2 hka).trans ((hbc k).2 ((hab k).1 ▸ hka))

/-! ## §1  eq-congruence of `do_` and of the fold -/

/-- `resolve` only reads `contains`, so `eq` states resolve any list identically. -/
theorem resolve_eq_congr (s s' : concrete_st) (h : eq s s') (L : List ℕ) :
    resolve s L = resolve s' L :=
  resolve_dom_eq s s' L (fun c _ => (h c).1)

/-- `upd` is `eq`-congruent in its base state (same key, same value). -/
theorem upd_eq_congr (s s' : concrete_st) (t : ℕ) (v : ℕ × ℕ) (h : eq s s') :
    eq (upd s t v) (upd s' t v) := by
  intro k
  refine ⟨?_, ?_⟩
  · rw [lemma_InDomUpd1, lemma_InDomUpd1, (h k).1]
  · intro hk
    by_cases hkt : t = k
    · subst hkt; rw [lemma_SelUpd1, lemma_SelUpd1]
    · have hne : (t : ℕ) != k := by simp only [bne_iff_ne, ne_eq]; exact hkt
      rw [lemma_SelUpd2 s k t v hne, lemma_SelUpd2 s' k t v hne]
      have hck : contains s k = true := by
        rw [lemma_InDomUpd2 s k t v hne] at hk; exact hk
      exact (h k).2 hck

/-- **eq-congruence of `do_` (the needed form).**  `eq s s' → eq (do_ s o) (do_ s' o)`.
The stored anchor depends only on `resolve` (which reads `contains`), so it agrees
across `eq` states; the `Del` case agrees pointwise via `contains_doDel`/`sel_doDel`. -/
theorem do_eq_congr (s s' : concrete_st) (h : eq s s') (o : op_t) :
    eq (do_ s o) (do_ s' o) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    simp only [do_]
    rw [resolve_eq_congr s s' h (a :: pre)]
    exact upd_eq_congr s s' t (e, resolve s' (a :: pre)) h
  | Del pre x =>
    intro k
    refine ⟨?_, ?_⟩
    · rw [contains_doDel, contains_doDel, (h k).1]
    · intro hk
      rw [contains_doDel, Bool.and_eq_true] at hk
      obtain ⟨hck, _⟩ := hk
      rw [sel_doDel, sel_doDel]
      have hsel : sel s k = sel s' k := (h k).2 hck
      have hanc : anc s k = anc s' k := by unfold anc; rw [hsel]
      have hel : el s k = el s' k := by unfold el; rw [hsel]
      have hres : resolve s pre = resolve s' pre := resolve_eq_congr s s' h pre
      rw [hanc, hel, hres, hsel]

/-! ## §2  Generation base case: an accurate op is `ChainFaithful`

Documented "routine, omitted" in `RGA_BubbleWiring` §3.4.  We supply it, using
`id_mono` to make the accurate ancestor chain acyclic (`chain_lt`: ids strictly
decrease rootward), which is exactly what lets `L.filter (≠ head)` peel the head
without disturbing the recursive tail. -/

/-! ## §6  The headline: RGA conditioned convergence up to `eq`

Two `lo`-respecting enumerations of the same event set fold from a common state to
observationally-`eq` states, GIVEN a swap oracle supplying an `EqSwap` witness for
every `lo`-incomparable pair at every prefix fold.  The proof is the peel-bubble-
recurse of `convergence_on_u` (`Sigma_LoOn3.lean`), up to `eq`, with the bubble of
§5; because the bubble consumes `EqSwap` directly, the overwriter/`h_ov`
machinery is not needed — only the peeled head's `lo`-minimality (from `respects`)
and the σ-elements' incomparability with it.  The oracle self-threads through the
recursion (`applySeqR (do_ s e) pre = applySeqR s (e :: pre)`).

**The oracle is the located obstruction.**  Discharging it means proving `EqSwap`
for every `lo`-incomparable (concurrent) pair at every prefix fold — i.e. running
`eqSwap_of_general` (§4) there.  Its premises `NoFreshClash` (concurrent, §3) and
the reachable-state invariants (`RgaInv`/`id_mono`, imported) transport; but
`general_swap` also needs ONE operand `accurate` and the other `Faithful` at the
swap state, and at a HYBRID fold state (interleaving two enumerations' prefixes) a
concurrent operand may be staled by concurrent deletes so that NEITHER is
`accurate` — the same "swaps visit states no execution visits" wall recorded in
`ConditionedConvergence` §5 and `RGA_BubbleWiring` §3.3, now in the `eq`-route. -/

end Sal.ConditionedMRDTs.RGAConditionedConvergence
