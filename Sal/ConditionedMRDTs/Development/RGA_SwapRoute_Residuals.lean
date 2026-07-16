import Sal.ConditionedMRDTs.Development.RGA_GeneralSwap
import Sal.ConditionedMRDTs.Development.RGA_ConvergenceEq
import Sal.ConditionedMRDTs.Development.RGA_BubbleWiring
import Sal.ConditionedMRDTs.Development.RGA_FaithfulThreading_Gate
import Sal.ConditionedMRDTs.Development.RGA_ChainFaithful_doDel
import Sal.ConditionedMRDTs.Development.RGA_BothFaithfulSwap
import Sal.ConditionedMRDTs.Development.RGA_InterleavedThreading
import Sal.ConditionedMRDTs.Development.RGA_StaledDel_Gate
import Sal.ConditionedMRDTs.Development.RGA_Faithful_PBT
import Sal.ConditionedMRDTs.Development.RGA_UpdateConvergence_Final
import Sal.ConditionedMRDTs.Development.RGA_MergeThreadDischarge
import Sal.ConditionedMRDTs.Development.RGA_GenDischarge
import Sal.ConditionedMRDTs.Development.RGA_EnablementBase
import Sal.ConditionedMRDTs.Development.RGA_RecPathFaithful
import Sal.ConditionedMRDTs.Development.RGA_WfOpReachable
import Sal.ConditionedMRDTs.Development.RGA_UpdateConvergence_Assembly
import Sal.ConditionedMRDTs.Development.RGA_OrderBridge
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_EqJoin_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_Final
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeBranchNew
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeFoldChain

/-!
# Residuals of the retired swap/faithfulness route

Theorems that depend on the retired swap-route files while the capstone
does not depend on them — cut from living chain files and from the retired
files themselves (dependency-ordered; full names unchanged, declared in
their original namespaces).
-/

set_option maxHeartbeats 1000000

/-! ## Cut from `RGA_ConditionedConvergence.lean` -/

namespace Sal.ConditionedMRDTs.RGAConditionedConvergence
open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap
open Sal.ConditionedMRDTs.RGABubbleWiring
open Sal.ConditionedMRDTs.RGAChainFaithfulDoDel

/-- One good step preserves `ChainFaithful`. -/
theorem chainFaithful_doStep (s : concrete_st) (L : List ℕ) (o : op_t)
    (hg : GoodStep s L o) (hcf : ChainFaithful s L) : ChainFaithful (do_ s o) L := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    obtain ⟨ht0, htL⟩ := hg
    exact chainFaithful_doIns s t r e a pre L ht0 htL hcf
  | Del pre x =>
    obtain ⟨h0, hacc⟩ := hg
    have hacc' : accurate (t, r, .Del pre x) s := hacc
    exact chainFaithful_doDel s t r x pre L h0 hacc' hcf


/-- **Threading (Layer 3).**  `ChainFaithful` is preserved along a `GoodFold`.
With `climbFaithful_of_chain` this threads `Faithful` along any fold whose steps
are fresh non-clashing `Ins`s / accurate `Del`s — the single-enumeration σ-walk.
(The cross-enumeration HYBRID states are where a concurrent `Del` need not be
accurate; that is the located obstruction, shared with the swap oracle of §6.) -/
theorem chainFaithful_fold (L : List ℕ) :
    ∀ (π : List op_t) (s : concrete_st),
      GoodFold L s π → ChainFaithful s L → ChainFaithful (applySeqR s π) L := by
  intro π
  induction π with
  | nil => intro s _ hcf; exact hcf
  | cons o rest ih =>
    intro s hgf hcf
    obtain ⟨hstep, hrest⟩ := hgf
    rw [applySeqR_cons]
    exact ih (do_ s o) hrest (chainFaithful_doStep s L o hstep hcf)


/-- On an all-dead state (`contains s _ = false` everywhere) every list is
`ChainFaithfulAux` at any fuel: each level's `resolve` is `0`, which is dead, so
the obligation is vacuous. -/
theorem chainFaithfulAux_empty (s : concrete_st) (hempty : ∀ k, contains s k = false) :
    ∀ n (L : List ℕ), ChainFaithfulAux s n L := by
  intro n
  induction n with
  | zero => intro L; exact trivial
  | succ m _ =>
    intro L
    simp only [ChainFaithfulAux]
    intro hlive
    rw [hempty (resolve s L)] at hlive
    exact absurd hlive (by simp)


/-- **Reachability-invariant base case.**  At `init_st` (empty) EVERY recorded
list is `ChainFaithful` — vacuously, since nothing is live.  This is the base of
the `ChainFaithful`-at-every-fold reachability invariant whose inductive step is
the located obstruction (§6). -/
theorem chainFaithful_init (L : List ℕ) : ChainFaithful init_st L :=
  chainFaithfulAux_empty init_st (fun k => contains_init k) L.length L


/-- The fuel-indexed engine: an accurate chain `leaf :: p` is `ChainFaithfulAux`
at any fuel `≥` its length.  Induction on `p`; the head peels off cleanly because
`chain_lt` makes `leaf ∉ p`. -/
theorem chainAux_accurate (s : concrete_st) (hmono : id_mono s) (h0 : contains s 0 = false) :
    ∀ (p : List ℕ) (leaf : ℕ) (n : ℕ), contains s leaf = true → IsAncPath s leaf p →
      (leaf :: p).length ≤ n → ChainFaithfulAux s n (leaf :: p) := by
  intro p
  induction p with
  | nil =>
    intro leaf n hleaf hpath hlen
    cases n with
    | zero => simp only [List.length_cons, List.length_nil] at hlen; omega
    | succ m =>
      have hres : resolve s [leaf] = leaf := resolve_live_head s leaf [] hleaf
      have hfl : ([leaf] : List ℕ).filter (fun x => x != leaf) = [] := by simp
      simp only [ChainFaithfulAux]
      intro _
      simp only [hres]
      refine ⟨?_, ?_⟩
      · rw [hfl]
        simp only [IsAncPath] at hpath
        rw [show resolve s ([] : List ℕ) = 0 from rfl, hpath]
      · rw [hfl]; exact aux_nil s h0 m
  | cons c cs ih =>
    intro leaf n hleaf hpath hlen
    have hp := hpath
    simp only [IsAncPath] at hpath
    obtain ⟨_, hcc, hrest⟩ := hpath
    cases n with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ m =>
      have hres : resolve s (leaf :: c :: cs) = leaf := resolve_live_head s leaf (c :: cs) hleaf
      have hf' : (c :: cs).filter (fun x => x != leaf) = c :: cs := by
        apply List.filter_eq_self.mpr
        intro a ha
        have hlt : a < leaf := chain_lt s hmono h0 (c :: cs) leaf hleaf hp a ha
        simp only [bne_iff_ne, ne_eq]; omega
      have hL2 : (leaf :: c :: cs).filter (fun x => x != leaf) = c :: cs := by
        rw [List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        exact hf'
      simp only [ChainFaithfulAux]
      intro _
      simp only [hres]
      refine ⟨?_, ?_⟩
      · rw [hL2]
        have hres2 := isancpath_resolve_self_filter s leaf (c :: cs) hp
        rw [hf'] at hres2
        exact hres2
      · rw [hL2]
        exact ih c m hcc hrest (by simp only [List.length_cons] at hlen ⊢; omega)


/-- Uniform accurate-chain form: `(leaf = 0 ∧ p = []) ∨ (live ∧ IsAncPath)`
gives `ChainFaithful s (leaf :: p)`. -/
theorem chainFaithful_of_accurate_chain (s : concrete_st) (hmono : id_mono s)
    (h0 : contains s 0 = false) (leaf : ℕ) (path : List ℕ)
    (h : (leaf = 0 ∧ path = []) ∨ (contains s leaf = true ∧ IsAncPath s leaf path)) :
    ChainFaithful s (leaf :: path) := by
  rcases h with ⟨hl0, hpnil⟩ | ⟨hlive, hpath⟩
  · subst hl0; subst hpnil
    show ChainFaithfulAux s 1 [0]
    have hr0 : resolve s ([0] : List ℕ) = 0 := by
      show (if contains s 0 then (0 : ℕ) else resolve s []) = 0
      rw [h0]; rfl
    simp only [ChainFaithfulAux]
    intro hlive
    rw [hr0, h0] at hlive
    exact absurd hlive (by simp)
  · exact chainAux_accurate s hmono h0 path leaf ((leaf :: path).length) hlive hpath (le_refl _)


/-- **Generation base case (Layer 2).**  `contains s 0 = false → id_mono s →
accurate o s → ChainFaithful s (recList o)`.  Dispatches `Ins`/`Del` to the
uniform chain form. -/
theorem chainFaithful_of_accurate (s : concrete_st) (o : op_t) (hmono : id_mono s)
    (h0 : contains s 0 = false) (hacc : accurate o s) :
    ChainFaithful s (recList o) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    show ChainFaithful s (a :: pre)
    apply chainFaithful_of_accurate_chain s hmono h0 a pre
    simpa only [accurate, opLeaf, opPath] using hacc
  | Del pre x =>
    show ChainFaithful s (x :: pre)
    apply chainFaithful_of_accurate_chain s hmono h0 x pre
    simpa only [accurate, opLeaf, opPath] using hacc

/-! ## §3  Threading `Faithful` / `NoFreshClash` along a fold

The per-step preservation lemmas are imported (`chainFaithful_doIns` for a fresh
non-clashing `Ins`, `chainFaithful_doDel` for an ACCURATE `Del`).  Together with
the §2 base case and `climbFaithful_of_chain` they thread `ChainFaithful` — and
hence `Faithful` — along any fold whose every step is "reachability-good"
(`GoodFold`).  `NoFreshClash` for concurrent pairs is monotone allocation. -/


/-- **`general_swap_bothFaithful` discharges `EqSwap` — NO operand `accurate`
(Layer 4, doubly-staled case).**  Both `a` and `b` need only be `Faithful` (each
staled by concurrent deletes); the swap still holds.  This is the lemma for the
hybrid state where NEITHER operand is `accurate` — it dissolves the earlier
"one operand must be accurate" reading of the obstruction. -/
theorem eqSwap_of_bothFaithful (s : concrete_st) (a b : op_t)
    (hdist : a.1 ≠ b.1) (h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hfa : fresh_ts a s) (hfb : fresh_ts b s)
    (hfaith_a : Faithful a s) (hfaith_b : Faithful b s)
    (hclash_ab : NoFreshClash a b) (hclash_ba : NoFreshClash b a) :
    EqSwap a b s :=
  general_swap_bothFaithful s a b hdist h0 hwf hmono hfa hfb hfaith_a hfaith_b hclash_ab hclash_ba

/-! ## §5  The generic `eq`-bubble

Mirrors `applySeq_bubble_to_front_loOn_u` (`Sigma_LoOn3.lean`) but up to `eq`:
bubble `e` to the front of `σ` by iterated adjacent swaps, transporting `eq`
through the fold with §1.  The per-step swap witnesses are supplied by `h_sw`
(whoever calls the bubble must produce them — for convergence, the swap oracle). -/


/-- **`general_swap` discharges `EqSwap` (Layer 4).**  Under the reachable-state
invariants, freshness, `Faithful a`, `accurate b`, and `NoFreshClash a b`, the
observational swap witness holds. -/
theorem eqSwap_of_general (s : concrete_st) (a b : op_t)
    (hdist : a.1 ≠ b.1) (h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hb : accurate b s) (hfa : fresh_ts a s) (hfb : fresh_ts b s)
    (hfaith : Faithful a s) (hclash : NoFreshClash a b) :
    EqSwap a b s :=
  general_swap s a b hdist h0 hwf hmono hb hfa hfb hfaith hclash


/-- **`NoFreshClash` for concurrent pairs.**  Under monotone allocation (`b`'s
fresh `Ins` id exceeds every id `a` recorded) or a genuine `Del` target, the
no-fresh-clash side condition holds.  Dispatches `b`'s op kind to the imported
`noFreshClash_of_freshIns` / `noFreshClash_of_del`. -/
theorem noFreshClash_concurrent (a b : op_t)
    (hIns : ∀ t2 r2 e2 anch2 pre2, b = (t2, r2, .Ins e2 pre2 anch2) →
      ∀ c ∈ recList a, c < t2)
    (hDel : ∀ t2 r2 xb pre2, b = (t2, r2, .Del pre2 xb) → xb ≠ 0) :
    NoFreshClash a b := by
  obtain ⟨t2, r2, op2⟩ := b
  cases op2 with
  | Ins e2 pre2 anch2 =>
    exact noFreshClash_of_freshIns a t2 r2 e2 anch2 pre2 (hIns t2 r2 e2 anch2 pre2 rfl)
  | Del pre2 xb =>
    exact noFreshClash_of_del a t2 r2 xb pre2 (hDel t2 r2 xb pre2 rfl)

/-! ## §4  Swap-at-fold up to `eq`

An observational swap witness at a fold state lifts to a fold swap (transported
through the suffix by §1's `applySeqR_eq_congr`); `general_swap` discharges the
witness under the faithfulness/accuracy side conditions. -/


/-- **RGA conditioned convergence, swap discharged from BOTH-`Faithful` (Layer 6).**
The corrected form: the swap oracle's semantic content is discharged by
`eqSwap_of_bothFaithful` — NEITHER swapped operand need be `accurate`, both may be
concurrently staled.  What remains (`hReady`) is purely a *threading* oracle: at
every prefix fold `applySeqR init_st pre`, each `lo`-incomparable pair `a b ∈ ev`
is `Faithful` there, mutually `NoFreshClash`, fresh, on the reachable-state
invariants.  There is no `accurate` anywhere.  So the residual obligation is
exactly `Faithful`-at-fold + `NoFreshClash` + `RgaInv`/`id_mono`-at-fold — see the
obstruction note below for which of these transport and which does not. -/
theorem RGA_conditioned_convergence_bothFaithful (lo : op_t → op_t → Prop) (ev : Set op_t)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ ev) (h₂p : listPermOf π₂ ev)
    (h₁r : respects π₁ lo) (h₂r : respects π₂ lo)
    (hReady : ∀ (pre : List op_t) (a b : op_t),
        (∀ x ∈ pre, x ∈ ev) → pre.Nodup → respects pre lo →
        a ∈ ev → b ∈ ev → a ∉ pre → b ∉ pre → a ≠ b → ¬ lo a b → ¬ lo b a →
        (∀ z ∈ ev, z ≠ a → lo z a → z ∈ pre) → (∀ z ∈ ev, z ≠ b → lo z b → z ∈ pre) →
        a.1 ≠ b.1 ∧ contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
        ∧ id_mono (applySeqR init_st pre)
        ∧ fresh_ts a (applySeqR init_st pre) ∧ fresh_ts b (applySeqR init_st pre)
        ∧ Faithful a (applySeqR init_st pre) ∧ Faithful b (applySeqR init_st pre)
        ∧ NoFreshClash a b ∧ NoFreshClash b a) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  apply RGA_conditioned_convergence lo ev π₁ π₂ h₁p h₂p h₁r h₂r
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  obtain ⟨hd, h0, hwf, hmono, hfa, hfb, hFa, hFb, hcab, hcba⟩ :=
    hReady pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact eqSwap_of_bothFaithful (applySeqR init_st pre) a b hd h0 hwf hmono hfa hfb hFa hFb hcab hcba

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS AFTER THE GAP-1 FIX — what closes, and the one fact M1 still lacks.

   GAP-1 (the over-quantified, unsatisfiable oracle) is FIXED above: the oracle of
   `eq_convergence` / `RGA_conditioned_convergence(_bothFaithful)` now ranges only
   over ELIGIBLE prefixes `pre` — nodup, `respects`-ordered, `E`-drawn, disjoint
   from the swapped pair, with BOTH events ENABLED (their `lo`-past `⊆ pre`).  This
   is exactly the delivery-prefix class M1/M2 speak about, and it self-threads
   through the recursion.  So `hReady` is now SATISFIABLE.

   Discharging the ten `hReady` conjuncts at an eligible prefix
   `s' = applySeqR init_st pre` (pre a `lo`-respecting `E`-prefix, `a`,`b` enabled):

   • `a.1 ≠ b.1`               — M2 `ConditionedConfiguration.distinctTs`.
   • `RgaInv s'` (`contains0`,`wf`) — RGA `RgaInv_do_opOK` transport over `pre`
                                  (each `E`-event `opOK`), or M2 `inv_fold` given
                                  `noopFeasible pre`.
   • `id_mono s'`              — GAP 3: RGA `id_mono` state-form; M2 emits the
                                  `causal_mono` vis/id-form (`id_mono_doIns/_doDel`
                                  transport under `mono_alloc`).
   • `fresh_ts a s'`,`fresh_ts b s'` — GAP 3: state-absence; M2 `freshTs` emits
                                  id-distinctness (`∀x∈pre, x.1≠a.1`); needs a
                                  contains-tracking step to reach state-absence.
   • `NoFreshClash a b`,`… b a` — GAP 3: RGA recList-form; M2
                                  `noFreshClash_concurrent` emits the vis-ancestor
                                  id-form (`§3 noFreshClash_concurrent` bridges it
                                  once `recList a = ids of {a} ∪ vis-ancestors a`).
   • `Faithful a s'`,`Faithful b s'` — **GAP 2, the one FATAL residue.**

   **GAP 2 (M1 does not provide this).**  `Faithful a s'` reduces (via
   `climbFaithful_of_chain`) to `ChainFaithful (recList a) (applySeqR init_st pre)`.
   M1 proves `ChainFaithful (recList w)` only at `foldDo s_c concurrent`
   (`chainFaithful_at_enablement`): `w`'s causal past folded CONTIGUOUSLY FIRST to
   `s_c` (where `HistFaithful s_c w` = `accurate w s_c`), then an `IncompFold` of
   concurrent steps.  The engine's eligible `pre` is a `lo`-INTERLEAVING: `a`'s
   causal past is present (enablement) but interleaved with concurrent ops, NOT
   contiguous-first, so `applySeqR init_st pre ≠ foldDo s_c concurrent`.

   The CONCURRENT-step half is covered — `RGAFaithfulThreadingGate.IncompFold`
   threads fresh non-clashing `Ins`s and *`Faithful`* `Del`s
   (`chainFaithful_doDel_faithful`, no `accurate`), so a concurrent staled `Del` is
   fine (this dissolves the old "interleaving-feasibility Del" worry).  The
   UNCOVERED half is the ANCESTOR steps: folding `a`'s own causal-ancestor `Ins`s
   (`w'.id ∈ recList a`) while `a` is still mid-build (`a` not yet `accurate`, so
   M1's `chainFaithful_doIns_reachable`, which needs `HistFaithful s a`, does NOT
   fire).  The single missing M1 lemma is the reachable-regime accurate-ancestor
   `Ins` BUILD-UP (deferred at `RGA_FaithfulThreading_Gate.lean:421-424`):

       accurate (t,r,.Ins e p a') s → [reachability of L] →
       ChainFaithful s L → ChainFaithful (do_ s (t,r,.Ins e p a')) L   -- even t ∈ L

   equivalently: an M1 variant of `chainFaithful_at_enablement` accepting an
   INTERLEAVED `lo`-respecting prefix (causal past a sub-list, all other steps
   `IncompStep`s), not the causal-past-contiguous `foldDo s_c concurrent`.

   VERDICT: with GAP-1 fixed, `RGA_update_convergence` reduces to exactly ONE open
   M1 fact — the interleaved-prefix / accurate-ancestor-`Ins` build-up lemma — plus
   the mechanical GAP-3 id/state-form bridges.  It is NOT the swap
   (`eqSwap_of_bothFaithful`, both-`Faithful`), NOT the concurrent `Del`
   (`chainFaithful_doDel_faithful`), NOT the oracle over-quantification (fixed
   here).  Routed to M1.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §7  Axiom audit — every headline kernel-clean.
All decls depend only on `propext, Classical.choice, Quot.sound`: no `sorryAx`,
no `native_decide`/`ofReduceBool`; the `Merge_Linearization` sorries are not
transitively touched. -/

#print axioms applySeqR_eq_congr
#print axioms chainFaithful_of_accurate
#print axioms chainFaithful_fold
#print axioms chainFaithful_init
#print axioms noFreshClash_concurrent
#print axioms eqSwap_of_general
#print axioms eqSwap_of_bothFaithful
#print axioms bubble_eq
#print axioms eq_convergence
#print axioms RGA_conditioned_convergence
#print axioms RGA_conditioned_convergence_bothFaithful

end Sal.ConditionedMRDTs.RGAConditionedConvergence

/-! ## Cut from `RGA_Instance.lean` -/

namespace Sal.ConditionedMRDTs.RGAInstance
open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient

/-- `WfOpReachable RGACondSig' WfOp WfOpGen` — `rga_wfOpReachable` transported. -/
theorem rga_wfOpReachable' : WfOpReachable RGACondSig' WfOp WfOpGen := by
  intro ρ hnd hts hgen
  rw [wfChain_transport]
  exact rga_wfOpReachable ρ hnd hts hgen

/-! ## §7. The `≈`-Join `EqJoinLemma3C` — the second (open) residual.

`EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOp` demands, for every `vis`, that
`mergeL s₀ s₁ s₂` be `IsCanonicalStateEq`-canonical for `ev₁ ∪ ev₂`, i.e. `≈`-equal
to the RAW fold `applySeq init_st ρ` of some `ρ` respecting `loOnEq rgaEqEquiv'
WfOp vis (ev₁∪ev₂)`.  The RGA has the two ingredients in principle —
`RGA_CanonFoldOK.RGA_update_convergence_final` (all respecting enumerations of a
backward-closed set fold `≈`-equal) and `RGA_MergeFoldChain.eq_merge_two_sided_final`
(`merge l a b ≈ fold l π`) — but they do NOT compose into this shape here, for two
reasons that this file makes precise rather than papering over:

* **Order mismatch (`loOnA` vs `loOnEq`).**  Every RGA convergence/merge lemma is
  stated over `loOnA` (`ConditionedConvergence.lean`, the *applicability-aware*
  order forced by the G2 refutation `G2_conditioned_convergence_refuted`), whereas
  the framework's canonical states live over `loOnEq` (the `eqCommutesOn`-based
  order).  No `loOnEq ⊆ loOnA` bridge lemma exists in the repo; without it the
  respecting-enumeration hypotheses of the two engines are incomparable.

* **Merge=fold is not yet a clean bridge.**  `eq_merge_two_sided_final` still
  carries `hD`/`hB`/`hBE`/`hcm`/`hbridge`(`CanonBirthBridge`)/`hMSR` — a
  domain/element/anchor apparatus plus a merge-fold reachability oracle — and its
  `hbridge`/`hBN` slot is the still-open GAP-1 (the branch-new-survivor
  cross-forest anchor identity, per `RGA_MergeThreadDischarge`'s status block).

Both are genuine, not cosmetic; so `rga_EqJoinLemma3C` is NOT constructed, and the
`≈`-Join is threaded as a hypothesis into the capstone below.  A precisely-located
adapter gap, per the honesty contract. -/

/-! ## §8. The capstone — `RA_linearizable_up_to_eq` on the RGA.

Every metatheorem input EXCEPT the two residuals of §5 (`inv_update`) and §7
(the `≈`-Join) is discharged concretely for `RGACondSig'`: `rgaEqEquiv'`,
`rgaCongVC'` (FULL — all three fields, `mergeL_congr` via `merge_eq_congr_inv`),
`rgaInvInvVC'` (FULL — `wf_congr` + `applicable_congr`), and `rga_wfOpReachable'`.
The two residuals are threaded as hypotheses `hP` (the full `InvPres`, whose
`inv_init`/`inv_mergeL` fields are proved in §5) and `hJoinEq`.  Given them, the
RGA quotient is per-version RA-linearizable up to `≈` on every reachable
configuration whose events are all `WfOpGen`. -/

theorem RGA_is_RA_linearizable
    (hP : InvPres RGACondSig' WfOp)
    (GenDisc : (Op RGACondSig'.AppOp → Op RGACondSig'.AppOp → Prop) →
        Set (Op RGACondSig'.AppOp) → Prop)
    (hJoinEq : EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOp GenDisc)
    (C : Configuration (QSig rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC'))
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC')).ReachableFrom
        (initConfig (QSig rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC') trivial) C)
    (hGenC : ∀ o ∈ (Configuration.core C).events, WfOpGen o)
    (hGenDisc : GDSupply rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC' GenDisc
        (Configuration.core C)) :
    IsRALinearizable3 C :=
  RA_linearizable_up_to_eq rgaEqEquiv' WfOp hP rgaCongVC' rgaInvInvVC'
    WfOpGen rga_wfOpReachable' GenDisc hJoinEq C hReach hGenC hGenDisc

#print axioms RGA_is_RA_linearizable

end Sal.ConditionedMRDTs.RGAInstance

/-! ## Cut from `RGA_UpdateConvergence_Final.lean` -/

namespace Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal
open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash ClimbFaithful)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList ChainFaithful climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAConditionedConvergence
open RGARecPathFaithful
open RGAInterleavedThreading
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (RGA_conditioned_convergence_bothFaithful)
open Sal.ConditionedMRDTs.RGAUpdateConvergenceAssembly (fresh_ts_state_of_ids)

/-- **Update-layer convergence (CONDITIONAL on `hReach`).**  Two `loOnA`-respecting
enumerations of a backward-closed `E` fold from `init_st` to observationally-`eq`
states.  No swap/`EqSwap`/`hReady` premise survives; the residual `hReach` supplies
exactly the seven reachability/linkage conjuncts `C` cannot (STATUS block). -/
theorem RGA_update_convergence
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E))
    (hReach : ∀ (pre : List op_t) (a b : op_t),
        (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
        a ∈ E → b ∈ E → a ∉ pre → b ∉ pre → a ≠ b →
        ¬ loOnA RGACondSig Cfg E a b → ¬ loOnA RGACondSig Cfg E b a →
        (∀ z ∈ E, z ≠ a → loOnA RGACondSig Cfg E z a → z ∈ pre) →
        (∀ z ∈ E, z ≠ b → loOnA RGACondSig Cfg E z b → z ∈ pre) →
        contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
        ∧ id_mono (applySeqR init_st pre)
        ∧ Faithful a (applySeqR init_st pre) ∧ Faithful b (applySeqR init_st pre)
        ∧ NoFreshClash a b ∧ NoFreshClash b a) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  apply RGA_conditioned_convergence_bothFaithful
    (loOnA RGACondSig Cfg E) E π₁ π₂ h₁p h₂p h₁r h₂r
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  obtain ⟨h0, hwf, hmono, hFa, hFb, hcab, hcba⟩ :=
    hReach pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact ⟨C.distinctTs E hE ha hb hab, h0, hwf, hmono,
    fresh_ts_config C E hE hids0 pre hsub a ha hanp,
    fresh_ts_config C E hE hids0 pre hsub b hb hbnp, hFa, hFb, hcab, hcba⟩

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — what closes, and the exact residual (`hReach`).

   CLOSED unconditionally from the abstract configuration `C`:
   • the SWAP: the engine discharges it via `eqSwap_of_bothFaithful` (NEITHER
     operand `accurate`).  No `EqSwap`/swap-oracle premise survives (grep-checked).
   • `a.1 ≠ b.1`            — `C.distinctTs`.
   • `fresh_ts a`,`fresh_ts b` — `C.freshTs` + `fresh_ts_state_of_ids` (§2b),
     modulo the mild nonzero-id discipline `hids0`.

   The ORDER layer of `Faithful` is also closed (§1/§2): `goodFold_of_stepwise`
   threads the three `GoodStep` cases, and the staled-`Del` (`faithful_del_of_accurate`,
   from `accurate` alone) and concurrent-`Ins` (`goodStep_ins_concurrent`, from
   freshness) cases need NO history linkage.

   NOT closed from `C` (bundled into `hReach`, hence NOT unconditional):

   (1) **Ancestor-`Ins` `AncInsLink` — the sharp stuck case.**  For a fold step
       `o = (t,·,.Ins e p anch)` with `t ∈ recList a`, `goodStep_ins_ancestor`
       demands `AncInsLink s (recList a) t anch`: `recList a = D ++ t :: R` with `D`
       all dead, `t` dead, `anch` live, `resolve s R = anch`.  The live/dead split
       and `resolve s R = anch` (i.e. `R`'s head = `anch` = `t`'s recorded parent)
       hold ONLY if `recList a` coincides with `a`'s genuine `vis`-ancestor chain,
       consecutive members are true parent-links, and `o`'s recorded anchor is the
       successor of `t` in `recList a` — the `RecListVisFaithful` linkage.
       `ConditionedConfiguration` relates events only through `vis`/`distinct_ts`/
       `causal_mono`/`Inv`; it never reaches the RGA-syntactic anchor lists, and it
       ADMITS events whose `recList` is inconsistent with `vis` (exactly the
       `RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins`
       counterexample).  So the linkage is neither a field of `C` nor derivable from
       its fields — it is a MODEL gap, matching the three prior verdicts.  This is
       why `Faithful a`/`Faithful b` sit in `hReach`.

   (2) **`NoFreshClash a b` / `b a`** — RGA form `b.1 ∉ recList a`.  M2's
       `noFreshClash_concurrent` gives the `vis`-ancestor id form; bridging needs
       `recList a ⊆ {a.1} ∪ vis-ancestor ids of a` — the SAME linkage as (1).

   (3) **`contains 0 = false`/`wf`/`id_mono` at the fold** — the reachable-state
       invariant.  M2's `inv_fold` yields `contains 0`/`wf` but needs
       `noopFeasible pre`, which the eligible-prefix oracle does NOT carry (its
       prefixes are `loOnA`-respecting sub-lists, not certified applicable-per-step);
       and `id_mono` is not even part of `RgaInv`.

   Two plumbing findings (why the naive M2 route does not apply directly):
   • `¬ loOnA a b → C.Concurrent a b` is FALSE: `loOnA` keeps only `vis`-edges that
     ALSO carry `appliesDependsOn`, so `¬ loOnA a b` does not give `¬ C.vis a b`.
     We route AROUND it — `distinctTs`/`freshTs` need no concurrency, and
     `NoFreshClash` is in `hReach` — so `conditioned_premises`' concurrency gate is
     never invoked.
   • `conditioned_premises` also needs `noopFeasible pre`, absent from the oracle.

   VERDICT: `RGA_update_convergence` closes CONDITIONALLY on `hReach`.  The swap
   oracle is eliminated and 3/10 conjuncts (+ the `Faithful` order layer) are
   discharged from `C`; the residual `hReach` is exactly the recList↔`vis` history
   linkage (feeding ancestor-`Ins` `AncInsLink`, `NoFreshClash`) plus the
   `noopFeasible`-of-eligible-interleaving reachable invariant — the facts a real
   RGA execution supplies by construction but the abstract configuration cannot.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §4  Axiom audit -/

#print axioms faithful_del_of_accurate
#print axioms goodFold_of_stepwise
#print axioms faithful_ins_of_stepwise
#print axioms fresh_ts_config
#print axioms RGA_update_convergence

end Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal

/-! ## Cut from `RGA_GenDischarge.lean` -/

namespace Sal.ConditionedMRDTs.RGAGenDischarge
open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (applySeqR)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open RGARecPathFaithful
open Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal (RGA_update_convergence)

theorem RGA_update_convergence_genDisc
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E))
    (hGen : GenDisc Cfg E) (hInv : ReachInv Cfg E) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  refine RGA_update_convergence C Cfg E hE hids0 π₁ π₂ h₁p h₂p h₁r h₂r ?_
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact hReach_of_genDisc Cfg E hGen hInv pre a b hsub hnd hresp
    ha hb hanp hbnp hab hnab hnba hena henb

/-! ## §8  Axiom audit -/

#print axioms faithful_of_accurate
#print axioms noFreshClash_of_accurate_fresh
#print axioms RGA_update_convergence_genDisc

end Sal.ConditionedMRDTs.RGAGenDischarge

/-! ## Cut from `RGA_MergeCanon.lean` -/

namespace Sal.ConditionedMRDTs.RGAMergeCanon
open Classical
open Sal.Emulation
open RGACanonConvergence (survP insertedIn deletedIn CanonMatch canonAnc resolve_eq_canonAnc)
open RGAMergeLinearization (contains_eq_domain)
open RGAMergeLinearizationTwoSided (birthEl)
open RGAMergeFoldChain (CanonBirthBridge)
open RGAMergeBranchNew (resolve_climb_start)

/-- **Merge-side glue.**  Assembles `CanonMatch (ρ₀++π₀) (merge σ₀' σ₁' σ₂')` from the leaf inputs,
precisely typing the residual: the three branch `CanonMatch` (`hcmᵢ`), σ₀' forest invariants
(`Hdec`/`Hstay`/`h0`), the per-id causal facts (`hcaus`), per-survivor membership (`hins_branch`),
and per-survivor `CanonBirthBridge` + 0-or-survivor birth-anchor (`hbridge`). Everything else is the
three clause lemmas (done). What LEFT to discharge is exactly these five hypotheses. -/
theorem canonMatch_merge_of_inputs
    (σ₀' σ₁' σ₂' : concrete_st) (ρ₀ π₀ ρ₁ ρ₂ : List op_t)
    (hcm0 : CanonMatch ρ₀ σ₀') (hcm1 : CanonMatch ρ₁ σ₁') (hcm2 : CanonMatch ρ₂ σ₂')
    (Hdec : ∀ y, contains σ₀' y = true → y ≠ 0 → anc σ₀' y < y)
    (Hstay : ∀ y, contains σ₀' y = true → (anc σ₀' y = 0 ∨ contains σ₀' (anc σ₀' y) = true))
    (h0 : contains σ₀' 0 = false)
    (hcaus : ∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
        ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
        ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
        ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
        ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
    (hins_branch : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        (contains σ₀' t = true → (t, r, .Ins e p a) ∈ ρ₀)
        ∧ (contains σ₁' t = true → (t, r, .Ins e p a) ∈ ρ₁)
        ∧ (contains σ₂' t = true → (t, r, .Ins e p a) ∈ ρ₂)
        ∧ (contains σ₀' t = true ∨ contains σ₁' t = true ∨ contains σ₂' t = true))
    (hbridge : ∀ (t r e a : ℕ) (p : List ℕ),
        (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
        CanonBirthBridge σ₀' (ρ₀ ++ π₀) (birthAnc σ₀' σ₁' σ₂' t) (a :: p)
        ∧ (birthAnc σ₀' σ₁' σ₂' t = 0
            ∨ survivors σ₀' σ₁' σ₂' (birthAnc σ₀' σ₁' σ₂' t) = true)) :
    CanonMatch (ρ₀ ++ π₀) (merge σ₀' σ₁' σ₂') := by
  have hdomain : ∀ c, contains (merge σ₀' σ₁' σ₂') c = true ↔ survP (ρ₀ ++ π₀) c := by
    intro c
    obtain ⟨hI0, hD1I, hD2I, hD01, hD02, hIu, hDu⟩ := hcaus c
    exact merge_domain_clause σ₀' σ₁' σ₂' ρ₀ π₀ ρ₁ ρ₂ c
      (hcm0.1 c) (hcm1.1 c) (hcm2.1 c) hI0 hD1I hD2I hD01 hD02 hIu hDu
  refine merge_canonMatch σ₀' σ₁' σ₂' (ρ₀ ++ π₀) hdomain ?_ ?_
  · intro t r e a p hins hsv
    obtain ⟨hs0, hs1, hs2, hib⟩ := hins_branch t r e a p hins hsv
    exact merge_el_clause σ₀' σ₁' σ₂' ρ₀ ρ₁ ρ₂ t r e a p hcm0 hcm1 hcm2 hs0 hs1 hs2 hib
  · intro t r e a p hins hsv
    obtain ⟨hbr, hbws⟩ := hbridge t r e a p hins hsv
    exact merge_anc_clause σ₀' σ₁' σ₂' (ρ₀ ++ π₀) t a p Hdec Hstay h0 hdomain hbr hbws

#print axioms canonMatch_merge_of_inputs

end Sal.ConditionedMRDTs.RGAMergeCanon

/-! ## Cut from `RGA_EnablementBase.lean` -/

namespace RGAEnablementBase
open Sal.ConditionedMRDTs.RGABubbleWiring
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (chainFaithful_of_accurate)
open RGAFaithfulThreadingGate (IncompStep IncompFold chainFaithful_incompFold foldDo)
open Sal.ConditionedMRDTs.RGAStaledDelGate (sIns Lclash contains_sIns)

/-- **(i) Generation base.**  On a root-free, `id_mono` state, `HistFaithful s w`
gives `ChainFaithful s (recList w)`.  This is the imported `chainFaithful_of_accurate`
re-exposed through `HistFaithful`; it is the base `chainFaithful_incompFold` threads. -/
theorem chainFaithful_of_histFaithful (s : concrete_st) (w : op_t)
    (hmono : id_mono s) (h0 : contains s 0 = false) (hHist : HistFaithful s w) :
    ChainFaithful s (recList w) :=
  chainFaithful_of_accurate s w hmono h0 hHist

/-! ## §4  Reachable-regime clash-`Ins` lemma (the counterexample's positive twin) -/


/-- **(ii) Enablement base — CLOSED (order layer).**  At the enablement fold of `w`,
`ChainFaithful (recList w)` holds.  Generation base + threading; the `IncompFold` and
`id_mono`/root-free premises are the reachability facts M2 supplies. -/
theorem chainFaithful_at_enablement (w : op_t) (s_c : concrete_st) (concurrent : List op_t)
    (hmono : id_mono s_c) (h0 : contains s_c 0 = false)
    (hHist : HistFaithful s_c w)
    (hincomp : IncompFold (recList w) s_c concurrent) :
    ChainFaithful (foldDo s_c concurrent) (recList w) :=
  chainFaithful_incompFold (recList w) concurrent s_c hincomp
    (chainFaithful_of_histFaithful s_c w hmono h0 hHist)


end RGAEnablementBase

/-! ## Cut from `RGA_MergeThreadDischarge.lean` -/

namespace RGAMergeThreadDischarge
open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence
open RGAMergeLinearization (BranchInv)
open RGAMergeLinearizationTwoSided
open RGARecPathFaithful
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash)

/-- **Two-sided bridge with `hThread` reduced to pieces and `hSwap` eliminated.**
`merge l a b ≈ fold l π` for any `lo`-respecting `π`, with NO free swap oracle and
NO bare `hThread`: `hThread` is reduced to the four `branchInv2_of_pieces` premises
(`hBN` being the residual GAP-1 branch-new anchor clause, the ONLY non-reachability
premise — see the OBSTRUCTION block) and `hSwap` to the both-`Faithful` merge-fold
reachability oracle `hMSR`. -/
theorem eq_merge_two_sided_of_reachable
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = birthEl l a b k)
    (hBN : ∀ k, survivors l a b k = true → contains l k = false →
        anc (applySeqR l π₀) k
          = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Faithful x (applySeqR l pre) ∧ Faithful y (applySeqR l pre)
        ∧ NoFreshClash x y ∧ NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hThread : BranchInv2 l a b (applySeqR l π₀) :=
    hThread_of_pieces l a b π₀ hD hB hBE hBN
  apply eq_merge_two_sided l a b lo ev π₀ π hThread h₀p hπp h₀r hπr
  intro pre x y hsub hnd hresp hx hy hxp hyp hxy hnxy hnyx henx heny
  obtain ⟨hd, h0, hwf, hmono, hfx, hfy, hFx, hFy, hcxy, hcyx⟩ :=
    hMSR pre x y hsub hnd hresp hx hy hxp hyp hxy hnxy hnyx henx heny
  exact eqSwap_of_bothFaithful (applySeqR l pre) x y hd h0 hwf hmono hfx hfy hFx hFy hcxy hcyx

#print axioms eq_merge_two_sided_of_reachable

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — what the Key Lemma closes, and the exact residual.

   CLOSED here, kernel-clean:

   • GAP-2′ (cross-branch stale-path `Del` preservation).  `branchInv_doDel_crossBranch_sub`
     re-supplies `hres : resolve a pre = anc a x` from the subchain-resolution Key
     Lemma (`RecPathFaithful (Del pre x) a`) — with NO full-`l`-chain requirement and
     NO `accurate a`.  This closes the documented witness `l = 0←1←2←3,
     Eb = [Del [1] 2, Del [1] 3]`: the `Del` of `3` carries `[1]` (a proper live
     subchain of `3`'s `l`-chain `[2,1]`), yet `resolve a [1] = anc a 3 = 1` by the
     Key Lemma, so `branchInv_doDel_crossBranch` applies where `hres_of_lchain` could
     not.  This is the GAP-2′ that the TwoSided file flagged as the residual blocker.

   • The `hSwap` oracle.  `eq_merge_two_sided_of_reachable` carries NO free `EqSwap`
     premise: it is discharged pointwise by `eqSwap_of_bothFaithful` (NEITHER operand
     `accurate`).  The per-swap both-`Faithful` inputs are the reachability oracle
     `hMSR` — the merge-fold analogue of the update side's `hReach`.  NB: the merge
     fold starts at the LCA `l`, not `init_st`, so `faithful_at_interleaved_fold`
     (init-anchored) does NOT transport; `hMSR` is a genuine merge-fold obligation.

   • Reduction of `hThread`.  `branchInv2_of_pieces` splits `BranchInv2` into
       (hD)  domain (applySeqR l π₀) = survivors l a b,
       (hB)  single-sided `BranchInv l (applySeqR l π₀)`  — threadable across Ea++Eb
             by `branchInv_doIns` (fresh ids) + `branchInv_doDel_crossBranch_sub`
             (step 1) for every `Del`, i.e. reachability-only,
       (hBE) branch-new-survivor element clause,
       (hBN) branch-new-survivor ANCHOR clause.

   NOT closed by the Key Lemma — the sharp residual (GAP-1):

   • **(hBN) branch-new survivor anchor coincidence.**  For a survivor `k` with
     `¬ contains l k` (an `a`-new or `b`-new node), `BranchInv2` demands
       anc (applySeqR l π₀) k = climb (anc l) (survivors l a b) (birthAnc l a b k),
     with `birthAnc = anc a k` / `anc b k`.  The subchain-resolution Key Lemma
     resolves a node's OWN recorded chain to its current stored anchor OVER THE
     ACTUAL FOLD FOREST — it does NOT reconcile that with a `climb` over the DISTINCT
     LCA-forest (`anc l`) started at the branch birth-anchor.  Concretely (b-new
     establishment): at `k`'s `Eb`-`Ins` birth over the combined, `a`-carrying state
     `s`, the stored anchor `resolve s (anch :: path)` generally DIFFERS from
     `anc b k = resolve b (anch :: path)` (the combined state already carries `a`'s
     deletions of `k`'s ancestors), and the two must be shown to `climb` to the same
     two-sided survivor over `anc l`.  That cross-forest reconciliation is genuinely
     NEW two-sided content, NOT expressible as a per-event reachability premise, so it
     is left as the explicit premise `hBN` rather than forced or `sorry`d.

   • (hD)/(hBE) are the minor residue: a domain (OR-set = live-set) induction and a
     branch-new birth-element preservation — reachability-flavoured, but not yet
     mechanized here; also left as explicit premises.

   VERDICT.  The Key Lemma DOES unblock the merge side's GAP-2′ (`hThread`'s
   cross-branch `Del` preservation) and eliminates the free swap oracle.  It does
   NOT, on its own, close `hThread`: the residual is GAP-1 (hBN, the branch-new
   survivor cross-forest anchor identity) plus the minor hD/hBE.  This matches — and
   sharpens — the TwoSided file's own OBSTRUCTION reading (GAP-1 branch-new + GAP-2′),
   now with GAP-2′ discharged.  It is not a divergence: `merge` and `fold` still agree
   on branch-new survivors (PBT-confirmed); the gap is the anchor-reconciliation lemma.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeThreadDischarge

/-! ## Cut from `RGA_MergeBranchNew.lean` -/

namespace RGAMergeBranchNew
open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence

/-- **Two-sided bridge, branch-new anchor discharged.**  `merge l a b ≈ fold l π`
with `hBN` replaced by the fold-chain identity `hFC` (`FoldBirthChain` per
branch-new survivor) together with the reachable invariants.  The free `hBN` of
`eq_merge_two_sided_of_reachable` is gone: it is built by `hBN_of_foldChain`. -/
theorem eq_merge_two_sided_of_foldChain
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hawf : wf a) (hbwf : wf b)
    (h0 : contains l 0 = false)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : RGAMergeLinearization.BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = RGAMergeLinearizationTwoSided.birthEl l a b k)
    (hFC : ∀ k, survivors l a b k = true → contains l k = false →
        FoldBirthChain l a b (applySeqR l π₀) k)
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful x (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash x y
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hHdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
    intro y hy hy0; rcases hlmono y hy with h | h
    · omega
    · exact h
  have hBN : ∀ k, survivors l a b k = true → contains l k = false →
      anc (applySeqR l π₀) k
        = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k) :=
    hBN_of_foldChain l a b (applySeqR l π₀) hHdec hlwf h0 hawf hbwf hD hFC
  exact RGAMergeThreadDischarge.eq_merge_two_sided_of_reachable
    l a b lo ev π₀ π hD hB hBE hBN h₀p hπp h₀r hπr hMSR

#print axioms eq_merge_two_sided_of_foldChain

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — `hBN` (GAP-1), what closed and the exact residual.

   CLOSED here, kernel-clean ([propext, Classical.choice, Quot.sound] only):

   • The CROSS-FOREST RECONCILIATION bridge (`resolve_climb_start`).  The
     OBSTRUCTION block named this as "genuinely NEW two-sided content": the merge's
     `climb` over the LCA forest and the fold's `resolve` of the recorded chain
     compute over DIFFERENT forests.  `resolve_climb_start` proves they agree for an
     in-forest start `w`:  `resolve s (w :: cw) = climb (anc l) (domain s) w`  when
     `IsAncPath l w cw`.  This is the exact climb=resolve identity the branch-new
     anchor clause needs, generalizing `resolve_climb_lchain` (which started one step
     above `w`, at `anc l w`) to start AT the birth-anchor `w`.

   • The SURVIVOR↔FOLD-LIVENESS bridge is exactly `hD`
     (`survivors l a b = contains (applySeqR l π₀)`), already a premise; here it is
     used as the set identity `survivors l a b = domain (applySeqR l π₀)` to swap the
     `climb` stop-set, and (via `betaf_start`) to discharge the off-forest fixpoint.

   • `hBN` REDUCTION (`hBN_of_foldChain`) + COMPOSITION
     (`eq_merge_two_sided_of_foldChain`).  `hBN` now follows from the per-node
     fold-chain identity `FoldBirthChain` alone; the composed two-sided bridge no
     longer carries a free `hBN` — it carries `hFC : FoldBirthChain …` plus the
     standard reachable invariants `wf l/a/b`, `id_mono l`, `contains l 0 = false`.
     All `climb`/`resolve` algebra is discharged.

   NOT closed — the sharp residual (`FoldBirthChain`, the fold-chain identity):

   • For a branch-new survivor `k`, `FoldBirthChain` demands, with `w := birthAnc`:
       (in-forest w)   ∃ cw, IsAncPath l w cw ∧ anc p k = resolve p (w :: cw)
       (off-forest w)  anc p k = w                                    (p = fold)
     This is what `subchain_resolve` (`RGA_SubchainResolve`) yields — `resolve p ck
     = anc p k` — PROVIDED `k`'s genuine fold ancestor chain `ck` equals `w :: cw`,
     i.e. `k`'s rootward chain in the fold coincides with its BIRTH-ANCHOR's LCA
     chain.  It does NOT hold definitionally: `k`'s fold chain is headed by `k`'s
     FOLD-BIRTH resolved anchor, whereas `w = anc a k` / `anc b k` is `k`'s
     BRANCH-FINAL anchor.  Reconciling the two (the mismatch the OBSTRUCTION block
     flagged: "the stored anchor `resolve s (anch::path)` generally DIFFERS from
     `anc b k`") needs the EVENT-LIST fold invariant — a branch-new analogue of
     `BranchInv`'s I4 threaded through `Ea ++ Eb` via `GoodBranchFold`, using
     cross-branch faithfulness (an `Eb`-`Del` never targets an `a`-new node; a
     `b`-new birth over the `a`-carrying combined state climbs to the same survivor).

   EXACT STUCK GOAL (the missing bridge lemma, name it `foldChain_of_goodFold`):
       ⊢ FoldBirthChain l a b (applySeqR l (Ea ++ Eb)) k
     for every branch-new survivor `k`, given `a = applySeqR l Ea`,
     `b = applySeqR l Eb`, and the `GoodBranchFold`/faithfulness data for Ea, Eb.
     This is a genuine event-list induction (branch-new I4 preservation across every
     `Eb` step + establishment at `a` / at each `b`-new `Ins` birth), NOT expressible
     as a per-event reachability premise — matching the OBSTRUCTION's reading that
     the branch-new cross-forest anchor identity is irreducible two-sided content.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeBranchNew

/-! ## Cut from `RGA_MergeFoldChain.lean` -/

namespace RGAMergeFoldChain
open Classical
open Sal.Emulation
open RGACanonConvergence
open RGAMergeBranchNew (FoldBirthChain eq_merge_two_sided_of_foldChain)
open RGAMergeLinearization (applySeqR)

theorem eq_merge_two_sided_final
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (F : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hawf : wf a) (hbwf : wf b)
    (h0 : contains l 0 = false)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : RGAMergeLinearization.BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = RGAMergeLinearizationTwoSided.birthEl l a b k)
    (hcm : CanonMatch F (applySeqR l π₀))
    (hbridge : ∀ k, survivors l a b k = true → contains l k = false →
        ∀ r e_k a_k : ℕ, ∀ p_k : List ℕ, (k, r, .Ins e_k p_k a_k) ∈ F →
          CanonBirthBridge l F (birthAnc l a b k) (a_k :: p_k))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful x (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash x y
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hFC : ∀ k, survivors l a b k = true → contains l k = false →
      FoldBirthChain l a b (applySeqR l π₀) k := by
    intro k hsvk hlkf
    have hck : contains (applySeqR l π₀) k = true := by rw [← hD k]; exact hsvk
    have hsurvF : survP F k := (hcm.1 k).mp hck
    obtain ⟨⟨r, e_k, p_k, a_k, hins⟩, _⟩ := id hsurvF
    exact foldChain_of_canon l a b (applySeqR l π₀) F hcm k r e_k a_k p_k hins hsurvF
      (hbridge k hsvk hlkf r e_k a_k p_k hins)
  exact eq_merge_two_sided_of_foldChain l a b lo ev π₀ π hlwf hlmono hawf hbwf h0
    hD hB hBE hFC h₀p hπp h₀r hπr hMSR

#print axioms eq_merge_two_sided_final

end RGAMergeFoldChain

/-! ## Cut from `RGA_ConvergenceEq.lean` -/

namespace Sal.ConditionedMRDTs.RGAConvergenceEq
open Classical
open Sal.Emulation (respects listPermOf)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq eqCommutesOn doW)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rga_inv_init')
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ WfOpGenQ wfOpQ_ins_of_genQ)
open Sal.ConditionedMRDTs.RGAOrderBridge (rc_is_Either')
open Sal.ConditionedMRDTs.RGACanonFoldOK
open RGAMergeLinearization (applySeqR applySeqR_nil applySeqR_cons)
open RGACanonConvergence

/-- **The two-sided merge bridge over the framework's order.**
`RGAMergeFoldChain.eq_merge_two_sided_final` is already ORDER-AGNOSTIC: its
linearization order is an abstract `lo` throughout — the two enumeration
hypotheses, the dependency-frontier closure conditions, and the `hMSR` swap
oracle all read the same abstract relation, and its proof engine (the
canon-fold on the branch plus the merge linearization) never consults `loOnA`.
This theorem exposes it instantiated at `lo := loOnEq rgaEqEquiv' WfOpQ
Cfg.vis ev`: the merge equals the fold of any `loOnEq`-respecting enumeration
of `ev` — the exact shape `EqJoinLemma3C`'s union-side canonical state
demands, with no order translation left. -/
theorem eq_merge_two_sided_eq
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (l a b : concrete_st) (ev : Set op_t) (π₀ π : List op_t)
    (F : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hawf : wf a) (hbwf : wf b)
    (h0 : contains l 0 = false)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : RGAMergeLinearization.BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = RGAMergeLinearizationTwoSided.birthEl l a b k)
    (hcm : CanonMatch F (applySeqR l π₀))
    (hbridge : ∀ k, survivors l a b k = true → contains l k = false →
        ∀ r e_k a_k : ℕ, ∀ p_k : List ℕ, (k, r, .Ins e_k p_k a_k) ∈ F →
          RGAMergeFoldChain.CanonBirthBridge l F (birthAnc l a b k) (a_k :: p_k))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis ev))
    (hπr : respects π (loOnEq rgaEqEquiv' WfOpQ Cfg.vis ev))
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup →
        respects pre (loOnEq rgaEqEquiv' WfOpQ Cfg.vis ev) →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y →
        ¬ loEqRGA Cfg ev x y → ¬ loEqRGA Cfg ev y x →
        (∀ z ∈ ev, z ≠ x → loEqRGA Cfg ev z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → loEqRGA Cfg ev z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful x (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.Faithful y (applySeqR l pre)
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash x y
        ∧ Sal.ConditionedMRDTs.RGAGeneralSwap.NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) :=
  RGAMergeFoldChain.eq_merge_two_sided_final l a b (loEqRGA Cfg ev) ev π₀ π F
    hlwf hlmono hawf hbwf h0 hD hB hBE hcm hbridge h₀p hπp h₀r hπr hMSR

/-! ## §6  Axiom audit -/

#print axioms canonStepOK_of_genR
#print axioms canonFoldOK_of_genR
#print axioms canonFoldOK_of_loOnEq
#print axioms RGA_update_convergence_eq
#print axioms anchorIns_not_eqCommutesOn
#print axioms loOnEq_anchor_edge
#print axioms eq_merge_two_sided_eq

end Sal.ConditionedMRDTs.RGAConvergenceEq

/-! ## Cut from `RGA_EnablementBase.lean` -/

namespace RGAEnablementBase
open Sal.ConditionedMRDTs.RGABubbleWiring
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (chainFaithful_of_accurate)
open RGAFaithfulThreadingGate (IncompStep IncompFold chainFaithful_incompFold foldDo)
open Sal.ConditionedMRDTs.RGAStaledDelGate (sIns Lclash contains_sIns)

/-- **`w` is `Faithful` at its enablement fold** (Ins form).  Projecting the threaded
`ChainFaithful` through `climbFaithful_of_chain` gives the top-level `ClimbFaithful`
that the incomparable swap consumes as `Faithful` for the enabled `Ins w`. -/
theorem faithful_at_enablement_ins (t r e a : ℕ) (pre : List ℕ)
    (s_c : concrete_st) (concurrent : List op_t)
    (hmono : id_mono s_c) (h0 : contains s_c 0 = false)
    (hHist : HistFaithful s_c (t, r, .Ins e pre a))
    (h0' : contains (foldDo s_c concurrent) 0 = false)
    (hincomp : IncompFold (recList (t, r, .Ins e pre a)) s_c concurrent) :
    Faithful (t, r, .Ins e pre a) (foldDo s_c concurrent) := by
  have hcf : ChainFaithful (foldDo s_c concurrent) (a :: pre) :=
    chainFaithful_at_enablement (t, r, .Ins e pre a) s_c concurrent hmono h0 hHist hincomp
  exact climbFaithful_of_chain (foldDo s_c concurrent) (a :: pre) h0' hcf

/-! ## §6  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms fresh_not_mem_recList
#print axioms chainFaithful_of_histFaithful
#print axioms chainFaithful_doIns_reachable
#print axioms incompStep_ins_of_hist
#print axioms clash_recList_excluded
#print axioms chainFaithful_at_enablement
#print axioms faithful_at_enablement_ins

end RGAEnablementBase

/-! ## Cut from `RGA_EqJoin_NF.lean` -/

namespace Sal.ConditionedMRDTs.RGAEqJoinNF
open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' RGACondSig'_init rgaCongVC')
open Sal.ConditionedMRDTs.RGAOrderBridge (rc_is_Either')
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAInstanceFinal (applySeq_eq_applySeqR)
open RGAMergeLinearization (applySeqR)

/-- **The NF union adapter.**  From the LCA enumeration `ρ₀`, a delta enumeration
`π₀`, the merge-fold fact `hMF`, AND the two sides' `noopFeasible` (`ρ₀` from
`init`, `π₀` from the LCA fold), the union's born-applicable canonical-state shape
follows.  The `IsCanonicalStateEq` shape is exactly `RGA_Instance_Final`'s; the new
content is the `noopFeasible` clause of `ρ₀ ++ π₀` via `noopFeasible_append`. -/
theorem isCanonicalStateEqNF_union_of_fold
    (W : op_t → concrete_st → Prop)
    (vis : op_t → op_t → Prop) (ev₁ ev₂ : Set op_t)
    (hcl₁ : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl₂ : fullClosureRel (D := RGACondSig') vis ev₂)
    (m : concrete_st) (ρ₀ π₀ : List op_t)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (h₀r : respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))))
    (hnf₀ : noopFeasible RGACondSig' ρ₀ init_st)
    (hnfπ : noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) m) :
    IsCanonicalStateEqNF rgaEqEquiv' W vis (ev₁ ∪ ev₂) m := by
  have hmemρ : ∀ a ∈ ρ₀, a ∈ ev₁ ∩ ev₂ := fun a ha => (h₀p.2 a).mp ha
  have hmemπ : ∀ a ∈ π₀, a ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) :=
    fun a ha => (hπp.2 a).mp ha
  refine ⟨ρ₀ ++ π₀, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨h₀p.1, hπp.1, ?_⟩
    intro a ha b hb heq
    exact (hmemπ b hb).2 (heq ▸ hmemρ a ha)
  · intro a
    constructor
    · intro ha
      rcases List.mem_append.mp ha with h | h
      · exact Set.mem_union_left _ (hmemρ a h).1
      · exact (hmemπ a h).1
    · intro ha
      by_cases hI : a ∈ ev₁ ∩ ev₂
      · exact List.mem_append.mpr (Or.inl ((h₀p.2 a).mpr hI))
      · exact List.mem_append.mpr (Or.inr ((hπp.2 a).mpr ⟨ha, hI⟩))
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen W vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((loOnEqQ_reduce_gen W vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl₁ b a hva haI.1, hcl₂ b a hva haI.2⟩
  · -- the born-applicable clause: `ρ₀ ++ π₀` is `noopFeasible` from `init`
    refine noopFeasible_append hnf₀ ?_
    show noopFeasible RGACondSig' π₀ (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ₀)
    rw [applySeq_eq_applySeqR, RGACondSig'_init]
    exact hnfπ
  · show rgaEqEquiv'.eqv
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)) m
    have hsplit : applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)
        = applySeqR (applySeqR init_st ρ₀) π₀ := by
      rw [applySeq_eq_applySeqR, RGACondSig'_init]
      simp only [applySeqR, List.foldl_append]
    rw [hsplit]
    exact hMF

/-! ## §2.5  The `≈`-vs-literal reconciliation (`mergeFold_transport`)

The merge machinery (`eq_merge_two_sided_final`) needs the branches as LITERAL folds; the framework
supplies them only up to `≈`.  The born-applicable re-base resolves this: run the machinery on the
literal born-applicable folds `σ_i' ≈ s_i`, then transport to the `≈`-classes `s₀ s₁ s₂` by ONE
`merge`-congruence step.  This lemma is that transport — it confines the entire `≈`-vs-literal tension
to `mergeL_congr`.  See `WALL1_ANALYSIS.md`. -/


end Sal.ConditionedMRDTs.RGAEqJoinNF

/-! ## Cut from `RGA_Instance_Final.lean` -/

namespace Sal.ConditionedMRDTs.RGAInstanceFinal
open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC'
  rga_inv_init' RGACondSig'_update RGACondSig'_mergeL RGACondSig'_init)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ WfOpGenQ rgaInvPresQ rga_wfOpReachableQ)
open Sal.ConditionedMRDTs.RGAConvergenceEq (loOnEqQ_reduce)
open RGAMergeLinearization (applySeqR)

/-- `loOnEq rgaEqEquiv' WfOpQ` does not read its event-set index. -/
theorem loOnEqQ_index_free (vis : op_t → op_t → Prop) (ev ev' : Set op_t)
    (e₁ e₂ : op_t) :
    loOnEq rgaEqEquiv' WfOpQ vis ev e₁ e₂
      ↔ loOnEq rgaEqEquiv' WfOpQ vis ev' e₁ e₂ :=
  (loOnEqQ_reduce vis ev e₁ e₂).trans (loOnEqQ_reduce vis ev' e₁ e₂).symm


/-- **The union adapter.**  From the LCA enumeration, a delta enumeration, and
the merge-fold fact, the union's canonical-state shape follows. -/
theorem isCanonicalStateEq_union_of_fold
    (vis : op_t → op_t → Prop) (ev₁ ev₂ : Set op_t)
    (hcl₁ : fullClosureRel (D := RGACondSig') vis ev₁)
    (hcl₂ : fullClosureRel (D := RGACondSig') vis ev₂)
    (m : concrete_st) (ρ₀ π₀ : List op_t)
    (h₀p : listPermOf ρ₀ (ev₁ ∩ ev₂))
    (h₀r : respects ρ₀ (loOnEq rgaEqEquiv' WfOpQ vis (ev₁ ∩ ev₂)))
    (hπp : listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)))
    (hπr : respects π₀ (loOnEq rgaEqEquiv' WfOpQ vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))))
    (hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) m) :
    IsCanonicalStateEq rgaEqEquiv' WfOpQ vis (ev₁ ∪ ev₂) m := by
  have hmemρ : ∀ a ∈ ρ₀, a ∈ ev₁ ∩ ev₂ := fun a ha => (h₀p.2 a).mp ha
  have hmemπ : ∀ a ∈ π₀, a ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) :=
    fun a ha => (hπp.2 a).mp ha
  refine ⟨ρ₀ ++ π₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨h₀p.1, hπp.1, ?_⟩
    intro a ha b hb heq
    exact (hmemπ b hb).2 (heq ▸ hmemρ a ha)
  · intro a
    constructor
    · intro ha
      rcases List.mem_append.mp ha with h | h
      · exact Set.mem_union_left _ (hmemρ a h).1
      · exact (hmemπ a h).1
    · intro ha
      by_cases hI : a ∈ ev₁ ∩ ev₂
      · exact List.mem_append.mpr (Or.inl ((h₀p.2 a).mpr hI))
      · exact List.mem_append.mpr (Or.inr ((hπp.2 a).mpr ⟨ha, hI⟩))
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((loOnEqQ_reduce vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl₁ b a hva haI.1, hcl₂ b a hva haI.2⟩
  · show rgaEqEquiv'.eqv
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)) m
    have hsplit : applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)
        = applySeqR (applySeqR init_st ρ₀) π₀ := by
      rw [applySeq_eq_applySeqR, RGACondSig'_init]
      simp only [applySeqR, List.foldl_append]
    rw [hsplit]
    exact hMF

#print axioms isCanonicalStateEq_union_of_fold

/-! ## §4  The `≈`-Join `EqJoinLemma3C`, reduced to the merge=delta-fold residual

`EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOpQ GenDisc` (its NEW `GenDisc`-carrying
form, GenericEqQuotient §4) demands `IsCanonicalStateEq (ev₁∪ev₂) (mergeL s₀ s₁ s₂)`
from the three side canonical states, full closure, and `GenDisc` on the two sides
and their union.  §3's `isCanonicalStateEq_union_of_fold` already discharges the
ENTIRE `IsCanonicalStateEq` *shape* assembly (nodup/perm of `ρ₀ ++ π₀`, the
`respects` append via `loOnEqQ_index_free` + full-closure cross-edge kill, the raw
`foldl_append` split) from ONE merge-fold fact `hMF`.  So the join reduces to
producing, from the LCA enumeration `ρ₀` (extracted from the intersection-side
canonical state), a `loOnEq`-respecting delta enumeration `π₀` of
`(ev₁∪ev₂)\(ev₁∩ev₂)` whose continued fold from the LCA-fold rep is `≈ mergeL`.

`RgaEqJoinResidual` names EXACTLY that remaining content.  Everything ABOVE it —
the union canonical-state shape — is closed here; nothing below it is smuggled in.
See the STATUS block for why the residual is not (yet) discharge-able from
`EqJoinLemma3C`'s hypotheses with the current swap-free machinery. -/


/-- **The `≈`-Join from the residual.**  The union canonical-state shape is closed
by §3; the ONLY input beyond `EqJoinLemma3C`'s own hypotheses is
`RgaEqJoinResidual` (the merge=delta-fold bridge).  Parametric in `GenDisc`, so it
holds for any generation-discipline instantiation, including the intended
`GenDisc2CEq`-family. -/
theorem rga_eqJoin_of_mergeFoldResidual
    (GenDisc : (op_t → op_t → Prop) → Set op_t → Prop)
    (hRes : RgaEqJoinResidual GenDisc) :
    EqJoinLemma3C RGACondSig' rgaEqEquiv' WfOpQ GenDisc := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir hev1 hev2 hcl1 hcl2
    hgd1 hgd2 hgdU hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, _hfold0⟩ := hcs0
  obtain ⟨π₀, hπp, hπr, hMF⟩ :=
    hRes vis events ev₁ ev₂ s₀ s₁ s₂ ρ₀ hI0 hI1 hI2 htr hir hev1 hev2
      hcl1 hcl2 hgd1 hgd2 hgdU h₀p h₀r hcs1 hcs2
  exact isCanonicalStateEq_union_of_fold vis ev₁ ev₂ hcl1 hcl2
    (RGACondSig'.mergeL s₀ s₁ s₂) ρ₀ π₀ h₀p h₀r hπp hπr hMF

#print axioms rga_eqJoin_of_mergeFoldResidual

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — `rga_EqJoinLemma3C` is NOT constructed; the residual is located EXACTLY.

   CLOSED here (kernel-clean, [propext, Classical.choice, Quot.sound]):

   • The ENTIRE union canonical-state SHAPE.  `isCanonicalStateEq_union_of_fold`
     (§3) + `rga_eqJoin_of_mergeFoldResidual` (§4) discharge every part of
     `EqJoinLemma3C`'s conclusion EXCEPT `RgaEqJoinResidual`: the `ρ₀`-extraction
     from the intersection-side canonical state, the `nodup`/`perm` of `ρ₀ ++ π₀`,
     the `respects`-append (via `loOnEqQ_index_free` + full-closure cross-edge kill),
     and the raw `foldl_append` split.  Nothing below `RgaEqJoinResidual` is smuggled.

   THE RESIDUAL (`RgaEqJoinResidual`), and why it is a genuine WALL, not mechanization
   debt.  Its core obligation is the merge=delta-fold bridge from the LCA:
       `eq (applySeqR (applySeqR init_st ρ₀) π₀) (mergeL s₀ s₁ s₂)`
   which — swapping `applySeqR init_st ρ₀ ≈ s₀` under merge congruence
   (`rgaCongVC'.mergeL_congr`) — is `eq (mergeL s₀ s₁ s₂) (applySeqR s₀ π₀)`, the
   classic bridge from `l := s₀`.  The swap-free toolkit
   (`merge_fold_indep_canon` ← `eq_merge2_of_branchInv2` ← `branchInv2_of_pieces`)
   is blocked at TWO independent points:

   • WALL 0 — no execution model from the abstract `vis`.  `EqJoinLemma3C` hands only
     `vis` trans/irrefl, `Inv sᵢ`, `fullClosureRel`, and `GenDisc`.  But
     `merge_fold_indep_canon`, `canonFoldOK_of_loOnEq`, and even the EXISTENCE of the
     delta enumeration `π₀` (`ConditionedExecutionModel`'s topological-extension lemma,
     stated for `loOnA D Cfg`, not `loOnEq`) all require a `ConditionedConfiguration`
     carrying `distinct_ts`, `causal_mono` (`vis a b → a.1 < b.1`), `BackClosed`, and
     nonzero ids — NONE of which are `EqJoinLemma3C` hypotheses.  They can only enter
     through a strengthened `GenDisc` (the `GenDisc2CEq`-family, re-exposed to carry a
     config witness); `rga_eqJoin_of_mergeFoldResidual` is deliberately parametric in
     `GenDisc` so that choice is orthogonal to the shape assembly proved here.

   • WALL 1 — the four branch pieces `hD`/`hB`/`hBE`/`hBN` (`branchInv2_of_pieces`).
     Even granting WALL 0's config, the reference-fold bridge `href` needs, at
     `l := s₀`, `a := s₁`, `b := s₂` and a reference delta fold `applySeqR l π₀`:
       – `hD` (`survivors l a b = contains (applySeqR l π₀)`): OR-set = live-set
         induction — `RGA_MergeThreadDischarge` STATUS: "not yet mechanized here".
       – `hB` (`BranchInv l (applySeqR l π₀)`): threadable per-`Del` by
         `branchInv_doDel_crossBranch_sub`, but only once `π₀`'s events are pinned to
         the branch `Ins`/`Del` with `RecPathFaithful` — "not yet mechanized here".
       – `hBE` (branch-new element): "not yet mechanized here".
       – `hBN` (branch-new anchor, GAP-1): reduces (`hBN_of_foldChain` →
         `foldChain_of_canon` → `canonBirthBridge_of_branchChain`) to `CanonMatch F
         (applySeqR l π₀)` + branch-`LiveChain` inputs (`hlive`/`hsurv`/`hsplit`) that
         `birthAnc l a b k = anc(branch) k` carries its branch's live recorded chain.
         The cross-forest reconciliation lemma (`resolve_climb_start`) IS closed, but
         those branch-`LiveChain` inputs require `s₁`, `s₂` to be LITERAL canonical
         states of their branch enumerations with the specific recorded inserts —
         content `IsCanonicalStateEq` supplies only up to `≈`, and the survivor/anchor
         projections needed are NOT `≈`-invariant in the combined-forest form.

   VERDICT.  The `≈`/order rebasing (`RGA_ConvergenceEq`) removed the OLD §7 order
   mismatch, and `merge_fold_indep_canon` removed the swap oracle — the two blockers
   RGA_Instance §7 named.  What remains is `RgaEqJoinResidual`: WALL 0 (execution
   model into `GenDisc`) + WALL 1 (the `hD`/`hB`/`hBE`/`hBN` branch-canon assembly,
   `hBN` the sharp GAP-1).  `rga_EqJoinLemma3C` is therefore reduced, not closed —
   `rga_eqJoin_of_mergeFoldResidual GenDisc hRes` produces it the moment `hRes` lands.
   ═══════════════════════════════════════════════════════════════════════════ -/

end Sal.ConditionedMRDTs.RGAInstanceFinal

/-! ## Cut from `RGA_EqJoin_NF.lean` -/

namespace Sal.ConditionedMRDTs.RGAEqJoinNF
open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' RGACondSig'_init rgaCongVC')
open Sal.ConditionedMRDTs.RGAOrderBridge (rc_is_Either')
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAInstanceFinal (applySeq_eq_applySeqR)
open RGAMergeLinearization (applySeqR)

/-- **`EqJoinLemma3C_NF` from the NF residual.**  The union canonical-state shape
(§2) closes everything except `RgaEqJoinResidual_NF`.  No `GenDisc`, no
`GDSupply` — the born-applicable `noopFeasible` witnesses carry the discipline the
`GenDisc2CEq`-route needed a strengthened generation discipline for (WALL 0). -/
theorem rga_eqJoin_of_mergeFoldResidual_NF
    (W : op_t → concrete_st → Prop) (hRes : RgaEqJoinResidual_NF W) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir _hdts hev1 hev2 hcl1 hcl2
    hcs0 hcs1 hcs2
  obtain ⟨ρ₀, h₀p, h₀r, hnf₀, _hfold0⟩ := hcs0
  obtain ⟨π₀, hπp, hπr, hnfπ, hMF⟩ :=
    hRes vis events ev₁ ev₂ s₀ s₁ s₂ ρ₀ hI0 hI1 hI2 htr hir hev1 hev2
      hcl1 hcl2 h₀p h₀r hnf₀ hcs1 hcs2
  exact isCanonicalStateEqNF_union_of_fold W vis ev₁ ev₂ hcl1 hcl2
    (RGACondSig'.mergeL s₀ s₁ s₂) ρ₀ π₀ h₀p h₀r hπp hπr hnf₀ hnfπ hMF

/-! ## §4  Axiom audit -/

#print axioms loOnEqQ_reduce_gen
#print axioms loOnEqQ_index_free_gen
#print axioms isCanonicalStateEqNF_union_of_fold
#print axioms rga_eqJoin_of_mergeFoldResidual_NF

end Sal.ConditionedMRDTs.RGAEqJoinNF

/-! ## Cut from `RGA_InvUpdateQ.lean` -/

namespace Sal.ConditionedMRDTs.RGAInvUpdateQ
open Sal.Emulation (Op)
open Sal.ConditionedMRDTs.GenericEqQuotient (InvPres WfChain WfOpReachable)
open Sal.ConditionedMRDTs.RGASig (resolve_mem isAncPath_not_mem)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rga_inv_init' rga_inv_mergeL')
open Sal.ConditionedMRDTs.RGACanonFoldOK (insertedIn_of_contains_fold)
open RGAMergeLinearization (applySeqR)

/-- `WfOpGenQ` strengthens `WfOpGen` (`x ∉ pre` from irreflexivity of `<`). -/
theorem wfOpGen_of_genQ (o : op_t) (h : WfOpGenQ o) : WfOpGen o := by
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a => exact h.1
  | Del pre x =>
    refine ⟨fun hx => ?_, h.1⟩
    exact absurd (h.2 x hx) (lt_irrefl x)


end Sal.ConditionedMRDTs.RGAInvUpdateQ
