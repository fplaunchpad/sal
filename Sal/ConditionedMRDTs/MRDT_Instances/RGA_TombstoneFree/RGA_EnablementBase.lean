import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_FaithfulThreading_Gate
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence

/-!
# M1 — the ENABLEMENT BASE lemma for faithful-threading

Roadmap milestone M1 (`ROADMAP_END_TO_END.md`): at the fold where an event `w`
becomes ENABLED (its causal past applied, arbitrary concurrent ops interleaved
before it), `ChainFaithful (recList w)` holds — so `w` is `Faithful` there, which
feeds the incomparable-swap threading of the free-canonicalization bubble.

This file is ADDITIVE: it modifies no existing file, introduces no `sorry`, and its
headlines are audited kernel-clean (`#print axioms`, no `sorryAx`, no
`native_decide`).

## The history invariant `HistFaithful`

The route the FaithfulThreading gate located (its §6 residual note) is to formalise
the per-event history fact fixed at `w`'s generation:

    `recList w` is `w`'s TRUE ancestor chain in the state — i.e. `accurate w s`.

We name this `HistFaithful s w`.  It is exactly the reachability predicate that
`RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins`'s counterexample
VIOLATES: that counterexample needs an inconsistent `recList` (`Lclash = [8,5]`
records the fresh id `5` as an ancestor of `8`, whose true anchor is the root).  A
genuine `recList` — one certified `HistFaithful` — never records a fresh id, because
every member of an accurate ancestor chain is LIVE (§2).  So the clash the
counterexample exploits cannot arise in the reachable (history-faithful) regime.

## What closes here

* **(i) Generation base** — `chainFaithful_of_histFaithful`: on a root-free,
  `id_mono` state, `HistFaithful s w → ChainFaithful s (recList w)` (this is the
  imported `chainFaithful_of_accurate`, re-exposed through `HistFaithful`).

* **Clash exclusion** (§2) — `fresh_not_mem_recList`: under `HistFaithful`, a fresh
  id (`≠ 0`, dead in `s`) is NEVER in `recList w`.  Hence `clash_recList_excluded`:
  the counterexample's `Lclash` is not a `HistFaithful` `recList` in `sIns`; and
  `chainFaithful_doIns_reachable`: in the history-faithful regime an accurate fresh
  `Ins` DOES preserve `ChainFaithful` (the `t ∉ L` guard of `chainFaithful_doIns` is
  discharged by `HistFaithful`, not assumed).  `incompStep_ins_of_hist` shows this is
  exactly what makes a concurrent fresh `Ins` an `IncompStep` for `recList w`.

* **(ii) Enablement fold** — `chainFaithful_at_enablement`: composing the generation
  base with the proved threading `chainFaithful_incompFold`, `ChainFaithful (recList
  w)` holds at the enablement fold `foldDo s_c concurrent`, where `s_c` is the
  post-causal-past state at which `HistFaithful s_c w` holds and `concurrent` is any
  interleaving that is `IncompFold` for `recList w`.  The `IncompFold` and
  `HistFaithful`/`id_mono` premises are the reachability facts the execution model
  (M2) discharges; here the ORDER-layer content is closed.
-/

set_option maxHeartbeats 1000000

open Sal.ConditionedMRDTs.RGABubbleWiring
  (recList ChainFaithful ChainFaithfulAux chainFaithful_doIns climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (chainFaithful_of_accurate)
open RGAFaithfulThreadingGate (IncompStep IncompFold chainFaithful_incompFold foldDo)

namespace RGAEnablementBase

/-! ## §1  `HistFaithful` — the per-event generation-time history invariant -/

/-- **`HistFaithful s w`** — `recList w` is `w`'s TRUE ancestor chain in `s`.
Definitionally `accurate w s`, named to mark it as the per-event fact fixed when `w`
is generated: the recorded path is the genuine root-ward chain of `w`'s leaf.  It is
the reachability predicate the clash counterexample violates (§2). -/
def HistFaithful (s : concrete_st) (w : op_t) : Prop := accurate w s

/-- `HistFaithful` spelled out on `recList`: the recorded list `leaf :: path` is a
genuine chain (root-degenerate, or a live leaf with `IsAncPath` tail).  This is the
shape both the generation base and the clash exclusion consume. -/
theorem histFaithful_chain (s : concrete_st) (w : op_t) (hHist : HistFaithful s w) :
    (opLeaf w.2.2 = 0 ∧ opPath w.2.2 = []) ∨
    (contains s (opLeaf w.2.2) = true ∧ IsAncPath s (opLeaf w.2.2) (opPath w.2.2)) := by
  simpa only [HistFaithful, accurate] using hHist

/-! ## §2  Clash exclusion — a `HistFaithful` `recList` never records a fresh id

The Part-1 counterexample `chainFaithful_not_preserved_under_clash_ins` needs the
fresh `Ins`'s id to lie IN the recorded list `L` (there, `5 ∈ [8,5]`).  Under
`HistFaithful`, `L = recList w` is an accurate chain, and every element of an
accurate chain is LIVE — so a fresh (dead) id is never in it.  The clash is excluded
by the invariant, not assumed away. -/

/-- The generic core: a fresh id (`≠ 0`, dead in `s`) is not in an accurate chain
`leaf :: path`.  The head is either the root `0` (`≠ t`) or a live leaf (`≠ t`, `t`
dead); each tail member is live (`isAncPath_mem`), hence `≠ t`. -/
theorem fresh_not_mem_chain (s : concrete_st) (leaf : ℕ) (path : List ℕ)
    (hacc : (leaf = 0 ∧ path = []) ∨
            (contains s leaf = true ∧ IsAncPath s leaf path))
    (t : ℕ) (ht0 : t ≠ 0) (hfresh : contains s t = false) :
    t ∉ leaf :: path := by
  intro hmem
  rcases hacc with ⟨hl0, hpnil⟩ | ⟨hlive, hpath⟩
  · subst hl0; subst hpnil
    rcases List.mem_cons.mp hmem with h | h
    · exact ht0 h
    · exact (List.not_mem_nil h)
  · rcases List.mem_cons.mp hmem with h | h
    · exact absurd hlive (by rw [← h, hfresh]; simp)
    · have hlv := isAncPath_mem s leaf path hpath t h
      rw [hfresh] at hlv; exact Bool.noConfusion hlv

/-- **Clash exclusion.**  Under `HistFaithful`, a fresh id (`≠ 0`, dead in `s`) is
never in `recList w`.  This is exactly the `t ∉ L` side condition of
`chainFaithful_doIns` — supplied by the history invariant, not assumed. -/
theorem fresh_not_mem_recList (s : concrete_st) (w : op_t) (hHist : HistFaithful s w)
    (t : ℕ) (ht0 : t ≠ 0) (hfresh : contains s t = false) :
    t ∉ recList w := by
  obtain ⟨tw, rw, opw⟩ := w
  have hchain := histFaithful_chain s (tw, rw, opw) hHist
  cases opw with
  | Ins e pre anch =>
      simp only [opLeaf, opPath] at hchain
      show t ∉ anch :: pre
      exact fresh_not_mem_chain s anch pre hchain t ht0 hfresh
  | Del pre x =>
      simp only [opLeaf, opPath] at hchain
      show t ∉ x :: pre
      exact fresh_not_mem_chain s x pre hchain t ht0 hfresh

/-! ## §3  Generation base (i) -/

/-- **(i) Generation base.**  On a root-free, `id_mono` state, `HistFaithful s w`
gives `ChainFaithful s (recList w)`.  This is the imported `chainFaithful_of_accurate`
re-exposed through `HistFaithful`; it is the base `chainFaithful_incompFold` threads. -/
theorem chainFaithful_of_histFaithful (s : concrete_st) (w : op_t)
    (hmono : id_mono s) (h0 : contains s 0 = false) (hHist : HistFaithful s w) :
    ChainFaithful s (recList w) :=
  chainFaithful_of_accurate s w hmono h0 hHist

/-! ## §4  Reachable-regime clash-`Ins` lemma (the counterexample's positive twin) -/

/-- **Reachable-regime clash-`Ins`.**  In the history-faithful regime an accurate
fresh `Ins` DOES preserve `ChainFaithful (recList w)` — precisely because the fresh
clash the Part-1 counterexample needs (`t ∈ recList w`) is excluded by
`fresh_not_mem_recList`.  The `t ∉ L` premise of `chainFaithful_doIns` is discharged
by `HistFaithful`; nothing is assumed away. -/
theorem chainFaithful_doIns_reachable (s : concrete_st) (w : op_t) (t r e a : ℕ)
    (pre : List ℕ) (ht0 : t ≠ 0) (hfresh : contains s t = false)
    (hHist : HistFaithful s w) (hcf : ChainFaithful s (recList w)) :
    ChainFaithful (do_ s (t, r, .Ins e pre a)) (recList w) :=
  chainFaithful_doIns s t r e a pre (recList w) ht0
    (fresh_not_mem_recList s w hHist t ht0 hfresh) hcf

/-- A concurrent fresh `Ins` (`≠ 0`, dead at the generation state where `HistFaithful`
holds) is an `IncompStep` for `recList w`.  The `Ins` branch of `IncompStep` is
`t ≠ 0 ∧ t ∉ L`; the second conjunct is exactly the clash exclusion.  (The state `s`
in `IncompStep` is not consulted on the `Ins` branch, so this holds at ANY swap-point
state, with freshness taken at the generation state `s_gen`.) -/
theorem incompStep_ins_of_hist (s s_gen : concrete_st) (w : op_t) (t r e a : ℕ)
    (pre : List ℕ) (ht0 : t ≠ 0) (hfresh : contains s_gen t = false)
    (hHist : HistFaithful s_gen w) :
    IncompStep s (recList w) (t, r, .Ins e pre a) :=
  ⟨ht0, fresh_not_mem_recList s_gen w hHist t ht0 hfresh⟩

/-! ### The concrete Part-1 list is not a `HistFaithful` `recList`

`Sal.ConditionedMRDTs.RGAStaledDelGate.sIns` has the two live root-children `{2,8}`; its
clash list `Lclash = [8,5]` records the fresh id `5` as `8`'s ancestor.  No op whose
`recList` is `Lclash` is `HistFaithful` in `sIns`: `5` is dead there, so the clash
exclusion forbids it. -/

open Sal.ConditionedMRDTs.RGAStaledDelGate (sIns Lclash contains_sIns)

theorem contains_sIns_five : contains sIns 5 = false := by
  cases h : contains sIns 5 with
  | false => rfl
  | true => rcases contains_sIns 5 h with h2 | h8 <;> simp_all

/-- **The counterexample's list is excluded.**  Any `w` with `recList w = Lclash`
(`= [8,5]`) fails `HistFaithful sIns w`: `5 ∈ Lclash` is fresh (dead) in `sIns`, which
the clash exclusion forbids for a history-faithful list.  So the Part-1 clash regime
is unreachable under the history invariant. -/
theorem clash_recList_excluded (w : op_t) (hrec : recList w = Lclash) :
    ¬ HistFaithful sIns w := by
  intro hHist
  have h5 : (5 : ℕ) ∉ recList w :=
    fresh_not_mem_recList sIns w hHist 5 (by decide) contains_sIns_five
  rw [hrec] at h5
  exact h5 (by decide)

/-! ## §5  (ii) The enablement fold

Compose the generation base (§3) with the proved threading `chainFaithful_incompFold`
(FaithfulThreading gate §6).  `s_c` is the state after `w`'s causal past has been
applied — where `HistFaithful s_c w` holds (its recorded chain is exactly its true
chain, freshly built) — and `concurrent` is the arbitrary concurrent interleaving
before `w`'s swap point, each step of which is `loOnA`-incomparable to `recList w`
(`IncompFold`: a fresh non-clashing `Ins` or a `Faithful` `Del`).  `ChainFaithful
(recList w)` then holds at the enablement fold, so `w` is `Faithful` there. -/

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
