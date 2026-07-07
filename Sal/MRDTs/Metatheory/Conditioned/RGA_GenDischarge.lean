import Sal.MRDTs.Metatheory.Conditioned.RGA_ReachDischarge

/-!
# From a PER-EVENT generation discipline to the update-layer bundle

*Additive; not committed; 0 `sorry` in what is kept.*

`RGA_ReachDischarge.RGAGenDiscipline` is a **per-PREFIX** bundle: at every eligible
prefix `pre` and swapped pair `a b` it asserts `FoldFaithSource a ∧ FoldFaithSource b
∧ contains 0 = false ∧ wf ∧ id_mono ∧ NoFreshClash a b ∧ NoFreshClash b a` — i.e.
`hReach` renamed.  This file isolates a strictly-more-primitive **per-EVENT**
predicate `GenDisc` — asserting only that each event's OWN recorded path is the true
live ancestor chain (`accurate`) and its OWN id is fresh, at the prefixes containing
its own dependencies — and DERIVES from it the two `Faithful` conjuncts and both
`NoFreshClash` conjuncts.  The reachable-state block (`contains 0 = false ∧ wf ∧
id_mono`) does NOT reduce to per-event accuracy (its `do_`-threading needs the
prefix's INTERNAL steps to each see their ancestors — a structural enumeration fact,
not an event's own generation); it is kept as an explicitly NAMED per-prefix residual
`ReachInv`.  See the closing STATUS block for the exact accounting.

The pivot is `faithful_of_accurate`: per-event `accurate o s` (o's recorded path is
o's true live chain) yields `Faithful o s` directly — bypassing the `GoodFold`
order-layer machinery that `FoldFaithSource` routes an `Ins` through.  Per-event
accuracy is therefore not only more primitive than `FoldFaithSource`, it is a
STRONGER hinge (it discharges `Faithful` for BOTH op kinds uniformly).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAGenDischarge

open Sal.Emulation
open Sal.Metatheory.RGAGeneralSwap (Faithful NoFreshClash)
open Sal.Metatheory.RGABubbleWiring (recList)
open Sal.Metatheory.RGAConditionedConvergence (applySeqR)
open Sal.Metatheory.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.Metatheory.G2Probe (RGACondSig)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open RGARecPathFaithful
  (target recPath RecPathFaithful recPathFaithful_of_accurate faithful_of_recPathFaithful
   recList_eq_target_recPath faithful_ins_root)
open Sal.Metatheory.RGAUpdateConvergenceFinal (RGA_update_convergence)

/-! ## §1  Non-degeneracy: a `Del`'s target is a genuine (nonzero) node -/

/-- The mild genuineness discipline: a `Del`'s target is nonzero (the root sentinel
is never a real delete target).  An `Ins` is unconstrained (a root-anchored `Ins`,
target `0`, is admissible and independently `Faithful`). -/
def NonDegen (o : op_t) : Prop :=
  match o with
  | (_, _, .Del _ x)   => x ≠ 0
  | (_, _, .Ins _ _ _) => True

/-! ## §2  The pivot: per-event `accurate` ⇒ `Faithful`

`accurate o s` says o's recorded path is the genuine live ancestor chain of its
target at `s`.  That is exactly `RecPathFaithful` at o's birth (`Reach.refl`), which
projects to `Faithful` (`faithful_of_recPathFaithful`).  The one degenerate shape —
a root-anchored `Ins` (target `0`) — is `Faithful` outright (`faithful_ins_root`); a
degenerate `Del` (target `0`) is excluded by `NonDegen`.  NO `GoodFold`, NO history
linkage: o's OWN accuracy suffices, for BOTH op kinds. -/
theorem faithful_of_accurate (o : op_t) (s : concrete_st)
    (h0 : contains s 0 = false) (hacc : accurate o s) (hnd : NonDegen o) :
    Faithful o s := by
  by_cases htgt : target o = 0
  · -- degenerate branch is forced; it must be a root `Ins`
    obtain ⟨t, r, op⟩ := o
    cases op with
    | Ins e pre a =>
      simp only [target, opLeaf] at htgt
      subst htgt
      simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨_, hpe⟩ | ⟨hc, _⟩
      · subst hpe; exact faithful_ins_root s t r e h0
      · rw [h0] at hc; exact absurd hc (by simp)
    | Del pre x =>
      simp only [target, opLeaf] at htgt
      simp only [NonDegen] at hnd
      exact absurd htgt hnd
  · exact faithful_of_recPathFaithful o s (recPathFaithful_of_accurate o s h0 hacc htgt)

/-! ## §3  The second win: per-event accuracy + freshness ⇒ `NoFreshClash`

`NoFreshClash a b` (for `b` an `Ins` of id `t2`) is `t2 ∉ recList a`.  A fresh id is
DEAD at the fold (`fresh_ts b`), while `accurate a` makes every entry of `recList a`
LIVE (target live, path entries live by `isAncPath_mem`) — so a fresh id can name no
entry of `a`'s recorded list.  A live/dead separation, from the two events' OWN
generation facts; NO cross-event history linkage. -/

/-- A fresh (dead, nonzero) id occurs in no entry of an `accurate` event's recorded
list: every entry is live at `s`, the id is dead. -/
theorem freshId_not_mem_recList (a : op_t) (s : concrete_st) (tb : ℕ)
    (hacc : accurate a s) (htb0 : tb ≠ 0) (htbdead : contains s tb = false) :
    tb ∉ recList a := by
  rw [recList_eq_target_recPath]
  simp only [accurate] at hacc
  rcases hacc with ⟨hl0, hp0⟩ | ⟨hlive, hpath⟩
  · have ht : target a = 0 := hl0
    have hp : recPath a = [] := hp0
    rw [ht, hp]
    simp only [List.mem_singleton]
    exact htb0
  · intro hmem
    have hlive' : contains s (target a) = true := hlive
    have hpath' : IsAncPath s (target a) (recPath a) := hpath
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · rw [hlive'] at htbdead; exact Bool.noConfusion htbdead
    · have hc : contains s tb = true := isAncPath_mem s (target a) (recPath a) hpath' tb htail
      rw [hc] at htbdead; exact Bool.noConfusion htbdead

/-- **`NoFreshClash a b` from per-event data.**  `accurate a` (every entry of
`recList a` live) plus `fresh_ts b` (b's created id dead) plus `NonDegen b` (a `Del`
b's target nonzero) yields the causal-freshness bound — for all four op-kind pairs. -/
theorem noFreshClash_of_accurate_fresh (a b : op_t) (s : concrete_st)
    (hacc : accurate a s) (hfb : fresh_ts b s) (hndb : NonDegen b) :
    NoFreshClash a b := by
  obtain ⟨tb, rb, ob⟩ := b
  cases ob with
  | Ins eb pb anchb =>
    simp only [fresh_ts] at hfb
    obtain ⟨htb0, htbdead⟩ := hfb
    have hnin : tb ∉ recList a := freshId_not_mem_recList a s tb hacc htb0 htbdead
    obtain ⟨ta, ra, oa⟩ := a
    cases oa with
    | Ins ea pa ancha => exact hnin
    | Del pa xa => exact hnin
  | Del pb xb =>
    obtain ⟨ta, ra, oa⟩ := a
    cases oa with
    | Ins ea pa ancha => trivial
    | Del pa xa =>
      simp only [NonDegen] at hndb
      exact hndb

/-! ## §4  The per-event generation discipline `GenDisc`

**Why this is strictly more primitive than `RGAGenDiscipline`.**  `RGAGenDiscipline`
asserts, per prefix and per swapped PAIR: `FoldFaithSource a` / `FoldFaithSource b`
(for an `Ins`, the per-STEP `GoodFold (recList ·)` order fact — a statement about the
WHOLE prefix's step classification), the reachable-state block, and both
`NoFreshClash`.  `GenDisc` asserts, per SINGLE event `o`: only that o's OWN recorded
path is o's true live chain (`accurate o`) and o's OWN id is fresh (`fresh_ts o`), at
the prefixes containing exactly o's own dependencies — plus the mild `NonDegen o`.
It names NO other event, NO `Faithful`/`GoodFold`, NO `wf`/`id_mono`/`contains 0`, NO
`NoFreshClash`.  The `Faithful` and `NoFreshClash` conjuncts of the bundle are here
DERIVED (§2, §3) from this single-event data. -/
def GenDisc (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  ∀ (o : op_t), o ∈ E → NonDegen o ∧
    ∀ (pre : List op_t),
      (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
      o ∉ pre →
      (∀ z ∈ E, z ≠ o → loOnA RGACondSig Cfg E z o → z ∈ pre) →
      accurate o (applySeqR init_st pre) ∧ fresh_ts o (applySeqR init_st pre)

/-! ## §5  The NAMED per-prefix residual `ReachInv`

The reachable-state block does NOT reduce to per-event accuracy: threading `RgaInv`
(`contains 0 = false ∧ wf`) and `id_mono` along a fold needs every INTERNAL step of
the prefix to be `accurate`+`fresh` at its own sub-fold — which requires that
sub-fold to already contain that step's ancestors (else the step's recorded path is
not the live chain and `accurate` fails there).  That internal backward-saturation is
a STRUCTURAL property of the enumeration, not an event's own generation.  So we keep
the block as an explicit, honestly per-prefix residual — the "reachable-state
invariant" the STATUS blocks of `RGA_UpdateConvergence_Final`/`RGA_ReachDischarge`
already isolate (it needs `noopFeasible` of the eligible interleaving). -/
def ReachInv (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  ∀ (pre : List op_t),
    (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
    contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
    ∧ id_mono (applySeqR init_st pre)

/-! ## §6  From per-event `GenDisc` (+ residual) to the `hReach` bundle -/

/-- The seven-conjunct per-prefix `hReach` bundle of `RGA_update_convergence`,
assembled at each eligible prefix from the per-event `GenDisc` (the four
`Faithful`/`NoFreshClash` conjuncts) and the named residual `ReachInv` (the
reachable-state block). -/
theorem hReach_of_genDisc
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (E : Set op_t)
    (hGen : GenDisc Cfg E) (hInv : ReachInv Cfg E)
    (pre : List op_t) (a b : op_t)
    (hsub : ∀ x ∈ pre, x ∈ E) (hnd : pre.Nodup)
    (hresp : respects pre (loOnA RGACondSig Cfg E))
    (ha : a ∈ E) (hb : b ∈ E) (hanp : a ∉ pre) (hbnp : b ∉ pre) (_hab : a ≠ b)
    (_hnab : ¬ loOnA RGACondSig Cfg E a b) (_hnba : ¬ loOnA RGACondSig Cfg E b a)
    (hena : ∀ z ∈ E, z ≠ a → loOnA RGACondSig Cfg E z a → z ∈ pre)
    (henb : ∀ z ∈ E, z ≠ b → loOnA RGACondSig Cfg E z b → z ∈ pre) :
    contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
    ∧ id_mono (applySeqR init_st pre)
    ∧ Faithful a (applySeqR init_st pre) ∧ Faithful b (applySeqR init_st pre)
    ∧ NoFreshClash a b ∧ NoFreshClash b a := by
  obtain ⟨h0, hwf, hmono⟩ := hInv pre hsub hnd hresp
  obtain ⟨hnda, hGa⟩ := hGen a ha
  obtain ⟨hndb, hGb⟩ := hGen b hb
  obtain ⟨hacca, hfa⟩ := hGa pre hsub hnd hresp hanp hena
  obtain ⟨haccb, hfb⟩ := hGb pre hsub hnd hresp hbnp henb
  exact ⟨h0, hwf, hmono,
    faithful_of_accurate a _ h0 hacca hnda,
    faithful_of_accurate b _ h0 haccb hndb,
    noFreshClash_of_accurate_fresh a b _ hacca hfb hndb,
    noFreshClash_of_accurate_fresh b a _ haccb hfa hnda⟩

/-! ## §7  The headline: update convergence conditional on per-event `GenDisc`

Composes `hReach_of_genDisc` into `RGA_update_convergence` (the `hReach`-parametric
headline of `RGA_UpdateConvergence_Final`).  No per-prefix `RGAGenDiscipline`, no
`hReach`, no swap survives as a premise: convergence is now conditional on the
PER-EVENT `GenDisc E` plus the named per-prefix residual `ReachInv E` (the
reachable-state invariant) plus the enumeration hypotheses. -/
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

end Sal.Metatheory.RGAGenDischarge
