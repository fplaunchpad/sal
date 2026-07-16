import Sal.ConditionedMRDTs.Development.RGA_ConvergenceEq
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.ConditionedExecutionModel
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonFoldOK
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_SubchainResolve

/-!
# The load-bearing bridge: `applicable` (accuracy at the ACTUAL prefix) ⟹ the
convergence engine's per-step obligation — DIRECTLY, no dependency-prefix transport

*Additive; modifies no existing file; 0 `sorry`, kernel-clean.*

## Why this file exists (the research finding it certifies)

`RGA_ConvergenceEq.canonFoldOK_of_loOnEq` derives the engine's per-step
discipline `CanonStepOK` from `GenDisc2CEq` — accuracy at the fold of each
event's *reordered `loOnEq`-dependency prefix*.  The pen-and-paper analysis
(`LOONA_VS_LOONEQ_ANALYSIS.md`) found `GenDisc2CEq` to be the WRONG condition:
it is *stronger* than convergence needs and is FALSE for genuine reachable
executions (e.g. `E = {Ins b, Ins a@b, Del b, Ins e [] a}`, where `Ins e [] a`'s
`loOnEq`-dependency prefix reorders it ahead of `Del b`, at a fold where its
honest empty path is inaccurate).  So it can never be discharged from honest
generation — it must stay an assumed premise that silently excludes honest runs.

The honest condition is the first-class `applicable` field
(`RGACondSig.applicable o s := accurate o s ∧ fresh_ts o s`) evaluated at the
**actual** delivery prefix, packaged per-prefix as `noopFeasible`
(`UpdateFeasibility_Gate`).  This file certifies the mathematically load-bearing
step of that re-basing: **`accurate o s` at the actual prefix `s` gives the
engine's chain obligation (`ChainOK` / `DelOK`) at `s` with NO transport** — the
`chainOK_transport` / `anc_transport` machinery of `canonStepOK_of_genR`, whose
entire job was to carry accuracy from a *dependency* prefix to the actual one,
simply collapses because the accuracy is already at the actual prefix.

* `chainOK_of_accurate_ins` / `delOK_of_accurate_del` — the two crux reductions.
* `chainOK_of_appOrNoop_ins` / `delOK_of_appOrNoop_del` — lifted to the
  `applicable`-OR-no-op disjunction the delivery discipline actually supplies:
  a no-op `Ins` is impossible under freshness, a no-op `Del` leaves its target
  absent (so `DelOK` holds vacuously) — the two no-op branches `noopFeasible`
  admits, discharged.

This is the "it is all there" step made kernel-checked: `applicable` alone
carries the per-step obligation; `GenDisc2CEq` was a detour.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGANoopFeasible

open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (appOrNoop)
open Sal.ConditionedMRDTs.RGACanonFoldOK
open RGACanonConvergence
open RGAMergeLinearization (applySeqR)

/-! ## §1  The two crux reductions: accuracy at the actual prefix ⟹ chain obligation -/

/-- **Crux (Ins).**  If an `Ins`'s recorded chain `a :: p` is `accurate` at the
state `s` it is actually applied to, then the engine's `ChainOK s (a :: p)`
holds there — DIRECTLY.  `accurate` makes every chain entry live, so the live
sublist is the whole chain and `IsAncPath` is exactly the recorded path.  No
transport from a dependency prefix: the accuracy is already at `s`. -/
theorem chainOK_of_accurate_ins (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false)
    (hacc : accurate (t, r, .Ins e p a) s) : ChainOK s (a :: p) := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro c cs hlive
  rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
  · subst ha0; subst hp0
    have hnil : liveSub s [0] = [] := by
      unfold liveSub
      rw [List.filter_cons, List.filter_nil, h0]
      simp
    rw [hnil] at hlive
    exact absurd hlive.symm (List.cons_ne_nil c cs)
  · have hmem : ∀ z ∈ p, contains s z = true := isAncPath_mem s a p hpath
    have hall : ∀ z ∈ (a :: p), contains s z = true := by
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · exact h ▸ hal
      · exact hmem z h
    have hfl : liveSub s (a :: p) = a :: p := by
      unfold liveSub; exact List.filter_eq_self.mpr hall
    rw [hfl] at hlive
    simp only [List.cons.injEq] at hlive
    obtain ⟨rfl, rfl⟩ := hlive
    exact hpath

/-- **Crux (Del).**  If a `Del`'s recorded chain `p` is `accurate` at the state
`s` it is actually applied to, then the engine's `DelOK s p x` holds there —
DIRECTLY.  `resolve` of an accurate path returns the target's stored anchor. -/
theorem delOK_of_accurate_del (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false)
    (hacc : accurate (t, r, .Del p x) s) : DelOK s p x := by
  simp only [accurate, opLeaf, opPath] at hacc
  rcases hacc with ⟨hx0, hp0⟩ | ⟨hxl, hpath⟩
  · subst hx0; subst hp0
    refine ⟨fun _ => rfl, fun hcx => ?_⟩
    rw [h0] at hcx; exact absurd hcx (by simp)
  · refine ⟨fun hx0 => ?_, fun _ => ?_⟩
    · rw [hx0, h0] at hxl; exact absurd hxl (by simp)
    · cases p with
      | nil =>
        simp only [IsAncPath] at hpath
        simp only [resolve]; exact hpath.symm
      | cons q qs =>
        simp only [IsAncPath] at hpath
        obtain ⟨hanc, hcq, _⟩ := hpath
        simp only [resolve, hcq, if_true, hanc]

/-! ## §2  Lifted to the delivery disjunction `applicable ∨ no-op`

`noopFeasible` supplies, at each actual prefix, `appOrNoop RGACondSig o s`
(`RGACondSig.applicable o s ∨ RGACondSig.update s o = s`).  The chain obligation
survives both disjuncts: applicable feeds §1; the no-op branch is discharged. -/

/-- A no-op `Ins` is impossible where its id is fresh: `do_` writes id `t`, so it
cannot leave a state with `contains s t = false` unchanged.  Hence under
freshness the chain obligation always comes from the applicable branch. -/
theorem chainOK_of_appOrNoop_ins (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false) (htf : contains s t = false)
    (h : appOrNoop RGACondSig (t, r, .Ins e p a) s) : ChainOK s (a :: p) := by
  rcases h with happ | hnoop
  · exact chainOK_of_accurate_ins s t r e a p h0 happ.1
  · exfalso
    have hnoop' : do_ s (t, r, .Ins e p a) = s := hnoop
    have hcontra : contains (do_ s (t, r, .Ins e p a)) t = true := by
      simp only [do_]; rw [lemma_InDomUpd1]; simp
    rw [hnoop', htf] at hcontra
    exact absurd hcontra (by simp)

/-- A no-op `Del` leaves its target absent (a genuine delete removes it), so
`DelOK` holds vacuously.  `x ≠ 0` rules out the degenerate root-target delete
(no honest op targets the root sentinel). -/
theorem delOK_of_appOrNoop_del (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false) (hxne : x ≠ 0)
    (h : appOrNoop RGACondSig (t, r, .Del p x) s) : DelOK s p x := by
  rcases h with happ | hnoop
  · exact delOK_of_accurate_del s t r x p h0 happ.1
  · have hnoop' : do_ s (t, r, .Del p x) = s := hnoop
    refine ⟨fun hx0 => absurd hx0 hxne, fun hcx => ?_⟩
    exfalso
    have habs : contains (do_ s (t, r, .Del p x)) x = false := by
      rw [contains_doDel]; simp
    rw [hnoop', hcx] at habs
    exact absurd habs (by simp)

/-! ## §3  `noopFeasible` ⟹ `CanonFoldOK`, over a good `loOnEq`-enum

The engine (`RGA_ConvergenceEq.canonFoldOK_of_genR`) derives `CanonFoldOK` from
`GenDisc2CEq` (accuracy at the reordered dependency prefix).  Here we derive it
from `noopFeasible` (accuracy at the ACTUAL prefix) instead.  The chain obligation
comes from §2 with NO transport; the freshness bullets collapse to a single fact —
**no earlier event references the fresh id** — supplied by `RefEdge` (references
induce order edges) plus the good-enum's `hlast`.  `RefEdge` is the honest
causal-reference wellformedness the reachability layer provides. -/

open Sal.ConditionedMRDTs.RGAConvergenceEq (GoodEnumR goodEnumR_append loEqRGA)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpGenQ)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.Emulation (respects listPermOf)

/-- The ids an op names: its leaf (anchor/target) followed by its recorded path. -/
def refsOf (z : op_t) : List ℕ := opLeaf z.2.2 :: opPath z.2.2

/-- **References induce order edges.**  If `b` names the id `a.1` (which, by
id-uniqueness, `a` alone creates), then the order `R` puts `a` before `b`.  On the
RGA's `loOnEq` this is causal-reference wellformedness (`a` creates a node `b`
sees ⟹ `vis a b`) plus the creator/user non-commutation — both honest-execution
facts the reachability layer supplies. -/
def RefEdge (E : Set op_t) (R : op_t → op_t → Prop) : Prop :=
  ∀ a ∈ E, ∀ b ∈ E, a.1 ∈ refsOf b → a.1 ≠ b.1 → R a b

/-- Split a `noopFeasible` snoc: the prefix is `noopFeasible` and the last op is
`appOrNoop` at the prefix fold. -/
theorem noopFeasible_snoc (F : List op_t) (o : op_t) (s : concrete_st)
    (h : noopFeasible RGACondSig (F ++ [o]) s) :
    noopFeasible RGACondSig F s ∧ appOrNoop RGACondSig o (applySeqR s F) := by
  induction F generalizing s with
  | nil =>
    simp only [List.nil_append] at h
    exact ⟨trivial, h.1⟩
  | cons a F' ih =>
    obtain ⟨ha, hrest⟩ := h
    obtain ⟨hF', ho⟩ := ih (do_ s a) hrest
    exact ⟨⟨ha, hF'⟩, ho⟩

/-- **`canonStepOK_of_noopFeasible`** — the per-event discipline at the event's OWN
application point, from `appOrNoop` at that point (via §2) plus the freshness core
(`RefEdge` + `WfOpGenQ` + id-uniqueness).  The `≈`-side mirror of
`canonStepOK_of_genR`, but sourcing accuracy from the actual prefix — so no
`depPack`, no `chainOK_transport`. -/
theorem canonStepOK_of_noopFeasible (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E R)
    (F : List op_t) (o : op_t)
    (hg : GoodEnumR E R (F ++ [o]))
    (hstep : appOrNoop RGACondSig o (applySeqR init_st F))
    (hnfF : noopFeasible RGACondSig F init_st)
    (hIH : ∀ σ : List op_t, σ.length ≤ F.length → GoodEnumR E R σ →
      noopFeasible RGACondSig σ init_st → CanonFoldOK [] init_st σ) :
    CanonStepOK F (applySeqR init_st F) o := by
  obtain ⟨hgF, hoE, honF, hlast⟩ := goodEnumR_append E R F o hg
  have hinvF : CanonInv F (applySeqR init_st F) :=
    canon_fold F [] init_st canonInv_init (hIH F le_rfl hgF hnfF)
  have h0 : contains (applySeqR init_st F) 0 = false := hinvF.1
  -- `o.1` is inserted nowhere in `F` (id-uniqueness + `CanonInv`)
  have hfresh : ∀ L : List op_t, (∀ x ∈ L, x ∈ F) → ¬ insertedIn L o.1 := by
    rintro L hL ⟨r', e', p', a', hm⟩
    have hmF : (o.1, r', .Ins e' p' a') ∈ F := hL _ hm
    have hne : (o.1, r', .Ins e' p' a') ≠ o := fun hEq => honF (hEq ▸ hmF)
    exact hdts _ o (hgF.1 _ hmF) hoE hne rfl
  -- the freshness core: no earlier event references `o.1`
  have hnoRef : ∀ z ∈ F, o.1 ∉ refsOf z := by
    intro z hzF hin
    have hzE : z ∈ E := hgF.1 z hzF
    have hne : o.1 ≠ z.1 :=
      hdts o z hoE hzE (fun heq => honF (heq ▸ hzF))
    exact hlast z hzF (href o hoE z hzE hin hne)
  obtain ⟨t, r, op⟩ := o
  have ht0 : t ≠ 0 := hids0 (t, r, op) hoE
  cases op with
  | Ins e p a =>
    have htf : contains (applySeqR init_st F) t = false := by
      cases hb : contains (applySeqR init_st F) t with
      | false => rfl
      | true =>
        exact absurd (insertedIn_of_contains_fold F t hb) (hfresh F (fun _ hx => hx))
    refine ⟨ht0, htf, ?_, ?_, ?_, ?_⟩
    · -- ¬ deletedIn F t : a `Del` in `F` with target `t` would reference `t`
      rintro ⟨t', r', p', hm⟩
      exact hnoRef (t', r', .Del p' t) hm (List.mem_cons_self ..)
    · -- t ∉ a :: p : `WfOpGenQ` puts every chain entry strictly below `t`
      intro hmem
      exact absurd ((hgen (t, r, .Ins e p a) hoE).2 t hmem) (lt_irrefl t)
    · -- monotone-alloc: an `Ins` in `F` whose chain names `t` would reference `t`
      intro t' r' e' p' a' hm hmem
      exact hnoRef (t', r', .Ins e' p' a') hm hmem
    · -- ChainOK from `appOrNoop` (§2)
      exact chainOK_of_appOrNoop_ins (applySeqR init_st F) t r e a p h0 htf hstep
  | Del p x =>
    have hxne : x ≠ 0 := (hgen (t, r, .Del p x) hoE).1
    exact delOK_of_appOrNoop_del (applySeqR init_st F) t r x p h0 hxne hstep

/-- **`canonFoldOK_of_noopFeasible`** — every `noopFeasible`, good `loOnEq`-enum of
a delivered set is `CanonFoldOK`-disciplined.  The `GenDisc2CEq`-free replacement
for `canonFoldOK_of_genR`: born-applicable delivery, not dependency-prefix
accuracy. -/
theorem canonFoldOK_of_noopFeasible (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E R) :
    ∀ (n : ℕ) (σ : List op_t), σ.length ≤ n → GoodEnumR E R σ →
      noopFeasible RGACondSig σ init_st → CanonFoldOK [] init_st σ := by
  intro n
  induction n with
  | zero =>
    intro σ hlen _ _
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
    trivial
  | succ n ih =>
    intro σ hlen hg hnf
    rcases List.eq_nil_or_concat σ with rfl | ⟨F, o, hEq⟩
    · trivial
    · rw [List.concat_eq_append] at hEq
      subst hEq
      have hlenF : F.length ≤ n := by
        rw [List.length_append] at hlen
        simp only [List.length_singleton] at hlen
        omega
      have hgF := (goodEnumR_append E R F o hg).1
      obtain ⟨hnfF, hstep⟩ := noopFeasible_snoc F o init_st hnf
      exact canonFoldOK_append F [] init_st o
        (ih F hlenF hgF hnfF)
        (canonStepOK_of_noopFeasible E R hdts hids0 hgen href F o hg hstep hnfF
          (fun τ hτ hgτ hnfτ => ih τ (hτ.trans hlenF) hgτ hnfτ))

/-! ## §4  RGA update convergence over born-applicable delivery

The `GenDisc2CEq`-free analogue of `RGA_ConvergenceEq.RGA_update_convergence_eq`:
two order-respecting, `noopFeasible` enumerations of the same delivered set fold
to observationally equal states.  Order-agnostic (`R` abstract), so the framework
instantiates `R := loEqRGA …` (the `≈`-conditioned order) at will. -/

/-- **RGA update convergence over `noopFeasible` delivery.**  Two `R`-respecting,
`noopFeasible` enumerations of `E` converge (`eq`).  Premises: id-uniqueness
(`hdts`), nonzero ids, per-op genuineness `WfOpGenQ`, and causal references
(`RefEdge`) — every input the reachable execution supplies; NO `GenDisc2CEq`. -/
theorem RGA_update_convergence_noop
    (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E R)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ R) (h₂r : respects π₂ R)
    (hnf₁ : noopFeasible RGACondSig π₁ init_st)
    (hnf₂ : noopFeasible RGACondSig π₂ init_st) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) :=
  RGA_update_convergence_canon π₁ π₂
    (fun o => (h₁p.2 o).trans (h₂p.2 o).symm)
    (canonFoldOK_of_noopFeasible E R hdts hids0 hgen href π₁.length π₁ le_rfl
      ⟨fun x hx => (h₁p.2 x).mp hx, h₁p.1, h₁r,
       fun _x _hx z hz _ _ => (h₁p.2 z).mpr hz⟩ hnf₁)
    (canonFoldOK_of_noopFeasible E R hdts hids0 hgen href π₂.length π₂ le_rfl
      ⟨fun x hx => (h₂p.2 x).mp hx, h₂p.1, h₂r,
       fun _x _hx z hz _ _ => (h₂p.2 z).mpr hz⟩ hnf₂)

/-- **Specialized to the framework's `≈`-order** `loEqRGA Cfg E`, with
id-uniqueness read off a `ConditionedConfiguration` (`C.distinctTs`).  The exact
shape the `≈`-Join consumes, with `noopFeasible`/`RefEdge` in place of
`GenDisc2CEq`. -/
theorem RGA_update_convergence_noop_loEq
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E (loEqRGA Cfg E))
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loEqRGA Cfg E)) (h₂r : respects π₂ (loEqRGA Cfg E))
    (hnf₁ : noopFeasible RGACondSig π₁ init_st)
    (hnf₂ : noopFeasible RGACondSig π₂ init_st) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) :=
  RGA_update_convergence_noop E (loEqRGA Cfg E)
    (fun _ _ ha hb hne => C.distinctTs E hE ha hb hne)
    hids0 hgen href π₁ π₂ h₁p h₂p h₁r h₂r hnf₁ hnf₂

/-! ## §5  Axiom audit -/

#print axioms chainOK_of_accurate_ins
#print axioms delOK_of_accurate_del
#print axioms chainOK_of_appOrNoop_ins
#print axioms delOK_of_appOrNoop_del
#print axioms canonStepOK_of_noopFeasible
#print axioms canonFoldOK_of_noopFeasible
#print axioms RGA_update_convergence_noop
#print axioms RGA_update_convergence_noop_loEq

end Sal.ConditionedMRDTs.RGANoopFeasible
