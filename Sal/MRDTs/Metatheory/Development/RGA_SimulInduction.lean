import Sal.MRDTs.Metatheory.Development.RGA_GenDischarge2
import Mathlib.Data.Finset.Card

/-!
# The simultaneous convergence∧faithfulness induction (update layer)

Mechanizes `SIMULTANEOUS_INDUCTION_DESIGN.md`: `P(S) = (Conv S) ∧ (Faith S)` by strong
induction on `|S|` over dependency-closed finite event sets `S ⊆ E`, with the ambient
order `loOnA RGACondSig Cfg E` FIXED at the full set `E` (so shrinking `S` never
re-parameterizes the order).  `Faith` is stated with the event LAST (`ρ ++ [o]`) — the
design's key economy; Faithful at the interior prefixes a swap visits is reached through
the INDUCTION HYPOTHESIS at strictly smaller dependency-closed sets, never as a
standalone per-prefix lemma (the three factored attempts' circularity).

Inputs per the design: `GenDisc2` (dependency-prefix accuracy, the satisfiable per-event
discipline) + `ReachInv` (fold invariants) + the configuration facts (`BackClosed`,
nonzero ids) — plus ONE order-level residual the design left implicit, `DepComp` (§2):
the deps-first reorder `ρ ≈ d ++ c` that seats `GenDisc2`'s accuracy is a
`loOnA`-respecting enumeration ONLY IF a dependency of a dependency is a dependency
(`lo b a → lo a o → lo b o`).  See the STATUS block at the end for the exact goal that
forces it.  NO `EligibleThread`, NO per-prefix `Faithful`/`hReach` hypothesis survives.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGASimulInduction

open Sal.Emulation
open Sal.Metatheory.RGAGeneralSwap (Faithful ClimbFaithful DelTargetFaithful NoFreshClash)
open Sal.Metatheory.RGABubbleWiring
  (recList ChainFaithful ChainFaithfulAux climbFaithful_of_chain)
open Sal.Metatheory.RGAConditionedConvergence
  (applySeqR applySeqR_append applySeqR_cons applySeqR_nil do_eq_congr resolve_eq_congr
   EqSwap eqSwap_of_bothFaithful bubble_eq)
open Sal.Metatheory.ConditionedConvergence (loOnA)
open Sal.Metatheory.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.Metatheory.RGASig (RGACondSig isAncPath_not_mem)
open RGAInterleavedThreading (GoodStep GoodFold)
open Sal.Metatheory.RGAGenDischarge
  (NonDegen ReachInv noFreshClash_of_accurate_fresh freshId_not_mem_recList)
open Sal.Metatheory.RGAGenDischarge2 (IsDepPre GenDisc2 chainFaithful_depPre_concTail)
open Sal.Metatheory.RGAUpdateConvergenceFinal
  (fresh_ts_config goodFold_of_stepwise goodStep_ins_concurrent)

/-! ## §0  Order plumbing (generic in the relation) -/

/-- A sublist of a `respects`-list `respects`. -/
theorem respects_sublist {α : Type} {R : α → α → Prop} {l₁ l₂ : List α}
    (h : l₁.Sublist l₂) (hr : respects l₂ R) : respects l₁ R := by
  unfold respects at hr ⊢
  exact List.Pairwise.sublist h hr

/-- The cross component of a `respects`-append: nothing in the suffix is `R`-below
anything in the prefix. -/
theorem respects_cross {α : Type} {R : α → α → Prop} {u v : List α}
    (h : respects (u ++ v) R) : ∀ a ∈ u, ∀ b ∈ v, ¬ R b a := by
  unfold respects at h
  exact (List.pairwise_append.mp h).2.2

/-- Builder for a `respects`-append from the two parts and the cross condition. -/
theorem respects_append {α : Type} {R : α → α → Prop} {u v : List α}
    (hu : respects u R) (hv : respects v R) (hcross : ∀ a ∈ u, ∀ b ∈ v, ¬ R b a) :
    respects (u ++ v) R := by
  unfold respects at hu hv ⊢
  exact List.pairwise_append.mpr ⟨hu, hv, hcross⟩

/-- Builder for `respects (u ++ [x])`. -/
theorem respects_concat {α : Type} {R : α → α → Prop} {u : List α} {x : α}
    (hu : respects u R) (hx : ∀ a ∈ u, ¬ R x a) : respects (u ++ [x]) R :=
  respects_append hu (by unfold respects; simp) (fun a ha b hb => by
    rw [List.mem_singleton] at hb; subst hb; exact hx a ha)

/-- In a `respects`-enumeration, an `R`-predecessor of `g` sits strictly left of `g`. -/
theorem pred_mem_left {α : Type} {R : α → α → Prop} {u v : List α} {g z : α}
    (hresp : respects (u ++ g :: v) R) (hz : z ∈ u ++ g :: v)
    (hlo : R z g) (hzg : z ≠ g) : z ∈ u := by
  unfold respects at hresp
  rcases List.mem_append.mp hz with h1 | h2
  · exact h1
  · exfalso
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hzg rfl
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp hresp).2.1).1 z h3 hlo

/-! ## §1  State glue: the `Del` projection of `ChainFaithful`, and `eq`-congruence
of `Faithful` — both pure definition-layer lifts of existing machinery. -/

/-- **`Del` projection of the threaded chain invariant.**  `ChainFaithful s (x :: p)`
(the fold-threaded invariant on the `Del`'s `recList`) projects to the `Del`'s own
`Faithful`: live target — level 1 is `DelTargetFaithful` and level 2 is
`ClimbFaithful p`; dead (concurrently deleted) target — `DelTargetFaithful` is vacuous
and the dead head is skipped by `resolve`.  Companion of `climbFaithful_of_chain`
(the `Ins` projection). -/
theorem faithful_del_of_chain (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false) (hx0 : x ≠ 0) (hxp : x ∉ p)
    (hcf : ChainFaithful s (x :: p)) : Faithful (t, r, .Del p x) s := by
  show ClimbFaithful s p ∧ DelTargetFaithful s p x ∧ x ≠ 0
  simp only [ChainFaithful, List.length_cons, ChainFaithfulAux] at hcf
  by_cases hx : contains s x = true
  · -- live target
    have hres : resolve s (x :: p) = x := resolve_live_head s x p hx
    rw [hres] at hcf
    obtain ⟨h1, h2⟩ := hcf hx
    have hfilt : (x :: p).filter (fun c => c != x) = p := by
      rw [List.filter_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      exact List.filter_eq_self.mpr (fun c hc => by
        simp only [bne_iff_ne, ne_eq]; exact fun e => hxp (e ▸ hc))
    rw [hfilt] at h1 h2
    refine ⟨?_, fun _ => h1, hx0⟩
    -- ClimbFaithful s p from the level-2 chain invariant
    intro hlive
    cases hp : p with
    | nil =>
      subst hp
      simp only [resolve] at hlive
      rw [h0] at hlive
      exact absurd hlive (by simp)
    | cons q qs =>
      subst hp
      simp only [List.length_cons, ChainFaithfulAux] at h2
      exact (h2 hlive).1
  · -- dead (concurrently deleted) target
    have hxf : contains s x = false := by
      cases h : contains s x
      · rfl
      · exact absurd h hx
    have hres : resolve s (x :: p) = resolve s p := resolve_dead_head s x p hxf
    rw [hres] at hcf
    refine ⟨?_, fun hlive => absurd hlive (by rw [hxf]; simp), hx0⟩
    intro hlive
    obtain ⟨h1, _⟩ := hcf hlive
    have hxv : x ≠ resolve s p := by
      intro e
      rw [e, hlive] at hxf
      exact Bool.noConfusion hxf
    have hfilt : (x :: p).filter (fun c => c != resolve s p)
        = x :: p.filter (fun c => c != resolve s p) := by
      rw [List.filter_cons]
      simp only [bne_iff_ne, ne_eq, hxv, not_false_eq_true, if_true]
    rw [hfilt, resolve_dead_head s x _ hxf] at h1
    exact h1

/-- `ClimbFaithful` is invariant across observationally-`eq` states (`resolve` reads
only `contains`; `anc` reads `sel` at a live key). -/
theorem climbFaithful_eq_congr (s s' : concrete_st) (h : eq s s') (L : List ℕ)
    (hc : ClimbFaithful s L) : ClimbFaithful s' L := by
  unfold ClimbFaithful at hc ⊢
  have hres : resolve s L = resolve s' L := resolve_eq_congr s s' h L
  rw [← hres]
  intro hlive'
  have hlive : contains s (resolve s L) = true := by
    rw [(h (resolve s L)).1]; exact hlive'
  have h1 := hc hlive
  have hresf := resolve_eq_congr s s' h (L.filter (fun c => c != resolve s L))
  have hanc : anc s (resolve s L) = anc s' (resolve s L) := by
    simp only [anc]
    rw [(h (resolve s L)).2 hlive]
  rw [← hresf, ← hanc]
  exact h1

/-- `DelTargetFaithful` is invariant across observationally-`eq` states. -/
theorem delTargetFaithful_eq_congr (s s' : concrete_st) (h : eq s s') (p : List ℕ) (x : ℕ)
    (hd : DelTargetFaithful s p x) : DelTargetFaithful s' p x := by
  intro hx'
  have hx : contains s x = true := by rw [(h x).1]; exact hx'
  have h1 := hd hx
  have hres := resolve_eq_congr s s' h p
  have hanc : anc s x = anc s' x := by simp only [anc]; rw [(h x).2 hx]
  rw [← hres, ← hanc]
  exact h1

/-- **`eq`-congruence of `Faithful`** — the transport the design uses to carry the
faithfulness fact across the `Conv`-supplied reorder `ρ ≈ d ++ c`. -/
theorem faithful_eq_congr (o : op_t) (s s' : concrete_st) (h : eq s s')
    (hf : Faithful o s) : Faithful o s' := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    exact climbFaithful_eq_congr s s' h (a :: p) hf
  | Del p x =>
    obtain ⟨hc, hd, hx0⟩ := hf
    exact ⟨climbFaithful_eq_congr s s' h p hc,
           delTargetFaithful_eq_congr s s' h p x hd, hx0⟩

/-! ## §2  The combined statement `P(S) = Conv S ∧ Faith S`, and the order residual -/

variable (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig) (E : Set op_t)

/-- `S` is a dependency-closed sub-Finset of the ambient event set `E`: members are
`E`-events and every `loOnA`-predecessor (taken in `E`, i.e. w.r.t. the FIXED ambient
order) of a member is a member.  The induction ranges over these; peeling a
quasi-maximal element preserves the class.  This is the induction-internal form of
the design's "backward-closed reachable event set". -/
def DC (S : Finset op_t) : Prop :=
  (∀ x ∈ S, x ∈ E) ∧
  ∀ w ∈ S, ∀ z ∈ E, z ≠ w → loOnA RGACondSig Cfg E z w → z ∈ S

/-- **(Conv S)**: any two `loOnA`-respecting enumerations of `S` fold from `init_st`
to observationally-`eq` states.  The order is the AMBIENT `loOnA … E`. -/
def Conv (S : Finset op_t) : Prop :=
  ∀ π₁ π₂ : List op_t,
    listPermOf π₁ ↑S → listPermOf π₂ ↑S →
    respects π₁ (loOnA RGACondSig Cfg E) → respects π₂ (loOnA RGACondSig Cfg E) →
    eq (applySeqR init_st π₁) (applySeqR init_st π₂)

/-- **(Faith S)**: every `o ∈ S` is `Faithful` at the fold of any `loOnA`-respecting
enumeration of `S` with `o` LAST (`ρ` enumerates `S \ {o}`).  NOT quantified over
arbitrary prefixes — the design's key economy; interior prefixes are reached through
the induction, not through this statement. -/
def Faith (S : Finset op_t) : Prop :=
  ∀ o ∈ S, ∀ ρ : List op_t,
    listPermOf ρ ↑(S.erase o) →
    respects (ρ ++ [o]) (loOnA RGACondSig Cfg E) →
    Faithful o (applySeqR init_st ρ)

/-- **`DepComp` — the located order-level residual (dependency composition).**
A `loOnA`-predecessor of a `loOnA`-predecessor is a `loOnA`-predecessor, within `E`.

WHY IT IS FORCED (the exact stuck goal): the `Faith` step seats `GenDisc2`'s accuracy
at the dependency prefix `d` = `{z : lo z o}` and invokes **(Conv (S \ {o}))** on the
pair `(ρ, d ++ c)` — which requires `respects (d ++ c) loOnA`.  Its cross-append
component is `∀ a ∈ d, ∀ b ∈ c, ¬ lo b a`; with `lo a o` (membership in `d`) and
`¬ lo b o` (membership in `c`), refuting `lo b a` is EXACTLY this composition.  The
design's parenthetical "a loOnA-respecting reorder of ρ to deps-first — legitimate
because …" is precisely this fact; it does not follow from `GenDisc2`/`ReachInv`/
`BackClosed` (all are silent on edges among three distinct events), and `loOnA`
(`loOnC ∨ vis∧appliesDependsOn`, `rc ≡ Either`) is not transitive by construction.
It is an ORDER-shape fact about a real execution's dependency graph — per-event
generation data, NOT a per-prefix `Faithful`/`EligibleThread`-style residual, so the
factored attempts' circularity does not reappear. -/
def DepComp : Prop :=
  ∀ b a o : op_t, b ∈ E → a ∈ E → o ∈ E →
    loOnA RGACondSig Cfg E b a → loOnA RGACondSig Cfg E a o →
    loOnA RGACondSig Cfg E b o

/-! ## §3  The single point where the induction hypothesis is consumed

Every `Faithful`-at-an-interior-prefix obligation (swap operands in `Conv`, staled
`Del` steps in `Faith`'s concurrent tail) is discharged HERE: package the prefix
`pre` together with the pending event `x` as a dependency-closed set
`T = pre ∪ {x}`, note the excluded witness `w ∈ S \ T` makes `T` strictly smaller,
and invoke `(Faith T)` from the induction hypothesis with `x` LAST.  This is the
step the three factored attempts could not take. -/

theorem faithful_of_ih (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S)
    (pre : List op_t) (x w : op_t)
    (hpre_sub : ∀ z ∈ pre, z ∈ S) (hx : x ∈ S) (hw : w ∈ S) (hxw : x ≠ w)
    (hwpre : w ∉ pre) (hxpre : x ∉ pre) (hnd : pre.Nodup)
    (hresp : respects (pre ++ [x]) (loOnA RGACondSig Cfg E))
    (hclosed : ∀ y ∈ pre ++ [x], ∀ z ∈ E, z ≠ y →
       loOnA RGACondSig Cfg E z y → z ∈ pre) :
    Faithful x (applySeqR init_st pre) := by
  classical
  set T : Finset op_t := insert x pre.toFinset with hT
  have hmemT : ∀ z, z ∈ T ↔ (z = x ∨ z ∈ pre) := by
    intro z
    simp [hT, Finset.mem_insert, List.mem_toFinset]
  have hTsub : ∀ z ∈ T, z ∈ S := by
    intro z hz
    rcases (hmemT z).mp hz with rfl | h
    · exact hx
    · exact hpre_sub z h
  have hTS : T ⊆ S.erase w := by
    intro z hz
    rw [Finset.mem_erase]
    refine ⟨?_, hTsub z hz⟩
    rcases (hmemT z).mp hz with rfl | h
    · exact hxw
    · rintro rfl; exact hwpre h
  have hTcard : T.card ≤ n := by
    have h1 : T.card ≤ (S.erase w).card := Finset.card_le_card hTS
    have h2 : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw
    omega
  have hTdc : DC Cfg E T := by
    refine ⟨fun z hz => hdc.1 z (hTsub z hz), ?_⟩
    intro y hy z hz hzy hlo
    have hy' : y ∈ pre ++ [x] := by
      rcases (hmemT y).mp hy with rfl | h
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton_self y))
      · exact List.mem_append.mpr (Or.inl h)
    exact (hmemT z).mpr (Or.inr (hclosed y hy' z hz hzy hlo))
  have hxT : x ∈ T := by rw [hT]; exact Finset.mem_insert_self x _
  have hTe : T.erase x = pre.toFinset := by
    rw [hT]
    exact Finset.erase_insert (by rw [List.mem_toFinset]; exact hxpre)
  have hperm : listPermOf pre ↑(T.erase x) := by
    refine ⟨hnd, fun a => ?_⟩
    rw [hTe]
    simp
  exact (ih T hTcard hTdc).2 x hxT pre hperm hresp

/-! ## §4  The `Faith` step

`o` is quasi-maximal (it is LAST in its own enumeration), so `o` IS the design's
peeled maximal element `m` and only the design's `o = m` branch is needed: split
`ρ` into `d` (exactly `o`'s `loOnA`-predecessors — `IsDepPre`) and `c` (the rest),
reorder `ρ ≈ d ++ c` by **(Conv (S \ {o}))** — the step the factored attempts could
not take — seat `GenDisc2`'s accuracy at `applySeqR init_st d`, thread it across `c`
(`chainFaithful_depPre_concTail`; `Del` steps `Faithful` through the IH), project to
`Faithful o`, and transport across `eq`. -/

theorem faith_step (C : ConditionedConfiguration RGACondSig)
    (hE : C.BackClosed E) (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (hDep : DepComp Cfg E)
    (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S) :
    Faith Cfg E S := by
  classical
  intro o ho ρ hρp hresp
  obtain ⟨hρnd, hρmem⟩ := hρp
  have hρS : ∀ z ∈ ρ, z ∈ S.erase o := fun z hz => Finset.mem_coe.mp ((hρmem z).mp hz)
  have hρsubS : ∀ z ∈ ρ, z ∈ S := fun z hz => Finset.mem_of_mem_erase (hρS z hz)
  have hρneo : ∀ z ∈ ρ, z ≠ o := fun z hz => (Finset.mem_erase.mp (hρS z hz)).1
  have hρsubE : ∀ z ∈ ρ, z ∈ E := fun z hz => hdc.1 z (hρsubS z hz)
  have hoE : o ∈ E := hdc.1 o ho
  have honotρ : o ∉ ρ := fun h => (hρneo o h) rfl
  have hρresp : respects ρ (loOnA RGACondSig Cfg E) :=
    respects_sublist (List.sublist_append_left ρ [o]) hresp
  have homax : ∀ z ∈ ρ, ¬ loOnA RGACondSig Cfg E o z := fun z hz =>
    respects_cross hresp z hz o (List.mem_singleton_self o)
  -- the deps-first split of ρ
  set P : op_t → Bool := fun z => decide (loOnA RGACondSig Cfg E z o) with hP
  set d : List op_t := ρ.filter P with hd
  set c : List op_t := ρ.filter (fun z => !P z) with hc
  have hd_mem : ∀ z, z ∈ d ↔ (z ∈ ρ ∧ loOnA RGACondSig Cfg E z o) := by
    intro z
    simp only [hd, hP, List.mem_filter, decide_eq_true_iff]
  have hc_mem : ∀ z, z ∈ c ↔ (z ∈ ρ ∧ ¬ loOnA RGACondSig Cfg E z o) := by
    intro z
    simp only [hc, hP, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
  have hperm : (d ++ c).Perm ρ := List.filter_append_perm P ρ
  have hdc_nodup : (d ++ c).Nodup := hperm.nodup_iff.mpr hρnd
  have hdsub : d.Sublist ρ := by rw [hd]; exact List.filter_sublist
  have hcsub : c.Sublist ρ := by rw [hc]; exact List.filter_sublist
  have hdresp := respects_sublist hdsub hρresp
  have hcresp := respects_sublist hcsub hρresp
  -- the cross condition — THE consumption point of `DepComp`
  have hcross : ∀ a ∈ d, ∀ b ∈ c, ¬ loOnA RGACondSig Cfg E b a := by
    intro a ha b hb hba
    obtain ⟨haρ, halo⟩ := (hd_mem a).mp ha
    obtain ⟨hbρ, hbno⟩ := (hc_mem b).mp hb
    exact hbno (hDep b a o (hρsubE b hbρ) (hρsubE a haρ) hoE hba halo)
  have hdcresp := respects_append hdresp hcresp hcross
  have hdcsubE : ∀ z ∈ d ++ c, z ∈ E := fun z hz => hρsubE z (hperm.mem_iff.mp hz)
  have hdsubE : ∀ z ∈ d, z ∈ E := fun z hz => hρsubE z ((hd_mem z).mp hz).1
  have hdnd : d.Nodup := List.Nodup.sublist hdsub hρnd
  -- `d` is o's dependency prefix
  have hdep : IsDepPre Cfg E o d := by
    refine ⟨hdsubE, hdnd, hdresp, ?_, fun z hz => ((hd_mem z).mp hz).2⟩
    intro z hzE hzo hlo
    have hzS : z ∈ S := hdc.2 o ho z hzE hzo hlo
    have hzρ : z ∈ ρ := (hρmem z).mpr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzo, hzS⟩))
    exact (hd_mem z).mpr ⟨hzρ, hlo⟩
  obtain ⟨hND, haccf⟩ := hGen o hoE
  have hacc := haccf d hdep
  obtain ⟨h0d, hwfd, hmonod⟩ := hInv d hdsubE hdnd hdresp
  -- (Conv (S \ {o})) supplies the reorder ρ ≈ d ++ c
  have hSodc : DC Cfg E (S.erase o) := by
    refine ⟨fun z hz => hdc.1 z (Finset.mem_of_mem_erase hz), ?_⟩
    intro w hw z hz hzw hlo
    have hzS : z ∈ S := hdc.2 w (Finset.mem_of_mem_erase hw) z hz hzw hlo
    refine Finset.mem_erase.mpr ⟨?_, hzS⟩
    rintro rfl
    exact homax w ((hρmem w).mpr (Finset.mem_coe.mpr hw)) hlo
  have hSocard : (S.erase o).card ≤ n := by
    rw [Finset.card_erase_of_mem ho]; omega
  have heq : eq (applySeqR init_st ρ) (applySeqR init_st (d ++ c)) :=
    (ih (S.erase o) hSocard hSodc).1 ρ (d ++ c) ⟨hρnd, hρmem⟩
      ⟨hdc_nodup, fun a => (hperm.mem_iff).trans (hρmem a)⟩ hρresp hdcresp
  -- the concurrent tail is a GoodFold for recList o (Del steps via the IH)
  have hgf : GoodFold (recList o) (applySeqR init_st d) c := by
    apply goodFold_of_stepwise (recList o) c (applySeqR init_st d)
    intro pfx x rest hsplit
    rw [← applySeqR_append]
    have hxc : x ∈ c := by
      rw [hsplit]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    have hxρ : x ∈ ρ := ((hc_mem x).mp hxc).1
    have hxE : x ∈ E := hρsubE x hxρ
    have hxnd : x ∉ d := fun hin =>
      (List.nodup_append.mp hdc_nodup).2.2 x hin x hxc rfl
    have hss : (d ++ pfx).Sublist (d ++ c) := by
      rw [hsplit]
      exact List.Sublist.append_left (List.sublist_append_left pfx (x :: rest)) d
    have hdpsubρ : ∀ z ∈ d ++ pfx, z ∈ ρ := fun z hz => hperm.mem_iff.mp (hss.subset hz)
    have hdpsubE : ∀ z ∈ d ++ pfx, z ∈ E := fun z hz => hρsubE z (hdpsubρ z hz)
    have hdpnd : (d ++ pfx).Nodup := List.Nodup.sublist hss hdc_nodup
    have hdpresp := respects_sublist hss hdcresp
    obtain ⟨t, rr, op⟩ := x
    cases op with
    | Ins e p an =>
      -- concurrent fresh Ins: its id names nothing on o's recorded list
      have ht0 : t ≠ 0 := hids0 _ hxE
      have hfr : fresh_ts (t, rr, .Ins e p an) (applySeqR init_st d) :=
        fresh_ts_config C E hE hids0 d hdsubE _ hxE hxnd
      have hnotm : t ∉ recList o := freshId_not_mem_recList o _ t hacc ht0 hfr.2
      exact goodStep_ins_concurrent _ (recList o) t rr e an p ht0 hnotm
    | Del p xx =>
      -- staled Del: Faithful at its own sub-fold, through the IH (Faith T)
      obtain ⟨h0dp, hwfdp, _⟩ := hInv (d ++ pfx) hdpsubE hdpnd hdpresp
      show contains (applySeqR init_st (d ++ pfx)) 0 = false
        ∧ wf (applySeqR init_st (d ++ pfx))
        ∧ Faithful (t, rr, .Del p xx) (applySeqR init_st (d ++ pfx))
      refine ⟨h0dp, hwfdp, ?_⟩
      have hxS : (t, rr, .Del p xx) ∈ S := hρsubS _ hxρ
      have hxo : (t, rr, .Del p xx) ≠ o := hρneo _ hxρ
      have hondp : o ∉ d ++ pfx := fun h => honotρ (hdpsubρ _ h)
      have hxndp : (t, rr, .Del p xx) ∉ d ++ pfx := by
        intro h
        rcases List.mem_append.mp h with h1 | h2
        · exact hxnd h1
        · have hcnd : c.Nodup := (List.nodup_append.mp hdc_nodup).2.1
          rw [hsplit] at hcnd
          exact (List.nodup_append.mp hcnd).2.2 _ h2 _ List.mem_cons_self rfl
      have hrespx : respects ((d ++ pfx) ++ [(t, rr, .Del p xx)])
          (loOnA RGACondSig Cfg E) := by
        refine respects_concat hdpresp ?_
        intro g hg
        rcases List.mem_append.mp hg with hgd | hgp
        · exact hcross g hgd _ hxc
        · have hcresp' : respects (pfx ++ (t, rr, .Del p xx) :: rest)
              (loOnA RGACondSig Cfg E) := by rw [← hsplit]; exact hcresp
          exact respects_cross hcresp' g hgp _ List.mem_cons_self
      have hclosedx : ∀ y ∈ (d ++ pfx) ++ [(t, rr, .Del p xx)], ∀ z ∈ E, z ≠ y →
          loOnA RGACondSig Cfg E z y → z ∈ d ++ pfx := by
        intro y hy z hzE hzy hlo
        have hyρ : y ∈ ρ := by
          rcases List.mem_append.mp hy with h1 | h2
          · exact hdpsubρ y h1
          · rw [List.mem_singleton] at h2; subst h2; exact hxρ
        have hzS : z ∈ S := hdc.2 y (hρsubS y hyρ) z hzE hzy hlo
        have hzo : z ≠ o := by rintro rfl; exact homax y hyρ hlo
        have hzdc : z ∈ d ++ c := hperm.mem_iff.mpr
          ((hρmem z).mpr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzo, hzS⟩)))
        rcases List.mem_append.mp hzdc with hzd | hzc
        · exact List.mem_append.mpr (Or.inl hzd)
        · -- z ∈ c : locate it strictly left of y
          rcases List.mem_append.mp hy with h1 | h2
          · rcases List.mem_append.mp h1 with hyd | hyp
            · exact absurd hlo (hcross y hyd z hzc)
            · obtain ⟨u, v, huv⟩ := List.append_of_mem hyp
              have hre : d ++ c
                  = (d ++ u) ++ y :: (v ++ (t, rr, .Del p xx) :: rest) := by
                rw [hsplit, huv]; simp [List.append_assoc]
              have hz' := hre ▸ hzdc
              have hresp' : respects ((d ++ u) ++ y :: (v ++ (t, rr, .Del p xx) :: rest))
                  (loOnA RGACondSig Cfg E) := hre ▸ hdcresp
              rcases List.mem_append.mp (pred_mem_left hresp' hz' hlo hzy) with h | h
              · exact List.mem_append.mpr (Or.inl h)
              · exact List.mem_append.mpr (Or.inr (by
                  rw [huv]; exact List.mem_append.mpr (Or.inl h)))
          · rw [List.mem_singleton] at h2; subst h2
            have hre : d ++ c = (d ++ pfx) ++ (t, rr, .Del p xx) :: rest := by
              rw [hsplit]; simp [List.append_assoc]
            have hz' := hre ▸ hzdc
            have hresp' : respects ((d ++ pfx) ++ (t, rr, .Del p xx) :: rest)
                (loOnA RGACondSig Cfg E) := hre ▸ hdcresp
            exact pred_mem_left hresp' hz' hlo hzy
      exact faithful_of_ih Cfg E n ih S hcard hdc (d ++ pfx) (t, rr, .Del p xx) o
        (fun z hz => hρsubS z (hdpsubρ z hz)) hxS ho hxo hondp hxndp hdpnd
        hrespx hclosedx
  -- seat the accuracy base at d, thread across c, project, transport
  have hcf : ChainFaithful (applySeqR init_st (d ++ c)) (recList o) :=
    chainFaithful_depPre_concTail o d c hmonod h0d hacc hgf
  obtain ⟨h0dc, _, _⟩ := hInv (d ++ c) hdcsubE hdc_nodup hdcresp
  have hfo : Faithful o (applySeqR init_st (d ++ c)) := by
    obtain ⟨t, rr, op⟩ := o
    cases op with
    | Ins e p an =>
      exact climbFaithful_of_chain _ (an :: p) h0dc hcf
    | Del p xx =>
      have hxx0 : xx ≠ 0 := hND
      have hpath : IsAncPath (applySeqR init_st d) xx p := by
        simp only [accurate, opLeaf, opPath] at hacc
        rcases hacc with ⟨hl0, _⟩ | ⟨_, hp⟩
        · exact absurd hl0 hxx0
        · exact hp
      have hxxp : xx ∉ p := isAncPath_not_mem _ h0d xx p hpath
      exact faithful_del_of_chain _ t rr xx p h0dc hxx0 hxxp hcf
  exact faithful_eq_congr o _ _ (eq_symm _ _ heq) hfo

/-! ## §5  The `Conv` step

Peel the LAST element `m` of `π₁` (quasi-maximal by `respects`), bubble `m` from its
position in `π₂` to the very end by adjacent faithful swaps (`eqSwap_of_bothFaithful`,
whose two `Faithful` obligations come from the IH `Faith` at the strictly smaller
prefix-sets — each excludes the swap partner), converge the `m`-less enumerations by
**(Conv (S \ {m}))**, and re-apply `m` through `do_`'s `eq`-congruence. -/

theorem conv_step (C : ConditionedConfiguration RGACondSig)
    (hE : C.BackClosed E) (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (_hDep : DepComp Cfg E)
    (n : ℕ)
    (ih : ∀ T : Finset op_t, T.card ≤ n → DC Cfg E T → Conv Cfg E T ∧ Faith Cfg E T)
    (S : Finset op_t) (hcard : S.card ≤ n + 1) (hdc : DC Cfg E S) :
    Conv Cfg E S := by
  classical
  intro π₁ π₂ h₁p h₂p h₁r h₂r
  rcases List.eq_nil_or_concat π₁ with rfl | ⟨ρ₁, m, hcat⟩
  · -- π₁ = [] : S is empty, so π₂ = [] too
    obtain ⟨_, hm₁⟩ := h₁p
    obtain ⟨_, hm₂⟩ := h₂p
    have hπ₂ : π₂ = [] := by
      cases hπ : π₂ with
      | nil => rfl
      | cons a l =>
        exact absurd ((hm₁ a).mpr ((hm₂ a).mp (by rw [hπ]; exact List.mem_cons_self)))
          List.not_mem_nil
    rw [hπ₂]
    exact Sal.Metatheory.RGAConditionedConvergence.eq_refl _
  · rw [List.concat_eq_append] at hcat
    subst hcat
    obtain ⟨h₁nd, h₁mem⟩ := h₁p
    obtain ⟨h₂nd, h₂mem⟩ := h₂p
    have hmS : m ∈ S := Finset.mem_coe.mp ((h₁mem m).mp
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self m))))
    have hmE : m ∈ E := hdc.1 m hmS
    have hmρ₁ : m ∉ ρ₁ := fun h =>
      (List.nodup_append.mp h₁nd).2.2 m h m (List.mem_singleton_self m) rfl
    -- quasi-maximality of m in S (m is last in the respects-enumeration π₁)
    have hmax : ∀ z ∈ S, z ≠ m → ¬ loOnA RGACondSig Cfg E m z := by
      intro z hz hzm
      have hzρ : z ∈ ρ₁ := by
        rcases List.mem_append.mp ((h₁mem z).mpr (Finset.mem_coe.mpr hz)) with h | h
        · exact h
        · rw [List.mem_singleton] at h; exact absurd h hzm
      exact respects_cross h₁r z hzρ m (List.mem_singleton_self m)
    have h₁resp : respects ρ₁ (loOnA RGACondSig Cfg E) :=
      respects_sublist (List.sublist_append_left ρ₁ [m]) h₁r
    have hρ₁perm : listPermOf ρ₁ ↑(S.erase m) := by
      refine ⟨(List.nodup_append.mp h₁nd).1, fun a => ?_⟩
      constructor
      · intro ha
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, Finset.mem_coe.mp
          ((h₁mem a).mp (List.mem_append.mpr (Or.inl ha)))⟩)
        rintro rfl; exact hmρ₁ ha
      · intro ha
        have haS := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
        rcases List.mem_append.mp ((h₁mem a).mpr (Finset.mem_coe.mpr haS.2)) with h | h
        · exact h
        · rw [List.mem_singleton] at h; exact absurd h haS.1
    -- split π₂ at m
    obtain ⟨σ, τ, hπ₂⟩ := List.append_of_mem ((h₂mem m).mpr (Finset.mem_coe.mpr hmS))
    subst hπ₂
    have h₂nd' := List.nodup_append.mp h₂nd
    have hmσ : m ∉ σ := fun h => h₂nd'.2.2 m h m List.mem_cons_self rfl
    have hmτ : m ∉ τ := (List.nodup_cons.mp h₂nd'.2.1).1
    have hστnd : (σ ++ τ).Nodup := by
      rw [List.nodup_append]
      exact ⟨h₂nd'.1, (List.nodup_cons.mp h₂nd'.2.1).2,
        fun a ha b hb => h₂nd'.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
    have hστperm : listPermOf (σ ++ τ) ↑(S.erase m) := by
      refine ⟨hστnd, fun a => ?_⟩
      constructor
      · intro ha
        have haπ₂ : a ∈ σ ++ m :: τ := by
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
        have hane : a ≠ m := by
          rintro rfl
          rcases List.mem_append.mp ha with h | h
          · exact hmσ h
          · exact hmτ h
        exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
          ⟨hane, Finset.mem_coe.mp ((h₂mem a).mp haπ₂)⟩)
      · intro ha
        have haS := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
        rcases List.mem_append.mp ((h₂mem a).mpr (Finset.mem_coe.mpr haS.2)) with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' haS.1
          · exact List.mem_append.mpr (Or.inr h')
    have hστresp : respects (σ ++ τ) (loOnA RGACondSig Cfg E) :=
      respects_sublist (List.Sublist.append_left (List.sublist_cons_self m τ) σ) h₂r
    -- bubble m to the very end of π₂, up to eq
    have hbubble : eq (applySeqR (applySeqR init_st σ) (τ ++ [m]))
        (applySeqR (applySeqR init_st σ) (m :: τ)) := by
      have hsw : ∀ α β y, τ = α ++ y :: β →
          EqSwap y m (applySeqR (applySeqR init_st σ) α) := by
        intro α β y hτ
        subst hτ
        rw [← applySeqR_append]
        have hyτ : y ∈ α ++ y :: β := List.mem_append.mpr (Or.inr List.mem_cons_self)
        have hyπ₂ : y ∈ σ ++ m :: (α ++ y :: β) :=
          List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hyτ))
        have hyS : y ∈ S := Finset.mem_coe.mp ((h₂mem y).mp hyπ₂)
        have hyE : y ∈ E := hdc.1 y hyS
        have hym : y ≠ m := by rintro rfl; exact hmτ hyτ
        have hpre_subS : ∀ z ∈ σ ++ α, z ∈ S := by
          intro z hz
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) := by
            rcases List.mem_append.mp hz with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inl h))))
          exact Finset.mem_coe.mp ((h₂mem z).mp hzπ₂)
        have hpre_subE : ∀ z ∈ σ ++ α, z ∈ E := fun z hz => hdc.1 z (hpre_subS z hz)
        have hpre_ss : (σ ++ α).Sublist (σ ++ m :: (α ++ y :: β)) :=
          List.Sublist.append_left
            (List.Sublist.cons m (List.sublist_append_left α (y :: β))) σ
        have hpre_nd : (σ ++ α).Nodup := List.Nodup.sublist hpre_ss h₂nd
        have hpre_resp := respects_sublist hpre_ss h₂r
        obtain ⟨h0, hwf, hmono⟩ := hInv (σ ++ α) hpre_subE hpre_nd hpre_resp
        have hynpre : y ∉ σ ++ α := by
          intro h
          rcases List.mem_append.mp h with h1 | h2
          · exact h₂nd'.2.2 y h1 y (List.mem_cons_of_mem _ hyτ) rfl
          · have hτnd : (α ++ y :: β).Nodup := (List.nodup_cons.mp h₂nd'.2.1).2
            exact (List.nodup_append.mp hτnd).2.2 y h2 y List.mem_cons_self rfl
        have hmnpre : m ∉ σ ++ α := by
          intro h
          rcases List.mem_append.mp h with h1 | h2
          · exact hmσ h1
          · exact hmτ (List.mem_append.mpr (Or.inl h2))
        -- dependency closure of the visited prefix σ ++ α (positional, from respects π₂)
        have hcl : ∀ g ∈ σ ++ α, ∀ z ∈ E, z ≠ g →
            loOnA RGACondSig Cfg E z g → z ∈ σ ++ α := by
          intro g hg z hzE hzg hlo
          have hgS : g ∈ S := hpre_subS g hg
          have hzS : z ∈ S := hdc.2 g hgS z hzE hzg hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          rcases List.mem_append.mp hg with hgσ | hgα
          · obtain ⟨u, v, huv⟩ := List.append_of_mem hgσ
            have hre : σ ++ m :: (α ++ y :: β)
                = u ++ g :: (v ++ m :: (α ++ y :: β)) := by
              rw [huv]; simp [List.append_assoc]
            have hzu := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzg
            exact List.mem_append.mpr (Or.inl (by
              rw [huv]; exact List.mem_append.mpr (Or.inl hzu)))
          · obtain ⟨u, v, huv⟩ := List.append_of_mem hgα
            have hgm : g ≠ m := by
              rintro rfl; exact hmτ (List.mem_append.mpr (Or.inl hgα))
            have hre : σ ++ m :: (α ++ y :: β)
                = (σ ++ m :: u) ++ g :: (v ++ y :: β) := by
              rw [huv]; simp [List.append_assoc]
            have hzσmu := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzg
            rcases List.mem_append.mp hzσmu with h | h
            · exact List.mem_append.mpr (Or.inl h)
            · rcases List.mem_cons.mp h with rfl | h'
              · exact absurd hlo (hmax g hgS hgm)
              · exact List.mem_append.mpr (Or.inr (by
                  rw [huv]; exact List.mem_append.mpr (Or.inl h')))
        -- predecessors of y land in σ ++ α
        have hcly : ∀ z ∈ E, z ≠ y → loOnA RGACondSig Cfg E z y → z ∈ σ ++ α := by
          intro z hzE hzy hlo
          have hzS : z ∈ S := hdc.2 y hyS z hzE hzy hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          have hre : σ ++ m :: (α ++ y :: β) = (σ ++ m :: α) ++ y :: β := by
            simp [List.append_assoc]
          have hzσmα := pred_mem_left (hre ▸ h₂r) (hre ▸ hzπ₂) hlo hzy
          rcases List.mem_append.mp hzσmα with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · rcases List.mem_cons.mp h with rfl | h'
            · exact absurd hlo (hmax y hyS hym)
            · exact List.mem_append.mpr (Or.inr h')
        -- predecessors of m land in σ
        have hclm : ∀ z ∈ E, z ≠ m → loOnA RGACondSig Cfg E z m → z ∈ σ ++ α := by
          intro z hzE hzm hlo
          have hzS : z ∈ S := hdc.2 m hmS z hzE hzm hlo
          have hzπ₂ : z ∈ σ ++ m :: (α ++ y :: β) :=
            (h₂mem z).mpr (Finset.mem_coe.mpr hzS)
          exact List.mem_append.mpr (Or.inl (pred_mem_left h₂r hzπ₂ hlo hzm))
        -- Faithful y / Faithful m at the prefix fold — through the IH (Faith T),
        -- each packaged set excluding the OTHER swap operand (strictly smaller)
        have hFy : Faithful y (applySeqR init_st (σ ++ α)) := by
          refine faithful_of_ih Cfg E n ih S hcard hdc (σ ++ α) y m hpre_subS hyS hmS
            hym hmnpre hynpre hpre_nd ?_ ?_
          · refine respects_concat hpre_resp ?_
            intro g hg
            rcases List.mem_append.mp hg with h1 | h2
            · exact respects_cross h₂r g h1 y (List.mem_cons_of_mem _ hyτ)
            · have hτss : (α ++ y :: β).Sublist (σ ++ m :: (α ++ y :: β)) :=
                List.Sublist.trans (List.sublist_cons_self m _)
                  (List.sublist_append_right σ _)
              exact respects_cross (respects_sublist hτss h₂r) g h2 y List.mem_cons_self
          · intro g hg z hzE hzg hlo
            rcases List.mem_append.mp hg with h1 | h2
            · exact hcl g h1 z hzE hzg hlo
            · rw [List.mem_singleton] at h2; subst h2
              exact hcly z hzE hzg hlo
        have hFm : Faithful m (applySeqR init_st (σ ++ α)) := by
          refine faithful_of_ih Cfg E n ih S hcard hdc (σ ++ α) m y hpre_subS hmS hyS
            (Ne.symm hym) hynpre hmnpre hpre_nd ?_ ?_
          · refine respects_concat hpre_resp ?_
            intro g hg
            exact hmax g (hpre_subS g hg) (fun e => hmnpre (e ▸ hg))
          · intro g hg z hzE hzg hlo
            rcases List.mem_append.mp hg with h1 | h2
            · exact hcl g h1 z hzE hzg hlo
            · rw [List.mem_singleton] at h2; subst h2
              exact hclm z hzE hzg hlo
        -- freshness and distinct ids from the configuration
        have hfy : fresh_ts y (applySeqR init_st (σ ++ α)) :=
          fresh_ts_config C E hE hids0 (σ ++ α) hpre_subE y hyE hynpre
        have hfm : fresh_ts m (applySeqR init_st (σ ++ α)) :=
          fresh_ts_config C E hE hids0 (σ ++ α) hpre_subE m hmE hmnpre
        have hdist : y.1 ≠ m.1 := C.distinctTs E hE hyE hmE hym
        -- NoFreshClash both ways: accuracy at each operand's dependency prefix
        -- (GenDisc2) + the other's freshness there (live/dead separation)
        set dy : List op_t := (σ ++ α).filter
          (fun z => decide (loOnA RGACondSig Cfg E z y)) with hdy
        have hdy_mem : ∀ z, z ∈ dy ↔ (z ∈ σ ++ α ∧ loOnA RGACondSig Cfg E z y) := by
          intro z; simp only [hdy, List.mem_filter, decide_eq_true_iff]
        have hdysub : dy.Sublist (σ ++ α) := by rw [hdy]; exact List.filter_sublist
        have hdysubE : ∀ z ∈ dy, z ∈ E := fun z hz => hpre_subE z (hdysub.subset hz)
        have hdepy : IsDepPre Cfg E y dy := by
          refine ⟨hdysubE, List.Nodup.sublist hdysub hpre_nd,
            respects_sublist hdysub hpre_resp, ?_, fun z hz => ((hdy_mem z).mp hz).2⟩
          intro z hzE hzy hlo
          exact (hdy_mem z).mpr ⟨hcly z hzE hzy hlo, hlo⟩
        have haccy := (hGen y hyE).2 dy hdepy
        have hfrm : fresh_ts m (applySeqR init_st dy) :=
          fresh_ts_config C E hE hids0 dy hdysubE m hmE
            (fun h => hmnpre (hdysub.subset h))
        have hclash_ym : NoFreshClash y m :=
          noFreshClash_of_accurate_fresh y m _ haccy hfrm (hGen m hmE).1
        set dm : List op_t := (σ ++ α).filter
          (fun z => decide (loOnA RGACondSig Cfg E z m)) with hdm
        have hdm_mem : ∀ z, z ∈ dm ↔ (z ∈ σ ++ α ∧ loOnA RGACondSig Cfg E z m) := by
          intro z; simp only [hdm, List.mem_filter, decide_eq_true_iff]
        have hdmsub : dm.Sublist (σ ++ α) := by rw [hdm]; exact List.filter_sublist
        have hdmsubE : ∀ z ∈ dm, z ∈ E := fun z hz => hpre_subE z (hdmsub.subset hz)
        have hdepm : IsDepPre Cfg E m dm := by
          refine ⟨hdmsubE, List.Nodup.sublist hdmsub hpre_nd,
            respects_sublist hdmsub hpre_resp, ?_, fun z hz => ((hdm_mem z).mp hz).2⟩
          intro z hzE hzm hlo
          exact (hdm_mem z).mpr ⟨hclm z hzE hzm hlo, hlo⟩
        have haccm := (hGen m hmE).2 dm hdepm
        have hfry : fresh_ts y (applySeqR init_st dm) :=
          fresh_ts_config C E hE hids0 dm hdmsubE y hyE
            (fun h => hynpre (hdmsub.subset h))
        have hclash_my : NoFreshClash m y :=
          noFreshClash_of_accurate_fresh m y _ haccm hfry (hGen y hyE).1
        -- the faithful swap (NEITHER operand accurate)
        exact eqSwap_of_bothFaithful _ y m hdist h0 hwf hmono hfy hfm hFy hFm
          hclash_ym hclash_my
      have hb := bubble_eq m τ [] (applySeqR init_st σ) hsw
      rw [List.append_nil] at hb
      exact hb
    -- converge the m-less enumerations by (Conv (S \ {m})), and finish
    have hSmdc : DC Cfg E (S.erase m) := by
      refine ⟨fun z hz => hdc.1 z (Finset.mem_of_mem_erase hz), ?_⟩
      intro w hw z hz hzw hlo
      have hzS : z ∈ S := hdc.2 w (Finset.mem_of_mem_erase hw) z hz hzw hlo
      refine Finset.mem_erase.mpr ⟨?_, hzS⟩
      rintro rfl
      exact hmax w (Finset.mem_of_mem_erase hw) (Finset.mem_erase.mp hw).1 hlo
    have hSmcard : (S.erase m).card ≤ n := by
      rw [Finset.card_erase_of_mem hmS]; omega
    have hrec : eq (applySeqR init_st ρ₁) (applySeqR init_st (σ ++ τ)) :=
      (ih (S.erase m) hSmcard hSmdc).1 ρ₁ (σ ++ τ) hρ₁perm hστperm h₁resp hστresp
    have hstep : eq (do_ (applySeqR init_st ρ₁) m) (do_ (applySeqR init_st (σ ++ τ)) m) :=
      do_eq_congr _ _ hrec m
    have e₁ : applySeqR init_st (ρ₁ ++ [m]) = do_ (applySeqR init_st ρ₁) m := by
      rw [applySeqR_append]; rfl
    have e₂ : applySeqR init_st ((σ ++ τ) ++ [m]) = do_ (applySeqR init_st (σ ++ τ)) m := by
      rw [applySeqR_append]; rfl
    have e₃ : applySeqR init_st ((σ ++ τ) ++ [m])
        = applySeqR (applySeqR init_st σ) (τ ++ [m]) := by
      rw [List.append_assoc, applySeqR_append]
    have e₄ : applySeqR init_st (σ ++ m :: τ) = applySeqR (applySeqR init_st σ) (m :: τ) :=
      applySeqR_append init_st σ (m :: τ)
    rw [e₁, e₄]
    refine Sal.Metatheory.RGAConditionedConvergence.eq_trans _ _ _ hstep ?_
    rw [← e₂, e₃]
    exact hbubble

/-! ## §6  `P(S)` by induction on `|S|`, and the headline exports -/

/-- **The simultaneous induction.**  `P(S) = (Conv S) ∧ (Faith S)` for every
dependency-closed `S`, by induction on `|S|`.  Each conjunct at `S` consumes BOTH
conjuncts at strictly smaller dependency-closed sets — `Faith` uses `Conv (S\{o})`
for the deps-first reorder and `Faith T` for the tail's staled `Del`s; `Conv` uses
`Faith T` for both swap operands and `Conv (S\{m})` after the peel.  No conjunct is
ever consumed at the SAME cardinality, so the mutual dependence that defeated the
factored attempts is resolved by the measure. -/
theorem P_all (C : ConditionedConfiguration RGACondSig)
    (hE : C.BackClosed E) (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (hDep : DepComp Cfg E) :
    ∀ n : ℕ, ∀ S : Finset op_t, S.card ≤ n → DC Cfg E S →
      Conv Cfg E S ∧ Faith Cfg E S := by
  intro n
  induction n with
  | zero =>
    intro S hcard _
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hS
    constructor
    · intro π₁ π₂ h₁p h₂p _ _
      have h₁ : π₁ = [] := by
        cases hπ : π₁ with
        | nil => rfl
        | cons a l =>
          exfalso
          have := (h₁p.2 a).mp (by rw [hπ]; exact List.mem_cons_self)
          simp at this
      have h₂ : π₂ = [] := by
        cases hπ : π₂ with
        | nil => rfl
        | cons a l =>
          exfalso
          have := (h₂p.2 a).mp (by rw [hπ]; exact List.mem_cons_self)
          simp at this
      rw [h₁, h₂]
      exact Sal.Metatheory.RGAConditionedConvergence.eq_refl _
    · intro o ho
      exact absurd ho (Finset.notMem_empty o)
  | succ n ihn =>
    intro S hcard hdc
    exact ⟨conv_step Cfg E C hE hids0 hGen hInv hDep n ihn S hcard hdc,
           faith_step Cfg E C hE hids0 hGen hInv hDep n ihn S hcard hdc⟩

/-- **The update-layer capstone via the simultaneous induction.**  Two
`loOnA`-respecting enumerations of a backward-closed `E` fold from `init_st` to
observationally-`eq` states.  Premises: the configuration facts (`BackClosed`,
nonzero ids), `GenDisc2` (per-event dependency-prefix accuracy — the satisfiable
generation discipline), `ReachInv` (fold invariants), and `DepComp` (dependency
composition, the order-level residual).  NO `EligibleThread`, NO `hReach`, NO
per-prefix `Faithful` hypothesis — everything per-prefix is DERIVED inside the
induction. -/
theorem RGA_update_convergence_simul
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (hDep : DepComp Cfg E)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E)) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  classical
  set S : Finset op_t := π₁.toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ a ∈ E := by
    intro a
    rw [hS, List.mem_toFinset]
    exact h₁p.2 a
  have hdc : DC Cfg E S :=
    ⟨fun x hx => (hmemS x).mp hx, fun w _ z hz _ _ => (hmemS z).mpr hz⟩
  have hP := P_all Cfg E C hE hids0 hGen hInv hDep S.card S le_rfl hdc
  refine hP.1 π₁ π₂ ⟨h₁p.1, fun a => ?_⟩ ⟨h₂p.1, fun a => ?_⟩ h₁r h₂r
  · exact (h₁p.2 a).trans ⟨fun h => Finset.mem_coe.mpr ((hmemS a).mpr h),
      fun h => (hmemS a).mp (Finset.mem_coe.mp h)⟩
  · exact (h₂p.2 a).trans ⟨fun h => Finset.mem_coe.mpr ((hmemS a).mpr h),
      fun h => (hmemS a).mp (Finset.mem_coe.mp h)⟩

/-- **The `Faith` conjunct exported at `E`.**  For `o ∈ E` and any
`loOnA`-respecting enumeration of `E` with `o` last, `o` is `Faithful` at the fold
of the rest — same premises, no per-prefix residual. -/
theorem RGA_faithful_simul
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (hDep : DepComp Cfg E)
    (o : op_t) (ρ : List op_t)
    (hp : listPermOf (ρ ++ [o]) E)
    (hr : respects (ρ ++ [o]) (loOnA RGACondSig Cfg E)) :
    Faithful o (applySeqR init_st ρ) := by
  classical
  set S : Finset op_t := (ρ ++ [o]).toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ a ∈ E := by
    intro a
    rw [hS, List.mem_toFinset]
    exact hp.2 a
  have hdc : DC Cfg E S :=
    ⟨fun x hx => (hmemS x).mp hx, fun w _ z hz _ _ => (hmemS z).mpr hz⟩
  have hoS : o ∈ S := by
    rw [hS, List.mem_toFinset]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton_self o))
  have honρ : o ∉ ρ := fun h =>
    (List.nodup_append.mp hp.1).2.2 o h o (List.mem_singleton_self o) rfl
  have hP := P_all Cfg E C hE hids0 hGen hInv hDep S.card S le_rfl hdc
  refine hP.2 o hoS ρ ⟨(List.nodup_append.mp hp.1).1, fun a => ?_⟩ hr
  constructor
  · intro ha
    refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, ?_⟩)
    · rintro rfl; exact honρ ha
    · rw [hS, List.mem_toFinset]; exact List.mem_append.mpr (Or.inl ha)
  · intro ha
    have h' := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
    have h'' : a ∈ ρ ++ [o] := by
      have := h'.2; rw [hS, List.mem_toFinset] at this; exact this
    rcases List.mem_append.mp h'' with h | h
    · exact h
    · rw [List.mem_singleton] at h; exact absurd h h'.1

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — the simultaneous induction CLOSES (0 sorry, kernel axioms only).

   WHAT CLOSED, per the design (`SIMULTANEOUS_INDUCTION_DESIGN.md`), all step
   cases by EXISTING lemmas:
   • `P(S) = (Conv S) ∧ (Faith S)` by induction on `|S|` over dependency-closed
     `S ⊆ E`, ambient order `loOnA … E` FIXED (no re-parameterization on peel).
   • (Faith S): `o` last ⇒ `o` quasi-maximal ⇒ the design's `o = m` branch covers
     ALL of Faith (the `o ≠ m` branch is subsumed).  `d`/`c` split by filter;
     `IsDepPre` for `d`; `accurate` seated by `GenDisc2`; `ρ ≈ d ++ c` by
     **(Conv (S\{o}))** — the reorder the factored attempts lacked; tail threaded
     by `chainFaithful_depPre_concTail` (fresh `Ins` arm: `freshId_not_mem_recList`
     from `accurate`+`fresh_ts_config`; `Del` arm: `Faithful` at its sub-fold from
     the IH `Faith T`, `T = (d ++ pfx) ∪ {x} ⊊ S` since `o ∉ T`); projected by
     `climbFaithful_of_chain` (Ins) / `faithful_del_of_chain` (§1, NEW glue: the
     `Del` projection of `ChainFaithful`, live and staled target both);
     transported by `faithful_eq_congr` (§1, NEW glue: `eq`-congruence).
   • (Conv S): peel the LAST element `m` of `π₁` (quasi-maximal by `respects`);
     bubble `m` to the end of `π₂` (`bubble_eq`), each adjacent swap by
     `eqSwap_of_bothFaithful` with BOTH `Faithful` obligations from the IH
     `Faith T` (`T = (σ ++ α) ∪ {y or m}`, each excludes the OTHER operand, so
     `|T| < |S|`), `fresh_ts`/distinct-ids from the configuration, `NoFreshClash`
     from `noFreshClash_of_accurate_fresh` at each operand's `IsDepPre` prefix
     (a filter of the visited prefix); then **(Conv (S\{m}))** + `do_eq_congr`.
   • NO conjunct is consumed at the same cardinality: the design's internal
     Faith-then-Conv ordering is not even needed — the mutual dependence is fully
     resolved by the cardinality measure.  This is the circularity-breaking
     content of the ONE simultaneous induction.

   THE HONEST ACCOUNTING — `DepComp` (§2), the one premise beyond
   `GenDisc2 + ReachInv` + configuration + enumeration hypotheses:

       exact goal that forces it (Faith step, the (Conv (S\{o})) application):
         ⊢ respects (d ++ c) (loOnA RGACondSig Cfg E)
       whose cross-append component is
         ⊢ ∀ a ∈ d, ∀ b ∈ c, ¬ loOnA RGACondSig Cfg E b a
       with `loOnA a o` (a ∈ d) and `¬ loOnA b o` (b ∈ c) in scope — refuting
       `loOnA b a` IS `loOnA b a → loOnA a o → loOnA b o`.

   The design asserts this reorder is "legitimate" from `m`-maximality, but
   maximality only bounds edges INTO `m`; the cross pairs are edges among `E'`.
   `loOnA` (`= loOnC ∨ vis ∧ appliesDependsOn`, `rc ≡ Either` for the RGA, hence
   `loOnA ⊆ vis`) is NOT transitive by construction: `vis b a ∧ ¬commutesOn b a`,
   `vis a o ∧ appliesDependsOn o a` give `vis b o` (if `vis` composes) but neither
   `¬commutesOn b o` nor `appliesDependsOn o b`.  `GenDisc2`/`ReachInv`/
   `BackClosed` are silent on three-event edge composition, so `DepComp` is
   genuinely additional.  It is ORDER-SHAPE data about a real execution's
   dependency graph (deps-of-deps are deps) — the same per-event generation level
   as `GenDisc2`, NOT a per-prefix `Faithful`/`EligibleThread` residual, so the
   located gap no longer contains convergence.  Discharging it for the concrete
   RGA semantics (path-ancestor chains are rootward-closed, so applicability-
   relevance composes) is a self-contained order-layer lemma, independent of this
   induction.

   RESIDUALS UNCHANGED from the design: merge-side `hBN`, the generic ≈-quotient
   (M5), satisfiability instantiation of `GenDisc2`/`ReachInv`/`DepComp` from the
   execution model.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §7  Axiom audit -/

#print axioms faithful_del_of_chain
#print axioms faithful_eq_congr
#print axioms faithful_of_ih
#print axioms faith_step
#print axioms conv_step
#print axioms P_all
#print axioms RGA_update_convergence_simul
#print axioms RGA_faithful_simul

end Sal.Metatheory.RGASimulInduction
