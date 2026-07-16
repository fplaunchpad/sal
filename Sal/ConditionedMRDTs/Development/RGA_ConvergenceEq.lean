import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonFoldOK
import Sal.ConditionedMRDTs.Development.RGA_OrderBridge
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeFoldChain
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_BranchCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_SubchainResolve

/-!
# RGA update convergence and merge bridge over the framework's `loOnEq` order

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_OrderBridge` proved `loOnA` and `loOnEq` INCOMPARABLE, so the loOnA-side
convergence (`RGA_CanonFoldOK.RGA_update_convergence_final`) does not transport
to the framework's `≈`-conditioned order.  This file re-derives the whole
update-convergence pipeline DIRECTLY over `loOnEq rgaEqEquiv' WfOpQ Cfg.vis E`.

## The structural finding

The `RGA_CanonFoldOK` derivation is ORDER-GENERIC: `loOnA` enters only through
the definitions `GoodEnum` / `IsDepPreC` / `GenDisc2C`; no lemma of §3–§6 uses
any property of `loOnA` itself, and the canonical-state engine (`canon_fold`,
`canonInv_doIns/doDel`, `eq_of_canonMatch2`) never mentions an order at all.
§1–§2 below therefore restate the dependency layer over an ABSTRACT relation
`R` and replay the derivation verbatim; §3 instantiates `R := loOnEq …`:

* `GenDisc2CEq` — the generation discipline with dependency prefixes taken as
  the `E`-internal transitive `loOnEq`-past (the exact `≈`-side mirror of
  `GenDisc2C`).  Anchor-closure is carried the same way it was on the `loOnA`
  side: `accurate` at the dependency fold forces every recorded-chain entry to
  be inserted IN the `loOnEq`-dependency prefix.
* `canonFoldOK_of_loOnEq` — every `loOnEq`-respecting enumeration of a
  backward-closed delivered set is `CanonFoldOK`-disciplined.
* `RGA_update_convergence_eq` — two `loOnEq`-respecting enumerations fold from
  `init_st` to observationally equal states: convergence over the framework's
  own order, no order mismatch left for `rga_EqJoinLemma3C`.

## Why `loOnEq` genuinely supplies the needed dependencies (§4)

The discipline is non-vacuous because the dependency edges the fold needs ARE
`loOnEq` edges: an `Ins` and the `Ins` of its anchor do NOT `≈`-commute
(`anchorIns_not_eqCommutesOn` — applying the anchor first seats the new node
under it, applying it second leaves the node re-resolved elsewhere; the two
guarded folds differ at `init_st` already), so a vis-edge from the anchor's
`Ins` is always a `loOnEq` edge (`loOnEq_anchor_edge`).  And every
`loOnEq`-dependency is a vis-edge chain (`depCR_loOnEq_sub_vis`), so the
dependency prefix stays inside the causal past — the concurrent-`Del`
exclusion of `GenDisc2C`'s satisfiability story carries over verbatim.

## Merge (§5)

`RGAMergeFoldChain.eq_merge_two_sided_final` already takes the linearization
order as an ABSTRACT `lo` — the merge bridge is order-agnostic.
`eq_merge_two_sided_eq` exposes it instantiated at `loOnEq rgaEqEquiv' WfOpQ`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGAConvergenceEq

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

/-! ## §1  The order-generic dependency layer

`RGA_CanonFoldOK`'s §1/§3, with the fixed order `loOnA RGACondSig Cfg E`
abstracted to an arbitrary relation `R`.  Every proof is the original one:
none used anything about `loOnA` beyond its occurrence in these definitions. -/

/-- An `E`-internal dependency edge of the abstract order `R`. -/
def DepER (E : Set op_t) (R : op_t → op_t → Prop) (z x : op_t) : Prop :=
  z ∈ E ∧ R z x

/-- Transitive dependency: the `E`-internal transitive closure of `R`. -/
def DepCR (E : Set op_t) (R : op_t → op_t → Prop) : op_t → op_t → Prop :=
  Relation.TransGen (DepER E R)

/-- `d` is an `R`-respecting `Nodup` enumeration of exactly `o`'s strict
transitive `R`-dependencies in `E` (`RGA_CanonFoldOK.IsDepPreC`, order-
abstract). -/
def IsDepPreR (E : Set op_t) (R : op_t → op_t → Prop)
    (o : op_t) (d : List op_t) : Prop :=
  (∀ x ∈ d, x ∈ E) ∧ d.Nodup ∧ respects d R ∧
  (∀ z ∈ E, z ≠ o → DepCR E R z o → z ∈ d) ∧
  (∀ x ∈ d, x ≠ o ∧ DepCR E R x o)

/-- The per-event generation discipline over `R`: each delivered event's
recorded path is accurate at the fold of its `R`-dependency prefix
(`RGA_CanonFoldOK.GenDisc2C`, order-abstract). -/
def GenDiscR (E : Set op_t) (R : op_t → op_t → Prop) : Prop :=
  ∀ o ∈ E, ∀ d : List op_t, IsDepPreR E R o d →
    accurate o (applySeqR init_st d)

/-- A good enumeration over `R`: members delivered, `Nodup`, `R`-respecting,
closed under `E`-internal `R`-predecessors (`RGA_CanonFoldOK.GoodEnum`,
order-abstract). -/
def GoodEnumR (E : Set op_t) (R : op_t → op_t → Prop) (σ : List op_t) : Prop :=
  (∀ x ∈ σ, x ∈ E) ∧ σ.Nodup ∧ respects σ R ∧
  (∀ x ∈ σ, ∀ z ∈ E, z ≠ x → R z x → z ∈ σ)

/-- Peeling the last event of a good enumeration (order-abstract
`goodEnum_append`). -/
theorem goodEnumR_append (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (o : op_t) (h : GoodEnumR E R (F ++ [o])) :
    GoodEnumR E R F ∧ o ∈ E ∧ o ∉ F ∧ (∀ x ∈ F, ¬ R o x) := by
  obtain ⟨hmem, hnd, hresp, hclose⟩ := h
  have hndF : F.Nodup ∧ ([o] : List op_t).Nodup ∧ ∀ a ∈ F, ∀ b ∈ [o], a ≠ b :=
    List.nodup_append.mp hnd
  have honF : o ∉ F :=
    fun hoF => hndF.2.2 o hoF o (List.mem_singleton_self o) rfl
  have hcross : ∀ a ∈ F, ∀ b ∈ [o], ¬ R b a :=
    (List.pairwise_append.mp hresp).2.2
  have hlast : ∀ x ∈ F, ¬ R o x :=
    fun x hx => hcross x hx o (List.mem_singleton_self o)
  refine ⟨⟨fun x hx => hmem x (List.mem_append_left _ hx),
           hndF.1,
           List.Pairwise.sublist (List.sublist_append_left F [o]) hresp,
           ?_⟩,
          hmem o (List.mem_append_right _ (List.mem_singleton_self o)), honF, hlast⟩
  intro x hx z hz hzx hlo
  rcases List.mem_append.mp (hclose x (List.mem_append_left _ hx) z hz hzx hlo) with h' | h'
  · exact h'
  · exact absurd hlo (List.mem_singleton.mp h' ▸ hlast x hx)

/-- Transitive dependencies of a member of a good enumeration are members. -/
theorem mem_of_depCR (E : Set op_t) (R : op_t → op_t → Prop)
    (σ : List op_t) (hg : GoodEnumR E R σ) :
    ∀ (x z : op_t), DepCR E R z x → x ∈ σ → z ∈ σ := by
  intro x z h
  induction h with
  | @single b h' =>
    intro hb
    by_cases hzb : z = b
    · rwa [hzb]
    · exact hg.2.2.2 b hb z h'.1 hzb h'.2
  | @tail b c _ hbc ih =>
    intro hc
    refine ih ?_
    by_cases hbc' : b = c
    · rwa [hbc']
    · exact hg.2.2.2 c hc b hbc.1 hbc' hbc.2

/-- `w`'s dependency sub-prefix carved out of `F`, in `F`'s order. -/
noncomputable def depListR (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (w : op_t) : List op_t :=
  F.filter (fun z => decide (z ≠ w ∧ DepCR E R z w))

theorem mem_depListR {E : Set op_t} {R : op_t → op_t → Prop}
    {F : List op_t} {w x : op_t} :
    x ∈ depListR E R F w ↔ x ∈ F ∧ x ≠ w ∧ DepCR E R x w := by
  simp only [depListR, List.mem_filter, decide_eq_true_eq]

/-- The carved sub-prefix IS a dependency prefix, provided `F` contains all of
`w`'s strict transitive dependencies. -/
theorem isDepPreR_depList (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (w : op_t)
    (hmemE : ∀ x ∈ F, x ∈ E) (hnd : F.Nodup) (hresp : respects F R)
    (hcomp : ∀ z ∈ E, z ≠ w → DepCR E R z w → z ∈ F) :
    IsDepPreR E R w (depListR E R F w) := by
  refine ⟨fun x hx => hmemE x (mem_depListR.mp hx).1,
          hnd.filter _,
          List.Pairwise.sublist (List.filter_sublist) hresp,
          fun z hz hzw hdep => mem_depListR.mpr ⟨hcomp z hz hzw hdep, hzw, hdep⟩,
          fun x hx => (mem_depListR.mp hx).2⟩

/-- For the LAST event of a good enumeration, its dependency sub-prefix of the
strict prefix is itself GOOD (transitive closure ⇒ backward closure). -/
theorem goodEnumR_depList_last (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (o : op_t) (hg : GoodEnumR E R (F ++ [o])) :
    GoodEnumR E R (depListR E R F o) := by
  obtain ⟨hgF, _hoE, _honF, hlast⟩ := goodEnumR_append E R F o hg
  refine ⟨fun x hx => hgF.1 x (mem_depListR.mp hx).1,
          hgF.2.1.filter _,
          List.Pairwise.sublist (List.filter_sublist) hgF.2.2.1,
          ?_⟩
  intro x hx z hz hzx hlo
  obtain ⟨hxF, _hxo, hxdep⟩ := mem_depListR.mp hx
  have hzF : z ∈ F := hgF.2.2.2 x hxF z hz hzx hlo
  have hzo : z ≠ o := by
    rintro rfl
    exact hlast x hxF hlo
  exact mem_depListR.mpr ⟨hzF, hzo, Relation.TransGen.head ⟨hz, hlo⟩ hxdep⟩

/-- `IsDepPreR` for the last event, from goodness of the whole enumeration. -/
theorem isDepPreR_depList_last (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (o : op_t) (hg : GoodEnumR E R (F ++ [o])) :
    IsDepPreR E R o (depListR E R F o) := by
  obtain ⟨hgF, _hoE, honF, _hlast⟩ := goodEnumR_append E R F o hg
  refine isDepPreR_depList E R F o hgF.1 hgF.2.1 hgF.2.2.1 ?_
  intro z hz hzo hdep
  have hzρ : z ∈ F ++ [o] :=
    mem_of_depCR E R (F ++ [o]) hg o z hdep
      (List.mem_append_right _ (List.mem_singleton_self o))
  rcases List.mem_append.mp hzρ with h' | h'
  · exact h'
  · exact absurd (List.mem_singleton.mp h') hzo

/-- `IsDepPreR` for a MEMBER of a good enumeration. -/
theorem isDepPreR_depList_mem (E : Set op_t) (R : op_t → op_t → Prop)
    (F : List op_t) (w : op_t) (hgF : GoodEnumR E R F) (hw : w ∈ F) :
    IsDepPreR E R w (depListR E R F w) :=
  isDepPreR_depList E R F w hgF.1 hgF.2.1 hgF.2.2.1
    (fun z _hz _hzw hdep => mem_of_depCR E R F hgF w z hdep hw)

/-! ## §2  The order-generic per-step discharge

`RGA_CanonFoldOK` §5–§6 replayed over `R`.  The order-free groundwork (§2/§4
there: fold-domain lemmas, `accurate_ins_entries`, `resolve_restrict`,
`anc_transport`, `chainOK_transport`, `canonFoldOK_append`) is reused as-is. -/

/-- Recorded-chain entries of a member of a good enumeration are root-or-
inserted in that member's dependency sub-prefix. -/
theorem chain_entries_memR (E : Set op_t) (R : op_t → op_t → Prop)
    (hGen : GenDiscR E R) (F : List op_t)
    (hgF : GoodEnumR E R F) (t' r' e' a' : ℕ) (p' : List ℕ)
    (hm : (t', r', .Ins e' p' a') ∈ F) :
    ∀ c ∈ a' :: p',
      c = 0 ∨ insertedIn (depListR E R F (t', r', .Ins e' p' a')) c := by
  intro c hc
  have hacc := hGen _ (hgF.1 _ hm) _ (isDepPreR_depList_mem E R F _ hgF hm)
  rcases accurate_ins_entries t' r' e' a' p' _ hacc c hc with h | h
  · exact Or.inl h
  · exact Or.inr (insertedIn_of_contains_fold _ c h)

/-- The dependency-fold package for the LAST event of a good enumeration. -/
theorem depPack_lastR (E : Set op_t) (R : op_t → op_t → Prop)
    (hGen : GenDiscR E R)
    (F : List op_t) (o : op_t) (hg : GoodEnumR E R (F ++ [o]))
    (hIH : ∀ σ : List op_t, σ.length ≤ F.length → GoodEnumR E R σ →
      CanonFoldOK [] init_st σ) :
    ∃ d : List op_t, (∀ x ∈ d, x ∈ F) ∧
      CanonInv d (applySeqR init_st d) ∧
      accurate o (applySeqR init_st d) ∧
      (∀ z rz ez az (pz : List ℕ), (z, rz, .Ins ez pz az) ∈ d →
        ∀ c ∈ az :: pz, c = 0 ∨ insertedIn d c) := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnumR_append E R F o hg
  refine ⟨depListR E R F o, fun x hx => (mem_depListR.mp hx).1, ?_, ?_, ?_⟩
  · exact canon_fold _ [] init_st canonInv_init
      (hIH _ (List.length_filter_le _ _) (goodEnumR_depList_last E R F o hg))
  · exact hGen o hoE _ (isDepPreR_depList_last E R F o hg)
  · intro z rz ez az pz hm c hc
    have hmF : (z, rz, .Ins ez pz az) ∈ F := (mem_depListR.mp hm).1
    rcases chain_entries_memR E R hGen F hgF z rz ez az pz hmF c hc with h | h
    · exact Or.inl h
    · refine Or.inr (insertedIn_mono ?_ h)
      intro x hx
      obtain ⟨hxF, _hxne, hxdep⟩ := mem_depListR.mp hx
      refine mem_depListR.mpr ⟨hxF, ?_, ?_⟩
      · rintro rfl; exact honF hxF
      · exact Relation.TransGen.trans hxdep (mem_depListR.mp hm).2.2

/-- **`canonStepOK_of_genR`** — the application discipline at the event's OWN
application point, from the generation discipline over the abstract `R`. -/
theorem canonStepOK_of_genR (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDiscR E R)
    (F : List op_t) (o : op_t)
    (hg : GoodEnumR E R (F ++ [o]))
    (hIH : ∀ σ : List op_t, σ.length ≤ F.length → GoodEnumR E R σ →
      CanonFoldOK [] init_st σ) :
    CanonStepOK F (applySeqR init_st F) o := by
  obtain ⟨hgF, hoE, honF, _hlast⟩ := goodEnumR_append E R F o hg
  have hinvF : CanonInv F (applySeqR init_st F) :=
    canon_fold F [] init_st canonInv_init (hIH F le_rfl hgF)
  have hfresh : ∀ L : List op_t, (∀ x ∈ L, x ∈ F) → ¬ insertedIn L o.1 := by
    rintro L hL ⟨r', e', p', a', hm⟩
    have hmF : (o.1, r', .Ins e' p' a') ∈ F := hL _ hm
    have hne : (o.1, r', .Ins e' p' a') ≠ o := fun hEq => honF (hEq ▸ hmF)
    exact hdts _ o (hgF.1 _ hmF) hoE hne rfl
  obtain ⟨d, hdsubF, hinvD, hacc, hchains⟩ := depPack_lastR E R hGen F o hg hIH
  obtain ⟨t, r, op⟩ := o
  have ht0 : t ≠ 0 := hids0 (t, r, op) hoE
  cases op with
  | Ins e p a =>
    refine ⟨ht0, ?_, ?_, ?_, ?_, ?_⟩
    · cases hb : contains (applySeqR init_st F) t with
      | false => rfl
      | true =>
        exact absurd (insertedIn_of_contains_fold F t hb)
          (hfresh F (fun _ hx => hx))
    · rintro ⟨t', r', p', hm⟩
      have haccδ := hGen _ (hgF.1 _ hm) _ (isDepPreR_depList_mem E R F _ hgF hm)
      simp only [accurate, opLeaf, opPath] at haccδ
      rcases haccδ with ⟨hx0, _⟩ | ⟨hxl, _⟩
      · exact ht0 hx0
      · exact hfresh (depListR E R F (t', r', .Del p' t))
          (fun x hx => (mem_depListR.mp hx).1)
          (insertedIn_of_contains_fold _ t hxl)
    · intro hmem
      rcases accurate_ins_entries t r e a p _ hacc t hmem with h | h
      · exact ht0 h
      · exact hfresh d hdsubF (insertedIn_of_contains_fold d t h)
    · intro t' r' e' p' a' hm hmem
      rcases chain_entries_memR E R hGen F hgF t' r' e' a' p' hm t hmem with h | h
      · exact ht0 h
      · exact hfresh (depListR E R F (t', r', .Ins e' p' a'))
          (fun x hx => (mem_depListR.mp hx).1) h
    · simp only [accurate, opLeaf, opPath] at hacc
      rcases hacc with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
      · subst ha0; subst hp0
        intro c cs heq
        have hnil : liveSub (applySeqR init_st F) [0] = [] := by
          unfold liveSub
          rw [List.filter_cons, List.filter_nil, hinvF.1]
          simp
        rw [hnil] at heq
        exact absurd heq (by simp)
      · exact fun c cs heq =>
          chainOK_transport F d hdsubF hinvF hinvD hchains p a hal hpath c cs heq
  | Del p x =>
    simp only [accurate, opLeaf, opPath] at hacc
    rcases hacc with ⟨hx0, hp0⟩ | ⟨hxl, hpath⟩
    · subst hx0; subst hp0
      refine ⟨fun _ => rfl, fun hcx => ?_⟩
      rw [hinvF.1] at hcx
      exact Bool.noConfusion hcx
    · refine ⟨fun hx0 => ?_, fun hcx => ?_⟩
      · rw [hx0, hinvD.1] at hxl
        exact Bool.noConfusion hxl
      · exact (anc_transport F d hdsubF hinvF hinvD hchains x hxl hcx p hpath).symm

/-- **`canonFoldOK_of_genR`** — every good enumeration over `R` is
`CanonFoldOK`-disciplined (strong induction on length). -/
theorem canonFoldOK_of_genR (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDiscR E R) :
    ∀ (n : ℕ) (σ : List op_t), σ.length ≤ n → GoodEnumR E R σ →
      CanonFoldOK [] init_st σ := by
  intro n
  induction n with
  | zero =>
    intro σ hlen _
    have hσ : σ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hσ
    trivial
  | succ n ih =>
    intro σ hlen hg
    rcases List.eq_nil_or_concat σ with rfl | ⟨F, o, hEq⟩
    · trivial
    · rw [List.concat_eq_append] at hEq
      subst hEq
      have hlenF : F.length ≤ n := by
        rw [List.length_append] at hlen
        simp only [List.length_singleton] at hlen
        omega
      have hgF := (goodEnumR_append E R F o hg).1
      exact canonFoldOK_append F [] init_st o (ih F hlenF hgF)
        (canonStepOK_of_genR E R hdts hids0 hGen F o hg
          (fun τ hτ hgτ => ih τ (hτ.trans hlenF) hgτ))

/-! ## §3  Instantiation at the framework's order `loOnEq rgaEqEquiv' WfOpQ`

The abstract `R` becomes the `≈`-conditioned linearization order the framework
(`GenericEqQuotient.EqJoinLemma3C` via `loOn_qsig_iff`) actually quantifies
over — NOT `loOnA` (incomparable, `RGA_OrderBridge`). -/

/-- The framework's `≈`-conditioned linearization order, RGA-specialized:
`loOnEq rgaEqEquiv' WfOpQ` over a configuration's `vis`. -/
abbrev loEqRGA (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : op_t → op_t → Prop :=
  loOnEq rgaEqEquiv' WfOpQ Cfg.vis E

/-- **`GenDisc2CEq` — the generation discipline over `loOnEq`.**  Each
delivered event's recorded path is accurate at the fold of its `E`-internal
transitive `loOnEq`-dependency prefix — the exact `≈`-side mirror of
`RGA_CanonFoldOK.GenDisc2C` (which reads its prefixes off `loOnA`).  Anchor-
closure is carried inside, as there: `accurate o` at the dependency fold forces
each recorded-chain entry to be INSERTED in the `loOnEq`-prefix — and §4 shows
those insert-edges are genuinely `loOnEq`-edges, while `depCR_loOnEq_sub_vis`
keeps the prefix inside `o`'s causal past (concurrent `Del`s stay excluded, so
the satisfiability story of `GenDisc2C` carries over verbatim). -/
def GenDisc2CEq (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  GenDiscR E (loEqRGA Cfg E)

/-- **`canonFoldOK_of_loOnEq`** — every `loOnEq`-respecting enumeration of the
backward-closed delivered set is `CanonFoldOK`-disciplined, from `GenDisc2CEq`
plus the execution model's id-uniqueness.  The `loOnA` derivation with the
order swapped: dependency-closure of the prefix is over `loOnEq` itself, so no
`loOnA`-edge (and no `appliesDependsOn` junk edge) is ever consulted. -/
theorem canonFoldOK_of_loOnEq
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hGen : GenDisc2CEq Cfg E)
    (π : List op_t) (hπp : listPermOf π E)
    (hπr : respects π (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E)) :
    CanonFoldOK [] init_st π :=
  canonFoldOK_of_genR E (loEqRGA Cfg E)
    (fun _ _ ha hb hne => C.distinctTs E hE ha hb hne)
    hids0 hGen π.length π le_rfl
    ⟨fun x hx => (hπp.2 x).mp hx, hπp.1, hπr,
     fun _x _hx z hz _ _ => (hπp.2 z).mpr hz⟩

/-- **HEADLINE — RGA update convergence over the FRAMEWORK's order.**  Two
`loOnEq rgaEqEquiv' WfOpQ`-respecting enumerations of the same backward-closed
delivered set `E` fold from `init_st` to observationally equal states.

Premises: the execution model (`C`/`hE`, supplying id-uniqueness; nonzero ids
`hids0`), the enumeration hypotheses, and `GenDisc2CEq` (each event `accurate`
at its own `loOnEq`-dependency prefix).  No `CanonFoldOK` residual, no swap
oracle, no per-prefix `Faithful`, no `DepComp`, no `ReachInv` — and, unlike
`RGA_update_convergence_final`, NO `loOnA` anywhere: this is convergence stated
over the order `EqJoinLemma3C`'s canonical states actually respect, so
`RGA_Instance`'s §7 adapter needs no order bridge. -/
theorem RGA_update_convergence_eq
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (h₂r : respects π₂ (loOnEq rgaEqEquiv' WfOpQ Cfg.vis E))
    (hGen : GenDisc2CEq Cfg E) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) :=
  RGA_update_convergence_canon π₁ π₂
    (fun o => (h₁p.2 o).trans (h₂p.2 o).symm)
    (canonFoldOK_of_loOnEq C Cfg E hE hids0 hGen π₁ h₁p h₁r)
    (canonFoldOK_of_loOnEq C Cfg E hE hids0 hGen π₂ h₂p h₂r)

/-! ## §4  The crux, verified: anchor dependencies ARE `loOnEq` edges

The honest worry (`RGA_OrderBridge`'s K-pair showed `loOnA`-edges that are NOT
`loOnEq`-edges) was that some anchor dependency might `≈`-commute, leaving the
`loOnEq`-dependency prefix anchor-open.  It cannot: an `Ins` and the `Ins` of
its anchor never `≈`-commute — with the anchor first the new node seats under
it, with the anchor second the node's path resolves elsewhere, and the two
guarded folds already differ at the `Inv`-state `init_st`. -/

/-- One `WfOpQ`-guarded step with a true guard is the raw step. -/
theorem doWQ_pos (o : op_t) (s : concrete_st) (h : WfOpQ o s) :
    doW RGACondSig' WfOpQ o s = do_ s o := by
  unfold doW
  rw [if_pos h]
  rfl

/-- `resolve` of an all-dead chain is the root. -/
theorem resolve_all_dead (s : concrete_st) :
    ∀ L : List ℕ, (∀ c ∈ L, contains s c = false) → resolve s L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    rw [resolve_dead_head s c cs (h c (List.mem_cons_self ..))]
    exact ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- `loOnEq rgaEqEquiv' WfOpQ` collapses to its vis-arm: `rc ≡ Either` empties
the rc-tiebreak arm (`RGA_OrderBridge.loOnEq_reduce`, at `WfOpQ`). -/
theorem loOnEqQ_reduce (vis : op_t → op_t → Prop) (ev : Set op_t) (e₁ e₂ : op_t) :
    loOnEq rgaEqEquiv' WfOpQ vis ev e₁ e₂
      ↔ (vis e₁ e₂ ∧ ¬ eqCommutesOn rgaEqEquiv' WfOpQ e₁ e₂) := by
  constructor
  · rintro (h | ⟨_, _, hrc, _⟩)
    · exact h
    · exact absurd hrc (by
        rw [rc_is_Either']
        exact fun h => Sal.Emulation.RcRes.noConfusion h)
  · exact Or.inl

/-- Every `loOnEq`-dependency is a vis-edge chain: `GenDisc2CEq`'s dependency
prefix sits inside the event's causal past (concurrent ops never enter it). -/
theorem depCR_loOnEq_sub_vis (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) {z x : op_t} (h : DepCR E (loEqRGA Cfg E) z x) :
    Relation.TransGen Cfg.vis z x := by
  induction h with
  | @single b h' =>
    exact Relation.TransGen.single ((loOnEqQ_reduce Cfg.vis E _ _).mp h'.2).1
  | @tail b c _ hbc ih =>
    exact Relation.TransGen.tail ih ((loOnEqQ_reduce Cfg.vis E _ _).mp hbc.2).1

/-- **An `Ins` and the `Ins` of its anchor do NOT `≈`-commute** (on genuine,
`WfOpGenQ` ops).  Witness state: `init_st`.  Anchor-first, the dependent node
stores anchor `x`; anchor-second, its path resolves to the root — the folds
differ at the dependent id, and `x ≠ 0` makes the difference observable. -/
theorem anchorIns_not_eqCommutesOn
    (x rx ex ax : ℕ) (px : List ℕ) (t r e : ℕ) (p : List ℕ)
    (hgx : WfOpGenQ (x, rx, .Ins ex px ax))
    (hgo : WfOpGenQ (t, r, .Ins e p x)) :
    ¬ eqCommutesOn rgaEqEquiv' WfOpQ (x, rx, .Ins ex px ax) (t, r, .Ins e p x) := by
  intro h
  have hx0 : x ≠ 0 := hgx.1
  have hxt : x < t := hgo.2 x (List.mem_cons_self ..)
  have hxtne : x ≠ t := Nat.ne_of_lt hxt
  -- the four `WfOpQ` guards: each id is fresh where its op fires
  have hfr_t1 : contains (do_ init_st (x, rx, .Ins ex px ax)) t = false := by
    simp only [do_]
    rw [lemma_InDomUpd1, contains_init]
    simp [hxtne]
  have hfr_x1 : contains (do_ init_st (t, r, .Ins e p x)) x = false := by
    simp only [do_]
    rw [lemma_InDomUpd1, contains_init]
    simp [Ne.symm hxtne]
  have g1 := wfOpQ_ins_of_genQ init_st x rx ex ax px hgx (contains_init x)
  have g2 := wfOpQ_ins_of_genQ _ t r e x p hgo hfr_t1
  have g3 := wfOpQ_ins_of_genQ init_st t r e x p hgo (contains_init t)
  have g4 := wfOpQ_ins_of_genQ _ x rx ex ax px hgx hfr_x1
  have hj := h init_st rga_inv_init'
  rw [doWQ_pos (x, rx, .Ins ex px ax) init_st g1,
      doWQ_pos (t, r, .Ins e p x) _ g2,
      doWQ_pos (t, r, .Ins e p x) init_st g3,
      doWQ_pos (x, rx, .Ins ex px ax) _ g4] at hj
  -- reduce both folds to explicit two-`upd` states
  have hdox : ∀ s : concrete_st,
      do_ s (x, rx, .Ins ex px ax) = upd s x (ex, resolve s (ax :: px)) :=
    fun s => by simp only [do_]
  have hdot : ∀ s : concrete_st,
      do_ s (t, r, .Ins e p x) = upd s t (e, resolve s (x :: p)) :=
    fun s => by simp only [do_]
  simp only [hdox, hdot] at hj
  have hr0 : resolve init_st (x :: p) = 0 :=
    resolve_all_dead init_st (x :: p) (fun c _ => contains_init c)
  have hr1 : resolve init_st (ax :: px) = 0 :=
    resolve_all_dead init_st (ax :: px) (fun c _ => contains_init c)
  simp only [hr0, hr1] at hj
  have hrx : resolve (upd init_st x (ex, 0)) (x :: p) = x :=
    resolve_live_head _ x p (by rw [lemma_InDomUpd1]; simp)
  have hr2 : resolve (upd init_st t (e, 0)) (ax :: px) = 0 := by
    refine resolve_all_dead _ _ ?_
    intro c hc
    have hclt : c < t := lt_trans (hgx.2 c hc) hxt
    rw [lemma_InDomUpd1, contains_init]
    simp [Ne.symm (Nat.ne_of_lt hclt)]
  simp only [hrx, hr2] at hj
  -- the two states disagree at the dependent id `t`: anchor `x` vs root `0`
  have hct : contains (upd (upd init_st x (ex, 0)) t (e, x)) t = true := by
    rw [lemma_InDomUpd1]
    simp
  have hsel := (hj t).2 hct
  rw [lemma_SelUpd1,
      lemma_SelUpd2 (upd init_st t (e, 0)) t x (ex, 0)
        (by simp only [bne_iff_ne, ne_eq]; exact hxtne),
      lemma_SelUpd1] at hsel
  injection hsel with _ h2
  exact hx0 h2

/-- **The anchor edge is a `loOnEq` edge**: a vis-edge from an anchor's `Ins`
to its dependent `Ins` survives into `loOnEq` — exactly the dependency
`CanonFoldOK` needs ordered first.  (Contrast the K-pair: `loOnA`'s EXTRA
edges beyond these may drop, but the anchor-closure edges never do.) -/
theorem loOnEq_anchor_edge (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t)
    (x rx ex ax : ℕ) (px : List ℕ) (t r e : ℕ) (p : List ℕ)
    (hgx : WfOpGenQ (x, rx, .Ins ex px ax))
    (hgo : WfOpGenQ (t, r, .Ins e p x))
    (hvis : Cfg.vis (x, rx, .Ins ex px ax) (t, r, .Ins e p x)) :
    loOnEq rgaEqEquiv' WfOpQ Cfg.vis E (x, rx, .Ins ex px ax) (t, r, .Ins e p x) :=
  Or.inl ⟨hvis, anchorIns_not_eqCommutesOn x rx ex ax px t r e p hgx hgo⟩

/-! ## §5  The merge bridge over `loOnEq` -/


end Sal.ConditionedMRDTs.RGAConvergenceEq
