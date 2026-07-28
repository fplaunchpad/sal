import Sal.ConditionedMRDTs.Metatheory.ConverseEq
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H

/-!
# Conditioned reachability arbitration adequacy: the `eqObs`-quotient lift

The `eqObs`-quotient (`≈`) analog of the flat capstone
`Metatheory/ArbAdequacyReach.lean` (`ra_linearizable3Arb_of_core_feasible_cd`). It
lifts the CONDITIONED per-version arb-transport of `Metatheory/ConverseEq.lean`
(`ra_lin_arb_transport`: conditioned per-version RA-lin IS the arb-recast at
`arb = rcArb`) to the FULL reachability adequacy, so the rc-free recast is
established over genuine observational equivalence (not `=`), at every reachable
`Inv`-configuration, framework-wide. The payoff (`loOnEqArbFamily`,
`loOnEq_isRALinearizable3Eq_via_arb_capstone`) re-derives the conditioned RA-lin
`GoodConfig3H.IsRALinearizable3Eq` as the `arb = rcArb` instantiation.

## The architecture

The flat `ArbAdequacyReach` re-threads the `GoodConfig3` reachability induction over
`IsCanonicalStateArb`, and its `ArbFamily` carries SIX clauses (extends-`vis`,
acyclic, antitone, vis-consistent, convergent, vis-local) because the flat engine
DERIVES its ternary Join Lemma from the CD/feasible VCs, and that derivation needs
the arbitration to be well-behaved.

The CONDITIONED engine is different: it runs over the `Inv`-subtype quotient `QSig`
(which carries `Inv`, needed to keep `≈`-congruence of `update`/`mergeL` in scope,
as the plain execution model has no `Inv`), mirroring `Metatheory/GoodConfig3H.lean`,
and it takes the `≈`-Join as a PRIMITIVE VC (`EqJoinLemma3C_ArbH`), not a derived
lemma. Consequently **five of the flat six `ArbFamily` clauses collapse for the
conditioned layer**:

* **antitone** is FREE for any `arb` (`loOnArb_mono`, ConverseEq);
* **extends-`vis`**, **vis-consistent**, **vis-local** hold structurally for any
  `arb` over the `loOnArb` layer (the vis-arm and absorber are arb-independent),
  stated here as `arbFamilyEq_extends_vis` / `_vis_consistent` / `_vis_local`, and
  used only to discharge the arb-agnostic congruence/extension lemmas;
* **acyclic** and **convergent** are NOT needed: they were the flat derivation's
  levers on the Join, and here the Join is the single primitive VC.

So `ArbFamilyEq` carries exactly the ONE genuine clause the conditioned engine
consumes: the abstract-arbitration `≈`-Join (`arb` + `join`). The apply re-attach
(`isCanonicalStateArbEqH_extend`) is arb-agnostic: the fresh causally-latest event's
maximality is killed by `vis`, never by `arb`. This mirrors, over `≈`, the
per-version transport `ConverseEq.ra_lin_arb_transport`, now at every reachable
configuration.

## Layout (kernel-clean; `#print axioms` at the foot)

* **§1** the arb-forms of the `GenericEqQuotient_H` datatype support:
  `IsCanonicalStateArbEqH`, `isCanonicalStateArbEqH_congr` (the createReplica
  congruence), `isCanonicalStateArbEqH_extend` (the apply re-attach, arb-agnostic),
  `EqJoinLemma3C_ArbH` (the merge VC). All `loOnEq ↦ loOnArb … arb`.
* **§2** the `ArbFamilyEq` structure and the five free/collapsed clauses, as theorems.
* **§3** the QSig-level per-version witness `IsCanonicalStateArbH` with its congr /
  extend / merged wrappers.
* **§4** `GoodConfig3ArbFEq` and the four transition lemmas
  `goodConfig3ArbFEq_init / _createReplica / _apply / _merge`, reusing the arb-
  agnostic structural preservations `GoodConfig3S`/`goodConfig3S_*`.
* **§5** the reachability induction `goodConfig3ArbFEq_of_reachF` and THE CAPSTONE
  `ra_linearizable3ArbEq_of_reach` (`IsRALinearizable3ArbEq` at every reachable
  `Inv`-config), composed with `ConverseEq.ra_lin_arb_transport`.
* **§6** THE INSTANCE: `loOnEqArbFamily` (`arb = rcArb`, `join` = `EqJoinLemma3C_H`)
  and `loOnEq_isRALinearizable3Eq_via_arb_capstone`, re-deriving
  `GoodConfig3H.IsRALinearizable3Eq` through the abstract engine.
-/

set_option maxHeartbeats 4000000

namespace Sal.ConditionedMRDTs.ArbReachEq

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs
  (Configuration Version Step3 Label3 IsLCA initConfig labeledTS3 core_vis
   GoodConfig3 goodConfig3_init)
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. The arb-forms of the `GenericEqQuotient_H` datatype support -/

/-- **Arb-canonical state up to `≈`, `H`-disciplined**, `IsCanonicalStateArbEqH`.
`GenericEqQuotient.IsCanonicalStateEqH` with the linearization order `loOnEq`
replaced by the abstract-arbitration order `loOnArb … arb` (ConverseEq): the fold
is RAW (`applySeq D.toCRDTSig D.init ρ`), lands `≈`-equal, and the witness carries
the datatype's delivery discipline `H`. At `arb = rcArb` this IS
`IsCanonicalStateEqH` (definitionally, via `loOnEq_isArb`). -/
def IsCanonicalStateArbEqH (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (arb : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnArb E W vis arb ev) ∧
    H ρ ∧ E.eqv (applySeq D.toCRDTSig D.init ρ) s

/-- Forget the discipline clause. -/
theorem isCanonicalStateArbEq_of_H (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis arb : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State)
    (h : IsCanonicalStateArbEqH H E W vis arb ev s) :
    IsCanonicalStateArbEq E W vis arb ev s := by
  obtain ⟨ρ, hperm, hresp, _, hfold⟩ := h
  exact ⟨ρ, hperm, hresp, hfold⟩

/-- **`≈`-closure of the arb-canonical state.** A representative `≈` to a canonical
state is itself canonical (existence read up to `≈`). The arb-analog of
`ConverseEq.isCanonicalStateEq_congr`. -/
theorem isCanonicalStateArbEq_eqClosed
    {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis arb : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)} {s u : D.State}
    (h : IsCanonicalStateArbEq E W vis arb ev u) (heq : E.eqv s u) :
    IsCanonicalStateArbEq E W vis arb ev s := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  exact ⟨ρ, hp, hr, E.equiv.trans hf (E.equiv.symm heq)⟩

/-- **The createReplica congruence**: transport `IsCanonicalStateArbEqH` under
`vis`-agreement on `ev`. The arb-form of `isCanonicalStateEqH_congr` (`loOnEq ↦
loOnArb … arb`): the arb-arm `arb e₁ e₂` is `vis`-independent, so it passes through
untouched; only the vis-arm and the absorber transport. -/
theorem isCanonicalStateArbEqH_congr (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    {vis vis' : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)} {σ : D.State}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (vis' a b ↔ vis a b))
    (h : IsCanonicalStateArbEqH H E W vis arb ev σ) :
    IsCanonicalStateArbEqH H E W vis' arb ev σ := by
  obtain ⟨ρ, hp, hr, hH, hf⟩ := h
  refine ⟨ρ, hp, ?_, hH, hf⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn h_lo
  have ha_E : a ∈ ev := (hp.2 a).mp ha
  have hb_E : b ∈ ev := (hp.2 b).mp hb
  apply hn
  rcases h_lo with ⟨hv, hnc⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨(h_vis b hb_E a ha_E).mp hv, hnc⟩
  · refine Or.inr ⟨fun hv => h1 ((h_vis b hb_E a ha_E).mpr hv),
      fun hv => h2 ((h_vis a ha_E b hb_E).mpr hv), h3, ?_⟩
    rintro ⟨e₃, he₃, hv, hnc⟩
    exact h4 ⟨e₃, he₃, (h_vis a ha_E e₃ he₃).mpr hv, hnc⟩

/-- **The apply re-attach**, `H`-disciplined and ARB-AGNOSTIC. The arb-form of
`isCanonicalStateEqH_extend` (`loOnEq ↦ loOnArb … arb`, `loOnEq_antimono ↦
loOnArb_mono`). The fresh, causally-latest, `applicable` event `e` extends the
witness. The maximality discharge touches only the vis-arm (`h_e_last`) and the
absorber's `¬ vis e₂ e₁` (`h_e_sees`); the arb-arm `arb e y` is never consulted, so
the re-attach holds for EVERY `arb`. This is why the conditioned engine needs no
acyclicity/vis-consistency clause on `arb`. -/
theorem isCanonicalStateArbEqH_extend (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp))
    (σ : D.State) (hσ : D.Inv σ) (e : Op D.AppOp)
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ vis e x)
    (happ : D.applicable e σ)
    (hHext : ∀ ρ : List (Op D.AppOp), listPermOf ρ ev → H ρ →
        D.applicable e (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [e]))
    (h : IsCanonicalStateArbEqH H E W vis arb ev σ) :
    IsCanonicalStateArbEqH H E W vis arb (insert e ev) (D.update σ e) := by
  obtain ⟨ρ, hp, hr, hH, hf⟩ := h
  have hInvFold : D.Inv (applySeq D.toCRDTSig D.init ρ) := hInvCong (E.equiv.symm hf) hσ
  have happFold : D.applicable e (applySeq D.toCRDTSig D.init ρ) :=
    (hA.applicable_congr e hInvFold hσ hf).mpr happ
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_fresh ((hp.2 x).mp hx)
  · rw [List.mem_append, List.mem_singleton, Set.mem_insert_iff]
    constructor
    · rintro (h' | rfl)
      · exact Or.inr ((hp.2 a).mp h')
      · exact Or.inl rfl
    · rintro (rfl | h')
      · exact Or.inr rfl
      · exact Or.inl ((hp.2 a).mpr h')
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun hn h' =>
        hn (loOnArb_mono (Set.subset_insert _ _) h')),
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    have hy_ev : y ∈ ev := (hp.2 y).mp hy
    rintro (⟨hv, _⟩ | ⟨_, h_nvis_ye, _, _⟩)
    · exact h_e_last y hy_ev hv
    · exact h_nvis_ye (h_e_sees y hy_ev)
  · exact hHext ρ hp hH happFold
  · rw [applySeq_append_single]
    exact hC.update_congr e hInvFold hσ hf

/-- **The abstract-arbitration `≈`-Join VC**: `EqJoinLemma3C_H` with `loOnEq ↦
loOnArb … arb`. The single genuine clause the conditioned reachability engine
consumes about `arb`. At `arb = rcArb` this IS `EqJoinLemma3C_H` (definitionally). -/
def EqJoinLemma3C_ArbH (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) (H : List (Op D.AppOp) → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (events : Set (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    HonJ vis events →
    D.Inv s₀ → D.Inv s₁ → D.Inv s₂ →
    (∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c) →
    (∀ a : Op D.AppOp, ¬ vis a a) →
    (∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel vis ev₁ → fullClosureRel vis ev₂ →
    IsCanonicalStateArbEqH H E W vis arb (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateArbEqH H E W vis arb ev₁ s₁ →
    IsCanonicalStateArbEqH H E W vis arb ev₂ s₂ →
    IsCanonicalStateArbEqH H E W vis arb (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-! ## §2. The `ArbFamilyEq` structure and the five free/collapsed clauses -/

/-- **The conditioned arbitration family.** The single genuine clause the conditioned
reachability engine consumes about the abstract rc-arm arbitration `arb`: the
abstract-arbitration `≈`-Join (`EqJoinLemma3C_ArbH`). The flat `ArbFamily`'s other
five clauses collapse (see the free-clause theorems below): antitone is
`loOnArb_mono`, extends-`vis`/vis-consistent/vis-local hold for any `arb`, and
acyclic/convergent were the flat derivation's levers on a Join that is here a
primitive VC. -/
structure ArbFamilyEq (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop) where
  /-- The abstract rc-arm arbitration (a plain binary relation on operations). -/
  arb : Op D.AppOp → Op D.AppOp → Prop
  /-- The abstract-arbitration `≈`-Join VC, the merge pillar. -/
  join : EqJoinLemma3C_ArbH D E W H arb HonJ

/-- **Free clause, extends-`vis`.** Every visible non-`≈`-commuting pair is ordered
by `loOnArb`, for ANY `arb` (the vis-arm is arb-independent). -/
theorem arbFamilyEq_extends_vis {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis arb : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (hvis : vis a b) (hnc : ¬ eqCommutesOn E W a b) :
    loOnArb E W vis arb ev a b :=
  Or.inl ⟨hvis, hnc⟩

/-- **Free clause, antitone.** `loOnArb` is monotone-decreasing in the event set for
ANY `arb` (`ConverseEq.loOnArb_mono`, stated here as the family clause). -/
theorem arbFamilyEq_antitone {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis arb : Op D.AppOp → Op D.AppOp → Prop} {ev ev' : Set (Op D.AppOp)}
    (h_sub : ev ⊆ ev') {a b : Op D.AppOp}
    (h : loOnArb E W vis arb ev' a b) : loOnArb E W vis arb ev a b :=
  loOnArb_mono h_sub h

/-- **Free clause, vis-consistent.** `loOnArb` never orders `a` before an event `b`
that `a` observed, for ANY `arb` (both arms vacuous on an observed pair). -/
theorem arbFamilyEq_vis_consistent {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {vis arb : Op D.AppOp → Op D.AppOp → Prop}
    (h_tr : ∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ vis a a)
    {ev : Set (Op D.AppOp)} {a b : Op D.AppOp}
    (hvis : vis b a) : ¬ loOnArb E W vis arb ev a b := by
  rintro (⟨hab, _⟩ | ⟨_, hnba, _, _⟩)
  · exact h_ir a (h_tr hab hvis)
  · exact hnba hvis

/-- **Free clause, vis-local.** `loOnArb` on `ev` depends only on `vis` restricted
to `ev`, for ANY `arb` (the arb-arm is `vis`-independent). -/
theorem arbFamilyEq_vis_local {E : EqEquiv D} {W : Op D.AppOp → D.State → Prop}
    {arb : Op D.AppOp → Op D.AppOp → Prop}
    {vis vis' : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)}
    (hva : ∀ a ∈ ev, ∀ b ∈ ev, (vis a b ↔ vis' a b))
    {a b : Op D.AppOp} (ha : a ∈ ev) (hb : b ∈ ev) :
    loOnArb E W vis arb ev a b ↔ loOnArb E W vis' arb ev a b := by
  have H0 : ∀ (v1 v2 : Op D.AppOp → Op D.AppOp → Prop),
      (∀ p ∈ ev, ∀ q ∈ ev, (v1 p q ↔ v2 p q)) →
      loOnArb E W v1 arb ev a b → loOnArb E W v2 arb ev a b := by
    intro v1 v2 hv hlo
    rcases hlo with ⟨hvab, hnc⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨(hv a ha b hb).mp hvab, hnc⟩
    · refine Or.inr ⟨fun hy => h1 ((hv a ha b hb).mpr hy),
        fun hy => h2 ((hv b hb a ha).mpr hy), h3, ?_⟩
      rintro ⟨e₃, he₃, hve, hnce⟩
      exact h4 ⟨e₃, he₃, (hv b hb e₃ he₃).mpr hve, hnce⟩
  exact ⟨H0 vis vis' hva, H0 vis' vis (fun p hp q hq => (hva p hp q hq).symm)⟩

/-! ## §3. The QSig-level per-version arb witness -/

/-- The version class `q` is `qmk` of a representative carrying an `H`-disciplined
arb-canonical RAW-fold witness. The arb-analog of `GoodConfig3H.IsCanonicalStateH`. -/
def IsCanonicalStateArbH (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) : Prop :=
  ∃ (σ : D.State) (hσ : D.Inv σ),
    q = qmk E σ hσ ∧ IsCanonicalStateArbEqH H E W Cq.vis arb ev σ

/-- Transport under `vis`-agreement (createReplica). -/
theorem isCanonicalStateArbH_congr (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {Cq Cq' : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig}
    {ev : Set (Op D.AppOp)} {q : QState D E}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (Cq'.vis a b ↔ Cq.vis a b))
    (h : IsCanonicalStateArbH H E W arb hP hC hA Cq ev q) :
    IsCanonicalStateArbH H E W arb hP hC hA Cq' ev q := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  exact ⟨σ, hσ, hq, isCanonicalStateArbEqH_congr H E W arb h_vis hcs⟩

/-- The apply-step extension: the fresh, `vis`-maximal, `qapplicable` event extends
the representative's witness; the class steps by `qdo`. Arb-agnostic re-attach. -/
theorem isCanonicalStateArbH_extend (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp)) (q : QState D E) (e : Op D.AppOp)
    (hgenW : ∀ s : D.State, D.applicable e s → W e s)
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, Cq.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ Cq.vis e x)
    (hqapp : qapplicable E W hA e q)
    (hHext : ∀ ρ : List (Op D.AppOp), listPermOf ρ ev → H ρ →
        D.applicable e (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [e]))
    (h : IsCanonicalStateArbH H E W arb hP hC hA Cq ev q) :
    IsCanonicalStateArbH H E W arb hP hC hA Cq (insert e ev)
      ((QSig E W hP hC hA).toCRDTSig.update q e) := by
  obtain ⟨σ, hσ, hq, hcs⟩ := h
  have happ : D.applicable e σ := by rw [hq] at hqapp; exact hqapp
  have hW : W e σ := hgenW σ happ
  refine ⟨D.update σ e, hP.inv_update σ e hσ hW, ?_, ?_⟩
  · rw [hq]
    show qdo E W hP hC hA (qmk E σ hσ) e = qmk E (D.update σ e) (hP.inv_update σ e hσ hW)
    rw [qdo_qmk]
    refine (qmk_eq_iff E).mpr ?_
    rw [show doW D W e σ = D.update σ e from if_pos hW]
    exact E.equiv.refl _
  · exact isCanonicalStateArbEqH_extend H E W arb hC hA hInvCong Cq.vis ev σ hσ e
      h_e_fresh h_e_sees h_e_last happ hHext hcs

/-- The arb-Join application: merged arb-H-canonical state from `EqJoinLemma3C_ArbH`. -/
theorem mergedArbH_of_join (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinH : EqJoinLemma3C_ArbH D E W H arb HonJ)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (events ev₁ ev₂ : Set (Op D.AppOp)) (sT s₁ s₂ : QState D E)
    (hHonJ : HonJ Cq.vis events)
    (htr : ∀ {a b c : Op D.AppOp}, Cq.vis a b → Cq.vis b c → Cq.vis a c)
    (hir : ∀ a : Op D.AppOp, ¬ Cq.vis a a)
    (hdts : ∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hsub₁ : ∀ a ∈ ev₁, a ∈ events) (hsub₂ : ∀ a ∈ ev₂, a ∈ events)
    (hcl₁ : fullClosureRel Cq.vis ev₁) (hcl₂ : fullClosureRel Cq.vis ev₂)
    (hcT : IsCanonicalStateArbH H E W arb hP hC hA Cq (ev₁ ∩ ev₂) sT)
    (hc₁ : IsCanonicalStateArbH H E W arb hP hC hA Cq ev₁ s₁)
    (hc₂ : IsCanonicalStateArbH H E W arb hP hC hA Cq ev₂ s₂) :
    IsCanonicalStateArbH H E W arb hP hC hA Cq (ev₁ ∪ ev₂)
      ((QSig E W hP hC hA).mergeL sT s₁ s₂) := by
  obtain ⟨σT, hσT, hqT, hcsT⟩ := hcT
  obtain ⟨σ₁, hσ₁, hq₁, hcs₁⟩ := hc₁
  obtain ⟨σ₂, hσ₂, hq₂, hcs₂⟩ := hc₂
  refine ⟨D.mergeL σT σ₁ σ₂, hP.inv_mergeL σT σ₁ σ₂ hσT hσ₁ hσ₂, ?_, ?_⟩
  · rw [hqT, hq₁, hq₂]; rfl
  · exact hJoinH Cq.vis events ev₁ ev₂ σT σ₁ σ₂ hHonJ hσT hσ₁ hσ₂
      htr hir hdts hsub₁ hsub₂ hcl₁ hcl₂ hcsT hcs₁ hcs₂

/-! ## §4. The reachability invariant and the four transition lemmas -/

/-- **The conditioned arb-disciplined reachability invariant**: the structural
`GoodConfig3S` facts + a per-version arb-H-canonical witness. The arb-analog of
`GoodConfig3H.GoodConfig3H`. -/
def GoodConfig3ArbFEq (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (C : Configuration (QSig E W hP hC hA)) : Prop :=
  GoodConfig3S C ∧
  ∀ (v : Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
    C.ver v = some (s, Ev) →
    IsCanonicalStateArbH H E W arb hP hC hA (Configuration.core C) Ev s

/-- **Init.** Version `0 = (init, ∅)`, witness `[]`, needs `H []`. -/
theorem goodConfig3ArbFEq_init (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hHnil : H []) :
    GoodConfig3ArbFEq H E W arb hP hC hA (initConfig (QSig E W hP hC hA) trivial) := by
  refine ⟨GoodConfig3S.ofGood (goodConfig3_init trivial), ?_⟩
  intro v s' E' hv
  have hver : (initConfig (QSig E W hP hC hA) trivial).ver v
      = if v = 0 then some ((QSig E W hP hC hA).init, (∅ : Set (Op D.AppOp)))
        else none := rfl
  rw [hver] at hv
  by_cases hv0 : v = 0
  · rw [if_pos hv0, Option.some.injEq, Prod.mk.injEq] at hv
    rw [← hv.1, ← hv.2]
    refine ⟨D.init, hP.inv_init, rfl, ?_⟩
    exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, hHnil,
      E.equiv.refl _⟩
  · rw [if_neg hv0] at hv; simp at hv

/-- **CreateReplica.** Store and `vis` unchanged. -/
theorem goodConfig3ArbFEq_createReplica (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    {C C' : Configuration (QSig E W hP hC hA)} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3ArbFEq H E W arb hP hC hA C) :
    GoodConfig3ArbFEq H E W arb hP hC hA C' := by
  refine ⟨goodConfig3S_createReplica h_fresh hL hvis hver h.1, ?_⟩
  intro w s' E' hw
  rw [hver] at hw
  exact isCanonicalStateArbH_congr H E W arb hP hC hA
    (fun a _ b _ => by rw [core_vis, core_vis, hvis])
    (h.2 w s' E' hw)

/-- **Apply.** The fresh event extends the parent's witness (arb-agnostic re-attach),
gated on born-applicability (`hgenW`/`hqapp`) and the `H`-extension (`hHext`). -/
theorem goodConfig3ArbFEq_apply (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    {C C' : Configuration (QSig E W hP hC hA)}
    {t : Timestamp} {r : Replica} {oo : D.AppOp}
    {v : Version} {s : QState D E} {ev : Set (Op D.AppOp)}
    {vnew : Version}
    (hgenW : ∀ s' : D.State, D.applicable (t, r, oo) s' → W (t, r, oo) s')
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, oo)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, oo)))
    (hver : C'.ver = fun w => if w = vnew
      then some ((QSig E W hP hC hA).update s (t, r, oo), ev ∪ {(t, r, oo)})
      else C.ver w)
    (hqapp : qapplicable E W hA (t, r, oo) s)
    (hHext : ∀ ρ : List (Op D.AppOp), listPermOf ρ ev → H ρ →
        D.applicable (t, r, oo) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, oo)]))
    (h : GoodConfig3ArbFEq H E W arb hP hC hA C) :
    GoodConfig3ArbFEq H E W arb hP hC hA C' := by
  refine ⟨goodConfig3S_apply h_head h_ver h_fresh_t hL hvis hver h.1, ?_⟩
  set e : Op D.AppOp := (t, r, oo) with he_def
  have hco := C.head_coherent r v h_head
  have hLr : C.L r = some ev := by rw [← hco.2, h_ver]; rfl
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some ((QSig E W hP hC hA).update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_vis_old : ∀ (E' : Set (Op D.AppOp)), (∀ x ∈ E', x ∈ C.events) →
      ∀ a, a ∈ E' → ∀ b, b ∈ E' → ((C.core).vis a b ↔ (C'.core).vis a b) := by
    intro E' hsub a _ b hb
    rw [core_vis, core_vis, hvis]
    constructor
    · exact Or.inl
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
  intro w s' E' hw
  by_cases hwn : w = vnew
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    have h_old : IsCanonicalStateArbH H E W arb hP hC hA (C.core) ev s := h.2 v s ev h_ver
    have h_old' : IsCanonicalStateArbH H E W arb hP hC hA (C'.core) ev s :=
      isCanonicalStateArbH_congr H E W arb hP hC hA
        (fun a ha b hb => (h_vis_old ev h_ev_events a ha b hb).symm) h_old
    have h_ext := isCanonicalStateArbH_extend H E W arb hP hC hA hInvCong (C'.core) ev s e
      hgenW he_not_ev
      (fun x hx => by
        rw [core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
      (fun x hx => by
        rw [core_vis, hvis]
        rintro (hex | ⟨he_ev, _⟩)
        · exact h_no_vis_out x hex
        · exact he_not_ev he_ev)
      hqapp hHext h_old'
    rw [Set.union_singleton]
    exact h_ext
  · rw [hver_old w hwn] at hw
    have h_old : IsCanonicalStateArbH H E W arb hP hC hA (C.core) E' s' := h.2 w s' E' hw
    exact isCanonicalStateArbH_congr H E W arb hP hC hA
      (fun a ha b hb => (h_vis_old E' (h.1.ver_events_sub w s' E' hw) a ha b hb).symm) h_old

/-- **Merge.** The fresh version's arb-canonical state is delivered by the abstract-
arbitration `≈`-Join (`mergedArbH_of_join`, from the family's `join` VC); old
versions transfer by `vis`-congruence. Gated on the join context `hHonJ`. -/
theorem goodConfig3ArbFEq_merge (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hJoinH : EqJoinLemma3C_ArbH D E W H arb HonJ)
    {C C' : Configuration (QSig E W hP hC hA)}
    {r₁ : Replica} {v₁ v₂ vT vm : Version}
    {s₁ s₂ sT : QState D E} {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (hHonJ : HonJ (Configuration.core C).vis (Configuration.core C).events)
    (h : GoodConfig3ArbFEq H E W arb hP hC hA C) :
    GoodConfig3ArbFEq H E W arb hP hC hA C' := by
  have hcTH : IsCanonicalStateArbH H E W arb hP hC hA (C.core) (ev₁ ∩ ev₂) sT := by
    rw [← C.lca_events h_lca h_ver₁ h_ver₂ h_verT]
    exact h.2 vT sT evT h_verT
  have hcl₁f : fullClosureRel (C.core).vis ev₁ :=
    fun a b hab hb => h.1.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb
  have hcl₂f : fullClosureRel (C.core).vis ev₂ :=
    fun a b hab hb => h.1.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb
  have hsub₁ : ∀ a ∈ ev₁, a ∈ (C.core).events := h.1.ver_events_sub v₁ s₁ ev₁ h_ver₁
  have hsub₂ : ∀ a ∈ ev₂, a ∈ (C.core).events := h.1.ver_events_sub v₂ s₂ ev₂ h_ver₂
  have hdts : ∀ a b : Op D.AppOp,
      a ∈ (C.core).events → b ∈ (C.core).events → a ≠ b → a.1 ≠ b.1 := by
    intro a b ha hb hne
    obtain ⟨r, s, hLr, hsa⟩ := ha
    obtain ⟨r', s', hLr', hsb⟩ := hb
    exact (C.core).timestamps_distinct hLr hsa hLr' hsb hne
  have h_mergedH := mergedArbH_of_join H HonJ E W arb hP hC hA hJoinH (C.core)
    (C.core).events ev₁ ev₂ sT s₁ s₂ hHonJ
    (fun hab hbc => h.1.vis_trans hab hbc) (fun a ha => h.1.vis_irrefl a ha) hdts
    hsub₁ hsub₂ hcl₁f hcl₂f hcTH (h.2 v₁ s₁ ev₁ h_ver₁) (h.2 v₂ s₂ ev₂ h_ver₂)
  refine ⟨goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver h.1, ?_⟩
  have hver_new : C'.ver vm
      = some ((QSig E W hP hC hA).mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_sameH : ∀ (E' : Set (Op D.AppOp)) (s' : QState D E),
      IsCanonicalStateArbH H E W arb hP hC hA (C.core) E' s' →
      IsCanonicalStateArbH H E W arb hP hC hA (C'.core) E' s' :=
    fun E' s' hcs => isCanonicalStateArbH_congr H E W arb hP hC hA
      (fun a _ b _ => by rw [core_vis, core_vis, hvis]) hcs
  intro w s' E' hw
  by_cases hwn : w = vm
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    exact h_sameH _ _ h_mergedH
  · rw [hver_old w hwn] at hw
    exact h_sameH E' s' (h.2 w s' E' hw)

/-! ## §5. The reachability induction and THE CAPSTONE -/

open LabeledTS in
/-- **`GoodConfig3ArbFEq` from reachability.** The `GoodConfig3H` reachability
induction re-threaded over the abstract-arbitration witness, driven by the four §4
transition lemmas. Gated on the family's arb-Join (`F.join`), the join context
`hHon`, and the honest/discipline conditions `hHnil`/`hHext`/`hBA`/`hInvCong` (the
same bundle `GoodConfig3H.goodConfig3H_of_reachF` consumes, `loOnEq ↦ loOnArb … arb`). -/
theorem goodConfig3ArbFEq_of_reachF (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (arb : Op D.AppOp → Op D.AppOp → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinH : EqJoinLemma3C_ArbH D E W H arb HonJ)
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Configuration.core C₀).vis (Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    GoodConfig3ArbFEq H E W arb hP hC hA C := by
  induction hReach with
  | refl => exact goodConfig3ArbFEq_init H E W arb hP hC hA hHnil
  | tail hprev hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    have hkeep := hstep
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3ArbFEq_createReplica H E W arb hP hC hA h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C' hN hL hvis hver hhead hparents =>
      obtain ⟨hqapp, hgw⟩ := hBA hprev hkeep h_head h_ver
      exact goodConfig3ArbFEq_apply H E W arb hP hC hA hInvCong hgw
        h_head h_ver h_fresh_t h_vnew hL hvis hver hqapp
        (fun ρ hρp hH happ => hHext hprev hkeep h_head h_ver ρ hρp hH happ) ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂
        C' hN hL hvis hver hhead hparents =>
      exact goodConfig3ArbFEq_merge H HonJ E W arb hP hC hA hJoinH
        h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver (hHon hprev) ih
    | query h_s h_val => exact ih

/-- **The version-representative predicate of a QSig-configuration.** `ev`, `σ` name
a stored version whose class is `qmk E σ hσ` with event set `ev`. This is the
`versions` a reachable configuration supplies to `ConverseEq.IsRALinearizable3ArbEq`. -/
def versionsOf (E : EqEquiv D) {W : Op D.AppOp → D.State → Prop}
    {hP : InvPres D W} {hC : CongVC D E} {hA : InvInvVC D E W}
    (C : Configuration (QSig E W hP hC hA)) : Set (Op D.AppOp) → D.State → Prop :=
  fun ev σ => ∃ (v : Version) (hσ : D.Inv σ), C.ver v = some (qmk E σ hσ, ev)

open LabeledTS in
/-- **THE CONDITIONED CAPSTONE.** From an `ArbFamilyEq` (the abstract-arbitration
`≈`-Join + the free/collapsed clauses) plus the honest/discipline conditions, every
reachable `Inv`-configuration is `ConverseEq.IsRALinearizable3ArbEq` against the
family's abstraction: every stored version's representative is an `arb`-respecting
canonical fold of its event set, up to `≈`. This is the reachability lift of
`ConverseEq.ra_lin_arb_transport`, `loOn`/`rc` absent from the abstraction. -/
theorem ra_linearizable3ArbEq_of_reach
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (F : ArbFamilyEq D E W H HonJ)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Configuration.core C₀).vis (Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    IsRALinearizable3ArbEq E W (Configuration.core C).vis F.arb (versionsOf E C) := by
  have hgood := goodConfig3ArbFEq_of_reachF H HonJ E W F.arb hP hC hA hInvCong
    F.join hHon hHnil hHext hBA C hReach
  intro ev σ hv
  obtain ⟨v, hσ, hver⟩ := hv
  obtain ⟨σ', hσ', hq, hcs⟩ := hgood.2 v (qmk E σ hσ) ev hver
  have heqv : E.eqv σ σ' := (qmk_eq_iff E).mp hq
  exact isCanonicalStateArbEq_eqClosed
    (isCanonicalStateArbEq_of_H H E W _ F.arb ev σ' hcs) heqv

/-! ## §6. THE INSTANCE: `loOnEq` through the abstract engine (arb = rcArb) -/

/-- **Transport in (definitional).** The `≈`-Join `EqJoinLemma3C_H` IS the
abstract-arbitration Join at `arb = rcArb` (`loOnArb … rcArb = loOnEq`, hence
`IsCanonicalStateArbEqH … rcArb = IsCanonicalStateEqH`, hence the two Join VCs
coincide). This is the `H`-layer form of `ConverseEq.loOnEq_isArb`. -/
theorem eqJoinLemma3C_ArbH_rcArb (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ) :
    EqJoinLemma3C_ArbH D E W H (rcArb D) HonJ := hJoinH

/-- **The `loOnEq` family**: `arb = rcArb`, `join` = `EqJoinLemma3C_H`. Since
`loOnArb … rcArb = loOnEq`, this is the concrete conditioned arbitration read as one
`ArbFamilyEq`; everything stated over the abstract engine specializes to the
conditioned layer. -/
def loOnEqArbFamily (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ) : ArbFamilyEq D E W H HonJ where
  arb := rcArb D
  join := eqJoinLemma3C_ArbH_rcArb E W H HonJ hJoinH

open LabeledTS in
/-- **The conditioned RA-lin re-derived through the abstract engine.** For any
datatype supplying the `≈`-route VCs (the same bundle
`GoodConfig3H.RA_linearizable_up_to_eq_H` consumes), every reachable
`Inv`-configuration is `GoodConfig3H.IsRALinearizable3Eq`, routed through the
fully-generic `goodConfig3ArbFEq_of_reachF` at `arb = rcArb`, the linearization order
pinned by the abstract `loOnArb` and only definitionally collapsed back to `loOnEq`
(and thence the paper `lo`). Companion of
`ArbAdequacyReach.ra_linearizable3_via_capstone`. -/
theorem loOnEq_isRALinearizable3Eq_via_arb_capstone
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (H : List (Op D.AppOp) → Prop)
    (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Configuration.core C₀).vis (Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3 (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    IsRALinearizable3Eq E W hP hC hA C := by
  have hgood := goodConfig3ArbFEq_of_reachF H HonJ E W (rcArb D) hP hC hA hInvCong
    (eqJoinLemma3C_ArbH_rcArb E W H HonJ hJoinH) hHon hHnil hHext hBA C hReach
  intro v s Ev hver
  obtain ⟨σ, hσ, hq, hcs⟩ := hgood.2 v s Ev hver
  refine ⟨σ, hσ, hq, ?_⟩
  obtain ⟨ρ, hperm, hresp, _hH, hfold⟩ := hcs
  refine ⟨ρ, hperm, ?_, hfold⟩
  have h1 : respects ρ (Sal.Emulation.loOn (D := (QSig E W hP hC hA).toCRDTSig)
      (Configuration.core (D := QSig E W hP hC hA) C) Ev) :=
    (respects_congr (loOn_qsig_iff E W hP hC hA
      (Configuration.core (D := QSig E W hP hC hA) C) Ev)).mpr hresp
  exact respects_lo_of_respects_loOn
    (C := Configuration.core (D := QSig E W hP hC hA) C) h1

/-! ## §7. Axiom audit -/

#print axioms ra_linearizable3ArbEq_of_reach
#print axioms loOnEq_isRALinearizable3Eq_via_arb_capstone

end Sal.ConditionedMRDTs.ArbReachEq
