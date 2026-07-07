import Sal.MRDTs.Metatheory.Conditioned.GenericEqQuotient
import Sal.MRDTs.Metatheory.Conditioned.UpdateFeasibility_Gate

/-!
# The `≈`-metatheorem over born-applicable delivery — the `noopFeasible` layer

*Additive; modifies no existing file; 0 `sorry`.*

The `GenDisc`-free replacement for the generation-discipline threading
(`GenericEqQuotient`'s `EqJoinLemma3C` / `GDSupply`, Task A).  The pen-and-paper
analysis (`LOONA_VS_LOONEQ_ANALYSIS.md`) showed the set-level `GenDisc` (the RGA's
`GenDisc2CEq`) to be un-dischargeable from honest generation.  The honest
discipline is a PER-WITNESS one: the canonical-state enumeration is
`noopFeasible` (`applicable`-or-no-op at every prefix).  This file re-states the
`≈`-canonical state and the datatype's `≈`-Join VC carrying that clause, with the
`GenDisc` premises DELETED.

* `IsCanonicalStateEqNF` — `IsCanonicalStateEq` with a `noopFeasible` witness.
* `EqJoinLemma3C_NF` — `EqJoinLemma3C` over `IsCanonicalStateEqNF`, no `GenDisc`.

The RGA discharges `EqJoinLemma3C_NF` via `canon_fold` (`RGA_NoopFeasible_CanonFold`
+ the merge bridge); the reachability layer (`GoodConfig3NF`) supplies the
`noopFeasible` witnesses born-applicably (`appOrNoop_qsig`).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.GenericEqQuotient

open Sal.Emulation
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)

variable {D : ConditionedMRDTSig}

/-- **Canonical state up to `≈`, born-applicable.**  `IsCanonicalStateEq` with the
witnessing enumeration additionally `noopFeasible` from `D.init` — each op
`applicable`-or-no-op at its own prefix fold.  This is the clause that restricts
canonical states to honest (born-applicable) linearizations, excluding the
`loOnEq`-respecting-but-infeasible interleavings that forced `GenDisc2CEq`. -/
def IsCanonicalStateEqNF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnEq E W vis ev) ∧
    noopFeasible D ρ D.init ∧
    E.eqv (applySeq D.toCRDTSig D.init ρ) s

/-- Forget the feasibility clause: a born-applicable canonical state is a
canonical state. -/
theorem isCanonicalStateEq_of_NF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State)
    (h : IsCanonicalStateEqNF E W vis ev s) : IsCanonicalStateEq E W vis ev s := by
  obtain ⟨ρ, hperm, hresp, _, hfold⟩ := h
  exact ⟨ρ, hperm, hresp, hfold⟩

/-- **The datatype's `≈`-Join Lemma over born-applicable delivery**
(`EqJoinLemma3C_NF`).  `EqJoinLemma3C` with `IsCanonicalStateEq` replaced by
`IsCanonicalStateEqNF` and the `GenDisc` premises DELETED: the feasibility clause
in the canonical-state hypotheses now carries the honest discipline the datatype's
`canon_fold` consumes, so no separate set-level generation discipline is asserted.

`hdts` (**timestamp uniqueness on `events`**) is the ONE generic execution-model fact the datatype
Join may consume: distinct events have distinct ids. It is NOT an RDT obligation — every reachable
configuration provides it (`Configuration.timestamps_distinct`), so `RA_linearizable_up_to_eq_NF`
supplies it from the reachable config. Carrying it here (rather than re-bundling a config witness per
RDT, à la the old `GenDisc`) keeps the framework generic and the per-RDT residual minimal. -/
def EqJoinLemma3C_NF (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) : Prop :=
  ∀ (vis : Op D.AppOp → Op D.AppOp → Prop) (events : Set (Op D.AppOp))
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    D.Inv s₀ → D.Inv s₁ → D.Inv s₂ →
    (∀ {a b c : Op D.AppOp}, vis a b → vis b c → vis a c) →
    (∀ a : Op D.AppOp, ¬ vis a a) →
    (∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
    (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
    fullClosureRel vis ev₁ → fullClosureRel vis ev₂ →
    IsCanonicalStateEqNF E W vis (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateEqNF E W vis ev₁ s₁ → IsCanonicalStateEqNF E W vis ev₂ s₂ →
    IsCanonicalStateEqNF E W vis (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-! ## §1  Guard transparency for born-applicable chains

At `W := applicable`-or-stronger the guarded fold SKIPS non-`W` ops, so guard
transparency (`applySeqW = applySeq`) does NOT hold for arbitrary `WfChain`s — a
`WfOpGen`-but-inaccurate op breaks it.  It holds for **born-applicable**
(`noopFeasible`) chains for a different reason: at each step the op is either
`W` (so `doW = update`) OR a LITERAL no-op (`update s o = s`, so `doW = s =
update`).  `GuardNoopChain` is that condition; `guardNoop_of_noopFeasible`
supplies it from `noopFeasible` plus the honest `applicable ⟹ W` (which the RGA's
`WfOpGenQ` discharges: `applicable ∧ monotone ⟹ WfOpA`). -/

/-- Each step's op is `W`-well-formed OR a literal no-op at the prefix fold.
Weaker than `WfChain` (`W` need not hold at no-op steps), and exactly what a
born-applicable delivery guarantees. -/
def GuardNoopChain (D : ConditionedMRDTSig) (W : Op D.AppOp → D.State → Prop) :
    D.State → List (Op D.AppOp) → Prop
  | _, [] => True
  | s, o :: ρ => (W o s ∨ D.update s o = s) ∧ GuardNoopChain D W (D.update s o) ρ

/-- **Guard transparency for `GuardNoopChain`.**  The guarded fold is the raw fold
whenever each step is `W`-well-formed or a literal no-op: `W` fires ⟹ `doW =
update`; else the step is a no-op and `doW = s = update`. -/
theorem applySeqW_eq_applySeq_of_guardNoop {W : Op D.AppOp → D.State → Prop}
    {s : D.State} {ρ : List (Op D.AppOp)} (hc : GuardNoopChain D W s ρ) :
    applySeqW D W s ρ = applySeq D.toCRDTSig s ρ := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih =>
    obtain ⟨hstep, hrest⟩ := hc
    have hdoW : doW D W o s = D.update s o := by
      by_cases hw : W o s
      · exact if_pos hw
      · rcases hstep with hw' | hnoop
        · exact absurd hw' hw
        · rw [hnoop]; exact if_neg hw
    show applySeqW D W (doW D W o s) ρ = applySeq D.toCRDTSig (D.update s o) ρ
    rw [hdoW]; exact ih hrest

/-- A `noopFeasible` chain of ops for which `applicable ⟹ W` is a
`GuardNoopChain`: the `applicable` disjunct upgrades to `W`, the no-op disjunct is
literal. -/
theorem guardNoop_of_noopFeasible {W : Op D.AppOp → D.State → Prop}
    {ρ : List (Op D.AppOp)} {s : D.State}
    (hnf : noopFeasible D ρ s)
    (hWA : ∀ o ∈ ρ, ∀ s', D.applicable o s' → W o s') :
    GuardNoopChain D W s ρ := by
  induction ρ generalizing s with
  | nil => trivial
  | cons o rest ih =>
    obtain ⟨hstep, hrest⟩ := hnf
    refine ⟨?_, ih hrest (fun o' ho' => hWA o' (List.mem_cons_of_mem o ho'))⟩
    rcases hstep with happ | hnoop
    · exact Or.inl (hWA o (List.mem_cons_self ..) s happ)
    · exact Or.inr hnoop

/-! ## §2  The one-way bridge: born-applicable canonical state ⟹ exec-canonical

`GoodConfig3NF` carries the DATATYPE-side `IsCanonicalStateEqNF` (a `noopFeasible`
witness folding by RAW `applySeq`).  This lemma projects it to the execution
model's `IsCanonicalState` at the class `qmk E σ`, discharging the base
`GoodConfig3.canonical` field.  No `WfOpReachable` — guard transparency comes from
the witness's own `noopFeasible` (via §1), so it survives the guard switch to
`applicable` where `WfOpReachable` fails.  The reverse direction (exec ⟹ NF) is
NOT proved (and not needed): the `noopFeasible` clause is supplied at construction
(apply step, `appOrNoop_qsig`) and consumed by the datatype's `canon_fold`. -/

/-- **Born-applicable canonical state ⟹ execution-model canonical state.**  The
`noopFeasible` witness of `IsCanonicalStateEqNF` is, verbatim, an
`IsCanonicalState` witness at `qmk E σ`: guard transparency (§1, from
`noopFeasible` + `hWA : applicable ⟹ W`) turns its raw fold into the quotient's
guarded fold. -/
theorem isCanonicalState_of_NF (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (Cq : Sal.Emulation.Configuration (QSig E W hP hC hA).toCRDTSig)
    (ev : Set (Op D.AppOp))
    (hWA : ∀ o ∈ ev, ∀ s', D.applicable o s' → W o s')
    (σ : D.State) (hσ : D.Inv σ)
    (h : IsCanonicalStateEqNF E W Cq.vis ev σ) :
    Sal.Emulation.IsCanonicalState Cq ev (qmk E σ hσ) := by
  obtain ⟨ρ, hperm, hresp, hnf, hfold⟩ := h
  have hGR : applySeqW D W D.init ρ = applySeq D.toCRDTSig D.init ρ :=
    applySeqW_eq_applySeq_of_guardNoop
      (guardNoop_of_noopFeasible hnf (fun o ho => hWA o ((hperm.2 o).mp ho)))
  have heqv : E.eqv (applySeqW D W D.init ρ) σ := by rw [hGR]; exact hfold
  refine ⟨ρ, hperm,
    (respects_congr (loOn_qsig_iff E W hP hC hA Cq ev)).mpr hresp, ?_⟩
  exact (qapplySeq_init E W hP hC hA ρ).trans ((qmk_eq_iff E).mpr heqv)

/-- `noopFeasible` composes along `++`: feasible prefix from `s`, feasible suffix
from the prefix fold.  (Also the union witness `ρ₀ ++ π₀` in the merge residual.) -/
theorem noopFeasible_append {ρ₁ ρ₂ : List (Op D.AppOp)} {s : D.State}
    (h₁ : noopFeasible D ρ₁ s)
    (h₂ : noopFeasible D ρ₂ (applySeq D.toCRDTSig s ρ₁)) :
    noopFeasible D (ρ₁ ++ ρ₂) s := by
  induction ρ₁ generalizing s with
  | nil => simpa using h₂
  | cons o rest ih =>
    obtain ⟨hstep, hrest⟩ := h₁
    exact ⟨hstep, ih hrest h₂⟩

/-- `loOnEq` is ANTI-monotone in the event set: growing `ev` only shrinks the
rc-tiebreak arm (`¬∃ e₃ ∈ ev …` gets harder).  Needed for the datatype-side
canonical-state extension (append a fresh event, `ev ⊆ insert e ev`). -/
theorem loOnEq_antimono (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop) {ev ev' : Set (Op D.AppOp)}
    (hsub : ev ⊆ ev') (e₁ e₂ : Op D.AppOp) :
    loOnEq E W vis ev' e₁ e₂ → loOnEq E W vis ev e₁ e₂ := by
  rintro (h | ⟨h1, h2, h3, h4⟩)
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, fun ⟨e₃, he₃, hv, hnc⟩ => h4 ⟨e₃, hsub he₃, hv, hnc⟩⟩

/-- **Transport `IsCanonicalStateEqNF` under `vis`-agreement.**  The witness, its
`noopFeasible`, and its fold are `vis`-independent; only `respects` (via `loOnEq`)
transports.  Datatype analog of `isCanonicalState_congr`. -/
theorem isCanonicalStateEqNF_congr (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    {vis vis' : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)} {σ : D.State}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (vis' a b ↔ vis a b))
    (h : IsCanonicalStateEqNF E W vis ev σ) :
    IsCanonicalStateEqNF E W vis' ev σ := by
  obtain ⟨ρ, hp, hr, hnf, hf⟩ := h
  refine ⟨ρ, hp, ?_, hnf, hf⟩
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

/-- **The datatype-side apply extension.**  Append the fresh, `vis`-maximal event
`e` (`applicable` at `σ`) to the born-applicable canonical witness.  `respects`
survives by `loOnEq_antimono`; `noopFeasible` by `applicable`-at-the-fold
(`applicable_congr` from `happ`, using `Inv` of the fold from `hInvCong`); the fold
extends by `update_congr`.  Used at the apply step of `GoodConfig3NF`. -/
theorem isCanonicalStateEqNF_extend (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hC : CongVC D E) (hA : InvInvVC D E W)
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (vis : Op D.AppOp → Op D.AppOp → Prop) (ev : Set (Op D.AppOp))
    (σ : D.State) (hσ : D.Inv σ) (e : Op D.AppOp)
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ vis e x)
    (happ : D.applicable e σ)
    (h : IsCanonicalStateEqNF E W vis ev σ) :
    IsCanonicalStateEqNF E W vis (insert e ev) (D.update σ e) := by
  obtain ⟨ρ, hp, hr, hnf, hf⟩ := h
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
        hn (loOnEq_antimono E W vis (Set.subset_insert _ _) _ _ h')),
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    have hy_ev : y ∈ ev := (hp.2 y).mp hy
    rintro (⟨hv, _⟩ | ⟨_, h_nvis_ye, _, _⟩)
    · exact h_e_last y hy_ev hv
    · exact h_nvis_ye (h_e_sees y hy_ev)
  · exact noopFeasible_append hnf ⟨Or.inl happFold, trivial⟩
  · rw [applySeq_append_single]
    exact hC.update_congr e hInvFold hσ hf

/-! ## §4  Axiom audit -/

#print axioms isCanonicalStateEq_of_NF
#print axioms noopFeasible_append
#print axioms applySeqW_eq_applySeq_of_guardNoop
#print axioms guardNoop_of_noopFeasible
#print axioms isCanonicalState_of_NF

end Sal.Metatheory.GenericEqQuotient
