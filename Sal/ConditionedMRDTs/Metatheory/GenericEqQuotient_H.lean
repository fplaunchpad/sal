import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_NF

/-!
# The H-parameterized canonical witness — feasibility clause replaced by a delivery discipline

*Additive; modifies no existing file; 0 `sorry`.*

The K2 refutation (`AgentNotes.md`, criss-cross rehoming) shows `IsCanonicalStateEqNF`'s
`noopFeasible` clause is UNSATISFIABLE at merge unions for the tombstone-free RGA: two branches
can record incompatible delete-orders in their survivors' parents, and no single born-applicable
sequence replays both.  The clause was never what consumers needed — it fed (a) the join residual's
premises and (b) guard transparency for the final (guarded) extraction, and the guarded extraction
target is itself unsatisfiable (FINDING #4).

This file re-parameterizes the datatype-side witness by an abstract per-datatype **delivery
discipline** `H : List (Op D.AppOp) → Prop` (for the RGA: `CanonFoldOK [] init_st` — the
engine-native, rehome-tolerant discipline, which merge unions DO satisfy via `canonFoldOK_concat`):

* `IsCanonicalStateEqH` — `IsCanonicalStateEq` + the `H` clause (mirror of `IsCanonicalStateEqNF`
  with `noopFeasible D · D.init ↦ H ·`).
* `EqJoinLemma3C_H` — the datatype's `≈`-Join Lemma over `H`-disciplined witnesses.
* `isCanonicalStateEqH_congr` / `isCanonicalStateEqH_extend` — the two transport lemmas the
  reachability induction needs; the extension takes the `H`-extension fact as an explicit
  hypothesis (`hHext` — for the RGA: `canonFoldOK_append` from born accuracy).
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.GenericEqQuotient

open Sal.Emulation

variable {D : ConditionedMRDTSig}

/-- **Canonical state up to `≈`, `H`-disciplined.**  `IsCanonicalStateEq` with the witnessing
enumeration additionally satisfying the datatype's delivery discipline `H`. -/
def IsCanonicalStateEqH (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ ρ : List (Op D.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOnEq E W vis ev) ∧
    H ρ ∧
    E.eqv (applySeq D.toCRDTSig D.init ρ) s

/-- Forget the discipline clause: an `H`-disciplined canonical state is a canonical state. -/
theorem isCanonicalStateEq_of_H (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (vis : Op D.AppOp → Op D.AppOp → Prop)
    (ev : Set (Op D.AppOp)) (s : D.State)
    (h : IsCanonicalStateEqH H E W vis ev s) : IsCanonicalStateEq E W vis ev s := by
  obtain ⟨ρ, hperm, hresp, _, hfold⟩ := h
  exact ⟨ρ, hperm, hresp, hfold⟩

/-- **The datatype's `≈`-Join Lemma over `H`-disciplined delivery.**  `EqJoinLemma3C_NF` with
`IsCanonicalStateEqNF` replaced by `IsCanonicalStateEqH`, and an abstract JOIN CONTEXT `HonJ`
(honest facts about the ambient visibility/event universe — e.g. same-replica `vis`-totality,
nonzero ids, the generation discipline — that a reachable configuration supplies and the RDT's
join discharge may consume). -/
def EqJoinLemma3C_H (D : ConditionedMRDTSig) (E : EqEquiv D)
    (W : Op D.AppOp → D.State → Prop) (H : List (Op D.AppOp) → Prop)
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
    IsCanonicalStateEqH H E W vis (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateEqH H E W vis ev₁ s₁ → IsCanonicalStateEqH H E W vis ev₂ s₂ →
    IsCanonicalStateEqH H E W vis (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- **Transport `IsCanonicalStateEqH` under `vis`-agreement.**  The witness, its discipline, and
its fold are `vis`-independent; only `respects` (via `loOnEq`) transports. -/
theorem isCanonicalStateEqH_congr (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    {vis vis' : Op D.AppOp → Op D.AppOp → Prop} {ev : Set (Op D.AppOp)} {σ : D.State}
    (h_vis : ∀ a ∈ ev, ∀ b ∈ ev, (vis' a b ↔ vis a b))
    (h : IsCanonicalStateEqH H E W vis ev σ) :
    IsCanonicalStateEqH H E W vis' ev σ := by
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

/-- **The `H`-disciplined apply extension.**  As `isCanonicalStateEqNF_extend`, with the
discipline extension supplied by `hHext` (for the RGA: `canonFoldOK_append` — the appended op is
`applicable` at the witness fold, hence `accurate` there, hence `CanonStepOK`). -/
theorem isCanonicalStateEqH_extend (H : List (Op D.AppOp) → Prop)
    (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
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
    (h : IsCanonicalStateEqH H E W vis ev σ) :
    IsCanonicalStateEqH H E W vis (insert e ev) (D.update σ e) := by
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
        hn (loOnEq_antimono E W vis (Set.subset_insert _ _) _ _ h')),
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

/-! ## Axiom audit -/

#print axioms isCanonicalStateEq_of_H
#print axioms isCanonicalStateEqH_congr
#print axioms isCanonicalStateEqH_extend

end Sal.ConditionedMRDTs.GenericEqQuotient
