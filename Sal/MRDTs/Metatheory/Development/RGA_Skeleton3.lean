import Sal.MRDTs.Metatheory.Development.GoodConfig3H
import Sal.MRDTs.Metatheory.Development.RGA_Skeleton2

/-!
# SKELETON 3 — the RAW-≈ capstone for the tombstone-free RGA

*Additive; modifies no existing file; 0 `sorry`.*

The corrected end-to-end chain at the corrected TARGET (`IsRALinearizable3Eq` — raw datatype folds,
up to `≈`; FINDING #4 made the guarded `IsRALinearizable3` unsatisfiable) over the corrected WITNESS
discipline (`H := CanonFoldOK [] init_st` — the K2 refutation made `noopFeasible` witnesses
unsatisfiable at merge unions).

* `rgaJoinH_of_canon` — the RGA's H-join (`EqJoinLemma3C_H`) from the two canonical leaves:
  `hEnum` (K1 — a delta enum with the engine-native discipline continued from the LCA fold) and
  `hCanon` (merge and δ-fold are both the canonical state of `ρ₀ ++ π₀`).  **The union witness is
  `ρ₀ ++ π₀` itself**: its discipline is `canonFoldOK_concat` (no from-init feasibility of any
  reordering — K2 dissolved), its `respects` is the LCA-first assembly (cross edges die on the
  branch closures), its fold is the merge by canonical uniqueness (`eq_of_canonMatch2`).
* `rga_RA_linearizable_skeleton3` — **THE CAPSTONE**: reachable `C` + honest premises
  (`hBA` born-applicability, `hHext` the discipline extension at applies) + the two canonical
  leaves ⟹ `IsRALinearizable3Eq C`.  Kernel-clean, 0 `sorry`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGASkeleton3

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3H
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.Metatheory.RGAInstanceNF (rga_invCong)
open Sal.Metatheory.RGAEqJoinNF (mergeFold_transport loOnEqQ_index_free_gen)
open Sal.Metatheory.RGACorrectedResidual (canonFoldOK_concat)
open Sal.Metatheory.RGAConditionedConvergence (eq_trans)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK eq_of_canonMatch2)

/-- The RGA's delivery discipline: the engine-native per-event canonical discipline from `init`. -/
def rgaH : List op_t → Prop := fun ρ => CanonFoldOK [] init_st ρ

/-- **The RGA's H-join from the two canonical leaves.**  The union's `H`-witness is `ρ₀ ++ π₀`. -/
theorem rgaJoinH_of_canon
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          CanonFoldOK [] init_st ρ₀ →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          CanonFoldOK [] init_st ρ₁ →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          CanonFoldOK [] init_st ρ₂ →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀)
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀)) :
    EqJoinLemma3C_H RGACondSig' rgaEqEquiv' WfOpA rgaH := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hI0 hI1 hI2 htr hir hdts hev1 hev2 hcl1 hcl2 hcs0 hcs1 hcs2
  -- re-type the witnesses at `op_t` (defeq to `Op RGACondSig'.AppOp`)
  have hcs0' : ∃ ρ : List op_t,
      listPermOf ρ (ev₁ ∩ ev₂) ∧ respects ρ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) ∧
      CanonFoldOK [] init_st ρ ∧
      rgaEqEquiv'.eqv (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ) s₀ := hcs0
  have hcs1' : ∃ ρ : List op_t,
      listPermOf ρ ev₁ ∧ respects ρ (loOnEq rgaEqEquiv' WfOpA vis ev₁) ∧
      CanonFoldOK [] init_st ρ ∧
      rgaEqEquiv'.eqv (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ) s₁ := hcs1
  have hcs2' : ∃ ρ : List op_t,
      listPermOf ρ ev₂ ∧ respects ρ (loOnEq rgaEqEquiv' WfOpA vis ev₂) ∧
      CanonFoldOK [] init_st ρ ∧
      rgaEqEquiv'.eqv (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ) s₂ := hcs2
  obtain ⟨ρ₀, h₀p, h₀r, h₀OK, hfold0⟩ := hcs0'
  obtain ⟨ρ₁, h₁p, h₁r, h₁OK, hfold1⟩ := hcs1'
  obtain ⟨ρ₂, h₂p, h₂r, h₂OK, hfold2⟩ := hcs2'
  obtain ⟨π₀, hπp, hπr, hπOK⟩ :=
    hEnum vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₀r h₀OK h₁p h₁r h₁OK h₂p h₂r h₂OK
  obtain ⟨hCMmerge, hCMfold⟩ :=
    hCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₁p h₂p hπp hπr h₀OK hπOK
  -- merge = δ-fold, by canonical uniqueness
  have heq1 : eq (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
      (applySeqR (applySeqR init_st ρ₀) π₀) :=
    eq_of_canonMatch2 (ρ₀ ++ π₀) (ρ₀ ++ π₀) _ _ (fun _ => Iff.rfl) hCMmerge hCMfold
  -- transport the literal-fold identity to the ≈-classes
  have hI0' : RGACondSig'.Inv (applySeqR init_st ρ₀) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold0) hI0
  have hI1' : RGACondSig'.Inv (applySeqR init_st ρ₁) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold1) hI1
  have hI2' : RGACondSig'.Inv (applySeqR init_st ρ₂) :=
    rga_invCong (rgaEqEquiv'.equiv.symm hfold2) hI2
  have hMF : eq (applySeqR (applySeqR init_st ρ₀) π₀) (RGACondSig'.mergeL s₀ s₁ s₂) :=
    mergeFold_transport hI0' hI1' hI2' hI0 hI1 hI2 hfold0 hfold1 hfold2 heq1
  -- the union witness: ρ₀ ++ π₀ itself
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
        (fun a b => loOnEqQ_index_free_gen WfOpA vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((Sal.Metatheory.RGAEqJoinNF.loOnEqQ_reduce_gen WfOpA vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl1 b a hva haI.1, hcl2 b a hva haI.2⟩
  · -- the discipline clause: `ρ₀ ++ π₀` is CanonFoldOK from init — K2 dissolved
    show CanonFoldOK [] init_st (ρ₀ ++ π₀)
    exact canonFoldOK_concat ρ₀ [] init_st π₀ h₀OK hπOK
  · show rgaEqEquiv'.eqv
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)) (RGACondSig'.mergeL s₀ s₁ s₂)
    have hsplit : applySeq RGACondSig'.toCRDTSig RGACondSig'.init (ρ₀ ++ π₀)
        = applySeqR (applySeqR init_st ρ₀) π₀ := by
      rw [Sal.Metatheory.RGAInstanceFinal.applySeq_eq_applySeqR]
      show applySeqR RGACondSig'.init (ρ₀ ++ π₀) = _
      rw [Sal.Metatheory.RGAInstance.RGACondSig'_init]
      simp only [applySeqR, List.foldl_append]
    rw [hsplit]
    exact hMF

/-- **THE CAPSTONE (raw-≈).**  The tombstone-free RGA is per-version RA-linearizable in the
paper's sense — every version of every reachable configuration is `qmk` of a representative that
is the RAW `do_`-fold of a `lo`-respecting linearization of its events, up to observational `≈` —
gated on the explicit residual:

* `hEnum` — K1 (the delta discipline; its core is DISCHARGED: `K1_canonFoldOK` from `GenDisc2C` =
  `genDisc2C_of_born` from born accuracy);
* `hCanon` — the two canonical facts (fold half generic `canon_fold`; merge half the RGA residual);
* `hHext` — the discipline extends at born-applicable applies (`canonFoldOK_append` + honest ids);
* `hBA` — born-applicable delivery (the honest-execution premise).

0 `sorry`; axioms ⊆ {propext, Classical.choice, Quot.sound}. -/
theorem rga_RA_linearizable_skeleton3
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          CanonFoldOK [] init_st ρ₀ →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          CanonFoldOK [] init_st ρ₁ →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          CanonFoldOK [] init_st ρ₂ →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀)
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀))
    (hHext : ∀ {C₀ C₁ : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.Metatheory.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.Metatheory.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.Metatheory.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List op_t, listPermOf ρ evh → rgaH ρ →
        RGACondSig'.applicable (t, r, o) (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ) →
        rgaH (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.Metatheory.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.Metatheory.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.Metatheory.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA C :=
  RA_linearizable_up_to_eq_H rgaH rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA
    (fun heqv hInv => rga_invCong heqv hInv)
    (rgaJoinH_of_canon hEnum hCanon)
    trivial
    (fun hreach hstep hhead hver ρ hρp hH happ => hHext hreach hstep hhead hver ρ hρp hH happ)
    hBA C hReach

/-! ## Axiom audit -/

#print axioms rgaJoinH_of_canon
#print axioms rga_RA_linearizable_skeleton3

end Sal.Metatheory.RGASkeleton3
