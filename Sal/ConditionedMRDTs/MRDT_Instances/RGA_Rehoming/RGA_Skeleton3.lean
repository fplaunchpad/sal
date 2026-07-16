import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_EqJoin_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Corrected_Residual

/-!
# SKELETON 3 — the RAW-≈ capstone for the tombstone-free RGA

*Additive; modifies no existing file; 0 `sorry`.*

The corrected end-to-end chain at the corrected TARGET (`IsRALinearizable3Eq` — raw datatype folds,
up to `≈`; FINDING #4 made the guarded `IsRALinearizable3` unsatisfiable) over the corrected WITNESS
discipline (`H := CanonFoldOK [] (init_st (α := α))` — the K2 refutation made `noopFeasible` witnesses
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
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton3

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAInstanceNF (rga_invCong)
open Sal.ConditionedMRDTs.RGAEqJoinNF (mergeFold_transport loOnEqQ_index_free_gen)
open Sal.ConditionedMRDTs.RGACorrectedResidual (canonFoldOK_concat)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (eq_trans)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK eq_of_canonMatch2)

/-- **Payload honesty** — SET-level, hence perm-invariant: every delete's target and every
insert's recorded-chain entry is the root or inserted in the list.  `CanonFoldOK` alone cannot
supply this (`DelOK`/`ChainOK` constrain only LIVE data, so dead-target deletes and junk chain
entries are fold-admissible), yet extending the discipline at a fresh apply needs it: the new
insert's id must not collide with any recorded dead id. -/
def HonestPayloads (ρ : List (op_t α)) : Prop :=
  (∀ (t r x : ℕ) (p : List ℕ), (t, r, app_op_t.Del p x) ∈ ρ →
      x = 0 ∨ RGACanonConvergence.insertedIn ρ x) ∧
  (∀ (t r : ℕ) (e : α) (a : ℕ) (p : List ℕ), (t, r, app_op_t.Ins e p a) ∈ ρ →
      ∀ c ∈ a :: p, c = 0 ∨ RGACanonConvergence.insertedIn ρ c)

/-- The RGA's delivery discipline: the engine-native per-event canonical discipline from `init`,
plus payload honesty (what the extension at fresh applies genuinely needs). -/
def rgaH : List (op_t α) → Prop := fun ρ => CanonFoldOK [] (init_st (α := α)) ρ ∧ HonestPayloads ρ

theorem rgaH_nil : rgaH ([] : List (op_t α)) :=
  ⟨trivial, fun _ _ _ _ h => absurd h (by simp),
    fun _ _ _ _ _ h => absurd h (by simp)⟩

/-- **The RGA's H-join from the two canonical leaves.**  The union's `H`-witness is `ρ₀ ++ π₀`. -/
theorem rgaJoinH_of_canon
    (HonJ : (op_t α → op_t α → Prop) → Set (op_t α) → Prop)
    (hEnum : ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq (rgaEqEquiv' α) WfOpA vis (ev₁ ∩ ev₂)) →
          CanonFoldOK [] (init_st (α := α)) ρ₀ →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₁) →
          CanonFoldOK [] (init_st (α := α)) ρ₁ →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₂) →
          CanonFoldOK [] (init_st (α := α)) ρ₂ →
        ∃ π₀ : List (op_t α),
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀)
    (hCanon : ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] (init_st (α := α)) ρ₀ → CanonFoldOK [] (init_st (α := α)) ρ₁ → CanonFoldOK [] (init_st (α := α)) ρ₂ →
        CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀)) :
    EqJoinLemma3C_H (RGACondSig' α) (rgaEqEquiv' α) WfOpA rgaH HonJ := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hHonJ hI0 hI1 hI2 htr hir hdts hev1 hev2 hcl1 hcl2 hcs0 hcs1 hcs2
  -- re-type the witnesses at `op_t α` (defeq to `Op (RGACondSig' α).AppOp`)
  have hcs0' : ∃ ρ : List (op_t α),
      listPermOf ρ (ev₁ ∩ ev₂) ∧ respects ρ (loOnEq (rgaEqEquiv' α) WfOpA vis (ev₁ ∩ ev₂)) ∧
      (CanonFoldOK [] (init_st (α := α)) ρ ∧ HonestPayloads ρ) ∧
      (rgaEqEquiv' α).eqv (applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init ρ) s₀ := hcs0
  have hcs1' : ∃ ρ : List (op_t α),
      listPermOf ρ ev₁ ∧ respects ρ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₁) ∧
      (CanonFoldOK [] (init_st (α := α)) ρ ∧ HonestPayloads ρ) ∧
      (rgaEqEquiv' α).eqv (applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init ρ) s₁ := hcs1
  have hcs2' : ∃ ρ : List (op_t α),
      listPermOf ρ ev₂ ∧ respects ρ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₂) ∧
      (CanonFoldOK [] (init_st (α := α)) ρ ∧ HonestPayloads ρ) ∧
      (rgaEqEquiv' α).eqv (applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init ρ) s₂ := hcs2
  obtain ⟨ρ₀, h₀p, h₀r, ⟨h₀OK, _h₀HP⟩, hfold0⟩ := hcs0'
  obtain ⟨ρ₁, h₁p, h₁r, ⟨h₁OK, h₁HP⟩, hfold1⟩ := hcs1'
  obtain ⟨ρ₂, h₂p, h₂r, ⟨h₂OK, h₂HP⟩, hfold2⟩ := hcs2'
  obtain ⟨π₀, hπp, hπr, hπOK⟩ :=
    hEnum vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ hHonJ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₀r h₀OK h₁p h₁r h₁OK h₂p h₂r h₂OK
  obtain ⟨hCMmerge, hCMfold⟩ :=
    hCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ hHonJ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₁p h₂p hπp hπr h₀OK h₁OK h₂OK hπOK
  -- merge = δ-fold, by canonical uniqueness
  have heq1 : eq (merge (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂))
      (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀) :=
    eq_of_canonMatch2 (ρ₀ ++ π₀) (ρ₀ ++ π₀) _ _ (fun _ => Iff.rfl) hCMmerge hCMfold
  -- transport the literal-fold identity to the ≈-classes
  have hI0' : (RGACondSig' α).Inv (applySeqR (init_st (α := α)) ρ₀) :=
    rga_invCong ((rgaEqEquiv' α).equiv.symm hfold0) hI0
  have hI1' : (RGACondSig' α).Inv (applySeqR (init_st (α := α)) ρ₁) :=
    rga_invCong ((rgaEqEquiv' α).equiv.symm hfold1) hI1
  have hI2' : (RGACondSig' α).Inv (applySeqR (init_st (α := α)) ρ₂) :=
    rga_invCong ((rgaEqEquiv' α).equiv.symm hfold2) hI2
  have hMF : eq (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀) ((RGACondSig' α).mergeL s₀ s₁ s₂) :=
    mergeFold_transport hI0' hI1' hI2' hI0 hI1 hI2 hfold0 hfold1 hfold2 heq1
  -- the union witness: ρ₀ ++ π₀ itself
  have hmemρ : ∀ a ∈ ρ₀, a ∈ ev₁ ∩ ev₂ := fun a ha => (h₀p.2 a).mp ha
  have hmemπ : ∀ a ∈ π₀, a ∈ (ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂) :=
    fun a ha => (hπp.2 a).mp ha
  have hFmem : ∀ a : op_t α, a ∈ ρ₀ ++ π₀ ↔ a ∈ ev₁ ∪ ev₂ := by
    intro a
    constructor
    · intro ha
      rcases List.mem_append.mp ha with h | h
      · exact Set.mem_union_left _ (hmemρ a h).1
      · exact (hmemπ a h).1
    · intro ha
      by_cases hI : a ∈ ev₁ ∩ ev₂
      · exact List.mem_append.mpr (Or.inl ((h₀p.2 a).mpr hI))
      · exact List.mem_append.mpr (Or.inr ((hπp.2 a).mpr ⟨ha, hI⟩))
  -- payload honesty at the union: branchwise, lifted along the memberships
  have hsplitmem : ∀ x : op_t α, x ∈ ρ₀ ++ π₀ → x ∈ ρ₁ ∨ x ∈ ρ₂ := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ((h₁p.2 x).mpr (hmemρ x h).1)
    · rcases (hmemπ x h).1 with h1 | h2
      · exact Or.inl ((h₁p.2 x).mpr h1)
      · exact Or.inr ((h₂p.2 x).mpr h2)
  have hlift1 : ∀ x : ℕ, RGACanonConvergence.insertedIn ρ₁ x →
      RGACanonConvergence.insertedIn (ρ₀ ++ π₀) x := by
    rintro x ⟨r', e', p', a', hm'⟩
    exact ⟨r', e', p', a',
      (hFmem _).mpr (Set.mem_union_left _ ((h₁p.2 _).mp hm'))⟩
  have hlift2 : ∀ x : ℕ, RGACanonConvergence.insertedIn ρ₂ x →
      RGACanonConvergence.insertedIn (ρ₀ ++ π₀) x := by
    rintro x ⟨r', e', p', a', hm'⟩
    exact ⟨r', e', p', a',
      (hFmem _).mpr (Set.mem_union_right _ ((h₂p.2 _).mp hm'))⟩
  refine ⟨ρ₀ ++ π₀, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨h₀p.1, hπp.1, ?_⟩
    intro a ha b hb heq
    exact (hmemπ b hb).2 (heq ▸ hmemρ a ha)
  · exact hFmem
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen WfOpA vis (ev₁ ∩ ev₂) (ev₁ ∪ ev₂) a b)).mp h₀r
    · exact (respects_congr
        (fun a b => loOnEqQ_index_free_gen WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))
          (ev₁ ∪ ev₂) a b)).mp hπr
    · intro a ha b hb hR
      have hva := ((Sal.ConditionedMRDTs.RGAEqJoinNF.loOnEqQ_reduce_gen WfOpA vis (ev₁ ∪ ev₂) b a).mp hR).1
      have haI := hmemρ a ha
      exact (hmemπ b hb).2 ⟨hcl1 b a hva haI.1, hcl2 b a hva haI.2⟩
  · -- the discipline clause: `ρ₀ ++ π₀` is CanonFoldOK from init (K2 dissolved), and its
    -- payload honesty lifts branchwise (HonestPayloads is set-level)
    show rgaH (ρ₀ ++ π₀)
    refine ⟨canonFoldOK_concat ρ₀ [] (init_st (α := α)) π₀ h₀OK hπOK, ?_, ?_⟩
    · intro t r x p hm
      rcases hsplitmem _ hm with h1 | h2
      · rcases h₁HP.1 t r x p h1 with h0 | hins
        · exact Or.inl h0
        · exact Or.inr (hlift1 x hins)
      · rcases h₂HP.1 t r x p h2 with h0 | hins
        · exact Or.inl h0
        · exact Or.inr (hlift2 x hins)
    · intro t r e a p hm c hc
      rcases hsplitmem _ hm with h1 | h2
      · rcases h₁HP.2 t r e a p h1 c hc with h0 | hins
        · exact Or.inl h0
        · exact Or.inr (hlift1 c hins)
      · rcases h₂HP.2 t r e a p h2 c hc with h0 | hins
        · exact Or.inl h0
        · exact Or.inr (hlift2 c hins)
  · show (rgaEqEquiv' α).eqv
      (applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init (ρ₀ ++ π₀)) ((RGACondSig' α).mergeL s₀ s₁ s₂)
    have hsplit : applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init (ρ₀ ++ π₀)
        = applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀ := by
      rw [Sal.ConditionedMRDTs.RGAInstanceFinal.applySeq_eq_applySeqR]
      show applySeqR (RGACondSig' α).init (ρ₀ ++ π₀) = _
      rw [Sal.ConditionedMRDTs.RGAInstance.RGACondSig'_init]
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
    (HonJ : (op_t α → op_t α → Prop) → Set (op_t α) → Prop)
    (hHon : ∀ {C₀ : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)},
      (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C₀ →
      HonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hEnum : ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq (rgaEqEquiv' α) WfOpA vis (ev₁ ∩ ev₂)) →
          CanonFoldOK [] (init_st (α := α)) ρ₀ →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₁) →
          CanonFoldOK [] (init_st (α := α)) ρ₁ →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq (rgaEqEquiv' α) WfOpA vis ev₂) →
          CanonFoldOK [] (init_st (α := α)) ρ₂ →
        ∃ π₀ : List (op_t α),
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀)
    (hCanon : ∀ (vis : op_t α → op_t α → Prop) (events ev₁ ev₂ : Set (op_t α)) (ρ₀ ρ₁ ρ₂ π₀ : List (op_t α)),
        HonJ vis events →
        (∀ {a b c : op_t α}, vis a b → vis b c → vis a c) → (∀ a : op_t α, ¬ vis a a) →
        (∀ a b : op_t α, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := (RGACondSig' α)) vis ev₁ → fullClosureRel (D := (RGACondSig' α)) vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq (rgaEqEquiv' α) WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] (init_st (α := α)) ρ₀ → CanonFoldOK [] (init_st (α := α)) ρ₁ → CanonFoldOK [] (init_st (α := α)) ρ₂ →
        CanonFoldOK ρ₀ (applySeqR (init_st (α := α)) ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR (init_st (α := α)) ρ₀) (applySeqR (init_st (α := α)) ρ₁) (applySeqR (init_st (α := α)) ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR (init_st (α := α)) ρ₀) π₀))
    (hHext : ∀ {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t α}
      {v : Sal.ConditionedMRDTs.Version}
      {sh : QState (RGACondSig' α) (rgaEqEquiv' α)} {evh : Set (Op (app_op_t α))},
      (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C₀ →
      Sal.ConditionedMRDTs.Step3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)
        C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (op_t α), listPermOf ρ evh → rgaH ρ →
        (RGACondSig' α).applicable (t, r, o) (applySeq (RGACondSig' α).toCRDTSig (RGACondSig' α).init ρ) →
        rgaH (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t α}
      {v : Sal.ConditionedMRDTs.Version}
      {sh : QState (RGACondSig' α) (rgaEqEquiv' α)} {evh : Set (Op (app_op_t α))},
      (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C₀ →
      Sal.ConditionedMRDTs.Step3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)
        C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable (rgaEqEquiv' α) WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', (RGACondSig' α).applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA))
    (hReach : (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA C :=
  RA_linearizable_up_to_eq_H rgaH HonJ (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA
    (fun heqv hInv => rga_invCong heqv hInv)
    (rgaJoinH_of_canon HonJ hEnum hCanon)
    (fun hreach => hHon hreach)
    rgaH_nil
    (fun hreach hstep hhead hver ρ hρp hH happ => hHext hreach hstep hhead hver ρ hρp hH happ)
    hBA C hReach

/-! ## Axiom audit -/

#print axioms rgaJoinH_of_canon
#print axioms rga_RA_linearizable_skeleton3

end Sal.ConditionedMRDTs.RGASkeleton3
