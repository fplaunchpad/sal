import Sal.ConditionedMRDTs.Development.RGA_Skeleton
import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_LoOnEq_Causal

/-!
# REFUTATION — the skeleton's `hEnum` is FALSE as stated

*Additive; modifies no existing file; 0 `sorry`.*

**Claim.** The `hEnum` hypothesis of `rga_RA_linearizable_skeleton` (`RGA_Skeleton.lean`) is
unprovable: there is a bog-standard three-op RGA execution satisfying every premise for which NO
delta enumeration is `noopFeasible` from the LCA fold.

**The execution.**  `insOpE` creates node `1`; `delOpE` deletes it; `insOnX` inserts node `3`
anchored ON node `1`, concurrent with `delOpE` (branch 1 applied `insOnX` before `delOpE`
arrived).  Then

* `ev₁ = {insOpE, insOnX, delOpE}`, `ev₂ = {insOpE, delOpE}`, LCA `= ev₁ ∩ ev₂ = ev₂`;
* every branch enum is `noopFeasible` from `init_st` and `loOnEq`-respecting
  (`ρ₁ = [insOpE, insOnX, delOpE]` applies `insOnX` while its anchor is live);
* the delta is the singleton `{insOnX}`, so `π₀ = [insOnX]` is forced;
* but `σ₀ = applySeqR init_st ρ₀` has node `1` DEAD — `insOnX` is neither `accurate`
  (anchor gone) nor a no-op (it writes id `3`).  `noopFeasible` fails.

**Why this does not break the RDT.**  The raw fold is fine: `do_ σ₀ insOnX` rehomes node `3` to
the root via its carried path (`resolve` climbs past the dead anchor), and `merge` reproduces
exactly that via `climb`.  What fails is only the BOOKKEEPING condition `noopFeasible` — the
LCA-first shape `ρ₀ ++ π₀` pre-applies LCA deletes that are concurrent with delta inserts,
destroying accuracy that no ordering freedom *within* `π₀` can restore.  The δ-A visibility
argument rules out causal `Del(x) → Ins-on-x` edges; it cannot rule out a CONCURRENT LCA delete,
because that delete is placed by the shape, not by the order.

**Consequence.**  The union-fold obligation must not demand `noopFeasible π₀` from `σ₀`.  Either
the engine premise weakens to rehome-faithfulness (the `Faithful`/`ClimbFaithful` family the
update layer already uses), or the union `CanonMatch` is produced from a from-`init` enumeration
(where `[insOpE, insOnX, delOpE]` IS feasible) and transported to the LCA-first fold by
convergence.  The proved merge bridge (`eq_merge_two_sided_eq`, `merge_fold_indep_canon`) needs
no `noopFeasible` for `π₀` — the requirement is an artifact of the canonical-engine packaging,
not of the mathematics.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAHEnumRefutation

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.UpdateFeasibilityGate (ins_del_noopFeasible contains_doDel_node1)
open Sal.ConditionedMRDTs.G2Probe (insOpE delOpE contains_doIns_self insOpE_applicable_at_init)
open Sal.ConditionedMRDTs.RGALoOnEqCausal (not_loOnEq_of_not_vis)
open Sal.ConditionedMRDTs.RGASkeleton (noopFeasible_transport rga_RA_linearizable_skeleton)
open RGAMergeLinearization (applySeqR)

/-! ## The three ops and the visibility order -/

/-- The delta insert: node `3` anchored on node `1` (path `[]`), CONCURRENT with `delOpE`. -/
def insOnX : op_t := (3, 1, app_op_t.Ins 66 [] 1)

theorem insOpE_ne_insOnX : insOpE ≠ insOnX := by decide
theorem delOpE_ne_insOnX : delOpE ≠ insOnX := by decide
theorem insOpE_ne_delOpE : insOpE ≠ delOpE := by decide

/-- Visibility: `insOpE` (the anchor's creator) precedes both other ops; `insOnX` and `delOpE`
are concurrent. -/
def visCE : op_t → op_t → Prop := fun a b => a = insOpE ∧ (b = insOnX ∨ b = delOpE)

theorem visCE_trans : ∀ {a b c : op_t}, visCE a b → visCE b c → visCE a c := by
  rintro a b c ⟨rfl, hb⟩ ⟨hb', _⟩
  exfalso
  rcases hb with rfl | rfl
  · exact insOpE_ne_insOnX hb'.symm
  · exact insOpE_ne_delOpE hb'.symm

theorem visCE_irrefl : ∀ a : op_t, ¬ visCE a a := by
  rintro a ⟨rfl, h | h⟩
  · exact insOpE_ne_insOnX h
  · exact insOpE_ne_delOpE h

/-! ## The event sets -/

def ev1CE : Set op_t := {o | o = insOpE ∨ o = insOnX ∨ o = delOpE}
def ev2CE : Set op_t := {o | o = insOpE ∨ o = delOpE}

theorem ev2_sub_ev1 : ∀ a ∈ ev2CE, a ∈ ev1CE := by
  intro a ha
  simp only [ev2CE, Set.mem_setOf_eq] at ha
  rcases ha with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

theorem ev1_closed : fullClosureRel (D := RGACondSig') visCE ev1CE := by
  intro a b hab _
  exact Or.inl hab.1

theorem ev2_closed : fullClosureRel (D := RGACondSig') visCE ev2CE := by
  intro a b hab _
  exact Or.inl hab.1

theorem inter_eq : ev1CE ∩ ev2CE = ev2CE := by
  ext a
  simp only [Set.mem_inter_iff, ev1CE, ev2CE, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inr rfl), Or.inr rfl⟩

theorem union_eq : ev1CE ∪ ev2CE = ev1CE := by
  ext a
  simp only [Set.mem_union, ev1CE, ev2CE, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact h
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · exact Or.inl

/-- The delta is the singleton `{insOnX}`. -/
theorem delta_mem (a : op_t) :
    a ∈ (ev1CE ∪ ev2CE) \ (ev1CE ∩ ev2CE) ↔ a = insOnX := by
  rw [Set.mem_diff, union_eq, inter_eq]
  simp only [ev1CE, ev2CE, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1 | h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact h1
    · exact absurd (Or.inr h1) h2
  · rintro rfl
    refine ⟨Or.inr (Or.inl rfl), ?_⟩
    rintro (h | h)
    · exact insOpE_ne_insOnX h.symm
    · exact delOpE_ne_insOnX h.symm

/-! ## The enumerations: perms and `loOnEq`-respect -/

theorem perm_ev2 : listPermOf [insOpE, delOpE] ev2CE := by
  refine ⟨by decide, fun a => ?_⟩
  constructor
  · intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr rfl
      · simp at h
  · intro ha
    simp only [ev2CE, Set.mem_setOf_eq] at ha
    rcases ha with rfl | rfl
    · simp
    · simp

theorem perm_rho0 : listPermOf [insOpE, delOpE] (ev1CE ∩ ev2CE) := inter_eq.symm ▸ perm_ev2

theorem perm_rho1 : listPermOf [insOpE, insOnX, delOpE] ev1CE := by
  refine ⟨by decide, fun a => ?_⟩
  constructor
  · intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (Or.inr rfl)
        · simp at h
  · intro ha
    simp only [ev1CE, Set.mem_setOf_eq] at ha
    rcases ha with rfl | rfl | rfl
    · simp
    · simp
    · simp

/-- `[insOpE, delOpE]` respects `loOnEq` over ANY ambient event set: the only backward pair is
`(delOpE, insOpE)`, and `¬visCE delOpE insOpE` kills it (`loOnEq ⊆ vis`). -/
theorem respects_insdel_any (ev : Set op_t) :
    respects [insOpE, delOpE] (loOnEq rgaEqEquiv' WfOpA visCE ev) := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact not_loOnEq_of_not_vis _ _ _ _ _ (fun hv => insOpE_ne_delOpE hv.1.symm)
  · simp at hb

/-- `ρ₁ = [insOpE, insOnX, delOpE]` respects `loOnEq` over any ambient set: all three backward
pairs fail visibility. -/
theorem respects_rho1_any (ev : Set op_t) :
    respects [insOpE, insOnX, delOpE] (loOnEq rgaEqEquiv' WfOpA visCE ev) := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact not_loOnEq_of_not_vis _ _ _ _ _ (fun hv => insOpE_ne_insOnX hv.1.symm)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact not_loOnEq_of_not_vis _ _ _ _ _ (fun hv => insOpE_ne_delOpE hv.1.symm)
      · simp at hb
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact not_loOnEq_of_not_vis _ _ _ _ _ (fun hv => insOpE_ne_delOpE hv.1.symm)
    · simp at hb

/-! ## Branch feasibility from `init_st` -/

/-- `ρ₀ = ρ₂ = [insOpE, delOpE]` is `noopFeasible` (transported from the `RGACondSig` fact). -/
theorem nf_rho0 : noopFeasible RGACondSig' [insOpE, delOpE] init_st := by
  rw [noopFeasible_transport]
  exact ins_del_noopFeasible

/-- Node `1`'s anchor is the root right after `insOpE`. -/
theorem anc1_after_ins : anc (do_ init_st insOpE) 1 = 0 := by
  show (sel (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 1).2 = 0
  have hdo : do_ init_st (1, 0, app_op_t.Ins 65 [] 0)
           = upd init_st 1 (65, resolve init_st (0 :: [])) := by
    simp only [do_]
  rw [hdo, lemma_SelUpd1]
  show resolve init_st (0 :: []) = 0
  rw [resolve_dead_head init_st 0 [] (by simp [init_st])]
  rfl

/-- Id `3` is fresh right after `insOpE`. -/
theorem s1_no3 : contains (do_ init_st insOpE) 3 = false := by
  show contains (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 3 = false
  have hdo : do_ init_st (1, 0, app_op_t.Ins 65 [] 0)
           = upd init_st 1 (65, resolve init_st (0 :: [])) := by
    simp only [do_]
  rw [hdo, lemma_InDomUpd1]
  simp [init_st]

/-- `insOnX` is applicable right after `insOpE`: its anchor (node `1`) is live with the claimed
(empty) chain, and its id `3` is fresh. -/
theorem insOnX_applicable_after_ins :
    accurate insOnX (do_ init_st insOpE) ∧ fresh_ts insOnX (do_ init_st insOpE) := by
  refine ⟨Or.inr ⟨?_, ?_⟩, ?_, ?_⟩
  · exact contains_doIns_self init_st 1 0 65 0 []
  · exact anc1_after_ins
  · decide
  · exact s1_no3

/-- `delOpE` is still applicable after `[insOpE, insOnX]`: node `1` is live and root-anchored
(the `insOnX` write at key `3` does not touch key `1`). -/
theorem delOpE_applicable_after_two :
    accurate delOpE (do_ (do_ init_st insOpE) insOnX)
      ∧ fresh_ts delOpE (do_ (do_ init_st insOpE) insOnX) := by
  have hdo : do_ (do_ init_st insOpE) insOnX
           = upd (do_ init_st insOpE) 3 (66, resolve (do_ init_st insOpE) (1 :: [])) := by
    simp only [insOnX, do_]
  refine ⟨Or.inr ⟨?_, ?_⟩, trivial⟩
  · show contains (do_ (do_ init_st insOpE) insOnX) 1 = true
    rw [hdo, lemma_InDomUpd1]
    have h1 : contains (do_ init_st insOpE) 1 = true :=
      contains_doIns_self init_st 1 0 65 0 []
    rw [h1]
    simp
  · show anc (do_ (do_ init_st insOpE) insOnX) 1 = 0
    show (sel (do_ (do_ init_st insOpE) insOnX) 1).2 = 0
    rw [hdo]
    have hsel : sel (upd (do_ init_st insOpE) 3 (66, resolve (do_ init_st insOpE) (1 :: []))) 1
              = sel (do_ init_st insOpE) 1 :=
      lemma_SelUpd2 (do_ init_st insOpE) 1 3 _ (by decide)
    rw [hsel]
    exact anc1_after_ins

/-- **The witnessing branch enum**: `ρ₁ = [insOpE, insOnX, delOpE]` is `noopFeasible` from
`init_st` — branch 1 applied `insOnX` while its anchor was still live. -/
theorem nf_rho1 : noopFeasible RGACondSig' [insOpE, insOnX, delOpE] init_st := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, trivial⟩
  · exact insOpE_applicable_at_init
  · exact insOnX_applicable_after_ins
  · exact delOpE_applicable_after_two

/-! ## The LCA fold kills the anchor -/

/-- The LCA fold state: node `1` created then deleted. -/
def σ0 : concrete_st := applySeqR init_st [insOpE, delOpE]

theorem sigma0_no1 : contains σ0 1 = false := by
  show contains (do_ (do_ init_st insOpE) (2, 0, app_op_t.Del [] 1)) 1 = false
  exact contains_doDel_node1 (do_ init_st insOpE) 2 0

theorem sigma0_no3 : contains σ0 3 = false := by
  show contains (do_ (do_ init_st insOpE) (2, 0, app_op_t.Del [] 1)) 3 = false
  rw [contains_doDel]
  rw [s1_no3]
  simp

/-- `insOnX` is NOT accurate at `σ0`: its anchor (node `1`) is dead. -/
theorem insOnX_not_accurate : ¬ accurate insOnX σ0 := by
  rintro (⟨h0, -⟩ | ⟨hc, -⟩)
  · exact absurd h0 (by decide)
  · have hc' : contains σ0 1 = true := hc
    rw [sigma0_no1] at hc'
    exact absurd hc' (by decide)

/-- `insOnX` is NOT a no-op at `σ0`: it writes the fresh id `3`. -/
theorem insOnX_not_noop : RGACondSig'.update σ0 insOnX ≠ σ0 := by
  intro h
  have h3 : contains (do_ σ0 insOnX) 3 = true := contains_doIns_self σ0 3 1 66 1 []
  have hupd : RGACondSig'.update σ0 insOnX = do_ σ0 insOnX := rfl
  rw [hupd] at h
  rw [h, sigma0_no3] at h3
  exact absurd h3 (by decide)

/-- Yet the RAW fold is perfectly fine: `do_ σ0 insOnX` rehomes node `3` to the root via the
carried path — the tombstone-free design working exactly as intended.  Only the bookkeeping
condition fails. -/
theorem raw_fold_rehomes : sel (do_ σ0 insOnX) 3 = (66, 0) := by
  have hdo : do_ σ0 insOnX = upd σ0 3 (66, resolve σ0 (1 :: [])) := by
    simp only [insOnX, do_]
  rw [hdo, lemma_SelUpd1]
  have hres : resolve σ0 (1 :: []) = resolve σ0 [] :=
    resolve_dead_head σ0 1 [] sigma0_no1
  rw [hres]
  rfl

/-! ## The forced delta enum -/

/-- Any perm of the delta is exactly `[insOnX]`. -/
theorem pi_forced (π : List op_t)
    (h : listPermOf π ((ev1CE ∪ ev2CE) \ (ev1CE ∩ ev2CE))) : π = [insOnX] := by
  obtain ⟨hnd, hmem⟩ := h
  have hall : ∀ a ∈ π, a = insOnX := fun a ha => (delta_mem a).mp ((hmem a).mp ha)
  have hin : insOnX ∈ π := (hmem insOnX).mpr ((delta_mem insOnX).mpr rfl)
  cases π with
  | nil => simp at hin
  | cons hd tl =>
    have hh : hd = insOnX := hall hd (by simp)
    subst hh
    cases tl with
    | nil => rfl
    | cons hd2 tl2 =>
      have h2 : hd2 = insOnX := hall hd2 (by simp)
      subst h2
      simp [List.nodup_cons] at hnd

/-! ## The refutation -/

/-- The `hEnum` hypothesis of `rga_RA_linearizable_skeleton`, verbatim
(`RGA_Skeleton.lean:154-167`). -/
def HEnumStatement : Prop :=
  ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
      (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
      (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
      fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
      listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
        noopFeasible RGACondSig' ρ₀ init_st →
      listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
        noopFeasible RGACondSig' ρ₁ init_st →
      listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
        noopFeasible RGACondSig' ρ₂ init_st →
      ∃ π₀ : List op_t,
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀)

/-- Guard: `HEnumStatement` IS the skeleton's `hEnum` slot — this partial application
typechecks only if the types agree. -/
noncomputable def _guardSlot (h : HEnumStatement) :=
  rga_RA_linearizable_skeleton h

/-- **`hEnum` is FALSE.**  The three-op execution satisfies every premise; the forced
`π₀ = [insOnX]` is neither applicable (dead anchor at `σ0`) nor a no-op (fresh id). -/
theorem hEnum_refuted : ¬ HEnumStatement := by
  intro h
  obtain ⟨π₀, hperm, -, hnf⟩ :=
    h visCE ev1CE ev1CE ev2CE [insOpE, delOpE] [insOpE, insOnX, delOpE] [insOpE, delOpE]
      visCE_trans visCE_irrefl (fun _ ha => ha) ev2_sub_ev1
      ev1_closed ev2_closed
      perm_rho0 (respects_insdel_any _) nf_rho0
      perm_rho1 (respects_rho1_any _) nf_rho1
      perm_ev2 (respects_insdel_any _) nf_rho0
  have hπ : π₀ = [insOnX] := pi_forced π₀ hperm
  subst hπ
  obtain ⟨hd, -⟩ := hnf
  rcases hd with happ | hnoop
  · exact insOnX_not_accurate happ.1
  · exact insOnX_not_noop hnoop

#print axioms hEnum_refuted

end Sal.ConditionedMRDTs.RGAHEnumRefutation
