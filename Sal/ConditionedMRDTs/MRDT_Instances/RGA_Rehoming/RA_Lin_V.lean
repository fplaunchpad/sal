import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Honest_Residual
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H_V

/-!
# RGA (rehoming) — RA-linearizability up to `≈` over the widened LTS `Step3V` (task #90)

*Additive; modifies no existing file; 0 `sorry`.*

The production capstone `rga_ra_linearizable3_eq` re-derived at every configuration
reachable in the ternary system **with the criss-cross gate lifted** — merges may resolve
a proper MCA antichain through the recursive virtual-LCA fold (`Step3V.mergeVirtual`).

What is genuinely new is all in the generic H-layer (`GoodConfig3H_V.lean`): the fold
induction consumes the RGA's `≈`-Join (`rgaJoinH_of_canon` over `rga_hEnum_discharged` +
`hCanon_of_leaves3`) at every intermediate antichain union `(E(acc), E(mᵢ))` — those
leaves were already stated for arbitrary closed event-set pairs under the ambient
`rgaHonJ`, so the K1/`GenDisc2C` route (the union restricted through
`isDepPreC_of_restrict` inside `rga_hEnum_discharged`) covers the unions verbatim.  **No
`noopFeasible` obligation appears at any union** (the probe's refutation is respected:
the H discipline `rgaH = CanonFoldOK + HonestPayloads` replaced it).

On the honesty side merges consume no honesty: `HonCore` transfers through
`mergeVirtual` by the same `honCore_merge` (it never read the LCA slot), and the
structural invariant by the same `goodConfig3S_merge` (its `sT` was always arbitrary).
`HonestDeliveryV` is `HonestDelivery` with the per-step quantification widened to
`Step3V`-reachable configurations; it implies the gated assumption
(`honestDelivery_of_honestDeliveryV`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton3

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs (Configuration Version Step3 Step3V Label3 initConfig
  labeledTS3 labeledTS3V)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA
  rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAInstanceNF (rga_invCong)
open Sal.ConditionedMRDTs.RGAK1Delta (rgaHonJ rga_hEnum_discharged
  rga_hMergeInputs_discharged loOnA_imp_vis genDisc2C_of_born)
open RGAMergeLinearization (applySeqR)

local notation "QD" => QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA
local notation "Cfg3" => Sal.ConditionedMRDTs.Configuration
  (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)
local notation "Reach3V" => LabeledTS.ReachableFrom
  (labeledTS3V (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA))
  (initConfig (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial)

/-! ## §1  The structural invariant over `Step3V` -/

/-- The structural invariant at every `Step3V`-reachable configuration: the virtual case
is `goodConfig3S_merge` verbatim (its LCA slot was always an arbitrary `sT`). -/
theorem goodConfig3S_of_reachV {C : Cfg3} (hReach : Reach3V C) : GoodConfig3S C := by
  induction hReach with
  | refl => exact GoodConfig3S.ofGood (Sal.ConditionedMRDTs.goodConfig3_init trivial)
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | base hb =>
      cases hb with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact goodConfig3S_createReplica h_fresh hL hvis hver ih
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3S_apply h_head h_ver h_fresh_t hL hvis hver ih
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver ih
      | query h_s h_val => exact ih
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver ih

/-! ## §2  The honest-delivery residual over `Step3V` -/

/-- **The honest-delivery residual, widened**: `HonestDelivery` with the per-apply-step
quantification over `Step3V`-reachable configurations (the step itself is still a
`Step3.apply` — `mergeVirtual` adds no apply steps).  Same two clauses: born accuracy and
born-applicable delivery. -/
def HonestDeliveryV : Prop :=
  ∀ {C₀ C₁ : Cfg3} {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica}
    {o : app_op_t α} {v : Sal.ConditionedMRDTs.Version}
    {sh : QState (RGACondSig' α) (rgaEqEquiv' α)} {evh : Set (Op (app_op_t α))},
    Reach3V C₀ →
    Step3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)
      C₀ (Label3.apply t r o) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    (∃ π : List (op_t α), listPermOf π evh ∧ respects π (fun a b : op_t α => C₀.vis a b) ∧
        accurate (t, r, o) (applySeqR (init_st (α := α)) π)) ∧
    qapplicable (rgaEqEquiv' α) WfOpA rgaInvInvVCA (t, r, o) sh ∧
    (∀ s', (RGACondSig' α).applicable (t, r, o) s' → WfOpA (t, r, o) s')

/-- The widened residual implies the gated one (gated reachability embeds by
`reachableV_of_reachable`): assuming `HonestDeliveryV` never weakens the old capstone. -/
theorem honestDelivery_of_honestDeliveryV (h : HonestDeliveryV (α := α)) :
    HonestDelivery (α := α) :=
  fun hreach hstep hhead hver =>
    h (Sal.ConditionedMRDTs.reachableV_of_reachable hreach) hstep hhead hver

/-- The honest-core invariant at every `Step3V`-reachable configuration — **merges
consume no honesty**: both merge cases are `honCore_merge` (events/vis bookkeeping only;
the LCA slot is never read). -/
theorem honCore_of_reachV (hHD : HonestDeliveryV (α := α)) {C : Cfg3}
    (hReach : Reach3V C) : HonCore C := by
  induction hReach with
  | refl => exact honCore_init
  | tail hpre hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | base hb =>
      have hb' := hb
      cases hb with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact honCore_createReplica h_fresh hL hvis ih
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        obtain ⟨hborn, hq, himp⟩ := hHD hpre hb' h_head h_ver
        exact honCore_apply h_head h_ver h_fresh_t hL hvis hborn
          (wfOpQ_of_hBA hq himp) ih
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact honCore_merge h_head₁ h_head₂ h_ver₁ h_ver₂ hL hvis ih
      | query h_s h_val => exact ih
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact honCore_merge h_head₁ h_head₂ h_ver₁ h_ver₂ hL hvis ih

/-- **hHon over `Step3V`, discharged**: the join context `rgaHonJ` at every
`Step3V`-reachable core — same witness (the re-typed core itself), same structural
fields, generation discipline from born accuracy via the widened `HonCore`. -/
theorem rga_hHon_dischargedV (hHD : HonestDeliveryV (α := α)) :
    ∀ {C₀ : Cfg3}, Reach3V C₀ →
      rgaHonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events := by
  intro C₀ hreach
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := honCore_of_reachV hHD hreach
  have hS := goodConfig3S_of_reachV hreach
  refine ⟨coreR C₀, ?_, ?_, hz, ?_, hd⟩
  · intro a b
    exact ⟨fun h => ⟨h, C₀.vis_src h, C₀.vis_tgt h⟩, fun h => h.1⟩
  · refine genDisc2C_of_born (coreR C₀)
      (Sal.ConditionedMRDTs.Configuration.core C₀).events lE hlE
      (fun a b ha hb' hne => ?_) hz
      (fun hab hbc => hS.vis_trans hab hbc) hS.vis_irrefl
      (fun o ho => ?_)
    · obtain ⟨ra, sa, hLa, hsa⟩ := ha
      obtain ⟨rb, sb, hLb, hsb⟩ := hb'
      exact C₀.timestamps_distinct hLa hsa hLb hsb hne
    · obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ho
      exact ⟨π, hπp,
        hπr.imp (fun hn hlo => hn (loOnA_imp_vis (coreR C₀) _ _ _ hlo)), hπacc⟩
  · exact fun a b _ _ h => C₀.causal_mono h

/-! ## §3  The honest capstone over `Step3V` -/

/-- **RGA RA-linearizability up to `≈` over the widened LTS, on the honest-delivery
residual alone.**  The datatype-side leaves are the gated theorem's, verbatim:
`rga_hEnum_discharged` (K1/`GenDisc2C` — already general in the event-set pair, so the
intermediate antichain unions of the virtual fold are instances), `hCanon_of_leaves3`,
`rga_hHext_discharged_core`. -/
theorem rga_RA_linearizable_honestV (hHD : HonestDeliveryV (α := α))
    (C : Cfg3) (hReach : Reach3V C) :
    IsRALinearizable3Eq (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA C :=
  RA_linearizable_up_to_eq_H_V rgaH rgaHonJ (rgaEqEquiv' α) WfOpA rgaInvPresA
    (rgaCongVC' α) rgaInvInvVCA
    (fun heqv hInv => rga_invCong heqv hInv)
    (rgaJoinH_of_canon rgaHonJ rga_hEnum_discharged
      (hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged))
    (fun hreach => rga_hHon_dischargedV hHD hreach)
    rgaH_nil
    (fun _hreach hstep hhead hver ρ hρp hH happ =>
      rga_hHext_discharged_core hstep hhead hver ρ hρp hH happ)
    (fun hreach hstep hhead hver => (hHD hreach hstep hhead hver).2)
    C hReach

end Sal.ConditionedMRDTs.RGASkeleton3

namespace Sal.ConditionedMRDTs

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA
  rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGASkeleton3 (HonestDeliveryV)

/-- **The rehoming RGA is RA-linearizable up to `≈` at every honestly-reachable-V
configuration** — `rga_ra_linearizable3_eq` with the criss-cross gate lifted
(`labeledTS3V`: merges may resolve a proper MCA antichain through the recursive
virtual-LCA fold), under the widened honest-delivery residual `HonestDeliveryV` (born
accuracy + born-applicable delivery, per apply step, at `Step3V`-reachable configs).
Same NB as the gated capstone: this certifies the structural fold-up-to-`≈` guarantee;
the observable read-side story is unchanged. -/
theorem rga_ra_linearizable3_eq_V
    (hHD : HonestDeliveryV (α := α))
    (C : Configuration (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA))
    (hReach : (labeledTS3V
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
      (initConfig (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA C :=
  RGASkeleton3.rga_RA_linearizable_honestV hHD C hReach

/-! ## Axiom audit -/

#print axioms RGASkeleton3.honCore_of_reachV
#print axioms RGASkeleton3.rga_hHon_dischargedV
#print axioms RGASkeleton3.honestDelivery_of_honestDeliveryV
#print axioms rga_ra_linearizable3_eq_V

end Sal.ConditionedMRDTs
