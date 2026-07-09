import Sal.ConditionedMRDTs.Metatheory.ProductEq
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RA_Lin
import Sal.ConditionedMRDTs.MRDT_Instances.PeritextTF.MarkStore

/-!
# The supply rerun — the RGA's honesty supplies over the PRODUCT LTS

*The cost center of the Peritext composite* (memo
`Development/COMPOSITION_PENPAPER.md` §2.5.6): the RGA's reachability-derived
supplies (`hHon` = the join context `rgaHonJ` at every reachable core; the
freshness half of `hHext`) were discharged by induction over the RGA's OWN
`Step3` (`RGA_TombstoneFree/RGA_Honest_Residual.lean`), and reachability does
not project (memo §2.1.4) — so they must be re-derived over the product LTS
`PeritextTF := RGA_TF ⊗ MarkStore`. The rerun's verdict, file-checked:

* **`inl`-apply steps affect the `proj₁` fragment of `(vis, events)` exactly
  as RGA-apply steps do** — `honCoreP_apply_inl` is the RGA's
  `honCore_apply` with events/`vis` read through `inlOp`;
* **every other step is a stutter for the fragment** — `inr`-applies add an
  `inr` event and only `… ∧ b = (t,r,inr o₂)` vis-edges, neither of which the
  `inl` fragment sees (`honCoreP_apply_inr`); createReplica/merge/query
  preserve `(vis, events)` outright (`honCoreP_transfer`);
* the **content lemmas are re-consumed, not re-proved**: `genDisc2C_of_born`,
  `loOnA_imp_vis`, `insertedIn_of_contains_fold`, `chainOK_of_accurate`,
  `delOK_of_accurate`, `canonFoldOK_append`, `canon_fold` are all imported
  from the RGA chain and applied at the re-typed projected core `coreP₁`
  (the `coreR` trick of `RGA_Honest_Residual` §1, composed with the
  `projCore₁` field transfers of `Metatheory/Product.lean` §O4);
* the RGA's `hHext` discharge (`RGA_HHext_Discharge`) used its reachability
  hypothesis for exactly ONE fact — stored timestamp freshness. Its body is
  otherwise config-free, so it is restated here as `rgaH_extend_of_fresh`
  (freshness over the witness list as a hypothesis) and the product `hHext`
  extracts the freshness from the product step's own `h_fresh_store` field.

The single behavioural assumption is `PeritextHonestDelivery` — the RGA's
`HonestDelivery` read through `proj₁` (memo §4 item 3): per `inl`-apply step,
born accuracy against a causal fold of the `inl` fragment of the head events,
plus born-applicable delivery. **Mark applies are unguarded**: their
`qapplicable` obligation is discharged outright (`applicable₂ = ⊤`), so the
composite assumes nothing about mark delivery.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.PeritextTF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.ProductEq
open Sal.ConditionedMRDTs (Configuration Version Step3 Label3 initConfig labeledTS3
  prodSig inlOp inrOp evRes₁ projList₁ mem_projList₁ listPermOf_projList₁
  inlOp_injective applySeq_prod projList₁_append)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA
  rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.RGAK1Delta (rgaHonJ loOnA_imp_vis genDisc2C_of_born pastE)
open Sal.ConditionedMRDTs.RGACanonFoldOK (GenDisc2C insertedIn_of_contains_fold
  canonFoldOK_append)
open Sal.ConditionedMRDTs.RGASkeleton3 (rgaH rgaH_nil HonestPayloads)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonInv CanonStepOK CanonFoldOK insertedIn)

/-- The product op payload: RGA character ops on the left, mark ops on the
right. -/
abbrev PAppOp : Type := app_op_t ⊕ MarkOp

/-- Product events. -/
abbrev POp : Type := Op PAppOp

local notation "PQD" => Sal.ConditionedMRDTs.ProductEq.prodQSig
  rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT
local notation "PCfg" => Sal.ConditionedMRDTs.Configuration
  (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT)
local notation "PReach" => LabeledTS.ReachableFrom
  (Sal.ConditionedMRDTs.labeledTS3 (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT))
  (Sal.ConditionedMRDTs.initConfig (Sal.ConditionedMRDTs.ProductEq.prodQSig
    rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA markInvT) trivial)

/-! ## §0  Small bricks -/

private theorem updateRep_self {α} (f : Replica → Option α) (r : Replica) (x : α) :
    updateRep f r x r = some x := by simp [updateRep]

private theorem updateRep_other {α} (f : Replica → Option α) {r r' : Replica} (x : α)
    (h : r' ≠ r) : updateRep f r x r' = f r' := by simp [updateRep, h]

/-! ## §1  The honest-delivery residual, read through `proj₁`

The RGA's `HonestDelivery` relativized to the product LTS (memo §4 item 3):
only `inl` (character) applies are constrained — born accuracy against a
causal fold of the `inl` fragment of the head version's events (the issuing
replica's RGA component IS that fold), `qapplicable` delivery at the head
class, and `applicable ⟹ WfOpA` for the delivered op. Mark applies carry no
assumption. -/
def PeritextHonestDelivery : Prop :=
  ∀ {C₀ C₁ : PCfg} {t : Timestamp} {r : Replica} {o₁ : app_op_t}
    {v : Version}
    {sh : QState (prodSig RGACondSig' MarkStore) (prodEqEquiv rgaEqEquiv')}
    {evh : Set POp},
    PReach C₀ →
    Step3 PQD C₀ (Label3.apply t r (Sum.inl o₁)) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    (∃ π : List op_t, listPermOf π (evRes₁ evh) ∧
        respects π (fun a b : op_t => C₀.vis (inlOp a) (inlOp b)) ∧
        accurate (t, r, o₁) (applySeqR init_st π)) ∧
    qapplicable (prodEqEquiv rgaEqEquiv') (prodW WfOpA)
      (prodInvInvVC rgaEqEquiv' WfOpA rgaInvInvVCA) (t, r, Sum.inl o₁) sh ∧
    (∀ s' : concrete_st, RGACondSig'.applicable (t, r, o₁) s' → WfOpA (t, r, o₁) s')

/-- The delivered `inl` op is `WfOpQ` somewhere: extract a representative of
the head class from the delivery clauses (the product analogue of
`RGA_Honest_Residual.wfOpQ_of_hBA` — the representative is a product state,
and its first component witnesses). -/
theorem wfOpQ_of_hBA_P {t : ℕ} {r : ℕ} {o₁ : app_op_t}
    {sh : QState (prodSig RGACondSig' MarkStore) (prodEqEquiv rgaEqEquiv')}
    (hq : qapplicable (prodEqEquiv rgaEqEquiv') (prodW WfOpA)
      (prodInvInvVC rgaEqEquiv' WfOpA rgaInvInvVCA) (t, r, Sum.inl o₁) sh)
    (himp : ∀ s' : concrete_st,
      RGACondSig'.applicable (t, r, o₁) s' → WfOpA (t, r, o₁) s') :
    ∃ σ : concrete_st, WfOpQ (t, r, o₁) σ := by
  obtain ⟨⟨σ, _hσ⟩, hrep⟩ := Quotient.exists_rep sh
  rw [← hrep] at hq
  have happ : RGACondSig'.applicable (t, r, o₁) σ.1 := hq
  exact ⟨σ.1, (himp σ.1 happ).1⟩

/-! ## §2  The structural invariant at every product-reachable configuration -/

theorem goodConfig3SP_of_reach {C : PCfg} (hReach : PReach C) : GoodConfig3S C := by
  induction hReach with
  | refl => exact GoodConfig3S.ofGood (Sal.ConditionedMRDTs.goodConfig3_init trivial)
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3S_createReplica h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3S_apply h_head h_ver h_fresh_t hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver ih
    | query h_s h_val => exact ih

/-! ## §3  Event-universe computations, per step shape -/

private theorem events_createReplica {C C' : PCfg} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅) :
    ∀ e : POp, e ∈ C'.events ↔ e ∈ C.events := by
  intro e
  constructor
  · rintro ⟨r', s', hLs, hse⟩
    rw [hL] at hLs
    by_cases hr : r' = r
    · subst hr
      rw [updateRep_self] at hLs
      injection hLs with hs
      subst hs
      exact hse.elim
    · rw [updateRep_other _ _ hr] at hLs
      exact ⟨r', s', hLs, hse⟩
  · rintro ⟨r', s', hLs, hse⟩
    by_cases hr : r' = r
    · subst hr
      rw [(C.dom_eq r').mp h_fresh] at hLs
      simp at hLs
    · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩

private theorem events_merge {C C' : PCfg} {r₁ r₂ : Replica} {v₁ v₂ : Version}
    {s₁ s₂ : (PQD).State} {ev₁ ev₂ : Set POp}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂)) :
    ∀ e : POp, e ∈ C'.events ↔ e ∈ C.events := by
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← (C.head_coherent r₁ v₁ h_head₁).2, h_ver₁]; rfl
  have hLr₂ : C.L r₂ = some ev₂ := by
    rw [← (C.head_coherent r₂ v₂ h_head₂).2, h_ver₂]; rfl
  intro e
  constructor
  · rintro ⟨r', s', hLs, hse⟩
    rw [hL] at hLs
    by_cases hr : r' = r₁
    · subst hr
      rw [updateRep_self] at hLs
      injection hLs with hs
      subst hs
      rcases hse with h1 | h2
      · exact ⟨r', ev₁, hLr₁, h1⟩
      · exact ⟨r₂, ev₂, hLr₂, h2⟩
    · rw [updateRep_other _ _ hr] at hLs
      exact ⟨r', s', hLs, hse⟩
  · rintro ⟨r', s', hLs, hse⟩
    by_cases hr : r' = r₁
    · subst hr
      rw [hLr₁] at hLs
      injection hLs with hs
      subst hs
      exact ⟨r', ev₁ ∪ ev₂, by rw [hL, updateRep_self], Or.inl hse⟩
    · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩

private theorem events_apply {C C' : PCfg} {t : Timestamp} {r : Replica} {o : PAppOp}
    {v : Version} {sh : (PQD).State} {evh : Set POp}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (sh, evh))
    (hL : C'.L = updateRep C.L r (evh ∪ {(t, r, o)})) :
    ∀ e : POp, e ∈ C'.events ↔ e ∈ C.events ∨ e = (t, r, o) := by
  have hLr : C.L r = some evh := by
    rw [← (C.head_coherent r v h_head).2, h_ver]; rfl
  have hevh_sub : ∀ a ∈ evh, a ∈ C.events := fun a ha => ⟨r, evh, hLr, ha⟩
  intro e
  constructor
  · rintro ⟨r', s', hLs, hse⟩
    rw [hL] at hLs
    by_cases hr : r' = r
    · subst hr
      rw [updateRep_self] at hLs
      injection hLs with hs
      subst hs
      rcases hse with h1 | h2
      · exact Or.inl (hevh_sub _ h1)
      · exact Or.inr h2
    · rw [updateRep_other _ _ hr] at hLs
      exact Or.inl ⟨r', s', hLs, hse⟩
  · rintro (he | rfl)
    · obtain ⟨r', s', hLs, hse⟩ := he
      by_cases hr : r' = r
      · subst hr
        rw [hLr] at hLs
        injection hLs with hs
        subst hs
        exact ⟨r', evh ∪ {(t, r', o)}, by rw [hL, updateRep_self], Or.inl hse⟩
      · exact ⟨r', s', by rw [hL, updateRep_other _ _ hr]; exact hLs, hse⟩
    · exact ⟨r, evh ∪ {(t, r, o)}, by rw [hL, updateRep_self], Or.inr rfl⟩

/-! ## §4  The honest-core invariant, product form

The RGA's `HonCore` (`RGA_Honest_Residual` §3) with the event universe and
visibility read through `inlOp`: the full product universe is listable, `inl`
ids are nonzero, `inl` deletes have nonzero targets, and every `inl` event was
born accurate at a causal fold of the `inl` fragment of its strict past. -/
def HonCoreP (C : PCfg) : Prop :=
  (∃ lE : List POp, listPermOf lE C.events) ∧
  (∀ o : op_t, inlOp o ∈ C.events → o.1 ≠ 0) ∧
  (∀ (t r x : ℕ) (p : List ℕ),
    inlOp ((t, r, app_op_t.Del p x) : op_t) ∈ C.events → x ≠ 0) ∧
  (∀ o : op_t, inlOp o ∈ C.events → ∃ π : List op_t,
      listPermOf π {z : op_t | inlOp z ∈ C.events ∧ C.vis (inlOp z) (inlOp o)} ∧
      respects π (fun a b : op_t => C.vis (inlOp a) (inlOp b)) ∧
      accurate o (applySeqR init_st π))

theorem honCoreP_init : HonCoreP (initConfig PQD trivial) := by
  have hev : ∀ e : POp, e ∈ (initConfig PQD trivial).events → False := by
    rintro e ⟨r, s, hLs, hse⟩
    have hLs' : (if r = 0 then (some (∅ : Set POp)) else none) = some s := hLs
    by_cases h : r = 0
    · subst h
      rw [if_pos rfl] at hLs'
      injection hLs' with hs
      subst hs
      exact hse
    · rw [if_neg h] at hLs'
      simp at hLs'
  exact ⟨⟨[], List.nodup_nil, fun a => ⟨fun h => by simp at h, fun h => (hev a h).elim⟩⟩,
    fun o ho => (hev _ ho).elim,
    fun t r x p h => (hev _ h).elim,
    fun o ho => (hev _ ho).elim⟩

/-- Events-preserving, vis-preserving steps transfer the whole invariant
(createReplica, merge — and query, which does not even change `C`). -/
theorem honCoreP_transfer {C C' : PCfg}
    (hE : ∀ e : POp, e ∈ C'.events ↔ e ∈ C.events)
    (hvis : C'.vis = C.vis)
    (h : HonCoreP C) : HonCoreP C' := by
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := h
  refine ⟨⟨lE, hlE.1, fun a => (hlE.2 a).trans (hE a).symm⟩,
    fun o ho => hz o ((hE _).mp ho),
    fun t r x p hm => hd t r x p ((hE _).mp hm),
    fun o ho => ?_⟩
  obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ((hE _).mp ho)
  refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
  · constructor
    · rintro ⟨hz', hv⟩
      exact ⟨(hE _).mpr hz', by rw [hvis]; exact hv⟩
    · rintro ⟨hz', hv⟩
      exact ⟨(hE _).mp hz', by rw [← hvis]; exact hv⟩
  · exact hπr.imp fun hn hv => hn (hvis ▸ hv)

/-- **An `inr` (mark) apply is a stutter for the `inl` fragment**: the new
event is `inr` (so the restricted universe is unchanged) and every new
vis-edge targets it (so restricted visibility is unchanged); only the full
event listing grows. This is memo §2.5.6's "stutter case", verbatim. -/
theorem honCoreP_apply_inr {C C' : PCfg} {t : Timestamp} {r : Replica} {o₂ : MarkOp}
    {v : Version} {sh : (PQD).State} {evh : Set POp}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (sh, evh))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hL : C'.L = updateRep C.L r (evh ∪ {(t, r, Sum.inr o₂)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (evh a ∧ b = (t, r, Sum.inr o₂)))
    (h : HonCoreP C) : HonCoreP C' := by
  have hE := events_apply h_head h_ver hL
  have hnew_not : ((t, r, Sum.inr o₂) : POp) ∉ C.events := fun hm => h_fresh_t _ hm rfl
  have hE₁ : ∀ e : op_t, inlOp e ∈ C'.events ↔ inlOp e ∈ C.events := by
    intro e
    rw [hE]
    constructor
    · rintro (h1 | h2)
      · exact h1
      · exfalso
        have hc : (Sum.inl e.2.2 : PAppOp) = Sum.inr o₂ :=
          congrArg (fun z : POp => z.2.2) h2
        exact Sum.inl_ne_inr hc
    · exact Or.inl
  have hvis₁ : ∀ a b : op_t,
      C'.vis (inlOp a) (inlOp b) ↔ C.vis (inlOp a) (inlOp b) := by
    intro a b
    rw [hvis]
    constructor
    · rintro (h1 | ⟨_, h2⟩)
      · exact h1
      · exfalso
        have hc : (Sum.inl b.2.2 : PAppOp) = Sum.inr o₂ :=
          congrArg (fun z : POp => z.2.2) h2
        exact Sum.inl_ne_inr hc
    · exact Or.inl
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := h
  refine ⟨⟨lE ++ [(t, r, Sum.inr o₂)], ?_, ?_⟩,
    fun o ho => hz o ((hE₁ _).mp ho),
    fun t' r' x p hm => hd t' r' x p ((hE₁ _).mp hm),
    fun o ho => ?_⟩
  · refine List.nodup_append.mpr ⟨hlE.1, List.nodup_singleton _, ?_⟩
    intro a ha b hb' heq
    rw [List.mem_singleton] at hb'
    subst hb'
    subst heq
    exact hnew_not ((hlE.2 _).mp ha)
  · intro a
    rw [List.mem_append, List.mem_singleton, hE a]
    exact or_congr (hlE.2 a) Iff.rfl
  · obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ((hE₁ _).mp ho)
    refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
    · exact (and_congr (hE₁ z) (hvis₁ z o)).symm
    · exact hπr.imp fun hn hv => hn ((hvis₁ _ _).mp hv)

/-- **The `inl` (character) apply** — the RGA's `honCore_apply`
(`RGA_Honest_Residual.lean:241`) with the universe and visibility read through
`inlOp`: freshness, the post-configuration's structural Lamport field, born
accuracy of the delivered op against the `inl` fragment of the head events,
and `WfOpQ` of the new op maintain all four clauses. -/
theorem honCoreP_apply_inl {C C' : PCfg} {t : Timestamp} {r : Replica} {o₁ : app_op_t}
    {v : Version} {sh : (PQD).State} {evh : Set POp}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (sh, evh))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hL : C'.L = updateRep C.L r (evh ∪ {(t, r, Sum.inl o₁)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (evh a ∧ b = (t, r, Sum.inl o₁)))
    (hborn : ∃ π : List op_t, listPermOf π (evRes₁ evh) ∧
        respects π (fun a b : op_t => C.vis (inlOp a) (inlOp b)) ∧
        accurate (t, r, o₁) (applySeqR init_st π))
    (hwfQ : ∃ σ : concrete_st, WfOpQ (t, r, o₁) σ)
    (h : HonCoreP C) : HonCoreP C' := by
  have hLr : C.L r = some evh := by
    rw [← (C.head_coherent r v h_head).2, h_ver]; rfl
  have hevh_sub : ∀ a ∈ evh, a ∈ C.events := fun a ha => ⟨r, evh, hLr, ha⟩
  have hnew_not : ((t, r, Sum.inl o₁) : POp) ∉ C.events := fun hm => h_fresh_t _ hm rfl
  have hE := events_apply h_head h_ver hL
  -- the new op's timestamp is nonzero: WfOpQ for inserts; Lamport-over-the-target
  -- for deletes (through the product Configuration's structural `causal_mono`)
  have ht0 : t ≠ 0 := by
    obtain ⟨σ, hq⟩ := hwfQ
    cases o₁ with
    | Ins e p a => exact hq.1.1
    | Del p x =>
      have hx0 : x ≠ 0 := by
        rintro rfl
        rcases hq.2 with h0 | hlt
        · exact hq.1 h0
        · exact Nat.not_lt_zero _ hlt
      obtain ⟨π, hπp, _, hπacc⟩ := hborn
      simp only [accurate, opLeaf, opPath] at hπacc
      rcases hπacc with ⟨h0eq, _⟩ | ⟨hlive, _⟩
      · exact absurd h0eq hx0
      · obtain ⟨rx, ex, px, ax, hmx⟩ := insertedIn_of_contains_fold π x hlive
        have hxevh : inlOp ((x, rx, app_op_t.Ins ex px ax) : op_t) ∈ evh :=
          (hπp.2 _).mp hmx
        have hvis' : C'.vis (inlOp ((x, rx, app_op_t.Ins ex px ax) : op_t))
            ((t, r, Sum.inl (app_op_t.Del p x)) : POp) := by
          rw [hvis]
          exact Or.inr ⟨hxevh, rfl⟩
        have hlt : x < t := C'.causal_mono hvis'
        intro ht
        rw [ht] at hlt
        exact Nat.not_lt_zero _ hlt
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := h
  refine ⟨⟨lE ++ [(t, r, Sum.inl o₁)], ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Nodup: the new op is fresh
    refine List.nodup_append.mpr ⟨hlE.1, List.nodup_singleton _, ?_⟩
    intro a ha b hb' heq
    rw [List.mem_singleton] at hb'
    subst hb'
    subst heq
    exact hnew_not ((hlE.2 _).mp ha)
  · -- membership
    intro a
    rw [List.mem_append, List.mem_singleton, hE a]
    exact or_congr (hlE.2 a) Iff.rfl
  · -- nonzero ids on the inl fragment
    intro o' ho'
    rcases (hE (inlOp o')).mp ho' with hold | heq
    · exact hz o' hold
    · have ho'' : o' = (t, r, o₁) := inlOp_injective heq
      rw [ho'']
      exact ht0
  · -- no root deletes on the inl fragment
    intro t' r' x p hm
    rcases (hE _).mp hm with hold | heq
    · exact hd t' r' x p hold
    · obtain ⟨σ, hq⟩ := hwfQ
      have heq' : ((t', r', app_op_t.Del p x) : op_t) = (t, r, o₁) :=
        inlOp_injective heq
      have h3 := congrArg (fun z : op_t => z.2.2) heq'
      cases o₁ with
      | Ins e p₀ a₀ => simp at h3
      | Del p₀ x₀ =>
        injection h3 with h3p h3x
        subst h3x
        rintro rfl
        rcases hq.2 with h0 | hlt
        · exact hq.1 h0
        · exact Nat.not_lt_zero _ hlt
  · -- born accuracy on the inl fragment
    intro o' ho'
    rcases (hE (inlOp o')).mp ho' with hold | heq
    · -- an old inl event: its restricted past and its witness are untouched
      obtain ⟨π, hπp, hπr, hπacc⟩ := hb o' hold
      have ho'ne : inlOp o' ≠ ((t, r, Sum.inl o₁) : POp) :=
        fun he => hnew_not (he ▸ hold)
      refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
      · constructor
        · rintro ⟨hz', hv⟩
          exact ⟨(hE _).mpr (Or.inl hz'), by rw [hvis]; exact Or.inl hv⟩
        · rintro ⟨hz', hv⟩
          rw [hvis] at hv
          rcases hv with hv | ⟨_, heq'⟩
          · rcases (hE (inlOp z)).mp hz' with hzo | hznew
            · exact ⟨hzo, hv⟩
            · exact absurd (hznew ▸ C.vis_src hv) hnew_not
          · exact absurd heq' ho'ne
      · refine hπr.imp_of_mem ?_
        intro a b ha _hb hn hv
        rw [hvis] at hv
        rcases hv with hv | ⟨_, heq'⟩
        · exact hn hv
        · exact hnew_not (heq' ▸ ((hπp.2 a).mp ha).1)
    · -- the new op: its restricted past is exactly `evRes₁ evh`
      obtain rfl : o' = (t, r, o₁) := inlOp_injective heq
      obtain ⟨π, hπp, hπr, hπacc⟩ := hborn
      refine ⟨π, ⟨hπp.1, fun z => (hπp.2 z).trans ?_⟩, ?_, hπacc⟩
      · constructor
        · intro hz'
          refine ⟨(hE _).mpr (Or.inl (hevh_sub _ hz')), ?_⟩
          rw [hvis]
          exact Or.inr ⟨hz', rfl⟩
        · rintro ⟨hz', hv⟩
          rw [hvis] at hv
          rcases hv with hv | ⟨hev, _⟩
          · exact absurd (C.vis_tgt hv) hnew_not
          · exact hev
      · refine hπr.imp_of_mem ?_
        intro a b ha _hb hn hv
        rw [hvis] at hv
        rcases hv with hv | ⟨_, heq'⟩
        · exact hn hv
        · exact hnew_not (heq' ▸ hevh_sub _ ((hπp.2 a).mp ha))

/-- The honest-core invariant at every product-reachable configuration —
the §2.5.6 rerun's induction. -/
theorem honCoreP_of_reach (hHD : PeritextHonestDelivery) {C : PCfg}
    (hReach : PReach C) : HonCoreP C := by
  induction hReach with
  | refl => exact honCoreP_init
  | tail hpre hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases ℓ with
    | createReplica r =>
      cases hstep with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact honCoreP_transfer (events_createReplica h_fresh hL) hvis ih
    | apply t r o =>
      cases o with
      | inl o₁ =>
        have hstep' := hstep
        cases hstep with
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hN hL hvis hver hhead hparents =>
          obtain ⟨hborn, hq, himp⟩ := hHD hpre hstep' h_head h_ver
          exact honCoreP_apply_inl h_head h_ver h_fresh_t hL hvis hborn
            (wfOpQ_of_hBA_P hq himp) ih
      | inr o₂ =>
        cases hstep with
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hN hL hvis hver hhead hparents =>
          exact honCoreP_apply_inr h_head h_ver h_fresh_t hL hvis ih
    | merge r₁ r₂ =>
      cases hstep with
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact honCoreP_transfer
          (events_merge h_head₁ h_head₂ h_ver₁ h_ver₂ hL) hvis ih
    | query r q vq =>
      cases hstep with
      | query h_s h_val => exact ih

/-! ## §5  The re-typed projected core

`rgaHonJ` wants a witness configuration over the raw `RGACondSig.toCRDTSig`
presenting the `inl` fragment of `(vis, events)`. This is `coreR`
(`RGA_Honest_Residual` §1) composed with `projCore₁` (`Product.lean` §O4):
event sets restrict along `evRes₁`, visibility along `inlOp`, and every
invariant field transfers (timestamps and replicas are preserved by the
injection). Nothing downstream reads `N`. -/
def coreP₁ (C : PCfg) : Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => (C.L r).map fun _ => init_st
  L := fun r => (C.L r).map evRes₁
  vis := fun a b => C.vis (inlOp a) (inlOp b)
  dom_eq := by intro r; cases h : C.L r <;> simp
  vis_src := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_src h
    exact ⟨r, evRes₁ s, by rw [hL]; rfl, hs⟩
  vis_tgt := fun {a b} h => by
    obtain ⟨r, s, hL, hs⟩ := C.vis_tgt h
    exact ⟨r, evRes₁ s, by rw [hL]; rfl, hs⟩
  vis_causal := fun {a b r s₁} h hL hb => by
    obtain ⟨s, hLs, rfl⟩ := Option.map_eq_some_iff.mp hL
    exact C.vis_causal h hLs hb
  timestamps_distinct := fun {a b r s r' s'} hL ha hL' hb hne => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.timestamps_distinct hsa ha hsb hb fun h => hne (inlOp_injective h)
  vis_total_same_replica := fun {a b r s r' s'} hL ha hL' hb hne hrep => by
    obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.mp hL
    obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp hL'
    exact C.vis_total_same_replica hsa ha hsb hb
      (fun h => hne (inlOp_injective h)) hrep

/-! ## §6  hHon, discharged over the product LTS -/

/-- **The product `hHon₁` supply** (memo §2.5.6, discharged): the RGA's join
context `rgaHonJ` holds at the `inl` fragment of every product-reachable
core. The witness is the re-typed projected core; visibility restriction is
`vis_src`/`vis_tgt`, Lamport is the structural `causal_mono`, id-uniqueness
is `timestamps_distinct` (all through `inlOp`, which preserves the `(t, r)`
prefix), and the generation discipline is `genDisc2C_of_born` — the RGA
content lemma, re-consumed, not re-proved — at the product honest-core
invariant. -/
theorem peritext_hHon_discharged (hHD : PeritextHonestDelivery) :
    ∀ {C₀ : PCfg}, PReach C₀ →
      rgaHonJ (visRes₁ (Sal.ConditionedMRDTs.Configuration.core C₀).vis)
        (evRes₁ (Sal.ConditionedMRDTs.Configuration.core C₀).events) := by
  intro C₀ hreach
  obtain ⟨⟨lE, hlE⟩, hz, hd, hb⟩ := honCoreP_of_reach hHD hreach
  have hS := goodConfig3SP_of_reach hreach
  refine ⟨coreP₁ C₀, ?_, ?_, hz, ?_, hd⟩
  · -- the witness's visibility is the restricted visibility, on events
    intro a b
    exact ⟨fun h => ⟨h, C₀.vis_src h, C₀.vis_tgt h⟩, fun h => h.1⟩
  · -- the generation discipline, from born accuracy at the fragment
    refine genDisc2C_of_born (coreP₁ C₀)
      (evRes₁ (Sal.ConditionedMRDTs.Configuration.core C₀).events)
      (projList₁ lE) (listPermOf_projList₁ hlE)
      (fun a b ha hb' hne => ?_) hz
      (fun hab hbc => hS.vis_trans hab hbc)
      (fun a hv => hS.vis_irrefl (inlOp a) hv)
      (fun o ho => ?_)
    · obtain ⟨ra, sa, hLa, hsa⟩ := ha
      obtain ⟨rb, sb, hLb, hsb⟩ := hb'
      exact C₀.timestamps_distinct hLa hsa hLb hsb
        (fun h => hne (inlOp_injective h))
    · obtain ⟨π, hπp, hπr, hπacc⟩ := hb o ho
      exact ⟨π, hπp,
        hπr.imp (fun hn hlo => hn (loOnA_imp_vis (coreP₁ C₀) _ _ _ hlo)), hπacc⟩
  · -- Lamport monotonicity is structural
    exact fun a b _ _ h => C₀.causal_mono h

/-! ## §7  hHext, discharged over the product LTS

The RGA's `rga_hHext_discharged` (`RGA_HHext_Discharge.lean`) consumed its
reachability/step hypotheses for exactly ONE fact: stored timestamp freshness
against the head version's events. Everything else in its body is config-free.
`rgaH_extend_of_fresh` is that body with the freshness as a hypothesis over
the witness list; the product `hHext` extracts the freshness from the PRODUCT
step's own `h_fresh_store` field and restricts it along `projList₁`. An `inr`
op is free — `projList₁` drops it, so the discipline is untouched. -/

/-- The RGA witness discipline `rgaH` extends at an applicable apply, given
freshness of the new timestamp against the witness list (config-free core of
`rga_hHext_discharged`; the proof body is that discharge's, with list-level
freshness in place of the store-level extraction). -/
theorem rgaH_extend_of_fresh (t r : ℕ) (o : app_op_t) (ρ : List op_t)
    (hfresh : ∀ x ∈ ρ, (x : op_t).1 ≠ t)
    (hH : rgaH ρ)
    (happ : RGACondSig'.applicable (t, r, o)
      (applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ)) :
    rgaH (ρ ++ [(t, r, o)]) := by
  obtain ⟨hOK, hHP⟩ := hH
  have hstate : applySeq RGACondSig'.toCRDTSig RGACondSig'.init ρ
      = applySeqR init_st ρ :=
    Sal.ConditionedMRDTs.RGAInstanceFinal.applySeq_eq_applySeqR RGACondSig'.init ρ
  rw [hstate] at happ
  have hacc : accurate (t, r, o) (applySeqR init_st ρ) := happ.1
  have hfr : fresh_ts (t, r, o) (applySeqR init_st ρ) := happ.2
  have hinv : CanonInv ρ (applySeqR init_st ρ) := by
    have h := RGACanonConvergence.canon_fold ρ [] init_st
      RGACanonConvergence.canonInv_init hOK
    rwa [List.nil_append] at h
  have h0 : contains (applySeqR init_st ρ) 0 = false := hinv.1
  have hlift : ∀ x : ℕ, insertedIn ρ x → insertedIn (ρ ++ [(t, r, o)]) x := by
    rintro x ⟨r', e', p', a', hm'⟩
    exact ⟨r', e', p', a', List.mem_append_left _ hm'⟩
  cases o with
  | Ins e p a =>
    have hstepOK : CanonStepOK ρ (applySeqR init_st ρ) (t, r, app_op_t.Ins e p a) := by
      refine ⟨hfr.1, hfr.2, ?_, ?_, ?_,
        RGACanonConvergence.chainOK_of_accurate _ t r e a p h0 hacc⟩
      · -- no id reuse: a recorded delete of t names an inserted id — freshness contra
        rintro ⟨t', r', p', hm'⟩
        rcases hHP.1 t' r' t p' hm' with h0' | hins
        · exact hfr.1 h0'
        · obtain ⟨r'', e'', p'', a'', hm''⟩ := hins
          exact hfresh _ hm'' rfl
      · -- t not in its own chain: accurate entries are live, t is fresh
        intro htmem
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
        · subst ha0; subst hp0
          rcases List.mem_cons.mp htmem with h | h
          · exact hfr.1 h
          · simp at h
        · have hlive : contains (applySeqR init_st ρ) t = true := by
            rcases List.mem_cons.mp htmem with h | h
            · exact h ▸ hal
            · exact isAncPath_mem _ a p hpath t h
          rw [hfr.2] at hlive
          exact Bool.noConfusion hlive
      · -- t not in prior chains: honest payloads make entries inserted — freshness contra
        intro t' r' e' p' a' hm' htmem
        rcases hHP.2 t' r' e' a' p' hm' t htmem with h0' | hins
        · exact hfr.1 h0'
        · obtain ⟨r'', e'', p'', a'', hm''⟩ := hins
          exact hfresh _ hm'' rfl
    refine ⟨canonFoldOK_append ρ [] init_st _ hOK hstepOK, ?_, ?_⟩
    · -- delete payloads: only old members (the appended op is an Ins)
      intro t' r' x' p' hm'
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.1 t' r' x' p' h with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift x' hins)
      · exfalso
        have hEq := List.mem_singleton.mp h
        simp at hEq
    · -- insert payloads: old members lift; the new op's chain is accurate-live
      intro t' r' e' a' p' hm' c hc
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.2 t' r' e' a' p' h c hc with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift c hins)
      · have hEq := List.mem_singleton.mp h
        have h3 := congrArg (fun z : op_t => z.2.2) hEq
        injection h3 with h3e h3p h3a
        have hchain : (a' : ℕ) :: p' = a :: p := by rw [h3a, h3p]
        rw [hchain] at hc
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨ha0, hp0⟩ | ⟨hal, hpath⟩
        · subst ha0; subst hp0
          rcases List.mem_cons.mp hc with h' | h'
          · exact Or.inl h'
          · simp at h'
        · have hlive : contains (applySeqR init_st ρ) c = true := by
            rcases List.mem_cons.mp hc with h' | h'
            · exact h' ▸ hal
            · exact isAncPath_mem _ a p hpath c h'
          exact Or.inr (hlift c (insertedIn_of_contains_fold ρ c hlive))
  | Del p x =>
    have hstepOK : CanonStepOK ρ (applySeqR init_st ρ) (t, r, app_op_t.Del p x) :=
      RGACanonConvergence.delOK_of_accurate _ t r x p h0 hacc
    refine ⟨canonFoldOK_append ρ [] init_st _ hOK hstepOK, ?_, ?_⟩
    · -- delete payloads: old members lift; the new del's nonzero target is accurate-live
      intro t' r' x' p' hm'
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.1 t' r' x' p' h with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift x' hins)
      · have hEq := List.mem_singleton.mp h
        have h3 := congrArg (fun z : op_t => z.2.2) hEq
        injection h3 with h3p h3x
        have hacc' := hacc
        simp only [accurate, opLeaf, opPath] at hacc'
        rcases hacc' with ⟨hx0, _⟩ | ⟨hxl, _⟩
        · exact Or.inl (h3x.trans hx0)
        · exact Or.inr (hlift x'
            (h3x ▸ insertedIn_of_contains_fold ρ x hxl))
    · -- insert payloads: only old members (the appended op is a Del)
      intro t' r' e' a' p' hm' c hc
      rcases List.mem_append.mp hm' with h | h
      · rcases hHP.2 t' r' e' a' p' h c hc with h0' | hins
        · exact Or.inl h0'
        · exact Or.inr (hlift c hins)
      · exfalso
        have hEq := List.mem_singleton.mp h
        simp at hEq

/-- **The product `hHext` supply**: the product witness discipline
`prodH rgaH` extends at every applicable product apply. `inr` ops are free
(`projList₁` drops them); `inl` ops feed the config-free core, with the
timestamp freshness extracted from the product step's `h_fresh_store`. -/
theorem peritext_hHext_discharged
    {C₀ C₁ : PCfg} {t : Timestamp} {r : Replica} {o : PAppOp}
    {v : Version}
    {sh : QState (prodSig RGACondSig' MarkStore) (prodEqEquiv rgaEqEquiv')}
    {evh : Set POp} :
    PReach C₀ →
    Step3 PQD C₀ (Label3.apply t r o) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    ∀ ρ : List POp, listPermOf ρ evh →
      prodH (D₁ := RGACondSig') (D₂ := MarkStore) rgaH ρ →
      (prodSig RGACondSig' MarkStore).applicable (t, r, o)
        (applySeq (prodSig RGACondSig' MarkStore).toCRDTSig
          (prodSig RGACondSig' MarkStore).init ρ) →
      prodH (D₁ := RGACondSig') (D₂ := MarkStore) rgaH (ρ ++ [(t, r, o)]) := by
  intro _hreach hstep hhead hver ρ hρp hH happ
  cases o with
  | inr o₂ =>
    show rgaH (projList₁ (ρ ++ [(t, r, Sum.inr o₂)]))
    rw [projList₁_append]
    show rgaH (projList₁ ρ ++ [])
    rw [List.append_nil]
    exact hH
  | inl o₁ =>
    -- stored freshness against evh, from the step's own side-condition
    have hfs : ∀ x : POp, x ∈ evh → x.1 ≠ t := by
      cases hstep with
      | apply h_head' h_ver' hft hfs' hvn hrk C' hN hL hvis hver2 hhead2 hparents =>
        intro x hx
        exact hfs' v sh evh hver x hx
    show rgaH (projList₁ (ρ ++ [(t, r, Sum.inl o₁)]))
    rw [projList₁_append]
    show rgaH (projList₁ ρ ++ [(t, r, o₁)])
    rw [applySeq_prod] at happ
    refine rgaH_extend_of_fresh t r o₁ (projList₁ ρ) ?_ hH happ
    intro x hx
    exact hfs (inlOp x) ((hρp.2 _).mp (mem_projList₁.mp hx))

/-! ## §8  hBA, discharged over the product LTS -/

/-- **The product `hBA` supply**: `inl` (character) applies are
born-applicable by `PeritextHonestDelivery`; `inr` (mark) applies are
UNGUARDED — the mark store's `applicable` is `⊤`, so their `qapplicable` is
discharged outright at any representative and the `W`-half is trivial
(`prodW`'s `inr` arm is `⊤`). The composite assumes nothing about mark
delivery. -/
theorem peritext_hBA_discharged (hHD : PeritextHonestDelivery)
    {C₀ C₁ : PCfg} {t : Timestamp} {r : Replica} {o : PAppOp}
    {v : Version}
    {sh : QState (prodSig RGACondSig' MarkStore) (prodEqEquiv rgaEqEquiv')}
    {evh : Set POp} :
    PReach C₀ →
    Step3 PQD C₀ (Label3.apply t r o) C₁ →
    C₀.head r = some v → C₀.ver v = some (sh, evh) →
    qapplicable (prodEqEquiv (D₂ := MarkStore) rgaEqEquiv') (prodW WfOpA)
        (prodInvInvVC rgaEqEquiv' WfOpA rgaInvInvVCA) (t, r, o) sh ∧
      (∀ s' : (prodSig RGACondSig' MarkStore).State,
        (prodSig RGACondSig' MarkStore).applicable (t, r, o) s' →
          prodW (D₂ := MarkStore) WfOpA (t, r, o) s') := by
  intro hreach hstep hhead hver
  cases o with
  | inl o₁ =>
    obtain ⟨_, hq, himp⟩ := hHD hreach hstep hhead hver
    exact ⟨hq, fun s' happ => himp s'.1 happ⟩
  | inr o₂ =>
    refine ⟨?_, fun s' _ => trivial⟩
    obtain ⟨⟨σ, hσ⟩, hrep⟩ := Quotient.exists_rep sh
    rw [← hrep]
    exact trivial

end Sal.ConditionedMRDTs.PeritextTF
