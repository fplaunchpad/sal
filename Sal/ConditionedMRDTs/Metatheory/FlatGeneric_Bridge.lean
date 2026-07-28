import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H
import Sal.ConditionedMRDTs.Metatheory.ConditionedContract
import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyReachEq

/-!
# The flat collapse of the generic conditioned framework

*Additive; 0 `sorry`.*

**One framework, mechanized as such.** A flat MRDT (`Inv = applicable = ⊤`) with a
closure-indexed Join Lemma (`JoinLemma3C`, what every production discharge already supplies via
`ConditionedContract`) instantiates the GENERIC conditioned metatheorem at the identity
observational equivalence — `≈ := =`, guard `W := ⊤`, witness discipline `H := ⊤` — and
inherits `IsRALinearizable3Eq` over the quotient ternary system from the same
`RA_linearizable_up_to_eq_H` that hosts the tombstone-free RGA.

The bridge content:

* the trivial bundles (`invPresTop`, `congVCEq`, `invInvVCTop`) — congruence under `=` is
  rewriting, invariant preservation at `Inv = ⊤` is vacuous;
* `eqCommutesOn ↔ commutes` at the identity equivalence with the trivial guard: `doW ⊤` is the
  raw update and the `Inv`-conditioning is total, so `≈`-commutation-on-`Inv` IS structural
  commutation — hence `loOnEq` at `=` IS the flat set-relative order `loOn`;
* a synthetic `Sal.Emulation.Configuration` presenting the `≈`-Join's ambient `(vis, events)`
  (visibility restricted to the union; same-replica `vis`-totality supplied by the join
  context `flatHonJ`, which a reachable core satisfies STRUCTURALLY);
* `eqJoinH_of_joinC` — the `≈`-Join at `=` from the flat `JoinLemma3C` at full closure;
* `flat_ra_linearizable3_eq` — the capstone: every honest-execution premise of
  `RA_linearizable_up_to_eq_H` is trivial at the flat parameters (`H = ⊤`; `qapplicable` is the
  lift of `⊤`; `flatHonJ` is a structural field of every configuration), so the theorem is
  UNCONDITIONAL.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.FlatGeneric

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs (Configuration Version Step3 Label3 initConfig labeledTS3
  JoinLemma3C fullClosure ConditionedContract)

variable {D : ConditionedMRDTSig}

/-! ## §1  The identity instantiation -/

/-- The identity observational equivalence. -/
def eqOfEq (D : ConditionedMRDTSig) : EqEquiv D := ⟨Eq, eq_equivalence⟩

/-- The trivial wellformedness guard. -/
def WTop (D : ConditionedMRDTSig) : Op D.AppOp → D.State → Prop := fun _ _ => True

theorem invPresTop (hInvT : ∀ s : D.State, D.Inv s) : InvPres D (WTop D) where
  inv_init := hInvT _
  inv_update := fun _ _ _ _ => hInvT _
  inv_mergeL := fun _ _ _ _ _ _ => hInvT _

theorem congVCEq (D : ConditionedMRDTSig) : CongVC D (eqOfEq D) where
  update_congr := fun o {s s'} _ _ h => by
    have h' : s = s' := h
    show D.update s o = D.update s' o
    rw [h']
  mergeL_congr := fun {l l' a a' b b'} _ _ _ _ _ _ hl ha hb => by
    have hl' : l = l' := hl
    have ha' : a = a' := ha
    have hb' : b = b' := hb
    show D.mergeL l a b = D.mergeL l' a' b'
    rw [hl', ha', hb']
  query_congr := fun q {s s'} _ _ h => by
    have h' : s = s' := h
    rw [h']

theorem invInvVCTop (D : ConditionedMRDTSig) : InvInvVC D (eqOfEq D) (WTop D) where
  wf_congr := by intros; exact Iff.rfl
  applicable_congr := fun o {s s'} _ _ h => by
    have h' : s = s' := h
    rw [h']

/-- `doW` at the trivial guard is the raw update. -/
theorem doW_top (o : Op D.AppOp) (s : D.State) : doW D (WTop D) o s = D.update s o :=
  if_pos trivial

/-- **The order collapse, pointwise**: at the identity equivalence with total `Inv` and the
trivial guard, `≈`-commutation-on-`Inv` IS structural commutation. -/
theorem eqCommutesOn_iff_commutes (hInvT : ∀ s : D.State, D.Inv s) (o₁ o₂ : Op D.AppOp) :
    eqCommutesOn (eqOfEq D) (WTop D) o₁ o₂ ↔ D.toCRDTSig.commutes o₁ o₂ := by
  constructor
  · intro h s
    have h' : doW D (WTop D) o₂ (doW D (WTop D) o₁ s)
        = doW D (WTop D) o₁ (doW D (WTop D) o₂ s) := h s (hInvT s)
    simp only [doW_top] at h'
    exact h'
  · intro h s _
    show doW D (WTop D) o₂ (doW D (WTop D) o₁ s)
        = doW D (WTop D) o₁ (doW D (WTop D) o₂ s)
    simp only [doW_top]
    exact h s

/-! ## §2  The join context and the synthetic configuration -/

/-- **The flat join context**: same-replica `vis`-totality on the ambient event universe — a
STRUCTURAL field of every configuration (`vis_total_same_replica`), so `hHon` needs no
reachability induction at all. -/
def flatHonJ (D : ConditionedMRDTSig) :
    (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop :=
  fun vis events =>
    ∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.2.1 = b.2.1 →
      vis a b ∨ vis b a

/-- The synthetic configuration presenting `(vis, U)`: one replica logging `U`, visibility
restricted to `U`-pairs. The invariant fields come from the `≈`-Join's own premises plus the
join context. -/
noncomputable def flatCfg (vis : Op D.AppOp → Op D.AppOp → Prop)
    (events U : Set (Op D.AppOp))
    (hUmem : ∀ x ∈ U, x ∈ events)
    (hdts : ∀ a b : Op D.AppOp, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1)
    (hHonJ : flatHonJ D vis events) :
    Sal.Emulation.Configuration D.toCRDTSig where
  N := fun r => if r = 0 then some D.init else none
  L := fun r => if r = 0 then some U else none
  vis := fun a b => vis a b ∧ a ∈ U ∧ b ∈ U
  dom_eq := by intro r; by_cases h : r = 0 <;> simp [h]
  vis_src := fun {a b} h => ⟨0, U, by simp, h.2.1⟩
  vis_tgt := fun {a b} h => ⟨0, U, by simp, h.2.2⟩
  vis_causal := by
    intro a b r s h hL _
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl] at hL
      injection hL with hs
      subst hs
      exact h.2.1
    · simp [hr] at hL
  timestamps_distinct := by
    intro a b r s r' s' hL hsa hL' hsb hne
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl] at hL
      injection hL with hs
      subst hs
      by_cases hr' : r' = 0
      · subst hr'
        rw [if_pos rfl] at hL'
        injection hL' with hs'
        subst hs'
        exact hdts a b (hUmem a hsa) (hUmem b hsb) hne
      · simp [hr'] at hL'
    · simp [hr] at hL
  vis_total_same_replica := by
    intro a b r s r' s' hL hsa hL' hsb hne hrep
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl] at hL
      injection hL with hs
      subst hs
      by_cases hr' : r' = 0
      · subst hr'
        rw [if_pos rfl] at hL'
        injection hL' with hs'
        subst hs'
        rcases hHonJ a b (hUmem a hsa) (hUmem b hsb) hne hrep with h | h
        · exact Or.inl ⟨h, hsa, hsb⟩
        · exact Or.inr ⟨h, hsb, hsa⟩
      · simp [hr'] at hL'
    · simp [hr] at hL

theorem flatCfg_vis (vis : Op D.AppOp → Op D.AppOp → Prop) (events U : Set (Op D.AppOp))
    (hUmem) (hdts) (hHonJ) (a b : Op D.AppOp) :
    (flatCfg (D := D) vis events U hUmem hdts hHonJ).vis a b
      ↔ (vis a b ∧ a ∈ U ∧ b ∈ U) := Iff.rfl

theorem mem_flatCfg_events (vis : Op D.AppOp → Op D.AppOp → Prop)
    (events U : Set (Op D.AppOp)) (hUmem) (hdts) (hHonJ) (e : Op D.AppOp) :
    e ∈ (flatCfg (D := D) vis events U hUmem hdts hHonJ).events ↔ e ∈ U := by
  constructor
  · rintro ⟨r, s, hL, hse⟩
    by_cases hr : r = 0
    · subst hr
      have hL' : (if (0 : Replica) = 0 then some U else none) = some s := hL
      rw [if_pos rfl] at hL'
      injection hL' with hs
      subst hs
      exact hse
    · have hL' : (if r = 0 then some U else none) = some s := hL
      simp [hr] at hL'
  · intro he
    exact ⟨0, U, show (if (0 : Replica) = 0 then some U else none) = some U by
      rw [if_pos rfl], he⟩

/-! ## §3  The order transport -/

/-- **`loOn` = `loOnEq` at the identity instantiation**, on members of the presented
universe. -/
theorem loOn_iff_loOnEq (hInvT : ∀ s : D.State, D.Inv s)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (events U : Set (Op D.AppOp))
    (hUmem) (hdts) (hHonJ)
    (ev : Set (Op D.AppOp)) (hsub : ∀ x ∈ ev, x ∈ U)
    (a b : Op D.AppOp) (ha : a ∈ ev) (hb : b ∈ ev) :
    loOn (flatCfg (D := D) vis events U hUmem hdts hHonJ) ev a b
      ↔ loOnEq (eqOfEq D) (WTop D) vis ev a b := by
  constructor
  · rintro (⟨hv, hnc⟩ | ⟨hnv1, hnv2, hrc, hnabs⟩)
    · exact Or.inl ⟨hv.1,
        fun hec => hnc ((eqCommutesOn_iff_commutes hInvT _ _).mp hec)⟩
    · refine Or.inr ⟨?_, ?_, hrc, ?_⟩
      · exact fun hv => hnv1 ⟨hv, hsub a ha, hsub b hb⟩
      · exact fun hv => hnv2 ⟨hv, hsub b hb, hsub a ha⟩
      · rintro ⟨e₃, he₃, hv, hnec⟩
        exact hnabs ⟨e₃, he₃, ⟨hv, hsub b hb, hsub e₃ he₃⟩,
          fun hc => hnec ((eqCommutesOn_iff_commutes hInvT _ _).mpr hc)⟩
  · rintro (⟨hv, hnec⟩ | ⟨hnv1, hnv2, hrc, hnabs⟩)
    · exact Or.inl ⟨⟨hv, hsub a ha, hsub b hb⟩,
        fun hc => hnec ((eqCommutesOn_iff_commutes hInvT _ _).mpr hc)⟩
    · refine Or.inr ⟨?_, ?_, hrc, ?_⟩
      · exact fun hv => hnv1 hv.1
      · exact fun hv => hnv2 hv.1
      · rintro ⟨e₃, he₃, hv, hnc⟩
        exact hnabs ⟨e₃, he₃, hv.1,
          fun hec => hnc ((eqCommutesOn_iff_commutes hInvT _ _).mp hec)⟩

/-- Witness transport, `≈`-side → flat side. -/
theorem isCanonical_of_eqH (hInvT : ∀ s : D.State, D.Inv s)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (events U : Set (Op D.AppOp))
    (hUmem) (hdts) (hHonJ)
    (ev : Set (Op D.AppOp)) (hsub : ∀ x ∈ ev, x ∈ U) (s : D.State)
    (h : IsCanonicalStateEqH (fun _ => True) (eqOfEq D) (WTop D) vis ev s) :
    IsCanonicalState (flatCfg (D := D) vis events U hUmem hdts hHonJ) ev s := by
  obtain ⟨ρ, hp, hr, _, hfold⟩ := h
  refine ⟨ρ, hp, ?_, hfold⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn hlo
  exact hn ((loOn_iff_loOnEq hInvT vis events U hUmem hdts hHonJ ev hsub b a
    ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mp hlo)

/-- Witness transport, flat side → `≈`-side. -/
theorem eqH_of_isCanonical (hInvT : ∀ s : D.State, D.Inv s)
    (vis : Op D.AppOp → Op D.AppOp → Prop) (events U : Set (Op D.AppOp))
    (hUmem) (hdts) (hHonJ)
    (ev : Set (Op D.AppOp)) (hsub : ∀ x ∈ ev, x ∈ U) (s : D.State)
    (h : IsCanonicalState (flatCfg (D := D) vis events U hUmem hdts hHonJ) ev s) :
    IsCanonicalStateEqH (fun _ => True) (eqOfEq D) (WTop D) vis ev s := by
  obtain ⟨ρ, hp, hr, hfold⟩ := h
  refine ⟨ρ, hp, ?_, trivial, hfold⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn hlo
  exact hn ((loOn_iff_loOnEq hInvT vis events U hUmem hdts hHonJ ev hsub b a
    ((hp.2 b).mp hb) ((hp.2 a).mp ha)).mpr hlo)

/-! ## §4  The `≈`-Join at `=` from the flat Join Lemma -/

/-- **The join bridge**: a flat data type's closure-indexed Join Lemma (at full closure) IS the
generic framework's `≈`-Join at the identity instantiation. -/
theorem eqJoinH_of_joinC (hInvT : ∀ s : D.State, D.Inv s)
    (hJoin : JoinLemma3C D (fullClosure D.toCRDTSig)) :
    EqJoinLemma3C_H D (eqOfEq D) (WTop D) (fun _ => True) (flatHonJ D) := by
  intro vis events ev₁ ev₂ s₀ s₁ s₂ hHonJ _ _ _ htr hirr hdts hev1 hev2 hcl1 hcl2
    hcs₀ hcs₁ hcs₂
  have hUmem : ∀ x ∈ ev₁ ∪ ev₂, x ∈ events := by
    intro x hx
    rcases hx with h | h
    · exact hev1 x h
    · exact hev2 x h
  -- the synthetic presentation
  have hsub1 : ∀ x ∈ ev₁, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_left _ hx
  have hsub2 : ∀ x ∈ ev₂, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_right _ hx
  have hsubI : ∀ x ∈ ev₁ ∩ ev₂, x ∈ ev₁ ∪ ev₂ := fun x hx => Set.mem_union_left _ hx.1
  have hsubU : ∀ x ∈ ev₁ ∪ ev₂, x ∈ ev₁ ∪ ev₂ := fun x hx => hx
  have h := hJoin (flatCfg (D := D) vis events (ev₁ ∪ ev₂) hUmem hdts hHonJ)
    ev₁ ev₂ s₀ s₁ s₂
    (fun {a b c} h1 h2 => ⟨htr h1.1 h2.1, h1.2.1, h2.2.2⟩)
    (fun a h => hirr a h.1)
    (fun a ha => (mem_flatCfg_events _ _ _ _ _ _ a).mpr (hsub1 a ha))
    (fun a ha => (mem_flatCfg_events _ _ _ _ _ _ a).mpr (hsub2 a ha))
    (fun a b hv hb => hcl1 a b hv.1 hb)
    (fun a b hv hb => hcl2 a b hv.1 hb)
    (isCanonical_of_eqH hInvT vis events _ hUmem hdts hHonJ _ hsubI s₀ hcs₀)
    (isCanonical_of_eqH hInvT vis events _ hUmem hdts hHonJ _ hsub1 s₁ hcs₁)
    (isCanonical_of_eqH hInvT vis events _ hUmem hdts hHonJ _ hsub2 s₂ hcs₂)
  exact eqH_of_isCanonical hInvT vis events _ hUmem hdts hHonJ _ hsubU _ h

/-! ## §5  The flat capstone -/

/-- `qapplicable` is trivially true when `applicable` is total. -/
theorem qapplicable_top (hAppT : ∀ (o : Op D.AppOp) (s : D.State), D.applicable o s)
    (o : Op D.AppOp) (sh : QState D (eqOfEq D)) :
    qapplicable (eqOfEq D) (WTop D) (invInvVCTop D) o sh := by
  obtain ⟨⟨σ, _⟩, hrep⟩ := Quotient.exists_rep sh
  rw [← hrep]
  exact hAppT o σ

/-- The flat join context holds at EVERY configuration — structurally
(`vis_total_same_replica` is a field). -/
theorem flatHonJ_of_config (hInvT : ∀ s : D.State, D.Inv s)
    (C₀ : Configuration (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
      (congVCEq D) (invInvVCTop D))) :
    flatHonJ D (Sal.ConditionedMRDTs.Configuration.core C₀).vis
      (Sal.ConditionedMRDTs.Configuration.core C₀).events := by
  intro a b ha hb hne hrep
  obtain ⟨ra, sa, hLa, hsa⟩ := ha
  obtain ⟨rb, sb, hLb, hsb⟩ := hb
  exact C₀.vis_total_same_replica hLa hsa hLb hsb hne hrep

/-- **THE FLAT CAPSTONE — every flat MRDT with a closure-indexed Join Lemma inherits
`IsRALinearizable3Eq` from the generic conditioned metatheorem**, unconditionally: at the flat
parameters every honest-execution premise is trivial or structural. -/
theorem flat_ra_linearizable3_eq
    (hInvT : ∀ s : D.State, D.Inv s)
    (hAppT : ∀ (o : Op D.AppOp) (s : D.State), D.applicable o s)
    (hJoin : JoinLemma3C D (fullClosure D.toCRDTSig))
    (C : Configuration (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
      (congVCEq D) (invInvVCTop D)))
    (hReach : (labeledTS3 (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
        (congVCEq D) (invInvVCTop D))).ReachableFrom
      (initConfig (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
        (congVCEq D) (invInvVCTop D)) trivial) C) :
    IsRALinearizable3Eq (eqOfEq D) (WTop D) (invPresTop hInvT)
      (congVCEq D) (invInvVCTop D) C :=
  Sal.ConditionedMRDTs.ArbReachEq.loOnEq_isRALinearizable3Eq_via_arb_capstone
    (eqOfEq D) (WTop D) (fun _ => True) (flatHonJ D)
    (eqJoinH_of_joinC hInvT hJoin)
    (invPresTop hInvT) (congVCEq D) (invInvVCTop D)
    (fun {_ s'} _ _ => hInvT s')
    (fun {C₀} _ => flatHonJ_of_config hInvT C₀)
    trivial
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => ⟨qapplicable_top hAppT _ _, fun _ _ => trivial⟩)
    C hReach

/-! ## Axiom audit -/

#print axioms eqCommutesOn_iff_commutes
#print axioms eqJoinH_of_joinC
#print axioms flat_ra_linearizable3_eq

/-- The full-closure Join Lemma bundled in any contract (`anti` along
`closure_below_full`). -/
def contractJoinFull (c : ConditionedContract) :
    JoinLemma3C c.D (Sal.ConditionedMRDTs.fullClosure c.D.toCRDTSig) :=
  Sal.ConditionedMRDTs.JoinLemma3C.anti c.closure_below_full c.join

end Sal.ConditionedMRDTs.FlatGeneric
