import Sal.CRDTs.Metatheory.Merge_Linearization_Set

/-!
# RA-linearizability from `CoreVCs + JoinPeelVCs`

The end-to-end bridge theorem on the corrected (set-relative)
foundation: for any `D` with `CoreVCs D` and `JoinPeelVCs D`, every
configuration reachable in the transition system is RA-linearizable.

The induction carries the **strengthened invariant**
`IsCanonicallyLinearizable` — every replica holds the *canonical
state* of its event set — together with transitivity and
irreflexivity of `vis` (reachability facts the σ-machinery consumes).
The Merge case is the Join Lemma (`join_lemma_of_peel`); the Apply
case is `isCanonicalState_extend`; Def-lin follows via
`isCanonicalState_lo_witness`. Combined with the discharges of
`JoinPeelVCs` (commuting class; `AWSet`), this replaces the broken
`ra_linearizable_of_vcs` route end to end.
-/

namespace Sal.Emulation

open Classical

section
variable {D : CRDTSig}

/-- Strengthened RA-lin: every replica holds the canonical state of
its event set. -/
def IsCanonicallyLinearizable (C : Configuration D) : Prop :=
  ∀ (r : Replica) (s : D.State) (E : Set (Op D.AppOp)),
    C.N r = some s → C.L r = some E → IsCanonicalState C E s

/-- The strengthened invariant implies the paper's Def-lin. -/
theorem isRALinearizable_of_canonical {C : Configuration D}
    (h : IsCanonicallyLinearizable C) : IsRALinearizable C := by
  intro r s E hN hL
  exact isCanonicalState_lo_witness (h r s E hN hL)

/-- `loOn` is local to the set: configurations agreeing on `vis` over
`E × E` induce the same canonical states of `E`. -/
theorem isCanonicalState_congr {C C' : Configuration D}
    {E : Set (Op D.AppOp)} {s : D.State}
    (h_vis : ∀ a ∈ E, ∀ b ∈ E, (C'.vis a b ↔ C.vis a b))
    (h : IsCanonicalState C E s) : IsCanonicalState C' E s := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  refine ⟨ρ, hp, ?_, hf⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn h_lo
  have ha_E : a ∈ E := (hp.2 a).mp ha
  have hb_E : b ∈ E := (hp.2 b).mp hb
  apply hn
  rcases h_lo with ⟨hv, hnc⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨(h_vis b hb_E a ha_E).mp hv, hnc⟩
  · refine Or.inr ⟨fun hv => h1 ((h_vis b hb_E a ha_E).mpr hv),
      fun hv => h2 ((h_vis a ha_E b hb_E).mpr hv), h3, ?_⟩
    rintro ⟨e₃, he₃, hv, hnc⟩
    exact h4 ⟨e₃, he₃, (h_vis a ha_E e₃ he₃).mpr hv, hnc⟩

/-- Fresh timestamps are not in the configuration. -/
theorem not_mem_events_of_fresh {C : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    (h_fresh : ∀ e', e' ∈ C.events → Op.time e' ≠ t) :
    ((t, r, o) : Op D.AppOp) ∉ C.events :=
  fun h => h_fresh _ h rfl

/-- The reachable-configuration invariant: canonical linearizability
plus `vis`-transitivity and irreflexivity. -/
def GoodConfig (C : Configuration D) : Prop :=
  IsCanonicallyLinearizable C ∧
  (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) ∧
  (∀ a : Op D.AppOp, ¬ C.vis a a)

theorem goodConfig_init : GoodConfig (initConfig D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r s E hN hL
    by_cases hr : r = 0
    · subst hr
      simp [initConfig] at hN hL
      subst hN; subst hL
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩,
        List.Pairwise.nil, rfl⟩
    · simp [initConfig, hr] at hN
  · intro a b c h _
    exact absurd h id
  · intro a h
    exact absurd h id

/-- **CreateReplica preserves the invariant.** -/
theorem goodConfig_createReplica {C C' : Configuration D} {r : Replica}
    (hN : C'.N = updateRep C.N r D.init)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (h : GoodConfig C) : GoodConfig C' := by
  obtain ⟨h_can, h_tr, h_ir⟩ := h
  refine ⟨?_, fun ha hb => hvis ▸ h_tr (hvis ▸ ha) (hvis ▸ hb),
    fun a ha => h_ir a (hvis ▸ ha)⟩
  intro r' s E hN' hL'
  rw [hN] at hN'; rw [hL] at hL'
  have h_same : ∀ E' s',
      IsCanonicalState C E' s' → IsCanonicalState C' E' s' :=
    fun E' s' => isCanonicalState_congr
      (fun a _ b _ => by rw [hvis])
  by_cases hr' : r' = r
  · subst hr'
    simp [updateRep] at hN' hL'
    subst hN'; subst hL'
    exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩,
      List.Pairwise.nil, rfl⟩
  · simp [updateRep, hr'] at hN' hL'
    exact h_same _ _ (h_can r' s E hN' hL')

/-- **Apply preserves the invariant.** -/
theorem goodConfig_apply {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {s : D.State} {ev : Set (Op D.AppOp)}
    (h_s : C.N r = some s) (h_ev : C.L r = some ev)
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hN : C'.N = updateRep C.N r (D.update s (t, r, o)))
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (h : GoodConfig C) : GoodConfig C' := by
  obtain ⟨h_can, h_tr, h_ir⟩ := h
  set e : Op D.AppOp := (t, r, o) with he_def
  have he_not_events : e ∉ C.events := not_mem_events_of_fresh h_fresh_t
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events :=
    fun x hx => ⟨r, ev, h_ev, hx⟩
  have he_not_ev : e ∉ ev := fun h => he_not_events (h_ev_events e h)
  -- No old vis-edge leaves e (its source would be a known event).
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Canonical linearizability.
    intro r' s' E' hN' hL'
    rw [hN] at hN'; rw [hL] at hL'
    by_cases hr' : r' = r
    · subst hr'
      simp [updateRep] at hN' hL'
      subst hN'; subst hL'
      -- Extend the canonical state of `ev` by the fresh event.
      have h_old : IsCanonicalState C ev s := h_can r' s ev h_s h_ev
      have h_old' : IsCanonicalState C' ev s := by
        refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
        rw [hvis]
        constructor
        · rintro (h | ⟨_, rfl⟩)
          · exact h
          · exact absurd hb he_not_ev
        · exact Or.inl
      have h_ext := isCanonicalState_extend (e := e) he_not_ev
        (fun x hx => by rw [hvis]; exact Or.inr ⟨hx, rfl⟩)
        (fun x hx => by
          rw [hvis]
          rintro (h | ⟨he_ev, _⟩)
          · exact h_no_vis_out x h
          · exact he_not_ev he_ev)
        h_old'
      exact h_ext
    · simp [updateRep, hr'] at hN' hL'
      have h_old : IsCanonicalState C E' s' := h_can r' s' E' hN' hL'
      refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
      have hb_ne : b ≠ e := fun hbe => he_not_events
        (hbe ▸ ⟨r', E', hL', hb⟩)
      rw [hvis]
      constructor
      · rintro (h | ⟨_, rfl⟩)
        · exact h
        · exact absurd rfl hb_ne
      · exact Or.inl
  · -- vis-transitivity.
    intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    rcases hab with hab | ⟨ha_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact Or.inl (h_tr hab hbc)
      · exact Or.inr ⟨C.vis_causal hab h_ev hb_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact absurd hbc (h_no_vis_out c)
      · exact absurd hb_ev he_not_ev
  · -- vis-irreflexivity.
    intro a ha
    rw [hvis] at ha
    rcases ha with ha | ⟨ha_ev, rfl⟩
    · exact h_ir a ha
    · exact he_not_ev ha_ev

/-- **Merge preserves the invariant** — the Join Lemma at work. -/
theorem goodConfig_merge (hJoin : JoinLemma D)
    {C C' : Configuration D} {r₁ r₂ : Replica}
    {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁ : C.N r₁ = some s₁) (h_s₂ : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (h : GoodConfig C) : GoodConfig C' := by
  obtain ⟨h_can, h_tr, h_ir⟩ := h
  have h_same : ∀ E' s',
      IsCanonicalState C E' s' → IsCanonicalState C' E' s' :=
    fun E' s' => isCanonicalState_congr
      (fun a _ b _ => by rw [hvis])
  refine ⟨?_, fun ha hb => hvis ▸ h_tr (hvis ▸ ha) (hvis ▸ hb),
    fun a ha => h_ir a (hvis ▸ ha)⟩
  intro r' s' E' hN' hL'
  rw [hN] at hN'; rw [hL] at hL'
  by_cases hr' : r' = r₁
  · subst hr'
    simp [updateRep] at hN' hL'
    subst hN'; subst hL'
    refine h_same _ _ (hJoin C ev₁ ev₂ s₁ s₂ h_tr h_ir
      (fun a ha => ⟨r', ev₁, h_ev₁, ha⟩)
      (fun a ha => ⟨r₂, ev₂, h_ev₂, ha⟩)
      (fun a b hv _ hb => C.vis_causal hv h_ev₁ hb)
      (fun a b hv _ hb => C.vis_causal hv h_ev₂ hb)
      (h_can r' s₁ ev₁ h_s₁ h_ev₁) (h_can r₂ s₂ ev₂ h_s₂ h_ev₂))
  · simp [updateRep, hr'] at hN' hL'
    exact h_same _ _ (h_can r' s' E' hN' hL')

open LabeledTS in
/-- **The bridge theorem, corrected.** For a CRDT satisfying the core
bundle and the peel identities, every reachable configuration is
RA-linearizable. -/
theorem ra_linearizable_of_core_join
    (hVC : CoreVCs D) (hPeel : JoinPeelVCs D)
    (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C := by
  have hJoin : JoinLemma D := join_lemma_of_peel hVC hPeel
  suffices h : GoodConfig C from isRALinearizable_of_canonical h.1
  induction hReach with
  | refl => exact goodConfig_init
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica _ _ hN hL hvis =>
      exact goodConfig_createReplica hN hL hvis ih
    | apply h_s h_ev h_fresh_t _ hN hL hvis =>
      exact goodConfig_apply h_s h_ev h_fresh_t hN hL hvis ih
    | merge h_s₁ h_s₂ h_ev₁ h_ev₂ _ hN hL hvis =>
      exact goodConfig_merge hJoin h_s₁ h_s₂ h_ev₁ h_ev₂ hN hL hvis ih
    | query _ _ => exact ih

end

end Sal.Emulation
