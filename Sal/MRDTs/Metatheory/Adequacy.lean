import Sal.MRDTs.Framework.MergeLaws
import Sal.MRDTs.Metatheory.StoreInvariant
import Sal.MRDTs.Metatheory.Join.SetRelativeReplay

/-!
# ADEQUACY: Join preserves canonical configurations

The generic theorems establish `CanonicalConfig` for every configuration
reachable in the ternary transition system `Step` (from `initConfig`). Every
stored version, including historical GCAs, therefore has a canonical replay;
`HasReplayWitness` is a direct corollary.

* `CanonicalConfig`: the reachability invariant (every version canonical, plus
  the store closure facts) and its per-transition preservation;
* `CanonicalJoinLaws.join`: the primary constructor from the canonical-state
  law bundle to global `Join`;
* `JoinProof.ofArbitraryStateLaws` / `JoinProof.ofFeasibleStateLaws`: retained
  lower-level and compatibility constructors;
* `replayWitness_of_join`: the derived replay bridge;
* `causalDeltaLaw_of_all_comm`: the commuting class gets `CausalDeltaLaw` for free;
* `canonicalConfig_merge_causal` / `replayWitness_of_causalJoin`: the **full-closure**
  bridge consumed by the Enable-wins route (`CausalJoin`).
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical

section
variable {D : MRDTSig}

/-- Every stored version has a replay witness for the proof-local order. This
is derived from `CanonicalConfig`; it is not the client correctness target. -/
def HasReplayWitness (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (Sal.MRDTs.Foundation.lo (Configuration.replayContext C)) ∧
      applySeq D.toUpdateSig D.init π = s

/-- The reachability invariant: **every allocated version** holds the canonical
state of its event set (GCAs are historical versions, so replica heads are not
enough), plus `vis` transitivity/irreflexivity and the two facts historical
versions need: their event sets stay inside the replica-observed universe
(feeds Apply-freshness) and stay causally closed (feeds the Join Lemma's
backward-closure premises). -/
structure CanonicalConfig (C : Configuration D) : Prop where
  canonical : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → IsCanonicalState (Configuration.replayContext C) E s
  vis_trans : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c
  vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a
  version_events_supported : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a ∈ E, a ∈ C.events
  version_events_causal : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a b, C.vis a b → b ∈ E → a ∈ E

/-- The strengthened invariant delivers per-version Def-lin
(`isCanonicalState_lo_witness`, reused). -/
theorem hasReplayWitness_of_canonical {C : Configuration D}
    (h : CanonicalConfig C) : HasReplayWitness C :=
  fun v s E hv => isCanonicalState_lo_witness (h.canonical v s E hv)

/-- The invariant holds initially: the only allocated version is `0 = (σ₀, ∅)`. -/
theorem canonicalConfig_init : CanonicalConfig (initConfig D) := by
  have hver : ∀ v, (initConfig D).ver v
      = if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v s E hv
    rw [hver] at hv
    by_cases h : v = 0
    · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.1, ← hv.2]
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩
    · rw [if_neg h] at hv
      simp at hv
  · intro a b c h _
    exact absurd h id
  · intro a h
    exact absurd h id
  · intro v s E hv a ha
    rw [hver] at hv
    by_cases h : v = 0
    · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.2] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [if_neg h] at hv
      simp at hv
  · intro v s E hv a b hab _
    exact absurd hab id

/-- **Fork preserves the invariant.** The fresh child version copies the
source head's canonical state and event set; visibility is unchanged. -/
theorem canonicalConfig_fork {C C' : Configuration D} {dst src : Replica}
    {v vnew : Version} {s : D.State} {ev : Set (Op D.AppOp)}
    (h_fresh : C.head dst = none)
    (h_sourceHead : C.head src = some v)
    (h_sourceVersion : C.ver v = some (s, ev))
    (hL : C'.headEvents = updateRep C.headEvents dst ev)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vnew then some (s, ev) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  have hLsrc : C.headEvents src = some ev :=
    C.headEvents_eq_of_head_ver h_sourceHead h_sourceVersion
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = dst
    · subst hr''
      simp [Configuration.headEvents, headEventsFrom, h_fresh] at hLr''
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.replayContext C) E' s' →
      IsCanonicalState (Configuration.replayContext C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [Configuration.replayContext_vis, Configuration.replayContext_vis, hvis]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w sw E hw
    by_cases hwnew : w = vnew
    · subst w
      rw [hver] at hw
      simp only [if_pos, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      exact h_same ev s (h.canonical v s ev h_sourceVersion)
    · simp only [hver, hwnew, ↓reduceIte] at hw
      exact h_same E sw (h.canonical w sw E hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w sw E hw a ha
    by_cases hwnew : w = vnew
    · subst w
      rw [hver] at hw
      simp only [if_pos, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      refine ⟨dst, ev, ?_, ha⟩
      rw [hL]
      simp [updateRep]
    · simp only [hver, hwnew, ↓reduceIte] at hw
      exact h_events a (h.version_events_supported w sw E hw a ha)
  · intro w sw E hw a b hab hb
    by_cases hwnew : w = vnew
    · subst w
      rw [hver] at hw
      simp only [if_pos, Option.some.injEq, Prod.mk.injEq] at hw
      rw [hvis] at hab
      rw [← hw.2] at hb ⊢
      exact h.version_events_causal v s ev h_sourceVersion a b hab hb
    · simp only [hver, hwnew, ↓reduceIte] at hw
      rw [hvis] at hab
      exact h.version_events_causal w sw E hw a b hab hb

/-- **Apply preserves the invariant**: the fresh version extends its parent's
canonical state (`isCanonicalState_extend`); every old version is untouched
because the fresh event lies outside its (universe-bounded) event set. -/
theorem canonicalConfig_apply {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hL : C'.headEvents = updateRep C.headEvents r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  set e : Op D.AppOp := (t, r, o) with he_def
  have hLr : C.headEvents r = some ev :=
    C.headEvents_eq_of_head_ver h_head h_ver
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some (D.update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  -- The event universe only grows (the touched replica's set grows).
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      rw [hLr, Option.some.injEq] at hLr''
      refine ⟨r'', ev ∪ {e}, ?_, Or.inl (hLr'' ▸ hx)⟩
      rw [hL]
      simp [updateRep]
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have hL'r : C'.headEvents r = some (ev ∪ {e}) := by
    rw [hL]
    simp [updateRep]
  -- Old event sets do not contain the fresh event.
  have h_old_no_e : ∀ (w : Version) (s' : D.State) (E' : Set (Op D.AppOp)),
      C.ver w = some (s', E') → e ∉ E' := by
    intro w s' E' hw hmem
    exact he_not_events (h.version_events_supported w s' E' hw e hmem)
  -- vis is unchanged on pairs of old events.
  have h_vis_old : ∀ (E' : Set (Op D.AppOp)), (∀ x ∈ E', x ∈ C.events) →
      ∀ a, a ∈ E' → ∀ b, b ∈ E' → (C'.vis a b ↔ C.vis a b) := by
    intro E' hsub a _ b hb
    rw [hvis]
    constructor
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
    · exact Or.inl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      -- extend the parent's canonical state by the fresh event
      have h_old : IsCanonicalState (Configuration.replayContext C) ev s :=
        h.canonical v s ev h_ver
      have h_old' : IsCanonicalState (Configuration.replayContext C') ev s := by
        refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
        rw [Configuration.replayContext_vis, Configuration.replayContext_vis]
        exact h_vis_old ev h_ev_events a ha b hb
      have h_ext := isCanonicalState_extend (e := e) he_not_ev
        (fun x hx => by
          rw [Configuration.replayContext_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
        (fun x hx => by
          rw [Configuration.replayContext_vis, hvis]
          rintro (hex | ⟨he_ev, _⟩)
          · exact h_no_vis_out x hex
          · exact he_not_ev he_ev)
        h_old'
      rw [Set.union_singleton]
      exact h_ext
    · rw [hver_old w hwn] at hw
      have h_old : IsCanonicalState (Configuration.replayContext C) E' s' :=
        h.canonical w s' E' hw
      refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
      rw [Configuration.replayContext_vis, Configuration.replayContext_vis]
      exact h_vis_old E' (h.version_events_supported w s' E' hw) a ha b hb
  · -- vis-transitivity
    intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    rcases hab with hab | ⟨ha_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact Or.inl (h.vis_trans hab hbc)
      · exact Or.inr ⟨h.version_events_causal v s ev h_ver a b hab hb_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact absurd hbc (h_no_vis_out c)
      · exact absurd hb_ev he_not_ev
  · -- vis-irreflexivity
    intro a ha
    rw [hvis] at ha
    rcases ha with ha | ⟨ha_ev, rfl⟩
    · exact h.vis_irrefl a ha
    · exact he_not_ev ha_ev
  · -- version_events_supported
    intro w s' E' hw a ha
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      rcases ha with ha | ha
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inl ha⟩
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inr ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.version_events_supported w s' E' hw a ha)
  · -- version_events_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · -- b is an old event of the parent set
        rcases hab with hab | ⟨_, rfl⟩
        · exact Or.inl (h.version_events_causal v s ev h_ver a b hab hb)
        · exact absurd hb he_not_ev
      · -- b is the fresh event
        have hb_e : b = e := hb
        subst hb_e
        rcases hab with hab | ⟨ha_ev, _⟩
        · exfalso
          obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_tgt hab
          exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
        · exact Or.inl ha_ev
    · rw [hver_old w hwn] at hw
      rcases hab with hab | ⟨_, rfl⟩
      · exact h.version_events_causal w s' E' hw a b hab hb
      · exact absurd hb (h_old_no_e w s' E' hw)

/-- **Merge preserves the invariant**, `Join` at work, with the GCA event
set delivered by the `gca_events` field (its maintainability is
`gca_events_of_storeInv`), and the GCA version's canonical state delivered by the
every-version coverage of `CanonicalConfig`. -/
theorem canonicalConfig_merge_at
    {C C' : Configuration D}
    (hJoin : JoinAt D (Configuration.replayContext C))
    {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_gca : IsGCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  have hLr₁ : C.headEvents r₁ = some ev₁ :=
    C.headEvents_eq_of_head_ver h_head₁ h_ver₁
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.gca_events h_gca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.replayContext C) E' s' →
      IsCanonicalState (Configuration.replayContext C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [Configuration.replayContext_vis, Configuration.replayContext_vis, hvis]
  have hL'r₁ : C'.headEvents r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      -- the Join Lemma at the projected replay context
      have hcT : IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂) sT := by
        rw [← hevT_eq]
        exact h.canonical vT sT evT h_verT
      have h_join := hJoin ev₁ ev₂ sT s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.version_events_supported v₁ s₁ ev₁ h_ver₁)
        (h.version_events_supported v₂ s₂ ev₂ h_ver₂)
        (fun a b hab _ hb => h.version_events_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab _ hb => h.version_events_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · -- version_events_supported
    intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.version_events_supported w s' E' hw a ha)
  · -- version_events_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.version_events_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.version_events_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.version_events_causal w s' E' hw a b hab hb


/-! ### Commuting updates discharge the causal-delta law

`↓e∖{e} = ∅`, so `B = init` and the bound is `commuting_peel` at an empty
GCA fold plus `merge_init`, no idempotence needed (the binary
`binaryCausalDeltaLaw_of_all_comm` consumed `merge_idem`; the ternary one does not). -/

theorem causalDeltaLaw_of_all_comm (hVC : MergeLaws D)
    (hPeel : CommutingPeelLaw D)
    (h_comm : ∀ a b : Op D.AppOp, D.toUpdateSig.commutes a b) : CausalDeltaLaw D := by
  intro C U A B e _ _ _ _ _ _ hA hB
  have h_down : downset C e \ {e} = ∅ := by
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (hx | hx)
    · exact fun hne => hne hx
    · intro _
      exfalso
      cases hx with
      | single h' => exact h'.2 (h_comm _ _)
      | tail _ h' => exact h'.2 (h_comm _ _)
  have hBinit : B = D.init := isCanonicalState_empty h_down hB
  subst hBinit
  obtain ⟨ρ, hpA, -, hfA⟩ := id hA
  have h0 : applySeq D.toUpdateSig D.init ([] : List (Op D.AppOp)) = D.init :=
    rfl
  have hpc := hPeel.commuting_peel D.init e [] ρ
    (fun x hx => absurd hx List.not_mem_nil)
    (fun x _ => h_comm e x)
  rw [h0] at hpc
  rw [hVC.merge_init] at hpc
  rw [← hfA, hVC.merge_comm, hpc]

/-- The original `Join`-driven form, as a thin wrapper over
`canonicalConfig_merge_at`. -/
theorem canonicalConfig_merge (hJoin : Join D)
    {C C' : Configuration D} {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_gca : IsGCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' :=
  canonicalConfig_merge_at (hJoin.at _) h_head₁ h_ver₁ h_ver₂ h_gca h_verT
    hL hvis hver h

/-! ### End-to-end: the `CanonicalConfig` induction against any `Join` -/

open LabeledTS in
/-- The per-version replay-witness bridge from an abstract ternary Join
Lemma, proved by induction over the sole MRDT transition system. -/
theorem replayWitness_of_join (hJoin : Join D)
    (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    HasReplayWitness C := by
  suffices h : CanonicalConfig C from hasReplayWitness_of_canonical h
  induction hReach with
  | refl => exact canonicalConfig_init
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | fork h_fresh h_sourceHead h_sourceVersion h_vnew h_rank C'
        hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vnew hver hhead
      exact canonicalConfig_fork h_fresh h_sourceHead h_sourceVersion hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vnew hver hhead
      exact canonicalConfig_apply h_head h_ver h_fresh_t hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_gca h_verT h_vm h_rank₁
        h_rank₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vm hver hhead
      exact canonicalConfig_merge hJoin h_head₁ h_ver₁ h_ver₂ h_gca h_verT
        hL hvis hver ih
    | query h_s h_val => exact ih

/-- The arbitrary-state contract implies the feasible one (context discarded);
`merge_init` supplies the unit law. The universal-law route is thereby an
adapter into the canonical-state contract. -/
theorem feasibleDeltaLaws_of_delta (hVC : MergeLaws D) (hΔ : DeltaLaws D) :
    FeasibleDeltaLaws D :=
  ⟨fun _ _ s _ _ => hVC.merge_init s,
   fun _ _ _ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
     hΔ.local_redistribute s₀ B t₁ (D.update B e) s₂,
   fun _ _ _ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
     hΔ.redistribute B t₀ t₁ t₂ (D.update B e)⟩

/-! ### Private plumbing (copies; the originals are private upstream) -/

private theorem listPermOf_length_lt_feasible {α : Type} {l l' : List α}
    {ev ev' : Set α} {x : α}
    (h : listPermOf l ev) (h' : listPermOf l' ev')
    (hsub : ev ⊆ ev') (hx : x ∈ ev') (hxn : x ∉ ev) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

private theorem exists_listPermOf_subset_feasible {α : Type} {l : List α}
    {T S : Set α} (h : listPermOf l T) (hsub : S ⊆ T) :
    ∃ l', listPermOf l' S := by
  classical
  refine ⟨l.filter (fun a => decide (a ∈ S)), h.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(h.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- The Join Lemma at a fixed configuration and union-enumeration length. -/
private def FeasibleJoinAtSize (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig) (n : ℕ) :
    Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (lU : List (Op D.AppOp)),
    listPermOf lU (ev₁ ∪ ev₂) → lU.length = n →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

/-- Side decomposition for the slim core. Only the replay laws and branch
commutativity are consumed. -/
private theorem side_decomposition (hVC : JoinCoreLaws D) (hCD : CausalDeltaLaw D)
    {C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig}
    (h_tr : ∀ {a b c : Op D.AppOp},
      C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {n : ℕ} (IH : ∀ m, m < n → FeasibleJoinAtSize C m)
    {U : Set (Op D.AppOp)} {lU : List (Op D.AppOp)}
    (hpU : listPermOf lU U) (hlen : lU.length = n)
    (h_inU : ∀ a ∈ U, a ∈ C.events)
    (h_clU : ∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b →
      b ∈ U → a ∈ U)
    {e : Op D.AppOp} (h_e : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    {A B : D.State}
    (hA : IsCanonicalState C (U \ {e}) A)
    (hB : IsCanonicalState C (downset C e \ {e}) B)
    {E : Set (Op D.AppOp)} {s t : D.State}
    (h_subE : E ⊆ U)
    (h_inE : ∀ a ∈ E, a ∈ C.events)
    (h_clE : ∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b →
      b ∈ E → a ∈ E)
    (h_eE : e ∈ E)
    (hs : IsCanonicalState C E s)
    (ht : IsCanonicalState C (E \ {e}) t) :
    s = D.merge B t (D.update B e) := by
  classical
  have hU := hVC.replay
  have hT : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  by_cases hEU : E = U
  · subst hEU
    have h_eq : D.merge B A (D.update B e) = D.update A e :=
      hCD C E A B e h_tr h_ir h_inE h_clE h_eE h_max hA hB
    have htA : t = A :=
      isCanonicalState_unique_of_replayLaws hU (fun a ha => h_inE a ha.1) ht hA
    have hsA : s = D.update A e :=
      isCanonicalState_unique_of_replayLaws hU h_inE hs
        (isCanonicalState_snoc h_eE h_max hA)
    rw [htA, h_eq]
    exact hsA
  · obtain ⟨lE, hpE, -, -⟩ := id hs
    obtain ⟨x, hxU, hxE⟩ : ∃ x ∈ U, x ∉ E := by
      by_contra h
      push_neg at h
      exact hEU (Set.Subset.antisymm h_subE h)
    have hlt : lE.length < n := by
      rw [← hlen]
      exact listPermOf_length_lt_feasible hpE hpU h_subE hxU hxE
    have h_dsubE : downset C e ⊆ E := downset_subset h_clE h_eE
    have hsetI : (E \ {e}) ∩ downset C e = downset C e \ {e} := by
      ext y
      constructor
      · rintro ⟨⟨_, hyne⟩, hyd⟩
        exact ⟨hyd, hyne⟩
      · rintro ⟨hyd, hyne⟩
        exact ⟨⟨h_dsubE hyd, hyne⟩, hyd⟩
    have hsetE : (E \ {e}) ∪ downset C e = E := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact hy.1
        · exact h_dsubE hy
      · intro hy
        by_cases hye : y = e
        · subst hye
          exact Or.inr self_mem_downset
        · exact Or.inl ⟨hy, hye⟩
    have hB' : IsCanonicalState C ((E \ {e}) ∩ downset C e) B := by
      rw [hsetI]
      exact hB
    have h_merge_can : IsCanonicalState C ((E \ {e}) ∪ downset C e)
        (D.merge B t (D.update B e)) := by
      refine IH lE.length hlt _ _ B t (D.update B e) lE ?_ rfl
        (fun a ha => h_inE a ha.1)
        (fun a ha => h_inE a (h_dsubE ha))
        (closure_diff_of_max h_subE h_clE h_max)
        downset_closed hB' ht hT
      rw [hsetE]
      exact hpE
    have h_merge_can' : IsCanonicalState C E
        (D.merge B t (D.update B e)) := by
      rw [← hsetE]
      exact h_merge_can
    exact isCanonicalState_unique_of_replayLaws hU h_inE hs h_merge_can'

/-! ### The canonical-state master induction -/

/-- **Global Join from the slim core, feasible delta laws, and the
causal-delta law.** This induction replaces the direct arbitrary-state
redistribution rewrites and empty-side unit law by their feasible-tuple forms;
the hypotheses each feasible law demands are exactly those in scope at its
call site. -/
theorem JoinProof.ofFeasibleStateLaws (hVC : JoinCoreLaws D)
    (hFΔ : FeasibleDeltaLaws D) (hCD : CausalDeltaLaw D) : Join D := by
  intro C ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  classical
  have hU := hVC.replay
  obtain ⟨l₁, hp₁, -, -⟩ := id hc₁
  obtain ⟨l₂, hp₂, -, -⟩ := id hc₂
  have hpU₀ := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  suffices gen : ∀ n, FeasibleJoinAtSize (D := D) C n by
    exact gen _ ev₁ ev₂ s₀ s₁ s₂ _ hpU₀ rfl h_in₁ h_in₂ h_cl₁ h_cl₂
      hc₀ hc₁ hc₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ev₁ ev₂ s₀ s₁ s₂ lU hpU hlen h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
    -- Empty sides collapse via the feasible unit law.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init := isCanonicalState_empty h_e₁ hc₁
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₁, Set.empty_inter]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      have hinit := hFΔ.init C ev₂ s₂ h_in₂ hc₂
      subst h_e₁
      rw [hs₀, hs₁, hinit, Set.empty_union]
      exact hc₂
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init := isCanonicalState_empty h_e₂ hc₂
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₂, Set.inter_empty]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      have hinit := hFΔ.init C ev₁ s₁ h_in₁ hc₁
      subst h_e₂
      rw [hs₀, hs₂, hVC.merge_comm, hinit, Set.union_empty]
      exact hc₁
    -- Select a loOn(∪)-maximal event; build A = σ(U∖e), B = σ(↓e∖e).
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have h_clU : ∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b →
        b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
      rintro a b hv hnc (h | h)
      · exact Or.inl (h_cl₁ a b hv hnc h)
      · exact Or.inr (h_cl₂ a b hv hnc h)
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_loOn_maximal_of_replayLaws hU h_tr h_ir hpU h_inU ⟨x₁, Or.inl hx₁⟩
    have h_e_lU : e ∈ lU := (hpU.2 e).mpr he_U
    have hpU' : listPermOf (lU.filter (· ≠ e)) ((ev₁ ∪ ev₂) \ {e}) :=
      filter_ne_listPermOf hpU h_e_lU
    have hlen' : (lU.filter (· ≠ e)).length = n - 1 := by
      rw [listPermOf_diff_length hpU h_e_lU hpU', hlen]
    have h_pos : 0 < n := by
      rw [← hlen]
      exact List.length_pos_of_mem h_e_lU
    obtain ⟨A, hA⟩ : ∃ A, IsCanonicalState C ((ev₁ ∪ ev₂) \ {e}) A :=
      isCanonicalState_exists_of_replayLaws hU h_tr h_ir hpU'
        (fun a ha => h_inU a ha.1)
    have h_dsub : downset C e ⊆ ev₁ ∪ ev₂ := downset_subset h_clU he_U
    obtain ⟨lB, hpB⟩ :=
      exists_listPermOf_subset_feasible hpU
        (fun x (hx : x ∈ downset C e \ {e}) => h_dsub hx.1)
    obtain ⟨B, hB⟩ : ∃ B, IsCanonicalState C (downset C e \ {e}) B :=
      isCanonicalState_exists_of_replayLaws hU h_tr h_ir hpB
        (fun a ha => h_inU a (h_dsub ha.1))
    have h_cd : D.merge B A (D.update B e) = D.update A e :=
      hCD C (ev₁ ∪ ev₂) A B e h_tr h_ir h_inU h_clU he_U h_max hA hB
    have h_target : IsCanonicalState C (ev₁ ∪ ev₂) (D.update A e) :=
      isCanonicalState_snoc he_U h_max hA
    by_cases he₁ : e ∈ ev₁
    · obtain ⟨t₁, ht₁⟩ : ∃ t, IsCanonicalState C (ev₁ \ {e}) t := by
        obtain ⟨l₁', hp₁', -, -⟩ := id hc₁
        have h_e_l₁ : e ∈ l₁' := (hp₁'.2 e).mpr he₁
        exact isCanonicalState_exists_of_replayLaws hU h_tr h_ir
          (filter_ne_listPermOf hp₁' h_e_l₁) (fun a ha => h_in₁ a ha.1)
      have hs₁d : s₁ = D.merge B t₁ (D.update B e) :=
        side_decomposition hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_left h_in₁ h_cl₁ he₁ hc₁ ht₁
      by_cases he₂ : e ∈ ev₂
      · -- e shared: feasible redistribution.
        obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
          obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
          have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
          exact isCanonicalState_exists_of_replayLaws hU h_tr h_ir
            (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
        have hs₂d : s₂ = D.merge B t₂ (D.update B e) :=
          side_decomposition hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂
            hc₂ ht₂
        have he₀ : e ∈ ev₁ ∩ ev₂ := ⟨he₁, he₂⟩
        have h_in₀ : ∀ a ∈ ev₁ ∩ ev₂, a ∈ C.events :=
          fun a ha => h_in₁ a ha.1
        have h_cl₀ : ∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b →
            b ∈ ev₁ ∩ ev₂ → a ∈ ev₁ ∩ ev₂ :=
          fun a b hv hnc hb =>
            ⟨h_cl₁ a b hv hnc hb.1, h_cl₂ a b hv hnc hb.2⟩
        obtain ⟨l₀', hp₀'⟩ :=
          exists_listPermOf_subset_feasible hpU
            (show (ev₁ ∩ ev₂) \ {e} ⊆ ev₁ ∪ ev₂ from
              fun x hx => Or.inl hx.1.1)
        obtain ⟨t₀, ht₀⟩ :
            ∃ t, IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t :=
          isCanonicalState_exists_of_replayLaws hU h_tr h_ir hp₀'
            (fun a ha => h_in₁ a ha.1.1)
        have hs₀d : s₀ = D.merge B t₀ (D.update B e) :=
          side_decomposition hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB
            (show ev₁ ∩ ev₂ ⊆ ev₁ ∪ ev₂ from fun x hx => Or.inl hx.1)
            h_in₀ h_cl₀ he₀ hc₀ ht₀
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ (ev₂ \ {e})) t₀ := by
          rw [diff_inter_diff]
          exact ht₀
        have hsetm : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ (ev₂ \ {e}))
            (D.merge t₀ t₁ t₂) := by
          refine IH (n - 1) (by omega) _ _ t₀ t₁ t₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
            hct₀' ht₁ ht₂
          rw [hsetm]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.merge t₀ t₁ t₂) := by
          rw [← hsetm]
          exact h_mid_can
        have h_mid : D.merge t₀ t₁ t₂ = A :=
          isCanonicalState_unique_of_replayLaws hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_redis := hFΔ.redistribute C ev₁ ev₂ t₀ t₁ t₂ B e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          ht₀ hB ht₁ ht₂
        rw [hs₀d, hs₁d, hs₂d, h_redis, h_mid, h_cd]
        exact h_target
      · -- e local to side 1: feasible local redistribution.
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ ev₂) s₀ := by
          rw [inter_diff_left_of_not_mem he₂]
          exact hc₀
        have hset₁ : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ ev₂)
            (D.merge s₀ t₁ s₂) := by
          refine IH (n - 1) (by omega) _ _ s₀ t₁ s₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) h_in₂
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            h_cl₂ hct₀' ht₁ hc₂
          rw [hset₁]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.merge s₀ t₁ s₂) := by
          rw [← hset₁]
          exact h_mid_can
        have h_mid : D.merge s₀ t₁ s₂ = A :=
          isCanonicalState_unique_of_replayLaws hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_lr := hFΔ.local_redistribute C ev₁ ev₂ s₀ B t₁ s₂ e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          hc₀ hB ht₁ hc₂
        rw [hs₁d, h_lr, h_mid, h_cd]
        exact h_target
    · -- e local to side 2: mirror via merge_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
        obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
        have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
        exact isCanonicalState_exists_of_replayLaws hU h_tr h_ir
          (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
      have hs₂d : s₂ = D.merge B t₂ (D.update B e) :=
        side_decomposition hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂ hc₂ ht₂
      have hct₀' : IsCanonicalState C (ev₁ ∩ (ev₂ \ {e})) s₀ := by
        rw [inter_diff_right_of_not_mem he₁]
        exact hc₀
      have hset₂ : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      have h_mid_can : IsCanonicalState C (ev₁ ∪ (ev₂ \ {e}))
          (D.merge s₀ s₁ t₂) := by
        refine IH (n - 1) (by omega) _ _ s₀ s₁ t₂
          (lU.filter (· ≠ e)) ?_ hlen'
          h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
          (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
          hct₀' hc₁ ht₂
        rw [hset₂]
        exact hpU'
      have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
          (D.merge s₀ s₁ t₂) := by
        rw [← hset₂]
        exact h_mid_can
      have h_mid : D.merge s₀ s₁ t₂ = A :=
        isCanonicalState_unique_of_replayLaws hU (fun a ha => h_inU a ha.1)
          h_mid_can' hA
      -- The mirrored feasible law instance (sides swapped).
      have h_max' : ∀ x ∈ ev₂ ∪ ev₁, x ≠ e →
          ¬ loOn C (ev₂ ∪ ev₁) e x := by
        rw [Set.union_comm]
        exact h_max
      have hc₀_swap : IsCanonicalState C (ev₂ ∩ ev₁) s₀ := by
        rw [Set.inter_comm]
        exact hc₀
      have h_lr := hFΔ.local_redistribute C ev₂ ev₁ s₀ B t₂ s₁ e
        h_tr h_ir h_in₂ h_in₁ h_cl₂ h_cl₁ he₂ he₁ h_max'
        hc₀_swap hB ht₂ hc₁
      rw [hs₂d, hVC.merge_comm s₀ s₁, h_lr,
        hVC.merge_comm s₀ t₂ s₁, h_mid, h_cd]
      exact h_target

/-- Package stronger arbitrary-state equations as the common canonical-state
Join-law contract. -/
def CanonicalJoinLaws.ofArbitrary (hVC : MergeLaws D) (hΔ : DeltaLaws D)
    (hCD : CausalDeltaLaw D) : CanonicalJoinLaws D where
  core := hVC.toJoinCore
  delta := feasibleDeltaLaws_of_delta hVC hΔ
  causal_delta := hCD

/-- The primary reusable constructor: the canonical-state law bundle implies
all-context `Join`. -/
theorem CanonicalJoinLaws.join (h : CanonicalJoinLaws D) : Join D :=
  JoinProof.ofFeasibleStateLaws h.core h.delta h.causal_delta

/-- The arbitrary-state constructor is the universal-law adapter followed by
the canonical-state Join theorem. -/
theorem JoinProof.ofArbitraryStateLaws (hVC : MergeLaws D) (hΔ : DeltaLaws D)
    (hCD : CausalDeltaLaw D) : Join D :=
  (CanonicalJoinLaws.ofArbitrary hVC hΔ hCD).join

/-- Compatibility name for the feasible-state Join constructor. -/
theorem join_of_feasible_delta (hVC : JoinCoreLaws D)
    (hFΔ : FeasibleDeltaLaws D) (hCD : CausalDeltaLaw D) : Join D :=
  JoinProof.ofFeasibleStateLaws hVC hFΔ hCD

/-- Compatibility name for the arbitrary-state Join constructor. -/
theorem join_of_delta (hVC : MergeLaws D) (hΔ : DeltaLaws D)
    (hCD : CausalDeltaLaw D) : Join D :=
  JoinProof.ofArbitraryStateLaws hVC hΔ hCD

end

section Bridge
variable {D : MRDTSig}

/-- Merge preservation from a full-closure join lemma (the `CanonicalConfig`
merge case verbatim, passing `version_events_causal` un-weakened). -/
theorem canonicalConfig_merge_causal (hJoin : CausalJoin D)
    {C C' : Configuration D} {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_gca : IsGCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  have hLr₁ : C.headEvents r₁ = some ev₁ :=
    C.headEvents_eq_of_head_ver h_head₁ h_ver₁
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.gca_events h_gca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.replayContext C) E' s' →
      IsCanonicalState (Configuration.replayContext C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [Configuration.replayContext_vis, Configuration.replayContext_vis, hvis]
  have hL'r₁ : C'.headEvents r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂) sT := by
        rw [← hevT_eq]
        exact h.canonical vT sT evT h_verT
      have h_join := hJoin (Configuration.replayContext C) ev₁ ev₂ sT s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.version_events_supported v₁ s₁ ev₁ h_ver₁)
        (h.version_events_supported v₂ s₂ ev₂ h_ver₂)
        (fun a b hab hb => h.version_events_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab hb => h.version_events_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.version_events_supported w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.version_events_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.version_events_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.version_events_causal w s' E' hw a b hab hb

open LabeledTS in
/-- The end-to-end bridge from a full-closure join lemma. -/
theorem replayWitness_of_causalJoin (hJoin : CausalJoin D)
    (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    HasReplayWitness C := by
  suffices h : CanonicalConfig C from hasReplayWitness_of_canonical h
  induction hReach with
  | refl => exact canonicalConfig_init
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | fork h_fresh h_sourceHead h_sourceVersion h_vnew h_rank C'
        hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vnew hver hhead
      exact canonicalConfig_fork h_fresh h_sourceHead h_sourceVersion hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vnew hver hhead
      exact canonicalConfig_apply h_head h_ver h_fresh_t hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_gca h_verT h_vm h_rank₁
        h_rank₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vm hver hhead
      exact canonicalConfig_merge_causal hJoin h_head₁ h_ver₁ h_ver₂ h_gca h_verT
        hL hvis hver ih
    | query h_s h_val => exact ih

end Bridge

end Sal.MRDTs
