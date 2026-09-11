import Sal.MRDTs.Metatheory.Adequacy

namespace Sal.MRDTs
open Sal.MRDTs.Foundation
open Classical
variable {D : MRDTSig} [ReplayPolicy D.toUpdateSig]

/-- Store bookkeeping needs only the actual merge result's witness,
not a join theorem about arbitrary triples of replay witnesses. -/
theorem canonicalConfig_merge_result
    {C C' : Configuration D}
    {r₁ : Replica}
    {v₁ v₂ vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C)
    (hresult : IsCanonicalState C.replayContext (ev₁ ∪ ev₂) (D.merge sT s₁ s₂)) :
    CanonicalConfig C' := by
  have hLr₁ : C.headEvents r₁ = some ev₁ :=
    C.headEvents_eq_of_head_ver h_head₁ h_ver₁
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
      exact h_same _ _ hresult
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

end Sal.MRDTs
