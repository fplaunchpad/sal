import Sal.ConditionedMRDTs.Metatheory.GenHonest

/-! # Witness-class canonicity — the corrected direct-witness route

`IsCanonicalState` is existential in its enumeration, and for datatypes whose
canonical states are **not unique** per event set (Shesha: a concurrent
`(ins x←a, del a)` pair folds to different live sets under the two orders)
the plain `JoinLemma3At` interface is too weak — the LCA slot and the branch
slots may be handed folds of incompatible enumeration choices, and the merge
of such a misaligned triple need not be canonical at all. This is not
hypothetical: `Shesha_Join_Refuted.lean` machine-checks a counterexample at
an honest configuration.

The repair: real executions only ever register folds of a restricted
**witness class** `W` (for Shesha: *effective* enumerations — every insert
applies). This file parameterizes the direct-witness route by `W`:

* `IsCanonicalStateW W` — canonicity with the witness drawn from `W`;
* `JoinLemma3AtW` — the ternary join over `W`-witnesses (the per-datatype
  hook, now with `W`-aligned inputs *and* a `W`-obligation on the output);
* `GoodConfigW P W` — the strengthened reachability invariant: the plain
  `GoodConfig3` **plus**, conditionally on `GenHonest D P`, a `W`-witness at
  every registered version;
* `ra_linearizable3_of_genHonest_reachW` — the capstone: per-version
  RA-linearizability at every `GenHonest`-honestly reachable configuration,
  from the `W`-join plus two `W`-bookkeeping facts (`W []`, and `W` extends
  by a fresh event whose guard `P` holds at the current fold).

The step cases mirror `Adequacy.lean`'s `goodConfig3_*` preservation lemmas;
the merge case re-derives the plain `canonical` field by weakening the
`W`-join's conclusion, so no (refuted) plain `JoinLemma3At` is ever needed. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

section CanonW

variable {D' : CRDTSig}

/-- `s` is the canonical state of `ev` **with a `W`-witness**: the fold of
some `loOn`-respecting enumeration drawn from the witness class `W`. -/
def IsCanonicalStateW (W : List (Op D'.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D') (ev : Set (Op D'.AppOp))
    (s : D'.State) : Prop :=
  ∃ ρ : List (Op D'.AppOp),
    listPermOf ρ ev ∧ respects ρ (loOn C ev) ∧ W ρ ∧
    applySeq D' D'.init ρ = s

/-- A `W`-witness is in particular a plain witness. -/
theorem IsCanonicalStateW.weaken {W : List (Op D'.AppOp) → Prop}
    {C : Sal.Emulation.Configuration D'} {ev : Set (Op D'.AppOp)}
    {s : D'.State} (h : IsCanonicalStateW W C ev s) :
    IsCanonicalState C ev s := by
  obtain ⟨ρ, hp, hr, -, hf⟩ := h
  exact ⟨ρ, hp, hr, hf⟩

/-- Mirror of `isCanonicalState_congr`: `loOn` is local to the set, and the
witness class does not mention the configuration. -/
theorem isCanonicalStateW_congr {W : List (Op D'.AppOp) → Prop}
    {C C' : Sal.Emulation.Configuration D'}
    {E : Set (Op D'.AppOp)} {s : D'.State}
    (h_vis : ∀ a ∈ E, ∀ b ∈ E, (C'.vis a b ↔ C.vis a b))
    (h : IsCanonicalStateW W C E s) : IsCanonicalStateW W C' E s := by
  obtain ⟨ρ, hp, hr, hW, hf⟩ := h
  refine ⟨ρ, hp, ?_, hW, hf⟩
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

/-- Mirror of `isCanonicalState_extend`, with the `W`-extension supplied: a
fresh event that observed everything in `ev` extends a `W`-canonical state by
one update. -/
theorem isCanonicalStateW_extend {W : List (Op D'.AppOp) → Prop}
    {C : Sal.Emulation.Configuration D'}
    {ev : Set (Op D'.AppOp)} {s : D'.State} {e : Op D'.AppOp}
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, C.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ C.vis e x)
    (hWext : ∀ ρ, listPermOf ρ ev → W ρ →
      applySeq D' D'.init ρ = s → W (ρ ++ [e]))
    (h : IsCanonicalStateW W C ev s) :
    IsCanonicalStateW W C (insert e ev) (D'.update s e) := by
  obtain ⟨ρ, hp, hr, hW, hs⟩ := h
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, hWext ρ hp hW hs, ?_⟩
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
      hn (loOn_mono (Set.subset_insert _ _) h')), ?_, ?_⟩
    · exact List.pairwise_singleton _ _
    · intro y hy b hb
      rw [List.mem_singleton] at hb; subst hb
      have hy_ev : y ∈ ev := (hp.2 y).mp hy
      rintro (⟨h_vis, _⟩ | ⟨_, h_nvis_ye, _, _⟩)
      · exact h_e_last y hy_ev h_vis
      · exact h_nvis_ye (h_e_sees y hy_ev)
  · rw [applySeq_append_single, hs]

end CanonW

section GoodW

variable {D : ConditionedMRDTSig}

/-- The ternary Join Lemma over `W`-witnesses, at a single configuration:
the per-datatype hook of the corrected direct-witness route. Note the inputs
are `W`-aligned *and* the output owes a `W`-witness. -/
def JoinLemma3AtW (D : ConditionedMRDTSig) (W : List (Op D.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalStateW W C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateW W C ev₁ s₁ → IsCanonicalStateW W C ev₂ s₂ →
    IsCanonicalStateW W C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- **The strengthened reachability invariant**: plain `GoodConfig3`, plus —
conditionally on the honesty of the configuration — a `W`-witness at every
registered version. The conditioning is what lets a (possibly dishonest)
final step keep the plain half. -/
structure GoodConfigW (P : Op D.AppOp → D.State → Prop)
    (W : List (Op D.AppOp) → Prop) (C : Configuration D) : Prop where
  good : GoodConfig3 C
  canonW : GenHonest D P C →
    ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
      C.ver v = some (s, E) →
      IsCanonicalStateW W (Configuration.core C) E s

variable {P : Op D.AppOp → D.State → Prop} {W : List (Op D.AppOp) → Prop}

/-- The invariant holds initially (`W []` seeds the empty witness). -/
theorem goodConfigW_init (hInit : D.Inv D.init) (hW0 : W []) :
    GoodConfigW P W (initConfig D hInit) := by
  refine ⟨goodConfig3_init hInit, ?_⟩
  intro _ v s E hv
  have hv' : (if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none)
      = some (s, E) := hv
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv'
    rw [← hv'.1, ← hv'.2]
    exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, hW0, rfl⟩
  · rw [if_neg h] at hv'
    exact absurd hv' (by simp)

/-- CreateReplica preserves the invariant (store and `vis` unchanged). -/
theorem goodConfigW_createReplica {C C' : Configuration D} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfigW P W C) (hHonC : GenHonest D P C) :
    GoodConfigW P W C' := by
  refine ⟨goodConfig3_createReplica h_fresh hL hvis hver h.good, ?_⟩
  intro _ v s E hv
  rw [hver] at hv
  refine isCanonicalStateW_congr (fun a _ b _ => ?_) (h.canonW hHonC v s E hv)
  rw [core_vis, core_vis, hvis]

/-- Apply preserves the invariant. The plain half is `goodConfig3_apply`
verbatim; the `W`-half extends the parent's `W`-witness by the fresh event,
whose guard `P` holds at the parent's fold **because the fresh event's causal
past in `C'` is exactly the parent's event set** — this is where the
conditional honesty hypothesis (`GenHonest D P C'`) is consumed. -/
theorem goodConfigW_apply {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (hWstep : ∀ (ρ : List (Op D.AppOp)) (s' : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s' → P (t, r, o) s' →
      W (ρ ++ [(t, r, o)]))
    (h : GoodConfigW P W C) (hHonC : GenHonest D P C) :
    GoodConfigW P W C' := by
  refine ⟨goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver h.good, ?_⟩
  intro hHonC' w s' E' hw
  set e : Op D.AppOp := (t, r, o) with he_def
  have hco := C.head_coherent r v h_head
  have hLr : C.L r = some ev := by
    rw [← hco.2, h_ver]; rfl
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some (D.update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ u, u ≠ vnew → C'.ver u = C.ver u := by
    intro u hu; rw [hver]; simp [hu]
  have hL'r : C'.L r = some (ev ∪ {e}) := by
    rw [hL]
    simp [updateRep]
  have h_vis_old : ∀ (E'' : Set (Op D.AppOp)), (∀ x ∈ E'', x ∈ C.events) →
      ∀ a, a ∈ E'' → ∀ b, b ∈ E'' → (C'.vis a b ↔ C.vis a b) := by
    intro E'' hsub a _ b hb
    rw [hvis]
    constructor
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
    · exact Or.inl
  by_cases hwn : w = vnew
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    -- the fresh event's causal past in `C'` is exactly `ev`
    have he_events' : e ∈ C'.events := ⟨r, ev ∪ {e}, hL'r, Or.inr rfl⟩
    have hpast : {e' ∈ C'.events | C'.vis e' e} = ev := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨hxev, hxvis⟩
        rw [hvis] at hxvis
        rcases hxvis with hx | ⟨hx, -⟩
        · obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_tgt hx
          exact absurd ⟨r₀, s₀, hL₀, hs₀⟩ he_not_events
        · exact hx
      · intro hx
        refine ⟨?_, ?_⟩
        · obtain ⟨r₀, s₀, hL₀, hs₀⟩ := h_ev_events x hx
          by_cases hr₀ : r₀ = r
          · subst hr₀
            rw [hLr, Option.some.injEq] at hL₀
            exact ⟨r₀, ev ∪ {e}, hL'r, Or.inl (hL₀ ▸ hs₀)⟩
          · refine ⟨r₀, s₀, ?_, hs₀⟩
            rw [hL]
            simp only [updateRep, if_neg hr₀]
            exact hL₀
        · rw [hvis]
          exact Or.inr ⟨hx, rfl⟩
    -- the parent's `W`-witness, transported to `C'`
    have h_old : IsCanonicalStateW W (Configuration.core C) ev s :=
      h.canonW hHonC v s ev h_ver
    have h_old' : IsCanonicalStateW W (Configuration.core C') ev s := by
      refine isCanonicalStateW_congr (fun a ha b hb => ?_) h_old
      rw [core_vis, core_vis]
      exact h_vis_old ev h_ev_events a ha b hb
    have h_ext := isCanonicalStateW_extend (e := e) he_not_ev
      (fun x hx => by
        rw [core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
      (fun x hx => by
        rw [core_vis, hvis]
        rintro (hex | ⟨he_ev, _⟩)
        · exact h_no_vis_out x hex
        · exact he_not_ev he_ev)
      (fun ρ hperm hW hfold => by
        refine hWstep ρ s hW hfold ?_
        have hP := hHonC' e he_events' ρ (by rw [hpast]; exact hperm)
        rw [hfold] at hP
        exact hP)
      h_old'
    rw [Set.union_singleton]
    exact h_ext
  · rw [hver_old w hwn] at hw
    refine isCanonicalStateW_congr (fun a ha b hb => ?_)
      (h.canonW hHonC w s' E' hw)
    rw [core_vis, core_vis]
    exact h_vis_old E' (h.good.ver_events_sub w s' E' hw) a ha b hb

/-- Merge preserves the invariant — the `W`-join at work. The plain
`canonical` field of `GoodConfig3 C'` is the *weakening* of the `W`-join's
conclusion, so the (refuted) plain `JoinLemma3At` is never consumed. -/
theorem goodConfigW_merge_at {C C' : Configuration D}
    (hHonC : GenHonest D P C)
    (hJoinW : JoinLemma3AtW D W (Configuration.core C))
    {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfigW P W C) : GoodConfigW P W C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by
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
  -- the W-join, at the pre-merge configuration
  have hVW := h.canonW hHonC
  have hcT : IsCanonicalStateW W (Configuration.core C) (ev₁ ∩ ev₂) sT := by
    rw [← hevT_eq]
    exact hVW vT sT evT h_verT
  have hW_new : IsCanonicalStateW W (Configuration.core C) (ev₁ ∪ ev₂)
      (D.mergeL sT s₁ s₂) :=
    hJoinW ev₁ ev₂ sT s₁ s₂
      (fun hab hbc => h.good.vis_trans hab hbc)
      (fun a ha => h.good.vis_irrefl a ha)
      (h.good.ver_events_sub v₁ s₁ ev₁ h_ver₁)
      (h.good.ver_events_sub v₂ s₂ ev₂ h_ver₂)
      (fun a b hab _ hb => h.good.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      (fun a b hab _ hb => h.good.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
      hcT
      (hVW v₁ s₁ ev₁ h_ver₁)
      (hVW v₂ s₂ ev₂ h_ver₂)
  have h_sameW : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalStateW W (Configuration.core C) E' s' →
      IsCanonicalStateW W (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalStateW_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- plain canonical: the weakened W-join at `vm`, congruence elsewhere
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      exact h_sameW _ _ hW_new |>.weaken
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.good.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.good.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.good.vis_irrefl a ha
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.good.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.good.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.good.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.good.ver_causal w s' E' hw a b hab hb
  · -- the W-half
    intro _ w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      exact h_sameW _ _ hW_new
    · rw [hver_old w hwn] at hw
      exact h_sameW E' s' (hVW w s' E' hw)

open LabeledTS in
/-- **The honest-reachability induction over the witness class**: the
strengthened invariant holds at every `GenHonest`-honestly reachable
configuration, given the `W`-join at honest configurations plus the two
`W`-bookkeeping facts. -/
theorem goodConfigW_of_genHonest_reach {hInit : D.Inv D.init}
    (hW0 : W [])
    (hWstep : ∀ (e : Op D.AppOp) (ρ : List (Op D.AppOp)) (s : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s → P e s → W (ρ ++ [e]))
    (hJoinW : ∀ C', GenHonest D P C' →
      JoinLemma3AtW D W (Configuration.core C'))
    {C : Configuration D}
    (hReach : HonestReach D (GenHonest D P) hInit C) :
    GoodConfigW P W C := by
  induction hReach with
  | init => exact goodConfigW_init hInit hW0
  | step _ hHon hstep ih =>
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfigW_createReplica h_fresh hL hvis hver ih hHon
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfigW_apply h_head h_ver h_fresh_t h_vnew hL hvis hver
        (fun ρ s' => hWstep _ ρ s') ih hHon
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfigW_merge_at hHon (hJoinW _ hHon)
        h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver ih
    | query h_s h_val => exact ih

/-- **The conditioned metatheorem, witness-class form**: per-version
RA-linearizability at every `GenHonest`-honestly reachable configuration,
from the `W`-join. This is the corrected replacement for feeding a plain
`JoinLemma3At` to `ra_linearizable3_of_honest_reach` — sound even for
datatypes whose canonical states are not unique per event set. -/
theorem ra_linearizable3_of_genHonest_reachW {hInit : D.Inv D.init}
    (hW0 : W [])
    (hWstep : ∀ (e : Op D.AppOp) (ρ : List (Op D.AppOp)) (s : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s → P e s → W (ρ ++ [e]))
    (hJoinW : ∀ C', GenHonest D P C' →
      JoinLemma3AtW D W (Configuration.core C'))
    {C : Configuration D}
    (hReach : HonestReach D (GenHonest D P) hInit C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good
    (goodConfigW_of_genHonest_reach hW0 hWstep hJoinW hReach).good

#print axioms ra_linearizable3_of_genHonest_reachW

end GoodW

end Sal.ConditionedMRDTs
