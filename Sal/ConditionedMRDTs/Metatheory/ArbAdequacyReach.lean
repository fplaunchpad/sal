import Sal.ConditionedMRDTs.Metatheory.ArbAdequacyFull

/-!
# Fully-generic arbitration adequacy: the reachability wiring

`Metatheory/ArbAdequacyFull.lean` establishes the mathematical core loOn-free: the
generic ternary Join Lemma `join_lemma3AtArb_of_cd_feasible` (the MERGE pillar),
`isCanonicalStateArb_extend` (the APPLY pillar), `isCanonicalStateArb_congr` (the
CREATEREPLICA pillar), and the fifth arbitration clause the reachability layer needs,
**vis-consistency** (`VisConsistentArbitration`).

This file assembles those pillars into the **end-to-end reachability theorem**: the
`GoodConfig3` transition induction re-threaded over `IsCanonicalStateArb`, so that
RA-linearizability against a fully-abstract arbitration holds at every reachable
configuration, with `loOn` **absent** from the statement and the fold pinned solely by
`ArbConvergence`.

## Contents (kernel-clean; `#print axioms` at the foot)

* **§1 `ArbFamily`**: a *reachability-gated arbitration family* `arb C E` with six
  clauses: extends-`vis`-on-noncomm, acyclic-on-reachable (gated on the two `vis`
  facts), antitone, vis-consistent (gated), convergent, and **vis-local** (the
  arbitration on `E` depends only on `vis|E`, the applicability condition of the
  `isCanonicalStateArb_congr` pillar, made an explicit clause). This is the "not a
  fixed relation" arbitration the reachability layer requires.

* **§2 `GoodConfig3ArbF`**: the reachability invariant re-threaded over
  `IsCanonicalStateArb`: the arb-canonical field plus the four `GoodConfig3` base fields
  (`vis_trans`, `vis_irrefl`, `ver_events_sub`, `ver_causal`), which carry the `vis`
  facts the family's per-config acyclicity/vis-consistency are gated on.

* **§3 the four transition lemmas** `goodConfig3ArbF_init / _createReplica / _apply /
  _merge`: the three canonical-preservation cases are the pillars (merge = the Join
  Lemma, apply = `isCanonicalStateArb_extend`, createReplica/old =
  `isCanonicalStateArb_congr`); the base-field preservation mirrors the flat
  `goodConfig3_*` lemmas.

* **§4 the reachability bridge + the capstone** `goodConfig3ArbF_of_reach` and
  `ra_linearizable3Arb_of_core_feasible_cd`: from the six-clause family + the ternary
  core VCs in arb-form, `IsRALinearizable3Arb` at every reachable configuration,
  composing with `isRALinearizable3Arb_of_goodConfig3Arb`.

* **§5 the generic converters** `cdvc3Arb_of_all_comm`, `feasibleDeltaVCs3Arb_of_delta`,
  `listPermOf_perm`: the arb-form VCs for the all-commuting class (needed for the LWW
  instance) and a small list helper.

* **§6 the `loOn` instance corollary** `loOn_isRALinearizable3Arb_via_capstone`, routed
  through the GENERIC capstone (not the loOn-refining partial of ArbAdequacy §3): the
  `loOn` family (`loOnFamily`) discharges all six clauses, so any datatype whose VCs hold
  is RA-linearizable against `loOn` **through the abstract engine**, fold pinned by
  `ArbConvergence`. `ra_linearizable3` from the weakened bundle is the `lo`-coarsening of
  this corollary (`ra_linearizable3_via_capstone`).

The LWW-ts instance (its family `lwwFamily` + the capstone corollary) lives in
`MRDT_Instances/LWWRegister/LWWRegister.lean`, which owns `lwwArb`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

set_option maxHeartbeats 2000000

variable {D : ConditionedMRDTSig}

/-! ## §1. The reachability-gated arbitration family -/

/-- **A reachability-gated arbitration family.** A configuration-indexed arbitration
`arb C E` satisfying the five clauses the fully-generic adequacy engine consumes
(acyclic-on-reachable, antitone, extends-`vis`-on-noncomm, vis-consistent, convergent)
plus **vis-locality**: the arbitration on an event set `E` depends only on `vis`
restricted to `E`. The two gated clauses (`acyclic`, `vis_consistent`) take the `vis`
strict-partial-order facts as hypotheses, since they hold only at reachable
configurations, which is exactly what `GoodConfig3ArbF` carries. Both target instances
(`loOnFamily`, `lwwFamily`) are `ArbFamily`s. -/
structure ArbFamily (D : ConditionedMRDTSig) where
  /-- The configuration-indexed set-relative arbitration. -/
  arb : Configuration D → Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop
  /-- Every visible non-commuting pair is ordered. -/
  extends_vis : ∀ (C : Configuration D) (E : Set (Op D.AppOp)) {a b : Op D.AppOp},
    a ∈ E → b ∈ E → C.vis a b → ¬ D.toCRDTSig.commutes a b → arb C E a b
  /-- Acyclic on every event set, gated on the two `vis` facts of a reachable config. -/
  acyclic : ∀ (C : Configuration D),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    ∀ (E : Set (Op D.AppOp)), (∀ a ∈ E, a ∈ C.events) →
    ∀ a : Op D.AppOp, ¬ Relation.TransGen (arbNe E (arb C)) a a
  /-- Antitone under carrier restriction (config fixed). -/
  antitone : ∀ (C : Configuration D) {E' E'' : Set (Op D.AppOp)} {a b : Op D.AppOp},
    E' ⊆ E'' → arb C E'' a b → arb C E' a b
  /-- Never orders an event before one it observed, gated on the two `vis` facts. -/
  vis_consistent : ∀ (C : Configuration D),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    VisConsistentArbitration C (arb C)
  /-- All respecting enumerations of an event set fold equally. -/
  convergent : ∀ (C : Configuration D), ArbConvergence C (arb C)
  /-- The arbitration on `E` depends only on `vis` restricted to `E` (the
  applicability side-condition of the `isCanonicalStateArb_congr` pillar). -/
  vis_local : ∀ (C C' : Configuration D) (E : Set (Op D.AppOp)),
    (∀ a ∈ E, ∀ b ∈ E, (C.vis a b ↔ C'.vis a b)) →
    ∀ a ∈ E, ∀ b ∈ E, (arb C E a b ↔ arb C' E a b)

/-! ## §2. The reachability invariant, re-threaded over `IsCanonicalStateArb` -/

/-- Every stored version holds the `arb`-canonical state of its event set, plus the
four `GoodConfig3` base facts (the `vis` strict partial order + the two store-closure
facts the transition induction and the family's gated clauses consume). -/
structure GoodConfig3ArbF (F : ArbFamily D) (C : Configuration D) : Prop where
  canonical : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → IsCanonicalStateArb C (F.arb C) E s
  vis_trans : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c
  vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a
  ver_events_sub : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a ∈ E, a ∈ C.events
  ver_causal : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a b, C.vis a b → b ∈ E → a ∈ E

/-! ## §3. The four transition lemmas -/

/-- **Init**: the only allocated version is `0 = (σ₀, ∅)`; its arb-canonical witness is
the empty enumeration (respecting `arb` vacuously). -/
theorem goodConfig3ArbF_init (F : ArbFamily D) (hInit : D.Inv D.init) :
    GoodConfig3ArbF F (initConfig D hInit) := by
  have hver : ∀ v, (initConfig D hInit).ver v
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

/-- **CreateReplica**: store and `vis` unchanged; each version's arb-canonical state
transfers by `isCanonicalStateArb_congr` (the family is vis-local and `vis` is fixed). -/
theorem goodConfig3ArbF_createReplica (F : ArbFamily D) {C C' : Configuration D}
    {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3ArbF F C) : GoodConfig3ArbF F C' := by
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      have hnone := (C.dom_eq r'').mp h_fresh
      rw [hnone] at hLr''
      simp at hLr''
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalStateArb C (F.arb C) E' s' →
      IsCanonicalStateArb C' (F.arb C') E' s' := by
    intro E' s' hcs
    exact isCanonicalStateArb_congr
      (F.vis_local C C' E' (fun a _ b _ => by rw [hvis])) hcs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v s E hv
    rw [hver] at hv
    exact h_same E s (h.canonical v s E hv)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro v s E hv a ha
    rw [hver] at hv
    exact h_events a (h.ver_events_sub v s E hv a ha)
  · intro v s E hv a b hab hb
    rw [hver] at hv
    rw [hvis] at hab
    exact h.ver_causal v s E hv a b hab hb

/-- **Apply**: the fresh version extends its parent's arb-canonical state by the causally-
latest event (`isCanonicalStateArb_extend`, consuming antitone + vis-consistency at the
post-state); every old version transfers by `isCanonicalStateArb_congr` (the fresh event
lies outside its set, so `vis` is unchanged there). -/
theorem goodConfig3ArbF_apply (F : ArbFamily D)
    {C C' : Configuration D}
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
    (h : GoodConfig3ArbF F C) : GoodConfig3ArbF F C' := by
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
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
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
  have hL'r : C'.L r = some (ev ∪ {e}) := by
    rw [hL]
    simp [updateRep]
  have h_old_no_e : ∀ (w : Version) (s' : D.State) (E' : Set (Op D.AppOp)),
      C.ver w = some (s', E') → e ∉ E' := by
    intro w s' E' hw hmem
    exact he_not_events (h.ver_events_sub w s' E' hw e hmem)
  have h_vis_old : ∀ (E' : Set (Op D.AppOp)), (∀ x ∈ E', x ∈ C.events) →
      ∀ a, a ∈ E' → ∀ b, b ∈ E' → (C'.vis a b ↔ C.vis a b) := by
    intro E' hsub a _ b hb
    rw [hvis]
    constructor
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
    · exact Or.inl
  -- the two vis facts at the post-state (needed by the gated vis-consistency clause)
  have hvi' : ∀ a, ¬ C'.vis a a := by
    intro a ha
    rw [hvis] at ha
    rcases ha with ha | ⟨ha_ev, rfl⟩
    · exact h.vis_irrefl a ha
    · exact he_not_ev ha_ev
  have hvt' : ∀ {a b c : Op D.AppOp}, C'.vis a b → C'.vis b c → C'.vis a c := by
    intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    rcases hab with hab | ⟨ha_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact Or.inl (h.vis_trans hab hbc)
      · exact Or.inr ⟨h.ver_causal v s ev h_ver a b hab hb_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact absurd hbc (h_no_vis_out c)
      · exact absurd hb_ev he_not_ev
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have h_old : IsCanonicalStateArb C (F.arb C) ev s :=
        h.canonical v s ev h_ver
      have h_old' : IsCanonicalStateArb C' (F.arb C') ev s :=
        isCanonicalStateArb_congr
          (F.vis_local C C' ev
            (fun a ha b hb => (h_vis_old ev h_ev_events a ha b hb).symm)) h_old
      have h_ext := isCanonicalStateArb_extend (arb := F.arb C')
        (fun hsub hab => F.antitone C' hsub hab)
        (F.vis_consistent C' hvt' hvi') he_not_ev
        (fun x hx => by rw [hvis]; exact Or.inr ⟨hx, rfl⟩) h_old'
      rw [Set.union_singleton]
      exact h_ext
    · rw [hver_old w hwn] at hw
      have h_old : IsCanonicalStateArb C (F.arb C) E' s' :=
        h.canonical w s' E' hw
      exact isCanonicalStateArb_congr
        (F.vis_local C C' E'
          (fun a ha b hb =>
            (h_vis_old E' (h.ver_events_sub w s' E' hw) a ha b hb).symm)) h_old
  · -- vis-transitivity
    intro a b c hab hbc
    exact hvt' hab hbc
  · -- vis-irreflexivity
    exact hvi'
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      rcases ha with ha | ha
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inl ha⟩
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inr ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · rcases hab with hab | ⟨_, rfl⟩
        · exact Or.inl (h.ver_causal v s ev h_ver a b hab hb)
        · exact absurd hb he_not_ev
      · have hb_e : b = e := hb
        subst hb_e
        rcases hab with hab | ⟨ha_ev, _⟩
        · exfalso
          obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_tgt hab
          exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
        · exact Or.inl ha_ev
    · rw [hver_old w hwn] at hw
      rcases hab with hab | ⟨_, rfl⟩
      · exact h.ver_causal w s' E' hw a b hab hb
      · exact absurd hb (h_old_no_e w s' E' hw)

/-- **Merge**: the fresh version's arb-canonical state is delivered by the generic ternary
Join Lemma (built from the family's five clauses + the arb-form VCs); every old version
transfers by `isCanonicalStateArb_congr` (`vis` unchanged). -/
theorem goodConfig3ArbF_merge (F : ArbFamily D)
    (hMC : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a)
    {C C' : Configuration D} {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (hCDc : CDVC3Arb C (F.arb C)) (hFΔc : FeasibleDeltaVCs3Arb C (F.arb C))
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3ArbF F C) : GoodConfig3ArbF F C' := by
  have hJoin : JoinLemma3AtArb C (F.arb C) :=
    join_lemma3AtArb_of_cd_feasible hMC
      ⟨F.arb C, F.extends_vis C, F.acyclic C h.vis_trans h.vis_irrefl⟩
      (fun hsub hab => F.antitone C hsub hab) (F.convergent C) hFΔc hCDc
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalStateArb C (F.arb C) E' s' →
      IsCanonicalStateArb C' (F.arb C') E' s' := by
    intro E' s' hcs
    exact isCanonicalStateArb_congr
      (F.vis_local C C' E' (fun a _ b _ => by rw [hvis])) hcs
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalStateArb C (F.arb C) (ev₁ ∩ ev₂) sT := by
        rw [← hevT_eq]
        exact h.canonical vT sT evT h_verT
      have h_join := hJoin ev₁ ev₂ sT s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab _ hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab _ hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
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
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

/-! ## §4. The reachability bridge and the capstone -/

open LabeledTS in
/-- **`GoodConfig3ArbF` holds at every reachable configuration.** The `GoodConfig3`
transition induction (`ra_linearizable3_of_join`), re-threaded over `IsCanonicalStateArb`
and driven by the four §3 lemmas. -/
theorem goodConfig3ArbF_of_reach (F : ArbFamily D)
    (hMC : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a)
    (hCD : ∀ C : Configuration D, CDVC3Arb C (F.arb C))
    (hFΔ : ∀ C : Configuration D, FeasibleDeltaVCs3Arb C (F.arb C))
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    GoodConfig3ArbF F C := by
  induction hReach with
  | refl => exact goodConfig3ArbF_init F hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3ArbF_createReplica F h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3ArbF_apply F h_head h_ver h_fresh_t h_vnew hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfig3ArbF_merge F hMC (hCD _) (hFΔ _)
        h_head₁ h_ver₁ h_ver₂ h_lca h_verT hL hvis hver ih
    | query h_s h_val => exact ih

open LabeledTS in
/-- **THE CAPSTONE.** From a six-clause arbitration family + the merge content in
arb-form (merge symmetry for the Join Lemma, `CDVC3Arb`/`FeasibleDeltaVCs3Arb` per
config), every reachable configuration is RA-linearizable against the family's
arbitration, `loOn` absent, the fold pinned solely by the family's `ArbConvergence`.
Composes `goodConfig3ArbF_of_reach` with `isRALinearizable3Arb_of_goodConfig3Arb`.
The merge-side hypothesis is exactly merge symmetry (`∀ l a b, mergeL l a b =
mergeL l b a`), NOT the full `CoreVCs3CD`: the rc-shaped `UpdateVCs` in that bundle
is never consumed by the arb engine (only `.mergeL_comm` is touched, down through
`join_lemma3AtArb_of_cd_feasible`), so the flat arb adequacy is genuinely rc-free at
the signature level. The `loOn` and LWW instances re-introduce their own order
structure (`UpdateVCs` for `loOn`, the timestamp order for LWW); the abstract
contract does not. -/
theorem ra_linearizable3Arb_of_core_feasible_cd (F : ArbFamily D)
    (hMC : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a)
    (hCD : ∀ C : Configuration D, CDVC3Arb C (F.arb C))
    (hFΔ : ∀ C : Configuration D, FeasibleDeltaVCs3Arb C (F.arb C))
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3Arb C (F.arb C) :=
  isRALinearizable3Arb_of_goodConfig3Arb
    (fun v s E hv =>
      (goodConfig3ArbF_of_reach F hMC hCD hFΔ C hReach).canonical v s E hv)

/-! ## §5. Generic converters (arb-form VCs for the all-commuting class) -/

/-- Two `listPermOf` enumerations of the same set are permutations of each other. -/
theorem listPermOf_perm {α : Type} {l₁ l₂ : List α} {E : Set α}
    (h₁ : listPermOf l₁ E) (h₂ : listPermOf l₂ E) : l₁.Perm l₂ :=
  List.Subperm.antisymm
    (List.subperm_of_subset h₁.1 (fun a ha => (h₂.2 a).mpr ((h₁.2 a).mp ha)))
    (List.subperm_of_subset h₂.1 (fun a ha => (h₁.2 a).mpr ((h₂.2 a).mp ha)))

/-- **(CD3) in arb-form for the all-commuting class**, for *any* arbitration: when every
pair commutes the noncomm-downset is empty, so `B = init` and the equation is
`merge_peel_comm3`; the arb-maximality premise and the respecting witnesses are inert.
(The arb-form of `cdVC3_of_all_comm`.) -/
theorem cdvc3Arb_of_all_comm (hVC : CoreVCs3 D)
    (h_comm : ∀ a b : Op D.AppOp, D.toCRDTSig.commutes a b) (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : CDVC3Arb C arb := by
  intro U A B e _ _ _ _ _ _ hA hB
  have h_down : downset (Configuration.core C) e \ {e} = ∅ := by
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
  have hBinit : B = D.init := isCanonicalStateArb_empty h_down hB
  subst hBinit
  obtain ⟨ρ, hpA, -, hfA⟩ := id hA
  have h0 : applySeq D.toCRDTSig D.init ([] : List (Op D.AppOp)) = D.init :=
    rfl
  have hpc := hVC.merge_peel_comm3 D.init e [] ρ
    (fun x hx => absurd hx List.not_mem_nil)
    (fun x _ => h_comm e x)
  rw [h0] at hpc
  rw [hVC.mergeL_init] at hpc
  rw [← hfA, hVC.mergeL_comm, hpc]

/-- **The feasible delta contract in arb-form**, for *any* arbitration, from the raw
`DeltaVCs3` laws (the arb-form of `feasibleDeltaVCs3_of_delta`; the canonical witnesses
and arb-maximality premises are discarded, since the redistribution laws are raw
`mergeL` algebra). -/
theorem feasibleDeltaVCs3Arb_of_delta (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D)
    (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) :
    FeasibleDeltaVCs3Arb C arb where
  feasible_init := fun _ s _ _ => hVC.mergeL_init s
  feasible_local_redistribute :=
    fun _ _ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      hΔ.local_redistribute s₀ B t₁ (D.update B e) s₂
  feasible_redistribute :=
    fun _ _ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      hΔ.redistribute B t₀ t₁ t₂ (D.update B e)

/-! ## §6. The `loOn` instance corollary, through the GENERIC capstone -/

/-- `loOn` is **vis-consistent**: given the `vis` strict-partial-order facts, `loOn`
never orders `a` before an event `b` that `a` observed. Both arms are vacuous: the
`vis`-arm because `vis a b ∧ vis b a` contradicts irreflexivity via transitivity, the
`rc`-arm because it demands `¬ vis b a`. -/
theorem loOn_vis_consistent {C : Configuration D}
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a) :
    VisConsistentArbitration C (fun E => loOn (Configuration.core C) E) := by
  intro E a b _ha _hb hvis hlo
  rcases hlo with ⟨hv_ab, _⟩ | ⟨_, hnv_ba, _, _⟩
  · exact h_ir a (h_tr hv_ab hvis)
  · exact hnv_ba hvis

/-- `loOn` is **vis-local**: on an event set `E`, `loOn (core C) E` depends only on
`vis` restricted to `E` (its `vis`-arm, `rc`-arm concurrency premises, and absorber
existential all range over `E`). -/
theorem loOn_vis_local {C C' : Configuration D} {E : Set (Op D.AppOp)}
    (hva : ∀ a ∈ E, ∀ b ∈ E, (C.vis a b ↔ C'.vis a b))
    {a b : Op D.AppOp} (ha : a ∈ E) (hb : b ∈ E) :
    loOn (Configuration.core C) E a b ↔ loOn (Configuration.core C') E a b := by
  have H : ∀ (X Y : Configuration D),
      (∀ p ∈ E, ∀ q ∈ E, (X.vis p q ↔ Y.vis p q)) →
      loOn (Configuration.core X) E a b → loOn (Configuration.core Y) E a b := by
    intro X Y hXY hlo
    rcases hlo with ⟨hv, hnc⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨(hXY a ha b hb).mp hv, hnc⟩
    · refine Or.inr ⟨fun hy => h1 ((hXY a ha b hb).mpr hy),
        fun hy => h2 ((hXY b hb a ha).mpr hy), h3, ?_⟩
      rintro ⟨e₃, he₃, hve, hnce⟩
      exact h4 ⟨e₃, he₃, (hXY b hb e₃ he₃).mpr hve, hnce⟩
  exact ⟨H C C' hva, H C' C (fun p hp q hq => (hva p hp q hq).symm)⟩

/-- **The `loOn` family**: `loOn (core C)` discharges all six `ArbFamily` clauses
(acyclicity via `loOnArbitration`, antitone via `loOn_mono`, extends-`vis` by
construction, vis-consistency + vis-locality above, convergence via `loOn_arbConvergence`).
-/
def loOnFamily (hU : UpdateVCs D.toCRDTSig) : ArbFamily D where
  arb := fun C E => loOn (Configuration.core C) E
  extends_vis := by intro C E a b _ha _hb hv hnc; exact loOn_of_vis_noncomm hv hnc
  acyclic := by
    intro C h_tr h_ir E h_in a
    exact (loOnArbitration C hU h_tr h_ir).acyclic E h_in a
  antitone := by intro C E' E'' a b hsub h; exact loOn_mono hsub h
  vis_consistent := by intro C h_tr h_ir; exact loOn_vis_consistent h_tr h_ir
  convergent := by intro C; exact loOn_arbConvergence hU
  vis_local := by intro C C' E hva a ha b hb; exact loOn_vis_local hva ha hb

open LabeledTS in
/-- **`loOn` RA-linearizability through the GENERIC engine.** For any datatype whose VCs
hold, every reachable configuration is RA-linearizable against `loOn`, routed through the
fully-generic `ra_linearizable3Arb_of_core_feasible_cd`, the fold pinned by `loOn`'s
`ArbConvergence` (not the loOn-refining partial of `ArbAdequacy §3`). -/
theorem loOn_isRALinearizable3Arb_via_capstone
    (hVC : CoreVCs3CD D) (hU : UpdateVCs D.toCRDTSig)
    (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D)
    {hInit : D.Inv D.init} (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3Arb C (fun E => loOn (Configuration.core C) E) :=
  ra_linearizable3Arb_of_core_feasible_cd (loOnFamily hU) hVC.mergeL_comm
    (fun C' => cdvc3Arb_of_cdvc3 hCD C')
    (fun C' => feasibleDeltaVCs3Arb_of_feasible hFΔ C') C hReach

open LabeledTS in
/-- **The weakened flat bundle implies Def-lin**, as the `loOn` instantiation of the
capstone: `IsRALinearizable3Arb` at `loOn` transports to the `lo`-form
`IsRALinearizable3` (`isRALinearizable3_of_isRALinearizable3Arb_loOn`). So the flat
adequacy re-derives through the abstract engine with the fold pinned by `ArbConvergence`. -/
theorem ra_linearizable3_via_capstone
    (hVC : CoreVCs3CD D) (hU : UpdateVCs D.toCRDTSig)
    (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D)
    {hInit : D.Inv D.init} (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_isRALinearizable3Arb_loOn
    (loOn_isRALinearizable3Arb_via_capstone hVC hU hFΔ hCD C hReach)

#print axioms ra_linearizable3Arb_of_core_feasible_cd
#print axioms loOn_isRALinearizable3Arb_via_capstone
#print axioms ra_linearizable3_via_capstone

end Sal.ConditionedMRDTs
