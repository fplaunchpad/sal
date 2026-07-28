import Sal.ConditionedMRDTs.Metatheory.WitnessClass
import Sal.ConditionedMRDTs.Metatheory.LCA_Lemma

/-! # Witness coherence — the ancestry-aligned direct-witness route

`JoinLemma3AtW` hands the datatype hook three *independently* canonical
slots. For datatypes with `loOn`-free choices that survive in the state
(Shesha: the display order of concurrent same-anchor inserts), the three
slots may realize **incompatible** choices — the LCA slot and a branch slot
can display a common live pair in opposite orders, and the merge of such a
misaligned triple need not be canonical at all. This is not hypothetical:
`Shesha_Presplice_Refuted.lean` machine-checks a counterexample at an honest
configuration, one level above `Shesha_Join_Refuted.lean`'s.

Real executions never produce the misalignment: a version's free choices are
*inherited* from its ancestors (a branch state displays the LCA's common
pairs in the LCA's order — branch agreement). This file threads that
inheritance through the reachability induction as an abstract **coherence
relation** `K` between the *witnesses* of DAG-related versions:

* `IsCanonWitness` — the explicit-witness form of `IsCanonicalStateW`;
* `JoinLemma3AtWC` — the join hook with named witnesses: the inputs come
  `K`-aligned along the store's ancestry (`K ρ₀ ρ₁`, `K ρ₀ ρ₂` — the LCA is
  a DAG ancestor of both branches), and the output owes alignment back
  (`K ρ₁ ρm`, `K ρ₂ ρm`);
* `GoodConfigWC` — the strengthened invariant: `GoodConfig3`, the store
  invariant (`StoreInv` — the DAG bookkeeping that makes ancestry usable),
  and, conditionally on honesty, a **global family** of witnesses, one per
  registered version, pairwise `K`-coherent along `Reaches`;
* `ra_linearizable3_of_genHonest_reachWC` — the capstone, from the aligned
  join plus three `K`-bookkeeping facts:
  - `hKrefl` — reflexivity;
  - `hKext` — a fresh event appended on the right preserves coherence;
  - `hKsub` — locality through a middleman: `K α β → K β γ → α ⊆ β → K α γ`
    (how the merge output's coherence propagates to the branches' own
    ancestors, whose events sit inside the branch).

The plain `GoodConfig3` half is re-derived by weakening, so neither refuted
plain hook is ever consumed. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

section CanonWitness

variable {D' : CRDTSig}

/-- `ρ` is a canonical `W`-witness realizing `s` as the fold of `ev` — the
explicit-witness form of `IsCanonicalStateW`. -/
def IsCanonWitness (W : List (Op D'.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D') (ev : Set (Op D'.AppOp))
    (s : D'.State) (ρ : List (Op D'.AppOp)) : Prop :=
  listPermOf ρ ev ∧ respects ρ (loOn C ev) ∧ W ρ ∧
    applySeq D' D'.init ρ = s

theorem IsCanonWitness.isCanonicalStateW {W : List (Op D'.AppOp) → Prop}
    {C : Sal.Emulation.Configuration D'} {ev : Set (Op D'.AppOp)}
    {s : D'.State} {ρ : List (Op D'.AppOp)}
    (h : IsCanonWitness W C ev s ρ) : IsCanonicalStateW W C ev s :=
  ⟨ρ, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Mirror of `isCanonicalStateW_congr`, with the witness fixed. -/
theorem isCanonWitness_congr {W : List (Op D'.AppOp) → Prop}
    {C C' : Sal.Emulation.Configuration D'}
    {E : Set (Op D'.AppOp)} {s : D'.State} {ρ : List (Op D'.AppOp)}
    (h_vis : ∀ a ∈ E, ∀ b ∈ E, (C'.vis a b ↔ C.vis a b))
    (h : IsCanonWitness W C E s ρ) : IsCanonWitness W C' E s ρ := by
  obtain ⟨hp, hr, hW, hf⟩ := h
  refine ⟨hp, ?_, hW, hf⟩
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

/-- Mirror of `isCanonicalStateW_extend`, with the witnesses fixed: a fresh
event that observed everything in `ev` extends a canonical witness by one
update. -/
theorem isCanonWitness_extend {W : List (Op D'.AppOp) → Prop}
    {C : Sal.Emulation.Configuration D'}
    {ev : Set (Op D'.AppOp)} {s : D'.State} {e : Op D'.AppOp}
    {ρ : List (Op D'.AppOp)}
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, C.vis x e)
    (h_e_last : ∀ x ∈ ev, ¬ C.vis e x)
    (hWext : W (ρ ++ [e]))
    (h : IsCanonWitness W C ev s ρ) :
    IsCanonWitness W C (insert e ev) (D'.update s e) (ρ ++ [e]) := by
  obtain ⟨hp, hr, hW, hs⟩ := h
  refine ⟨⟨?_, fun a => ?_⟩, ?_, hWext, ?_⟩
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

end CanonWitness

section GoodWC

variable {D : ConditionedMRDTSig}

/-- **The ancestry-aligned ternary join** over `W`-witnesses: the
per-datatype hook of the coherent direct-witness route. The inputs come
with *named* witnesses, `K`-aligned along the store's ancestry (the LCA is
a DAG ancestor of both branches), and the output owes a witness `K`-aligned
with both branch witnesses. -/
def JoinLemma3AtWC (D : ConditionedMRDTSig) (W : List (Op D.AppOp) → Prop)
    (K : List (Op D.AppOp) → List (Op D.AppOp) → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (ρ₀ ρ₁ ρ₂ : List (Op D.AppOp)),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonWitness W C (ev₁ ∩ ev₂) s₀ ρ₀ →
    IsCanonWitness W C ev₁ s₁ ρ₁ →
    IsCanonWitness W C ev₂ s₂ ρ₂ →
    K ρ₀ ρ₁ → K ρ₀ ρ₂ →
    ∃ ρm : List (Op D.AppOp),
      IsCanonWitness W C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂) ρm ∧
      K ρ₁ ρm ∧ K ρ₂ ρm

/-- **The coherent reachability invariant**: `GoodConfig3`, the store
invariant, and — conditionally on honesty — one witness per registered
version, pairwise `K`-coherent along the version DAG's ancestry. -/
structure GoodConfigWC (P : Op D.AppOp → D.State → Prop)
    (W : List (Op D.AppOp) → Prop)
    (K : List (Op D.AppOp) → List (Op D.AppOp) → Prop)
    (C : Configuration D) : Prop where
  good : GoodConfig3 C
  store : StoreInv C.ver C.parents
  canonWC : GenHonest D P C →
    ∃ F : Version → List (Op D.AppOp),
      (∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
        C.ver v = some (s, E) →
        IsCanonWitness W (Configuration.core C) E s (F v)) ∧
      (∀ u v : Version, (C.ver u).isSome → (C.ver v).isSome →
        Reaches C.parents u v → K (F u) (F v))

variable {P : Op D.AppOp → D.State → Prop} {W : List (Op D.AppOp) → Prop}
  {K : List (Op D.AppOp) → List (Op D.AppOp) → Prop}

/-- Ancestry from an allocated target starts allocated (`parents_alloc`
along the path). -/
theorem reaches_alloc_src
    {ver : Version → Option (D.State × Set (Op D.AppOp))}
    {parents : Version → List Version}
    (halloc : ∀ v p, p ∈ parents v → (ver p).isSome)
    {a b : Version} (hr : Reaches parents a b) (hb : (ver b).isSome) :
    (ver a).isSome := by
  induction hr with
  | refl => exact hb
  | tail _ hstep ih => exact ih (halloc _ _ hstep)

/-- The invariant holds initially. -/
theorem goodConfigWC_init (hInit : D.Inv D.init) (hW0 : W [])
    (hKrefl : ∀ ρ, K ρ ρ) :
    GoodConfigWC P W K (initConfig D hInit) := by
  refine ⟨goodConfig3_init hInit, storeInv_init hInit, ?_⟩
  intro _
  refine ⟨fun _ => [], ?_, fun u v _ _ _ => hKrefl []⟩
  intro v s E hv
  have hv' : (if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none)
      = some (s, E) := hv
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv'
    rw [← hv'.1, ← hv'.2]
    exact ⟨⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, hW0, rfl⟩
  · rw [if_neg h] at hv'
    exact absurd hv' (by simp)

/-- CreateReplica preserves the invariant (store, `vis`, DAG unchanged). -/
theorem goodConfigWC_createReplica {C C' : Configuration D} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (hparents : C'.parents = C.parents)
    (h : GoodConfigWC P W K C) (hHonC : GenHonest D P C) :
    GoodConfigWC P W K C' := by
  refine ⟨goodConfig3_createReplica h_fresh hL hvis hver h.good,
    by rw [hver, hparents]; exact h.store, ?_⟩
  intro _
  obtain ⟨F, hprops, hcoh⟩ := h.canonWC hHonC
  refine ⟨F, ?_, ?_⟩
  · intro v s E hv
    rw [hver] at hv
    refine isCanonWitness_congr (fun a _ b _ => ?_) (hprops v s E hv)
    rw [core_vis, core_vis, hvis]
  · intro u v hu hv hr
    rw [hver] at hu hv
    rw [hparents] at hr
    exact hcoh u v hu hv hr

/-- Apply preserves the invariant: the fresh version's witness is the
parent's extended by the fresh event (`hKext` keeps it coherent with every
ancestor); ancestry into old versions is unchanged. -/
theorem goodConfigWC_apply {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (h_fresh_store : ∀ w sw Ew, C.ver w = some (sw, Ew) →
      ∀ e' ∈ Ew, Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (hparents : C'.parents = fun w => if w = vnew then [v] else C.parents w)
    (hWstep : ∀ (ρ : List (Op D.AppOp)) (s' : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s' → P (t, r, o) s' →
      W (ρ ++ [(t, r, o)]))
    (hKrefl : ∀ ρ, K ρ ρ)
    (hKext : ∀ (ρ σ : List (Op D.AppOp)) (e : Op D.AppOp),
      K ρ σ → e ∉ ρ → K ρ (σ ++ [e]))
    (h : GoodConfigWC P W K C) (hHonC : GenHonest D P C) :
    GoodConfigWC P W K C' := by
  have hpar_new' : C'.parents vnew = [v] := by rw [hparents]; simp
  have hpar_old' : ∀ w, w ≠ vnew → C'.parents w = C.parents w := by
    intro w hw; rw [hparents]; simp [hw]
  have hver_new : C'.ver vnew
      = some (D.update s (t, r, o), ev ∪ {(t, r, o)}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  refine ⟨goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver h.good,
    storeInv_apply_extend (e := (t, r, o)) (snew := D.update s (t, r, o))
      h.store h_vnew h_ver
      (fun w sw Ew hw hmem => h_fresh_store w sw Ew hw _ hmem rfl)
      hver_new hver_old hpar_new' hpar_old', ?_⟩
  intro hHonC'
  obtain ⟨F, hprops, hcoh⟩ := h.canonWC hHonC
  set e : Op D.AppOp := (t, r, o) with he_def
  -- plumbing (as in `goodConfigW_apply`)
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
  -- the extended witness at the fresh version
  have h_old : IsCanonWitness W (Configuration.core C) ev s (F v) :=
    hprops v s ev h_ver
  have h_old' : IsCanonWitness W (Configuration.core C') ev s (F v) := by
    refine isCanonWitness_congr (fun a ha b hb => ?_) h_old
    rw [core_vis, core_vis]
    exact h_vis_old ev h_ev_events a ha b hb
  have hWnew : W (F v ++ [e]) := by
    refine hWstep (F v) s h_old.2.2.1 h_old.2.2.2 ?_
    have hP := hHonC' e he_events' (F v) (by rw [hpast]; exact h_old.1)
    rw [h_old.2.2.2] at hP
    exact hP
  have h_ext := isCanonWitness_extend (e := e) he_not_ev
    (fun x hx => by
      rw [core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
    (fun x hx => by
      rw [core_vis, hvis]
      rintro (hex | ⟨he_ev, _⟩)
      · exact h_no_vis_out x hex
      · exact he_not_ev he_ev)
    hWnew h_old'
  -- an old witness never mentions the fresh event
  have he_not_F : ∀ (u : Version), (C.ver u).isSome → e ∉ F u := by
    intro u hu hmem
    obtain ⟨⟨su, Eu⟩, hu'⟩ := Option.isSome_iff_exists.mp hu
    have hEu : e ∈ Eu := ((hprops u su Eu hu').1.2 e).mp hmem
    exact he_not_events (h.good.ver_events_sub u su Eu hu' e hEu)
  refine ⟨fun w => if w = vnew then F v ++ [e] else F w, ?_, ?_⟩
  · -- per-version witness properties
    intro w s' E' hw
    beta_reduce
    by_cases hwn : w = vnew
    · rw [hwn] at hw
      rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2, if_pos hwn, Set.union_singleton]
      exact h_ext
    · rw [hver_old w hwn] at hw
      rw [if_neg hwn]
      refine isCanonWitness_congr (fun a ha b hb => ?_) (hprops w s' E' hw)
      rw [core_vis, core_vis]
      exact h_vis_old E' (h.good.ver_events_sub w s' E' hw) a ha b hb
  · -- coherence along the extended DAG
    intro u w hu hw hr
    beta_reduce
    by_cases hwn : w = vnew
    · rw [hwn] at hr
      rcases reaches_new_target h.store.parents_alloc h_vnew hpar_new'
          hpar_old' (fun p hp => by
            rw [List.mem_singleton] at hp
            rw [hp, h_ver]; rfl) hr with hu_eq | ⟨p, hp, hrp⟩
      · rw [if_pos hu_eq, if_pos hwn]
        exact hKrefl _
      · rw [List.mem_singleton] at hp
        rw [hp] at hrp
        have huold : (C.ver u).isSome :=
          reaches_alloc_src h.store.parents_alloc hrp (by rw [h_ver]; rfl)
      -- `u` is old: the fresh version has no allocation in `C`
        have hune : u ≠ vnew := by
          intro he'
          rw [he', h_vnew] at huold
          simp at huold
        rw [if_neg hune, if_pos hwn]
        exact hKext (F u) (F v) e
          (hcoh u v huold (by rw [h_ver]; rfl) hrp) (he_not_F u huold)
    · rw [hver_old w hwn] at hw
      have hrw : Reaches C.parents u w :=
        reaches_old_of_new h.store.parents_alloc h_vnew hpar_old' hr hw
      have huold : (C.ver u).isSome :=
        reaches_alloc_src h.store.parents_alloc hrw hw
      have hune : u ≠ vnew := by
        intro he'
        rw [he', h_vnew] at huold
        simp at huold
      rw [if_neg hune, if_neg hwn]
      exact hcoh u w huold hw hrw

/-- Merge preserves the invariant — the aligned join at work: the invariant
supplies the LCA-to-branch coherence (`Reaches` along the two `IsLCA` legs),
the join returns the merged witness aligned with both branches, and `hKsub`
propagates its coherence to every deeper ancestor (whose events sit inside
the branch by `events_mono`). The plain `GoodConfig3` half is the weakening
of the join's conclusion. -/
theorem goodConfigWC_merge_at {C C' : Configuration D}
    (hHonC : GenHonest D P C)
    (hJoinWC : JoinLemma3AtWC D W K (Configuration.core C))
    {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (h_vm : C.ver vm = none)
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (hparents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w)
    (hKrefl : ∀ ρ, K ρ ρ)
    (hKsub : ∀ (α β γ : List (Op D.AppOp)), K α β → K β γ →
      (∀ x ∈ α, x ∈ β) → K α γ)
    (h : GoodConfigWC P W K C) : GoodConfigWC P W K C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hpar_new' : C'.parents vm = [v₁, v₂] := by rw [hparents]; simp
  have hpar_old' : ∀ w, w ≠ vm → C'.parents w = C.parents w := by
    intro w hw; rw [hparents]; simp [hw]
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
  -- the aligned join, at the pre-merge configuration
  obtain ⟨F, hprops, hcoh⟩ := h.canonWC hHonC
  have hcT : IsCanonWitness W (Configuration.core C) (ev₁ ∩ ev₂) sT
      (F vT) := by
    rw [← hevT_eq]
    exact hprops vT sT evT h_verT
  have hK01 : K (F vT) (F v₁) :=
    hcoh vT v₁ (by rw [h_verT]; rfl) (by rw [h_ver₁]; rfl) h_lca.1
  have hK02 : K (F vT) (F v₂) :=
    hcoh vT v₂ (by rw [h_verT]; rfl) (by rw [h_ver₂]; rfl) h_lca.2.1
  obtain ⟨ρm, hρm, hKm1, hKm2⟩ :=
    hJoinWC ev₁ ev₂ sT s₁ s₂ (F vT) (F v₁) (F v₂)
      (fun hab hbc => h.good.vis_trans hab hbc)
      (fun a ha => h.good.vis_irrefl a ha)
      (h.good.ver_events_sub v₁ s₁ ev₁ h_ver₁)
      (h.good.ver_events_sub v₂ s₂ ev₂ h_ver₂)
      (fun a b hab _ hb => h.good.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      (fun a b hab _ hb => h.good.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
      hcT (hprops v₁ s₁ ev₁ h_ver₁) (hprops v₂ s₂ ev₂ h_ver₂)
      hK01 hK02
  have h_sameW : ∀ (E' : Set (Op D.AppOp)) (s' : D.State)
      (ρ' : List (Op D.AppOp)),
      IsCanonWitness W (Configuration.core C) E' s' ρ' →
      IsCanonWitness W (Configuration.core C') E' s' ρ' := by
    intro E' s' ρ' hcs
    refine isCanonWitness_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩,
    storeInv_merge_extend (sm := D.mergeL sT s₁ s₂) h.store h_vm h_ver₁
      h_ver₂ hver_new hver_old hpar_new' hpar_old', ?_⟩
  · -- plain canonical: the weakened aligned join at `vm`
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      exact (h_sameW _ _ _ hρm).isCanonicalStateW.weaken
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
  · -- the coherent family
    intro _
    refine ⟨fun w => if w = vm then ρm else F w, ?_, ?_⟩
    · intro w s' E' hw
      beta_reduce
      by_cases hwn : w = vm
      · rw [hwn] at hw
        rw [hver_new, Option.some.injEq, Prod.mk.injEq] at hw
        rw [← hw.1, ← hw.2, if_pos hwn]
        exact h_sameW _ _ _ hρm
      · rw [hver_old w hwn] at hw
        rw [if_neg hwn]
        exact h_sameW _ _ _ (hprops w s' E' hw)
    · intro u w hu hw hr
      beta_reduce
      by_cases hwn : w = vm
      · rw [hwn] at hr
        rcases reaches_new_target h.store.parents_alloc h_vm hpar_new'
            hpar_old' (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp'
              · rw [h_ver₁]; rfl
              · rw [List.mem_singleton] at hp'
                rw [hp', h_ver₂]; rfl) hr with hu_eq | ⟨p, hp, hrp⟩
        · rw [if_pos hu_eq, if_pos hwn]
          exact hKrefl _
        · rcases List.mem_cons.mp hp with hp₁ | hp'
          · -- through the first branch
            rw [hp₁] at hrp
            have huold : (C.ver u).isSome :=
              reaches_alloc_src h.store.parents_alloc hrp
                (by rw [h_ver₁]; rfl)
            have hune : u ≠ vm := by
              intro he'
              rw [he', h_vm] at huold
              simp at huold
            rw [if_neg hune, if_pos hwn]
            refine hKsub (F u) (F v₁) ρm
              (hcoh u v₁ huold (by rw [h_ver₁]; rfl) hrp) hKm1 ?_
            intro x hx
            obtain ⟨⟨su, Eu⟩, hu'⟩ := Option.isSome_iff_exists.mp huold
            have hxEu : x ∈ Eu := (((hprops u su Eu hu').1).2 x).mp hx
            exact (((hprops v₁ s₁ ev₁ h_ver₁).1).2 x).mpr
              (storeInv_events_mono_reaches h.store hrp hu' h_ver₁ hxEu)
          · -- through the second branch
            rw [List.mem_singleton] at hp'
            rw [hp'] at hrp
            have huold : (C.ver u).isSome :=
              reaches_alloc_src h.store.parents_alloc hrp
                (by rw [h_ver₂]; rfl)
            have hune : u ≠ vm := by
              intro he'
              rw [he', h_vm] at huold
              simp at huold
            rw [if_neg hune, if_pos hwn]
            refine hKsub (F u) (F v₂) ρm
              (hcoh u v₂ huold (by rw [h_ver₂]; rfl) hrp) hKm2 ?_
            intro x hx
            obtain ⟨⟨su, Eu⟩, hu'⟩ := Option.isSome_iff_exists.mp huold
            have hxEu : x ∈ Eu := (((hprops u su Eu hu').1).2 x).mp hx
            exact (((hprops v₂ s₂ ev₂ h_ver₂).1).2 x).mpr
              (storeInv_events_mono_reaches h.store hrp hu' h_ver₂ hxEu)
      · rw [hver_old w hwn] at hw
        have hrw : Reaches C.parents u w :=
          reaches_old_of_new h.store.parents_alloc h_vm hpar_old' hr hw
        have huold : (C.ver u).isSome :=
          reaches_alloc_src h.store.parents_alloc hrw hw
        have hune : u ≠ vm := by
          intro he'
          rw [he', h_vm] at huold
          simp at huold
        rw [if_neg hune, if_neg hwn]
        exact hcoh u w huold hw hrw

open LabeledTS in
/-- **The honest-reachability induction over the coherent witness family**:
the strengthened invariant holds at every `GenHonest`-honestly reachable
configuration, given the aligned join at honest configurations plus the
`W`- and `K`-bookkeeping facts. -/
theorem goodConfigWC_of_genHonest_reach {hInit : D.Inv D.init}
    (hW0 : W [])
    (hWstep : ∀ (e : Op D.AppOp) (ρ : List (Op D.AppOp)) (s : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s → P e s → W (ρ ++ [e]))
    (hKrefl : ∀ ρ, K ρ ρ)
    (hKext : ∀ (ρ σ : List (Op D.AppOp)) (e : Op D.AppOp),
      K ρ σ → e ∉ ρ → K ρ (σ ++ [e]))
    (hKsub : ∀ (α β γ : List (Op D.AppOp)), K α β → K β γ →
      (∀ x ∈ α, x ∈ β) → K α γ)
    (hJoinWC : ∀ C', GenHonest D P C' →
      JoinLemma3AtWC D W K (Configuration.core C'))
    {C : Configuration D}
    (hReach : HonestReach D (GenHonest D P) hInit C) :
    GoodConfigWC P W K C := by
  induction hReach with
  | init => exact goodConfigWC_init hInit hW0 hKrefl
  | step _ hHon hstep ih =>
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfigWC_createReplica h_fresh hL hvis hver hparents ih hHon
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfigWC_apply h_head h_ver h_fresh_t h_fresh_store h_vnew
        hL hvis hver hparents (fun ρ s' => hWstep _ ρ s') hKrefl hKext ih hHon
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfigWC_merge_at hHon (hJoinWC _ hHon)
        h_head₁ h_ver₁ h_ver₂ h_lca h_verT h_vm hL hvis hver hparents
        hKrefl hKsub ih
    | query h_s h_val => exact ih

/-- **The conditioned metatheorem, coherent-witness form**: per-version
RA-linearizability at every `GenHonest`-honestly reachable configuration,
from the ancestry-aligned join. Sound even for datatypes whose
`loOn`-free choices survive in the state (where the plain `W`-join is
refutable, `Shesha_Presplice_Refuted.lean`). -/
theorem ra_linearizable3_of_genHonest_reachWC {hInit : D.Inv D.init}
    (hW0 : W [])
    (hWstep : ∀ (e : Op D.AppOp) (ρ : List (Op D.AppOp)) (s : D.State),
      W ρ → applySeq D.toCRDTSig D.init ρ = s → P e s → W (ρ ++ [e]))
    (hKrefl : ∀ ρ, K ρ ρ)
    (hKext : ∀ (ρ σ : List (Op D.AppOp)) (e : Op D.AppOp),
      K ρ σ → e ∉ ρ → K ρ (σ ++ [e]))
    (hKsub : ∀ (α β γ : List (Op D.AppOp)), K α β → K β γ →
      (∀ x ∈ α, x ∈ β) → K α γ)
    (hJoinWC : ∀ C', GenHonest D P C' →
      JoinLemma3AtWC D W K (Configuration.core C'))
    {C : Configuration D}
    (hReach : HonestReach D (GenHonest D P) hInit C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good
    (goodConfigWC_of_genHonest_reach hW0 hWstep hKrefl hKext hKsub
      hJoinWC hReach).good

#print axioms ra_linearizable3_of_genHonest_reachWC

end GoodWC

end Sal.ConditionedMRDTs
