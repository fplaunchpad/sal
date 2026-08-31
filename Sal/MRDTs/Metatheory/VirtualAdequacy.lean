import Sal.MRDTs.Metatheory.Adequacy
import Sal.MRDTs.Metatheory.VirtualMergeBase

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical


/-! ## Virtual merge bases: fold canonicity and the widened adequacy

The virtual construction re-supplies, from the ternary join lemma alone, the two facts
the adequacy induction consumed about the merge-base slot: its event set is the intersection
(`maximalCommonAncestorsWithAny_events_cover`, `GCA_Lemma.lean`) and its state is canonical for that set
(`virtualMergeBaseState_canonical`, the fold induction below, the virtual-join claim). `canonicalConfig_mergeVirtual_at` then mirrors `canonicalConfig_merge_at`, and the
reachability bridges re-thread over the widened LTS `labeledTSV`. The per-datatype VC
surface for `Join` datatypes does not move. That is the headline. -/

section VirtualMergeBase
variable {D : MRDTSig}

/-- The union of the registered event sets over a finite support. -/
def unionEvents (C : Configuration D) (S : Finset Version) : Set (Op D.AppOp) :=
  {e | ∃ u ∈ S, ∃ su Eu, C.ver u = some (su, Eu) ∧ e ∈ Eu}

theorem unionEvents_empty (C : Configuration D) :
    unionEvents C ∅ = (∅ : Set (Op D.AppOp)) := by
  ext e
  constructor
  · rintro ⟨u, hu, -⟩
    exact absurd hu (Finset.notMem_empty u)
  · intro h
    exact absurd h (Set.notMem_empty e)

theorem unionEvents_singleton {C : Configuration D} {v : Version} {s : D.State}
    {E : Set (Op D.AppOp)} (hv : C.ver v = some (s, E)) :
    unionEvents C {v} = E := by
  ext e
  constructor
  · rintro ⟨u, hu, su, Eu, hu', he⟩
    rw [Finset.mem_singleton] at hu
    subst hu
    rw [hv, Option.some.injEq, Prod.mk.injEq] at hu'
    rw [hu'.2]
    exact he
  · intro he
    exact ⟨v, Finset.mem_singleton_self v, s, E, hv, he⟩

theorem unionEvents_union (C : Configuration D) (X Y : Finset Version) :
    unionEvents C (X ∪ Y) = unionEvents C X ∪ unionEvents C Y := by
  ext e
  constructor
  · rintro ⟨u, hu, su, Eu, hu', he⟩
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Or.inl ⟨u, hu, su, Eu, hu', he⟩
    · exact Or.inr ⟨u, hu, su, Eu, hu', he⟩
  · rintro (⟨u, hu, su, Eu, hu', he⟩ | ⟨u, hu, su, Eu, hu', he⟩)
    · exact ⟨u, Finset.mem_union_left _ hu, su, Eu, hu', he⟩
    · exact ⟨u, Finset.mem_union_right _ hu, su, Eu, hu', he⟩

/-- **Proposition 1 at the `Finset` level**: the maximal antichain's event-set
union is exactly the support union intersected with `E(w)`. -/
theorem maximalCommonAncestorsWithAny_unionEvents {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) {S : Finset Version} {w : Version}
    (hS : ∀ u ∈ S, (C.ver u).isSome)
    {sw : D.State} {Ew : Set (Op D.AppOp)} (hw : C.ver w = some (sw, Ew)) :
    unionEvents C (maximalCommonAncestorsWithAny C.parents S w) = unionEvents C S ∩ Ew := by
  ext e
  have hcov := maximalCommonAncestorsWithAny_events_cover hSI C.parents_lt (S := (↑S : Set Version))
    (fun u hu => hS u (Finset.mem_coe.mp hu)) hw e
  constructor
  · rintro ⟨m, hm, sm, Em, hm', he⟩
    obtain ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩ :=
      hcov.mp ⟨m, mem_maximalCommonAncestorsWithAny C.parents hm, sm, Em, hm', he⟩
    exact ⟨⟨u, Finset.mem_coe.mp huS, su, Eu, hu, heEu⟩, heEw⟩
  · rintro ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩
    obtain ⟨m, hmMaximal, sm, Em, hm', he⟩ :=
      hcov.mpr ⟨⟨u, Finset.mem_coe.mpr huS, su, Eu, hu, heEu⟩, heEw⟩
    exact ⟨m, (mem_maximalCommonAncestorsWithAny_iff C.parents C.parents_lt).mpr
      hmMaximal, sm, Em, hm', he⟩

/-- The abstract per-configuration join hook the fold consumes: **full-closure**
premises (what `CanonicalConfig.version_events_causal` supplies at every intermediate antichain
union), canonical triple in, canonical union out. Both `JoinAt` (weak closure,
implied by full) and `CausalJoin` instantiate it, so one fold induction serves both
routes. -/
private def VJoinHook (C : Configuration D) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState (Configuration.replayContext C) ev₁ s₁ →
    IsCanonicalState (Configuration.replayContext C) ev₂ s₂ →
    IsCanonicalState (Configuration.replayContext C) (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

private theorem vJoinHook_of_joinAt {C : Configuration D} (hG : CanonicalConfig C)
    (hJ : JoinAt D (Configuration.replayContext C)) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ ev₁ ev₂ s₀ s₁ s₂ (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2
      (fun a b hab _ hb => hcl1 a b hab hb)
      (fun a b hab _ hb => hcl2 a b hab hb) h₀ hs₁ hs₂

private theorem vJoinHook_of_joinF {C : Configuration D} (hG : CanonicalConfig C)
    (hJ : CausalJoin D) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ (Configuration.replayContext C) ev₁ ev₂ s₀ s₁ s₂
      (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2 hcl1 hcl2 h₀ hs₁ hs₂

/-- The canonicity claim at a fixed joint-support measure (the strong-induction
package, mirroring the event-set cardinality induction in `Adequacy`). -/
private def VCanonAt (C : Configuration D) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : D.State) (Ew : Set (Op D.AppOp)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    IsCanonicalState (Configuration.replayContext C)
      (unionEvents C S ∩ Ew) (virtualBaseAux C.ver C.parents C.parents_lt S w)

/-- **The fold induction, inner layer** (note §5): along the ascending-rank fold every
scratch node's state is canonical for its union event set. The inner merge-base slot of each
sub-pair is canonical by the outer induction (`IH`) plus covering; the hook joins. -/
private theorem vfold_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hHook : VJoinHook C)
    {n : ℕ} (IH : ∀ k, k < n → VCanonAt C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (maximalCommonAncestorsWithAny C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : D.State),
      (∀ x ∈ accS, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      IsCanonicalState (Configuration.replayContext C) (unionEvents C accS) acc →
      IsCanonicalState (Configuration.replayContext C)
        (unionEvents C (accS ∪ pending.toFinset))
        (vfoldAux C.ver C.parents C.parents_lt accS acc pending) := by
  -- every antichain member is allocated (it reaches the allocated `w₀`)
  have halloc : ∀ x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀, (C.ver x).isSome := fun x hx =>
    reaches_alloc hSI (mem_maximalCommonAncestorsWithAny C.parents hx).1.2 hw₀
  induction pending with
  | nil =>
    intro accS acc _ _ hacc
    rw [vfoldAux_nil]
    simpa using hacc
  | cons m ms ih =>
    intro accS acc haccS hpend hacc
    rw [vfoldAux_cons]
    have hmM : m ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀ := hpend m List.mem_cons_self
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp (halloc m hmM)
    have hsd : stateD C.ver m = sm := by
      simp [stateD, hm]
    -- the sub-pair's virtual merge base is canonical for the honest intersection (outer IH)
    have hsub : accS ∪ {m} ⊆ maximalCommonAncestorsWithAny C.parents S₀ w₀ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact haccS x hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hmM
    have hcard : (supportOf C.parents (accS ∪ {m})).card < n :=
      Nat.lt_of_le_of_lt
        (Finset.card_le_card (supportOf_mono C.parents C.parents_lt hsub)) hstrict
    have hinner := IH _ hcard accS m sm Em rfl
      (fun u hu => halloc u (haccS u hu)) hm
    -- hook side conditions at (unionEvents accS, Em)
    have h1 : ∀ a ∈ unionEvents C accS, a ∈ C.events := by
      rintro a ⟨u, hu, su, Eu, hu', ha⟩
      exact hG.version_events_supported u su Eu hu' a ha
    have hcl1 : ∀ a b, C.vis a b → b ∈ unionEvents C accS →
        a ∈ unionEvents C accS := by
      rintro a b hab ⟨u, hu, su, Eu, hu', hb⟩
      exact ⟨u, hu, su, Eu, hu', hG.version_events_causal u su Eu hu' a b hab hb⟩
    have hjoin := hHook (unionEvents C accS) Em
      (virtualBaseAux C.ver C.parents C.parents_lt accS m) acc sm
      h1 (hG.version_events_supported m sm Em hm) hcl1
      (fun a b hab hb => hG.version_events_causal m sm Em hm a b hab hb)
      hinner hacc (hG.canonical m sm Em hm)
    -- fold the union back into the grown support and recurse
    have hset : unionEvents C accS ∪ Em = unionEvents C (accS ∪ {m}) := by
      rw [unionEvents_union, unionEvents_singleton hm]
    rw [hset] at hjoin
    have hstep := ih (accS ∪ {m})
      (D.merge (virtualBaseAux C.ver C.parents C.parents_lt accS m) acc sm)
      (fun x hx => hsub hx) (fun x hx => hpend x (List.mem_cons_of_mem m hx)) hjoin
    have hsets : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hsets] at hstep
    rw [hsd]
    exact hstep

/-- The canonicity claim at every measure, by strong induction. -/
private theorem virtualBaseAux_canonical_at {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hHook : VJoinHook C) :
    ∀ n, VCanonAt C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S w sw Ew hmeas hS hw
    rcases hsort : (maximalCommonAncestorsWithAny C.parents S w).sort (· ≤ ·) with _ | ⟨m₁, ms₁⟩
    · -- empty antichain: covering forces an empty intersection; `σ₀` is canonical
      rw [virtualBaseAux_of_sort_nil C.ver C.parents C.parents_lt hsort]
      have hM : maximalCommonAncestorsWithAny C.parents S w = ∅ := by
        rw [← Finset.sort_toFinset (maximalCommonAncestorsWithAny C.parents S w) (· ≤ ·), hsort]
        rfl
      have hcov := maximalCommonAncestorsWithAny_unionEvents hSI hS hw
      rw [hM, unionEvents_empty] at hcov
      rw [← hcov]
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩
    · have hm₁M : m₁ ∈ maximalCommonAncestorsWithAny C.parents S w := by
        rw [← Finset.mem_sort (· ≤ ·), hsort]
        exact List.mem_cons_self
      have hm₁alloc : (C.ver m₁).isSome :=
        reaches_alloc hSI (mem_maximalCommonAncestorsWithAny C.parents hm₁M).1.2 (by rw [hw]; rfl)
      obtain ⟨⟨sm₁, Em₁⟩, hm₁⟩ := Option.isSome_iff_exists.mp hm₁alloc
      have hsd₁ : stateD C.ver m₁ = sm₁ := by simp [stateD, hm₁]
      have hcov := maximalCommonAncestorsWithAny_unionEvents hSI hS hw
      rw [virtualBaseAux_of_sort_cons C.ver C.parents C.parents_lt hsort]
      rcases ms₁ with _ | ⟨m₂, ms₂⟩
      · -- singleton antichain: the existing GCA rule
        rw [vfoldAux_nil, hsd₁]
        have hM : maximalCommonAncestorsWithAny C.parents S w = {m₁} := by
          rw [← Finset.sort_toFinset (maximalCommonAncestorsWithAny C.parents S w) (· ≤ ·), hsort]
          rfl
        rw [hM, unionEvents_singleton hm₁] at hcov
        rw [← hcov]
        exact hG.canonical m₁ sm₁ Em₁ hm₁
      · -- proper antichain: strict support drop, then the fold
        have hm₂M : m₂ ∈ maximalCommonAncestorsWithAny C.parents S w := by
          rw [← Finset.mem_sort (· ≤ ·), hsort]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        have hne : m₁ ≠ m₂ := by
          have hnd := Finset.sort_nodup (maximalCommonAncestorsWithAny C.parents S w) (· ≤ ·)
          rw [hsort, List.nodup_cons] at hnd
          intro h
          exact hnd.1 (h ▸ List.mem_cons_self)
        have hstrict : (supportOf C.parents (maximalCommonAncestorsWithAny C.parents S w)).card < n :=
          hmeas ▸ Finset.card_lt_card
            (supportOf_maximalCommonAncestorsWithAny_ssubset C.parents C.parents_lt hm₁M hm₂M hne)
        have hfold := vfold_canonical hSI hG hHook IH (by rw [hw]; rfl) hstrict
          (m₂ :: ms₂) {m₁} (stateD C.ver m₁)
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)
          (by rw [unionEvents_singleton hm₁, hsd₁]; exact hG.canonical m₁ sm₁ Em₁ hm₁)
        have hMset : ({m₁} ∪ (m₂ :: ms₂).toFinset : Finset Version)
            = maximalCommonAncestorsWithAny C.parents S w := by
          rw [← Finset.sort_toFinset (maximalCommonAncestorsWithAny C.parents S w) (· ≤ ·), hsort]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
            List.mem_cons]
        rw [hMset, hcov] at hfold
        exact hfold

/-- **The fold canonicity (the virtual-join claim)**: at any
configuration satisfying the reachability invariant and the ternary join lemma, the
recursive antichain merge of a head pair is **canonical for the pair's event-set
intersection**, exactly what the adequacy induction demanded of a registered GCA. -/
theorem virtualMergeBaseState_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C)
    (hJoin : JoinAt D (Configuration.replayContext C))
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := virtualBaseAux_canonical_at hSI hG (vJoinHook_of_joinAt hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- **Virtual merge preserves the invariant**, `canonicalConfig_merge_at` with the
registered GCA slot replaced by the recursive antichain merge: `gca_events` is
re-supplied by `maximalCommonAncestorsWithAny_events_cover` and the slot's canonicity by
`virtualMergeBaseState_canonical`; the rest is verbatim. The extra `StoreInv` hypothesis is
what plain/honest reachability already carries (`storeInv_reachableV`). -/
theorem canonicalConfig_mergeVirtual_at
    {C C' : Configuration D}
    (hJoin : JoinAt D (Configuration.replayContext C))
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualMergeBaseState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  have hLr₁ : C.headEvents r₁ = some ev₁ :=
    C.headEvents_eq_of_head_ver h_head₁ h_ver₁
  have hver_new : C'.ver vm
      = some (D.merge (virtualMergeBaseState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
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
  · -- canonical: the virtual merge-base slot is canonical for the intersection
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂)
          (virtualMergeBaseState C v₁ v₂) :=
        virtualMergeBaseState_canonical hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin ev₁ ev₂ (virtualMergeBaseState C v₁ v₂) s₁ s₂
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

/-- The `Join`-driven wrapper (mirror of `canonicalConfig_merge`). -/
theorem canonicalConfig_mergeVirtual (hJoin : Join D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualMergeBaseState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' :=
  canonicalConfig_mergeVirtual_at (hJoin.at _) hSI h_head₁ h_ver₁ h_ver₂ hL hvis hver h

/-- The full-closure variant (the `CausalJoin` route owes nothing new either:
intermediate antichain unions and their meets are fully causally closed). -/
theorem virtualMergeBaseState_canonicalF {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C)
    (hJoin : CausalJoin D)
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := virtualBaseAux_canonical_at hSI hG (vJoinHook_of_joinF hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- Virtual-merge preservation from the full-closure join (mirror of
`canonicalConfig_merge_causal`; consumed by the Enable-wins route). -/
theorem canonicalConfig_mergeVirtual_causal (hJoin : CausalJoin D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.headEvents = updateRep C.headEvents r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualMergeBaseState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : CanonicalConfig C) : CanonicalConfig C' := by
  have hLr₁ : C.headEvents r₁ = some ev₁ :=
    C.headEvents_eq_of_head_ver h_head₁ h_ver₁
  have hver_new : C'.ver vm
      = some (D.merge (virtualMergeBaseState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
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
      have hcT : IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂)
          (virtualMergeBaseState C v₁ v₂) :=
        virtualMergeBaseState_canonicalF hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin (Configuration.replayContext C) ev₁ ev₂
        (virtualMergeBaseState C v₁ v₂) s₁ s₂
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
/-- **The widened `CanonicalConfig` induction**: `StoreInv` is carried alongside (the
virtual case reads it); every gated case is the existing per-step lemma. -/
theorem canonicalConfig_reachableV (hJoin : Join D) {C : Configuration D}
    (hReach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C) :
    CanonicalConfig C := by
  have h : StoreInv C.ver C.parents ∧ CanonicalConfig C := by
    induction hReach with
    | refl => exact ⟨storeInv_init, canonicalConfig_init⟩
    | tail _ hs ih =>
      obtain ⟨ℓ, hstep⟩ := hs
      refine ⟨storeInv_stepV hstep ih.1, ?_⟩
      cases hstep with
      | base hstep' =>
        cases hstep' with
        | fork h_fresh h_sourceHead h_sourceVersion h_vnew h_rank C'
            hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ h_vnew hver hhead
          exact canonicalConfig_fork h_fresh h_sourceHead h_sourceVersion hL hvis hver ih.2
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ h_vnew hver hhead
          exact canonicalConfig_apply h_head h_ver h_fresh_t hL hvis hver ih.2
        | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_gca h_verT h_vm h_rank₁
            h_rank₂ C' hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ h_vm hver hhead
          exact canonicalConfig_merge hJoin h_head₁ h_ver₁ h_ver₂ h_gca h_verT
            hL hvis hver ih.2
        | query h_s h_val => exact ih.2
      | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
          hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update
          _ _ h_vm hver hhead
        exact canonicalConfig_mergeVirtual hJoin ih.1 h_head₁ h_ver₁ h_ver₂
          hL hvis hver ih.2
  exact h.2

open LabeledTS in
/-- **The widened bridge** (re-thread of `replayWitness_of_join`): a replay
witness at every configuration reachable in the LTS **with the
criss-cross gate lifted**, from the same `Join`, no new per-datatype VC. -/
theorem replayWitnessV_of_join (hJoin : Join D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C) :
    HasReplayWitness C :=
  hasReplayWitness_of_canonical (canonicalConfig_reachableV hJoin hReach)

open LabeledTS in
/-- The widened delta-law bridge. -/
theorem replayWitnessV_of_delta
    (hVC : MergeLaws D) (hΔ : DeltaLaws D) (hCD : CausalDeltaLaw D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C) :
    HasReplayWitness C :=
  replayWitnessV_of_join (JoinProof.ofArbitraryStateLaws hVC hΔ hCD) C hReach

open LabeledTS in
/-- The widened full-closure bridge (re-thread of `replayWitness_of_causalJoin`). -/
theorem replayWitnessV_of_causalJoin (hJoin : CausalJoin D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualMergeBase D)).ReachableFrom (initConfig D) C) :
    HasReplayWitness C := by
  suffices h : StoreInv C.ver C.parents ∧ CanonicalConfig C from
    hasReplayWitness_of_canonical h.2
  induction hReach with
  | refl => exact ⟨storeInv_init, canonicalConfig_init⟩
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    refine ⟨storeInv_stepV hstep ih.1, ?_⟩
    cases hstep with
    | base hstep' =>
      cases hstep' with
      | fork h_fresh h_sourceHead h_sourceVersion h_vnew h_rank C'
          hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update
          _ _ h_vnew hver hhead
        exact canonicalConfig_fork h_fresh h_sourceHead h_sourceVersion hL hvis hver ih.2
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update
          _ _ h_vnew hver hhead
        exact canonicalConfig_apply h_head h_ver h_fresh_t hL hvis hver ih.2
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_gca h_verT h_vm h_rank₁
          h_rank₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update
          _ _ h_vm hver hhead
        exact canonicalConfig_merge_causal hJoin h_head₁ h_ver₁ h_ver₂ h_gca h_verT
          hL hvis hver ih.2
      | query h_s h_val => exact ih.2
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update
        _ _ h_vm hver hhead
      exact canonicalConfig_mergeVirtual_causal hJoin ih.1 h_head₁ h_ver₁ h_ver₂
        hL hvis hver ih.2

/-! ### Axiom audit (the virtual-merge-base adequacy layer) -/

#print axioms virtualMergeBaseState_canonical
#print axioms virtualMergeBaseState_canonicalF
#print axioms canonicalConfig_mergeVirtual_at
#print axioms replayWitnessV_of_join
#print axioms replayWitnessV_of_causalJoin

end VirtualMergeBase
