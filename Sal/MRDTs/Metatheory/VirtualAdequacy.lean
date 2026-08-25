import Sal.MRDTs.Metatheory.Adequacy
import Sal.MRDTs.Metatheory.VirtualLCA

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical


/-! ## Virtual LCAs: fold canonicity and the widened adequacy

The virtual construction re-supplies, from the ternary join lemma alone, the two facts
the adequacy induction consumed about the LCA slot: its event set is the intersection
(`mca_events_cover`, `LCA_Lemma.lean`) and its state is canonical for that set
(`virtualLCAState_canonical`, the fold induction below, the virtual-join claim). `goodConfig3_mergeVirtual_at` then mirrors `goodConfig3_merge_at`, and the
reachability bridges re-thread over the widened LTS `labeledTS3V`. The per-datatype VC
surface for `JoinLemma3` datatypes does not move. That is the headline. -/

section VirtualLCA
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

/-- **Proposition 1 at the `Finset` level**: the MCA antichain's event-set union is
exactly the support-union ∩ `E(w)` (from `mca_events_cover` + the `mcaFinset`
characterization). -/
theorem mcaFinset_unionEvents {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) {S : Finset Version} {w : Version}
    (hS : ∀ u ∈ S, (C.ver u).isSome)
    {sw : D.State} {Ew : Set (Op D.AppOp)} (hw : C.ver w = some (sw, Ew)) :
    unionEvents C (mcaFinset C.parents S w) = unionEvents C S ∩ Ew := by
  ext e
  have hcov := mca_events_cover hSI C.parents_lt (S := (↑S : Set Version))
    (fun u hu => hS u (Finset.mem_coe.mp hu)) hw e
  constructor
  · rintro ⟨m, hm, sm, Em, hm', he⟩
    obtain ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩ :=
      hcov.mp ⟨m, mcaFinset_isMCA C.parents hm, sm, Em, hm', he⟩
    exact ⟨⟨u, Finset.mem_coe.mp huS, su, Eu, hu, heEu⟩, heEw⟩
  · rintro ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩
    obtain ⟨m, hmMCA, sm, Em, hm', he⟩ :=
      hcov.mpr ⟨⟨u, Finset.mem_coe.mpr huS, su, Eu, hu, heEu⟩, heEw⟩
    exact ⟨m, (mem_mcaFinset C.parents C.parents_lt).mpr hmMCA, sm, Em, hm', he⟩

/-- The abstract per-configuration join hook the fold consumes: **full-closure**
premises (what `GoodConfig3.ver_causal` supplies at every intermediate antichain
union), canonical triple in, canonical union out. Both `JoinLemma3At` (weak closure,
implied by full) and `JoinLemma3F` instantiate it, so one fold induction serves both
routes. -/
private def VJoinHook (C : Configuration D) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState (Configuration.core C) ev₁ s₁ →
    IsCanonicalState (Configuration.core C) ev₂ s₂ →
    IsCanonicalState (Configuration.core C) (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

private theorem vJoinHook_of_joinAt {C : Configuration D} (hG : GoodConfig3 C)
    (hJ : JoinLemma3At D (Configuration.core C)) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ ev₁ ev₂ s₀ s₁ s₂ (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2
      (fun a b hab _ hb => hcl1 a b hab hb)
      (fun a b hab _ hb => hcl2 a b hab hb) h₀ hs₁ hs₂

private theorem vJoinHook_of_joinF {C : Configuration D} (hG : GoodConfig3 C)
    (hJ : JoinLemma3F D) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ (Configuration.core C) ev₁ ev₂ s₀ s₁ s₂
      (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2 hcl1 hcl2 h₀ hs₁ hs₂

/-- The canonicity claim at a fixed joint-support measure (the strong-induction
package, mirroring `JoinAt3`). -/
private def VCanonAt (C : Configuration D) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : D.State) (Ew : Set (Op D.AppOp)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    IsCanonicalState (Configuration.core C)
      (unionEvents C S ∩ Ew) (vlcaAux C.ver C.parents C.parents_lt S w)

/-- **The fold induction, inner layer** (note §5): along the ascending-rank fold every
scratch node's state is canonical for its union event set. The inner LCA slot of each
sub-pair is canonical by the outer induction (`IH`) plus covering; the hook joins. -/
private theorem vfold_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C) (hHook : VJoinHook C)
    {n : ℕ} (IH : ∀ k, k < n → VCanonAt C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (mcaFinset C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : D.State),
      (∀ x ∈ accS, x ∈ mcaFinset C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ mcaFinset C.parents S₀ w₀) →
      IsCanonicalState (Configuration.core C) (unionEvents C accS) acc →
      IsCanonicalState (Configuration.core C)
        (unionEvents C (accS ∪ pending.toFinset))
        (vfoldAux C.ver C.parents C.parents_lt accS acc pending) := by
  -- every antichain member is allocated (it reaches the allocated `w₀`)
  have halloc : ∀ x ∈ mcaFinset C.parents S₀ w₀, (C.ver x).isSome := fun x hx =>
    reaches_alloc hSI (mcaFinset_isMCA C.parents hx).1.2 hw₀
  induction pending with
  | nil =>
    intro accS acc _ _ hacc
    rw [vfoldAux_nil]
    simpa using hacc
  | cons m ms ih =>
    intro accS acc haccS hpend hacc
    rw [vfoldAux_cons]
    have hmM : m ∈ mcaFinset C.parents S₀ w₀ := hpend m List.mem_cons_self
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp (halloc m hmM)
    have hsd : stateD C.ver m = sm := by
      simp [stateD, hm]
    -- the sub-pair's virtual LCA is canonical for the honest intersection (outer IH)
    have hsub : accS ∪ {m} ⊆ mcaFinset C.parents S₀ w₀ := by
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
      exact hG.ver_events_sub u su Eu hu' a ha
    have hcl1 : ∀ a b, C.vis a b → b ∈ unionEvents C accS →
        a ∈ unionEvents C accS := by
      rintro a b hab ⟨u, hu, su, Eu, hu', hb⟩
      exact ⟨u, hu, su, Eu, hu', hG.ver_causal u su Eu hu' a b hab hb⟩
    have hjoin := hHook (unionEvents C accS) Em
      (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm
      h1 (hG.ver_events_sub m sm Em hm) hcl1
      (fun a b hab hb => hG.ver_causal m sm Em hm a b hab hb)
      hinner hacc (hG.canonical m sm Em hm)
    -- fold the union back into the grown support and recurse
    have hset : unionEvents C accS ∪ Em = unionEvents C (accS ∪ {m}) := by
      rw [unionEvents_union, unionEvents_singleton hm]
    rw [hset] at hjoin
    have hstep := ih (accS ∪ {m})
      (D.merge (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm)
      (fun x hx => hsub hx) (fun x hx => hpend x (List.mem_cons_of_mem m hx)) hjoin
    have hsets : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hsets] at hstep
    rw [hsd]
    exact hstep

/-- The canonicity claim at every measure, by strong induction. -/
private theorem vlcaAux_canonical_at {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C) (hHook : VJoinHook C) :
    ∀ n, VCanonAt C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S w sw Ew hmeas hS hw
    rcases hsort : (mcaFinset C.parents S w).sort (· ≤ ·) with _ | ⟨m₁, ms₁⟩
    · -- empty antichain: covering forces an empty intersection; `σ₀` is canonical
      rw [vlcaAux_of_sort_nil C.ver C.parents C.parents_lt hsort]
      have hM : mcaFinset C.parents S w = ∅ := by
        rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
        rfl
      have hcov := mcaFinset_unionEvents hSI hS hw
      rw [hM, unionEvents_empty] at hcov
      rw [← hcov]
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩
    · have hm₁M : m₁ ∈ mcaFinset C.parents S w := by
        rw [← Finset.mem_sort (· ≤ ·), hsort]
        exact List.mem_cons_self
      have hm₁alloc : (C.ver m₁).isSome :=
        reaches_alloc hSI (mcaFinset_isMCA C.parents hm₁M).1.2 (by rw [hw]; rfl)
      obtain ⟨⟨sm₁, Em₁⟩, hm₁⟩ := Option.isSome_iff_exists.mp hm₁alloc
      have hsd₁ : stateD C.ver m₁ = sm₁ := by simp [stateD, hm₁]
      have hcov := mcaFinset_unionEvents hSI hS hw
      rw [vlcaAux_of_sort_cons C.ver C.parents C.parents_lt hsort]
      rcases ms₁ with _ | ⟨m₂, ms₂⟩
      · -- singleton antichain: the existing LCA rule
        rw [vfoldAux_nil, hsd₁]
        have hM : mcaFinset C.parents S w = {m₁} := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          rfl
        rw [hM, unionEvents_singleton hm₁] at hcov
        rw [← hcov]
        exact hG.canonical m₁ sm₁ Em₁ hm₁
      · -- proper antichain: strict support drop, then the fold
        have hm₂M : m₂ ∈ mcaFinset C.parents S w := by
          rw [← Finset.mem_sort (· ≤ ·), hsort]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        have hne : m₁ ≠ m₂ := by
          have hnd := Finset.sort_nodup (mcaFinset C.parents S w) (· ≤ ·)
          rw [hsort, List.nodup_cons] at hnd
          intro h
          exact hnd.1 (h ▸ List.mem_cons_self)
        have hstrict : (supportOf C.parents (mcaFinset C.parents S w)).card < n :=
          hmeas ▸ Finset.card_lt_card
            (supportOf_mca_ssubset C.parents C.parents_lt hm₁M hm₂M hne)
        have hfold := vfold_canonical hSI hG hHook IH (by rw [hw]; rfl) hstrict
          (m₂ :: ms₂) {m₁} (stateD C.ver m₁)
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)
          (by rw [unionEvents_singleton hm₁, hsd₁]; exact hG.canonical m₁ sm₁ Em₁ hm₁)
        have hMset : ({m₁} ∪ (m₂ :: ms₂).toFinset : Finset Version)
            = mcaFinset C.parents S w := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
            List.mem_cons]
        rw [hMset, hcov] at hfold
        exact hfold

/-- **The fold canonicity (the virtual-join claim)**: at any
configuration satisfying the reachability invariant and the ternary join lemma, the
recursive antichain merge of a head pair is **canonical for the pair's event-set
intersection**, exactly what the adequacy induction demanded of a registered LCA. -/
theorem virtualLCAState_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C)
    (hJoin : JoinLemma3At D (Configuration.core C))
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
      (virtualLCAState C v₁ v₂) := by
  have h := vlcaAux_canonical_at hSI hG (vJoinHook_of_joinAt hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- **Virtual merge preserves the invariant**, `goodConfig3_merge_at` with the
registered LCA slot replaced by the recursive antichain merge: `lca_events` is
re-supplied by `mca_events_cover` and the slot's canonicity by
`virtualLCAState_canonical`; the rest is verbatim. The extra `StoreInv` hypothesis is
what plain/honest reachability already carries (`storeInv_reachableV`). -/
theorem goodConfig3_mergeVirtual_at
    {C C' : Configuration D}
    (hJoin : JoinLemma3At D (Configuration.core C))
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm
      = some (D.merge (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [Configuration.core_vis, Configuration.core_vis, hvis]
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
  · -- canonical: the virtual LCA slot is canonical for the intersection
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
          (virtualLCAState C v₁ v₂) :=
        virtualLCAState_canonical hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin ev₁ ev₂ (virtualLCAState C v₁ v₂) s₁ s₂
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
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

/-- The `JoinLemma3`-driven wrapper (mirror of `goodConfig3_merge`). -/
theorem goodConfig3_mergeVirtual (hJoin : JoinLemma3 D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' :=
  goodConfig3_mergeVirtual_at (hJoin.at _) hSI h_head₁ h_ver₁ h_ver₂ hL hvis hver h

/-- The full-closure variant (the `JoinLemma3F` route owes nothing new either:
intermediate antichain unions and their meets are fully causally closed). -/
theorem virtualLCAState_canonicalF {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C)
    (hJoin : JoinLemma3F D)
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
      (virtualLCAState C v₁ v₂) := by
  have h := vlcaAux_canonical_at hSI hG (vJoinHook_of_joinF hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- Virtual-merge preservation from the full-closure join (mirror of
`goodConfig3_mergeF`; consumed by the Enable-wins route). -/
theorem goodConfig3_mergeVirtualF (hJoin : JoinLemma3F D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.merge (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm
      = some (D.merge (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [Configuration.core_vis, Configuration.core_vis, hvis]
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
  · intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
          (virtualLCAState C v₁ v₂) :=
        virtualLCAState_canonicalF hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin (Configuration.core C) ev₁ ev₂
        (virtualLCAState C v₁ v₂) s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
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

open LabeledTS in
/-- **The widened `GoodConfig3` induction**: `StoreInv` is carried alongside (the
virtual case reads it); every gated case is the existing per-step lemma. -/
theorem goodConfig3_reachableV (hJoin : JoinLemma3 D) {C : Configuration D}
    (hReach : (labeledTSV D (canonicalVirtualLCA D)).ReachableFrom (initConfig D) C) :
    GoodConfig3 C := by
  have h : StoreInv C.ver C.parents ∧ GoodConfig3 C := by
    induction hReach with
    | refl => exact ⟨storeInv_init, goodConfig3_init⟩
    | tail _ hs ih =>
      obtain ⟨ℓ, hstep⟩ := hs
      refine ⟨storeInv_stepV hstep ih.1, ?_⟩
      cases hstep with
      | base hstep' =>
        cases hstep' with
        | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_createReplica h_fresh hL hvis hver ih.2
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hN hL hvis hver hhead hparents =>
          exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih.2
        | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
            h_rank₂ C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_merge hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
            hL hvis hver ih.2
        | query h_s h_val => exact ih.2
      | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3_mergeVirtual hJoin ih.1 h_head₁ h_ver₁ h_ver₂
          hL hvis hver ih.2
  exact h.2

open LabeledTS in
/-- **The widened bridge** (re-thread of `ra_linearizable3_of_join`): per-version
RA-linearizability at every configuration reachable in the LTS **with the
criss-cross gate lifted**, from the same `JoinLemma3`, no new per-datatype VC. -/
theorem ra_linearizable3V_of_join (hJoin : JoinLemma3 D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualLCA D)).ReachableFrom (initConfig D) C) :
    IsRALinearizableJoin C :=
  isRALinearizable3_of_good (goodConfig3_reachableV hJoin hReach)

open LabeledTS in
/-- The widened route-B bridge (mirror of `ra_linearizable_of_core_delta_cd3`). -/
theorem ra_linearizable_of_core_delta_cd3V
    (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D) (hCD : CDVC3 D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualLCA D)).ReachableFrom (initConfig D) C) :
    IsRALinearizableJoin C :=
  ra_linearizable3V_of_join (join_lemma3_of_cd hVC hΔ hCD) C hReach

open LabeledTS in
/-- The widened full-closure bridge (re-thread of `ra_linearizable3_of_joinF`). -/
theorem ra_linearizable3V_of_joinF (hJoin : JoinLemma3F D)
    (C : Configuration D)
    (hReach : (labeledTSV D (canonicalVirtualLCA D)).ReachableFrom (initConfig D) C) :
    IsRALinearizableJoin C := by
  suffices h : StoreInv C.ver C.parents ∧ GoodConfig3 C from
    isRALinearizable3_of_good h.2
  induction hReach with
  | refl => exact ⟨storeInv_init, goodConfig3_init⟩
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    refine ⟨storeInv_stepV hstep ih.1, ?_⟩
    cases hstep with
    | base hstep' =>
      cases hstep' with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_createReplica h_fresh hL hvis hver ih.2
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih.2
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
          h_rank₂ C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_mergeF hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
          hL hvis hver ih.2
      | query h_s h_val => exact ih.2
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_mergeVirtualF hJoin ih.1 h_head₁ h_ver₁ h_ver₂
        hL hvis hver ih.2

/-! ### Axiom audit (the virtual-LCA adequacy layer) -/

#print axioms virtualLCAState_canonical
#print axioms virtualLCAState_canonicalF
#print axioms goodConfig3_mergeVirtual_at
#print axioms ra_linearizable3V_of_join
#print axioms ra_linearizable3V_of_joinF

end VirtualLCA


