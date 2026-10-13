import Sal.MRDTs.Instances.MVRLiveCertified
import Sal.MRDTs.Paper1.CertifiedMVRVC

/-! Execution preservation parameterized by the newly VC-derived merge rule.
No legacy MVR representation-merge or execution correctness theorem is used. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Execution
open Foundation Instances.MVRLive
open Classical
local instance : ReplayPolicy D.toUpdateSig := rc

def HistoryMerge : Prop :=
  ∀ (C : Configuration D), CertifiedExecution D issuance C → Transitive C.vis →
  ∀ E₁ E₂ : Set Event, E₁ ⊆ C.events → E₂ ⊆ C.events →
  (∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁) →
  (∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂) →
  E₁.Finite → E₂.Finite → ∀ l a b : State,
  Represents (E₁ ∩ E₂) l → Represents E₁ a → Represents E₂ b →
  Represents (E₁ ∪ E₂) (merge l a b)

theorem version_finite {C : Configuration D} (good : CanonicalConfig C)
    {v : Version} {s : State} {E : Set Event} (hv : C.ver v = some (s,E)) : E.Finite := by
  obtain ⟨π,hp,_,_⟩ := good.canonical v s E hv
  exact Set.Finite.subset (List.finite_toSet π) (fun e he => (hp.2 e).mpr he)

theorem union_finite {C : Configuration D} (good : CanonicalConfig C)
    (S : Finset Version) (allocated : ∀ v ∈ S, (C.ver v).isSome) : (unionEvents C S).Finite := by
  induction S using Finset.induction_on with
  | empty => simpa only [unionEvents_empty] using Set.finite_empty
  | @insert v S _ ih =>
    obtain ⟨⟨s,E⟩,hv⟩ := Option.isSome_iff_exists.mp (allocated v (by simp))
    have union : unionEvents C (insert v S) = E ∪ unionEvents C S := by
      rw [Finset.insert_eq,unionEvents_union,unionEvents_singleton hv]
    rw [union]
    exact (version_finite good hv).union (ih (fun w hw => allocated w (Finset.mem_insert_of_mem hw)))

private def VCVRepAt (C : Configuration D) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : State) (Ew : Set (Event)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    Represents
      (unionEvents C S ∩ Ew) (virtualBaseAux C.ver C.parents C.parents_lt S w)

/-- Each scratch state represents its union history. The outer induction
supplies the sub-pair's intersection history for the three-way merge. -/
private theorem vcVfoldRepresents (historyMerge : HistoryMerge) {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C) (execution : CertifiedExecution D issuance C)
    {n : ℕ} (IH : ∀ k, k < n → VCVRepAt C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (maximalCommonAncestorsWithAny C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : State),
      (∀ x ∈ accS, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      Represents (unionEvents C accS) acc →
      Represents
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
    -- Both histories are causally closed.
    have hcl1 : ∀ a b, C.vis a b → b ∈ unionEvents C accS →
        a ∈ unionEvents C accS := by
      rintro a b hab ⟨u, hu, su, Eu, hu', hb⟩
      exact ⟨u, hu, su, Eu, hu', hG.version_events_causal u su Eu hu' a b hab hb⟩
    have hsup1 : unionEvents C accS ⊆ C.events := by
      rintro e ⟨v,hv,sv,Ev,hver,he⟩
      exact hG.version_events_supported v sv Ev hver e he
    have hjoin := historyMerge C execution (fun _ _ _ h k => hG.vis_trans h k) (unionEvents C accS) Em
      hsup1 (fun e he => hG.version_events_supported m sm Em hm e he)
      hcl1 (fun a b hab hb => hG.version_events_causal m sm Em hm a b hab hb)
      (union_finite hG accS (fun u hu => halloc u (haccS u hu)))
      (version_finite hG hm) _ _ _ hinner hacc (hR m sm Em hm)
    -- fold the union back into the grown support and recurse
    have hset : unionEvents C accS ∪ Em = unionEvents C (accS ∪ {m}) := by
      rw [unionEvents_union, unionEvents_singleton hm]
    rw [hset] at hjoin
    have hstep := ih (accS ∪ {m})
      (merge (virtualBaseAux C.ver C.parents C.parents_lt accS m) acc sm)
      (fun x hx => hsub hx) (fun x hx => hpend x (List.mem_cons_of_mem m hx)) hjoin
    have hsets : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hsets] at hstep
    rw [hsd]
    exact hstep

/-- The history characterization at every support size, by strong induction. -/
private theorem vcVirtualBaseAuxRepresentsAt (historyMerge : HistoryMerge) {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C) (execution : CertifiedExecution D issuance C) :
    ∀ n, VCVRepAt C n := by
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
      exact represents_empty
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
        exact hR m₁ sm₁ Em₁ hm₁
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
        have hfold := vcVfoldRepresents historyMerge hSI hG hR execution IH (by rw [hw]; rfl) hstrict
          (m₂ :: ms₂) {m₁} (stateD C.ver m₁)
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)
          (by rw [unionEvents_singleton hm₁, hsd₁]; exact hR m₁ sm₁ Em₁ hm₁)
        have hMset : ({m₁} ∪ (m₂ :: ms₂).toFinset : Finset Version)
            = maximalCommonAncestorsWithAny C.parents S w := by
          rw [← Finset.sort_toFinset (maximalCommonAncestorsWithAny C.parents S w) (· ≤ ·), hsort]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
            List.mem_cons]
        rw [hMset, hcov] at hfold
        exact hfold

/-- Recursive antichain merge represents the pair's event-set intersection.
This uses history-compatible states, not arbitrary canonical replays. -/
theorem vcVirtualMergeBaseStateRepresents (historyMerge : HistoryMerge) {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C)
    (hR : RepConfig C) (execution : CertifiedExecution D issuance C)
    {v₁ v₂ : Version} {s₁ s₂ : State} {ev₁ ev₂ : Set (Event)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    Represents (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := vcVirtualBaseAuxRepresentsAt historyMerge hSI hG hR execution _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

theorem representedConfig (historyMerge : HistoryMerge) {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  induction reach with
  | init => exact ⟨storeInv_init,canonicalConfig_init,repConfig_init⟩
  | @step C C' l previous mint step after ih =>
    obtain ⟨hSI,hG,hR⟩ := ih
    refine ⟨storeInv_stepV step.toRaw hSI,?_⟩
    cases step.toRaw with
    | base raw =>
      cases raw with
      | fork fresh sourceHead sourceVersion freshVersion rank C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ freshVersion hver hhead
        exact ⟨canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver hG,
          repConfig_store hver hR (hR _ _ _ sourceVersion)⟩
      | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvnew hversions hheads
        have hG' := canonicalConfig_apply hhead hver hfresh hL hvis hversions hG
        exact ⟨hG',repConfig_apply hver hversions (fun a ha => hfresh a ha) hG hG' mint after hR⟩
      | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
        have hT := hR _ _ _ hvT
        rw [C.gca_events hgca hv₁ hv₂ hvT] at hT
        have hm := historyMerge C (.virtual previous) (fun _ _ _ h k => hG.vis_trans h k) _ _
          (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
          (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          (version_finite hG hv₁) (version_finite hG hv₂) _ _ _
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := vcVirtualMergeBaseStateRepresents historyMerge hSI hG hR (.virtual previous) hv₁ hv₂
      have hm := historyMerge C (.virtual previous) (fun _ _ _ h k => hG.vis_trans h k) _ _
        (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
        (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        (version_finite hG hv₁) (version_finite hG hv₂) _ _ _
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩


/-- Both ordinary and recursive-virtual certified executions preserve raw
history representation via the supplied VC-derived merge rule. -/
theorem representedExecution (historyMerge : HistoryMerge) {C : Configuration D}
    (execution : CertifiedExecution D issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  cases execution with
  | ordinary reach => exact representedConfig historyMerge reach.toV
  | virtual reach => exact representedConfig historyMerge reach

theorem representedVersions (historyMerge : HistoryMerge) {C : Configuration D}
    (execution : CertifiedExecution D issuance C) :
    ∀ v s E, C.ver v = some (s,E) → Represents E s :=
  (representedExecution historyMerge execution).2.2

/-- The only merge premise in the induction is discharged by the five new raw
VCs and their strict finite-history Join derivation. -/
theorem vcHistoryMerge : HistoryMerge := by
  intro C execution trans E₁ E₂ sup₁ sup₂ closed₁ closed₂ finite₁ finite₂ l a b hl ha hb
  exact RawVC.represents_merge C execution trans E₁ E₂ sup₁ sup₂ closed₁ closed₂
    finite₁ finite₂ hl ha hb

theorem vcRepresentedConfig {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C :=
  representedConfig vcHistoryMerge reach

theorem vcRepresentedVersions {C : Configuration D}
    (execution : CertifiedExecution D issuance C) :
    ∀ v s E, C.ver v = some (s,E) → Represents E s :=
  representedVersions vcHistoryMerge execution

#print axioms vcVirtualMergeBaseStateRepresents
#print axioms representedConfig
#print axioms representedVersions

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.Execution
