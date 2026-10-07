import Sal.MRDTs.Paper1.EfficientVCExecution
import Sal.MRDTs.Paper1.GuardedRawModel

/-! Execution and recursive virtual-base preservation parameterized by a
separately derived representation Join. No existing datatype Join is called. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.RawExecution
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]
open EfficientORSet.AbstractSpec
variable (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α)))
local instance : ReplayPolicy (D α).toUpdateSig := rc

theorem version_enumerated {C : Configuration (D α)} (good : CanonicalConfig C)
    {v : Version} {s : State α} {E : Set (Event α)} (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E := by
  obtain ⟨π,hp,_,_⟩ := good.canonical v s E hv
  exact ⟨π,hp⟩

theorem union_enumerated {C : Configuration (D α)} (good : CanonicalConfig C)
    (S : Finset Version) (allocated : ∀ v ∈ S, (C.ver v).isSome) :
    ∃ π, listPermOf π (unionEvents C S) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[],by simp [unionEvents_empty,listPermOf]⟩
  | @insert v S _ ih =>
    obtain ⟨⟨s,E⟩,hv⟩ := Option.isSome_iff_exists.mp (allocated v (by simp))
    obtain ⟨π,hp⟩ := version_enumerated good hv
    obtain ⟨xs,hxs⟩ := ih (fun w hw => allocated w (Finset.mem_insert_of_mem hw))
    have union : unionEvents C (insert v S) = E ∪ unionEvents C S := by
      rw [Finset.insert_eq,unionEvents_union,unionEvents_singleton hv]
    rw [union]
    exact ⟨_,listPermOf_union (D := (D α).toUpdateSig) hp hxs⟩

/-- Adapts the VC-derived represented Join to execution scratch states.
Enumeration and support remain explicit, including for virtual-base folds. -/
theorem vcHistoryMerge (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)} (good : CanonicalConfig C)
    (E₁ E₂ : Set (Event α)) (l a b : State α)
    (enum₁ : ∃ π, listPermOf π E₁) (enum₂ : ∃ π, listPermOf π E₂)
    (sup₁ : AbstractMRDT.Supported C.replayContext E₁)
    (sup₂ : AbstractMRDT.Supported C.replayContext E₂)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (side₁ : Represents C.vis E₁ a) (side₂ : Represents C.vis E₂ b) :
    Represents C.vis (E₁ ∪ E₂) (merge l a b) := by
  obtain ⟨π,hp⟩ := enum₁
  obtain ⟨xs,hxs⟩ := enum₂
  obtain ⟨intersection,hint⟩ := AbstractMRDT.enumeration_subset hp Set.inter_subset_left
  have trans : Transitive C.vis := fun _ _ _ h k => good.vis_trans h k
  have mono : ∀ x y, C.vis x y → x.time < y.time := fun _ _ h => C.causal_mono h
  have result := rawJoin C.replayContext E₁ E₂ l a b trans good.vis_irrefl sup₁ sup₂
    closed₁ closed₂
    ⟨base,⟨intersection,hint⟩,(fun x h => sup₁ x h.1),trans,mono⟩
    ⟨side₁,⟨π,hp⟩,sup₁,trans,mono⟩ ⟨side₂,⟨xs,hxs⟩,sup₂,trans,mono⟩
  exact result.1

end Sal.MRDTs.Paper1.EfficientORSet.RawExecution

namespace Sal.MRDTs.Paper1.EfficientORSet.RawExecution
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]
open EfficientORSet.AbstractSpec
variable (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α)))
local instance : ReplayPolicy (D α).toUpdateSig := rc

def RepConfig (C : Configuration (D α)) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → Represents C.vis E s

private def VCVRepAt (C : Configuration (D α)) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : State α) (Ew : Set (Event α)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    Represents C.vis
      (unionEvents C S ∩ Ew) (virtualBaseAux C.ver C.parents C.parents_lt S w)

/-- Each scratch state represents its union history. The outer induction
supplies the sub-pair's intersection history for the three-way merge. -/
private theorem vc_vfold_represents (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C)
    {n : ℕ} (IH : ∀ k, k < n → VCVRepAt C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (maximalCommonAncestorsWithAny C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : State α),
      (∀ x ∈ accS, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ maximalCommonAncestorsWithAny C.parents S₀ w₀) →
      Represents C.vis (unionEvents C accS) acc →
      Represents C.vis
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
    have enumAcc := union_enumerated hG accS (fun u hu => halloc u (haccS u hu))
    have supAcc : AbstractMRDT.Supported C.replayContext (unionEvents C accS) := by
      rintro a ⟨u,hu,su,Eu,hu',ha⟩
      exact hG.version_events_supported u su Eu hu' a ha
    have hjoin := vcHistoryMerge rawJoin hG (unionEvents C accS) Em _ _ _
      enumAcc (version_enumerated hG hm) supAcc (hG.version_events_supported m sm Em hm)
      hcl1 (fun a b hab hb => hG.version_events_causal m sm Em hm a b hab hb)
      hinner hacc (hR m sm Em hm)
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
private theorem vc_virtualBaseAux_represents_at (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C) :
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
      exact represents_empty C.vis
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
        have hfold := vc_vfold_represents rawJoin hSI hG hR IH (by rw [hw]; rfl) hstrict
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
theorem vcVirtualMergeBaseStateRepresents (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C)
    (hR : RepConfig C)
    {v₁ v₂ : Version} {s₁ s₂ : State α} {ev₁ ev₂ : Set (Event α)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    Represents C.vis (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := vc_virtualBaseAux_represents_at rawJoin hSI hG hR _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

end Sal.MRDTs.Paper1.EfficientORSet.RawExecution

namespace Sal.MRDTs.Paper1.EfficientORSet.RawExecution
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
open EfficientORSet.AbstractSpec
variable (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α)))
local instance : ReplayPolicy (D α).toUpdateSig := rc

theorem vcRepresentedConfig (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  induction reach with
  | init => exact ⟨storeInv_init,canonicalConfig_init,repConfig_init⟩
  | @step C C' l _ mint step _ ih =>
    obtain ⟨hSI,hG,hR⟩ := ih
    refine ⟨storeInv_stepV step.toRaw hSI,?_⟩
    cases step.toRaw with
    | base raw =>
      cases raw with
      | fork fresh sourceHead sourceVersion freshVersion rank C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ freshVersion hver hhead
        exact ⟨canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver hG,
          repConfig_store hvis hver hR (hR _ _ _ sourceVersion)⟩
      | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvnew hversions hheads
        refine ⟨canonicalConfig_apply hhead hver hfresh hL hvis hversions hG,?_⟩
        exact repConfig_apply hver (fun he => hfresh _ he rfl) hvis hversions hG hR
      | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
        have hT := hR _ _ _ hvT
        rw [C.gca_events hgca hv₁ hv₂ hvT] at hT
        have hm := vcHistoryMerge rawJoin hG _ _ _ _ _
          (version_enumerated hG hv₁) (version_enumerated hG hv₂)
          (hG.version_events_supported _ _ _ hv₁) (hG.version_events_supported _ _ _ hv₂)
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := vcVirtualMergeBaseStateRepresents rawJoin hSI hG hR hv₁ hv₂
      have hm := vcHistoryMerge rawJoin hG _ _ _ _ _
          (version_enumerated hG hv₁) (version_enumerated hG hv₂)
          (hG.version_events_supported _ _ _ hv₁) (hG.version_events_supported _ _ _ hv₂)
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩

theorem vcRepresentedVersions (rawJoin : AbstractMRDT.RepresentationJoin (representation (α := α))) {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s := by
  obtain ⟨_,good,represented⟩ := vcRepresentedConfig rawJoin reach
  intro v s E hv
  obtain ⟨π,hp,_⟩ := good.canonical v s E hv
  exact ⟨represented v s E hv,⟨π,hp⟩,
    good.version_events_supported v s E hv,
    (fun _ _ _ h k => good.vis_trans h k),(fun _ _ h => C.causal_mono h)⟩


end Sal.MRDTs.Paper1.EfficientORSet.RawExecution
