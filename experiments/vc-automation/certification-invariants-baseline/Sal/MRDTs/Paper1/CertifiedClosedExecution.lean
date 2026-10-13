import Sal.MRDTs.Metatheory.AdequacyResult
import Sal.MRDTs.Metatheory.CertifiedAdequacy
import Sal.MRDTs.Metatheory.Correctness

/-! Certified execution adequacy for a full-causal-closure merge contract.
The recursive virtual merge proof descends strictly in ancestry support; each
scratch state is canonical for its union history. No weak-conflict-closure
JoinAt is required, and no datatype-specific Join theorem is invoked. -/
namespace Sal.MRDTs.Paper1.CertifiedClosedExecution
open Foundation Classical
variable {D : MRDTSig} [P : ReplayPolicy D.toUpdateSig]

/-- The usual canonical triple/union contract with full visibility closure. -/
def ClosedJoinAt (D : MRDTSig) [P : ReplayPolicy D.toUpdateSig]
    (C : ReplayContext D.toUpdateSig) : Prop :=
  ∀ (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ e, ¬ C.vis e e) →
    (∀ e ∈ E₁, e ∈ C.events) → (∀ e ∈ E₂, e ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁) →
    (∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂) →
    @IsCanonicalState _ P C (E₁ ∩ E₂) l →
    @IsCanonicalState _ P C E₁ a → @IsCanonicalState _ P C E₂ b →
    @IsCanonicalState _ P C (E₁ ∪ E₂) (D.merge l a b)

private def VJoinHook (C : Configuration D) : Prop :=
  ∀ (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State),
    (∀ e ∈ E₁, e ∈ C.events) → (∀ e ∈ E₂, e ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁) →
    (∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂) →
    IsCanonicalState C.replayContext (E₁ ∩ E₂) l →
    IsCanonicalState C.replayContext E₁ a → IsCanonicalState C.replayContext E₂ b →
    IsCanonicalState C.replayContext (E₁ ∪ E₂) (D.merge l a b)

private theorem vJoinHook_of_closedJoinAt {C : Configuration D}
    (good : CanonicalConfig C) (join : ClosedJoinAt D C.replayContext) : VJoinHook C :=
  fun E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb =>
    join E₁ E₂ l a b good.vis_trans good.vis_irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb

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
    (hJoin : ClosedJoinAt D (Configuration.replayContext C))
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.replayContext C) (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := virtualBaseAux_canonical_at hSI hG (vJoinHook_of_closedJoinAt hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h


/-- Ordinary and recursive virtual merges preserve all stored canonical
states under the full-closure contract, proved simultaneously with store
bookkeeping. Mint eligibility is checked at the original execution node. -/
theorem canonicalConfig_of_mintCertifiedV {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → ClosedJoinAt D C.replayContext)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    CanonicalConfig C := by
  have invariants : StoreInv C.ver C.parents ∧ CanonicalConfig C := by
    induction reach with
    | init => exact ⟨storeInv_init,canonicalConfig_init⟩
    | @step C C' l previous mint step after ih =>
      obtain ⟨store,good⟩ := ih
      have hJoin := join C mint
      have hook := vJoinHook_of_closedJoinAt good hJoin
      refine ⟨storeInv_stepV step.toRaw store,?_⟩
      cases step.toRaw with
      | base raw =>
        cases raw with
        | fork fresh sourceHead sourceVersion freshVersion rank C' hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ freshVersion hver hhead
          exact canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver good
        | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ hvnew hversions hheads
          exact canonicalConfig_apply hhead hver hfresh hL hvis hversions good
        | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
          have base := good.canonical _ _ _ hvT
          rw [C.gca_events hgca hv₁ hv₂ hvT] at base
          have merged := hook _ _ _ _ _
            (good.version_events_supported _ _ _ hv₁)
            (good.version_events_supported _ _ _ hv₂)
            (good.version_events_causal _ _ _ hv₁)
            (good.version_events_causal _ _ _ hv₂)
            base (good.canonical _ _ _ hv₁) (good.canonical _ _ _ hv₂)
          exact canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver good merged
        | query hs hv => exact good
      | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
        have base := virtualMergeBaseState_canonical store good hJoin hv₁ hv₂
        have merged := hook _ _ _ _ _
          (good.version_events_supported _ _ _ hv₁)
          (good.version_events_supported _ _ _ hv₂)
          (good.version_events_causal _ _ _ hv₁)
          (good.version_events_causal _ _ _ hv₂)
          base (good.canonical _ _ _ hv₁) (good.canonical _ _ _ hv₂)
        exact canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver good merged
  exact invariants.2

theorem canonicalConfig_of_mintCertified {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → ClosedJoinAt D C.replayContext)
    {C : Configuration D} (reach : MintCertifiedReach D I C) : CanonicalConfig C :=
  canonicalConfig_of_mintCertifiedV join reach.toV

theorem canonicalConfig_of_execution {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → ClosedJoinAt D C.replayContext)
    {C : Configuration D} (execution : CertifiedExecution D I C) : CanonicalConfig C := by
  cases execution with
  | ordinary reach => exact canonicalConfig_of_mintCertified join reach
  | virtual reach => exact canonicalConfig_of_mintCertifiedV join reach

theorem replayWitness_of_execution {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → ClosedJoinAt D C.replayContext)
    {C : Configuration D} (execution : CertifiedExecution D I C) : HasReplayWitness C :=
  hasReplayWitness_of_canonical (canonicalConfig_of_execution join execution)

#print axioms virtualMergeBaseState_canonical
#print axioms canonicalConfig_of_mintCertifiedV
end Sal.MRDTs.Paper1.CertifiedClosedExecution
