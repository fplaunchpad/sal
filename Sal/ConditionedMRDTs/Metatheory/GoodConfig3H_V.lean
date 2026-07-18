import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H

/-!
# The H-disciplined metatheorem over the widened LTS `Step3V` (task #90)

*Additive; modifies no existing file; 0 `sorry`.*

The virtual-LCA extension (`LCA_Lemma.lean` §8–§9, `Adequacy.lean` §VirtualLCA) carried
the PLAIN `GoodConfig3` adequacy through the widened step relation `Step3V`.  This file
carries the **H-disciplined layer** (`GoodConfig3H`) through it, so the production
Eq-quotient capstones (the rehoming RGA's `rga_ra_linearizable3_eq`, the flats'
identity-Eq capstones) can run at every `Step3V`-reachable configuration:

* `vfold_canonicalH` / `vlcaAuxH_canonical_at` — **the H-layer fold induction**: along
  the ascending-rank antichain fold, every scratch node's state is `H`-canonical
  (`IsCanonicalStateH`) **for its own union event set**.  Each step consumes the
  datatype's `≈`-Join (`EqJoinLemma3C_H`) at the sub-pair `(E(acc), E(mᵢ))` — the hook is
  already stated for *arbitrary* closed subsets of the ambient universe under the ambient
  join context `HonJ`, so no per-datatype condition is re-presented at intermediate
  unions: predecessor-closure of a union is the union of the branch closures
  (`fullClosureRel` is union-closed), and everything else in the hook's premise list is
  ambient.  For the rehoming RGA the hook's own discharge routes the union through
  K1/`GenDisc2C` (`rga_hEnum_discharged` + `isDepPreC_of_restrict`); **no `noopFeasible`
  clause appears anywhere at unions** (the H layer replaced it — the probe's refutation
  of `noopFeasible` at antichain unions is respected by construction).
* `virtualLCAState_canonicalH` — the head-pair corollary: the recursive antichain merge
  is `H`-canonical for the pair's event-set intersection.
* `goodConfig3H_mergeVirtual` — the mergeVirtual preservation step (mirror of
  `goodConfig3H_merge` with the registered LCA slot replaced by `virtualLCAState`).
* `goodConfig3H_of_reachV` / `RA_linearizable_up_to_eq_H_V` — the reachability induction
  and the RAW-≈ metatheorem over `labeledTS3V` (the criss-cross gate lifted), from the
  SAME per-datatype hypotheses as the gated theorem (the honest premises now quantified
  over `Step3V`-reachable configurations).

**Statement hygiene** (from the rehoming probe, `whiteboard/rehoming-vlca-probe.md` §4):
scratch-node canonicity is stated per node FOR ITS OWN UNION ONLY (`VCanonAtH` fixes the
pair `(S, w)` and speaks of `unionEvents S ∩ E(w)`), and nothing is claimed about
intermediate scratch states across fold orders — the probe's 3-antichain shows they are
enumeration-order-dependent; only the returned LCA state is order-independent, and the
fixed ascending-rank fold makes even that claim unnecessary here.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.GoodConfig3H

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs (Configuration Version Step3 Step3V Label3 initConfig
  labeledTS3 labeledTS3V core_vis StoreInv storeInv_init storeInv_stepV
  virtualLCAState vlcaAux vfoldAux stateD mcaFinset supportOf unionEvents)

variable {D : ConditionedMRDTSig}
variable (H : List (Op D.AppOp) → Prop)
variable (HonJ : (Op D.AppOp → Op D.AppOp → Prop) → Set (Op D.AppOp) → Prop)
variable (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
variable (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)

/-! ## §1  The H-layer fold canonicity -/

/-- The H-canonicity claim at a fixed joint-support measure — **per scratch node, for its
own union event set only** (statement hygiene: nothing about other fold orders). -/
private def VCanonAtH (C : Configuration (QSig E W hP hC hA)) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : QState D E) (Ew : Set (Op D.AppOp)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C)
      (unionEvents (D := QSig E W hP hC hA) C S ∩ Ew)
      (vlcaAux C.ver C.parents C.parents_lt S w)

/-- **The H-layer fold induction, inner layer** (mirror of `Adequacy.vfold_canonical`):
along the ascending-rank fold every scratch node's state is `H`-canonical for its union
event set.  The sub-pair's inner LCA slot is `H`-canonical by the outer induction plus
covering; the datatype's `≈`-Join (`mergedH_of_join`) joins — its closure premises at the
union are the union of the branch closures, its context (`HonJ`) is ambient. -/
private theorem vfold_canonicalH {C : Configuration (QSig E W hP hC hA)}
    (hSI : StoreInv C.ver C.parents) (hS : GoodConfig3S C)
    (hcanon : ∀ (v : Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
      C.ver v = some (s, Ev) →
      IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C) Ev s)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHonJ : HonJ (Sal.ConditionedMRDTs.Configuration.core C).vis
      (Sal.ConditionedMRDTs.Configuration.core C).events)
    {n : ℕ} (IH : ∀ k, k < n → VCanonAtH H E W hP hC hA C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (mcaFinset C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : QState D E),
      (∀ x ∈ accS, x ∈ mcaFinset C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ mcaFinset C.parents S₀ w₀) →
      IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C)
        (unionEvents (D := QSig E W hP hC hA) C accS) acc →
      IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C)
        (unionEvents (D := QSig E W hP hC hA) C (accS ∪ pending.toFinset))
        (vfoldAux C.ver C.parents C.parents_lt accS acc pending) := by
  -- ambient facts, once: distinct timestamps and allocation of antichain members
  have hdts : ∀ a b : Op D.AppOp,
      a ∈ (Sal.ConditionedMRDTs.Configuration.core C).events →
      b ∈ (Sal.ConditionedMRDTs.Configuration.core C).events → a ≠ b → a.1 ≠ b.1 := by
    intro a b ha hb hne
    obtain ⟨r, s, hLr, hsa⟩ := ha
    obtain ⟨r', s', hLr', hsb⟩ := hb
    exact (Sal.ConditionedMRDTs.Configuration.core C).timestamps_distinct
      hLr hsa hLr' hsb hne
  have halloc : ∀ x ∈ mcaFinset C.parents S₀ w₀, (C.ver x).isSome := fun x hx =>
    Sal.ConditionedMRDTs.reaches_alloc hSI
      (Sal.ConditionedMRDTs.mcaFinset_isMCA C.parents hx).1.2 hw₀
  induction pending with
  | nil =>
    intro accS acc _ _ hacc
    rw [Sal.ConditionedMRDTs.vfoldAux_nil]
    simpa using hacc
  | cons m ms ih =>
    intro accS acc haccS hpend hacc
    rw [Sal.ConditionedMRDTs.vfoldAux_cons]
    have hmM : m ∈ mcaFinset C.parents S₀ w₀ := hpend m List.mem_cons_self
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp (halloc m hmM)
    have hsd : stateD C.ver m = sm := by
      simp [stateD, hm]
    -- the sub-pair's virtual LCA is H-canonical for the intersection (outer IH)
    have hsub : accS ∪ {m} ⊆ mcaFinset C.parents S₀ w₀ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact haccS x hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hmM
    have hcard : (supportOf C.parents (accS ∪ {m})).card < n :=
      Nat.lt_of_le_of_lt
        (Finset.card_le_card
          (Sal.ConditionedMRDTs.supportOf_mono C.parents C.parents_lt hsub)) hstrict
    have hinner := IH _ hcard accS m sm Em rfl
      (fun u hu => halloc u (haccS u hu)) hm
    -- the join's side conditions at (unionEvents accS, Em): membership and closure,
    -- both UNION-CLOSED from the structural invariant (probe §5: per-event components)
    have h1 : ∀ a ∈ unionEvents (D := QSig E W hP hC hA) C accS,
        a ∈ (Sal.ConditionedMRDTs.Configuration.core C).events := by
      rintro a ⟨u, hu, su, Eu, hu', ha⟩
      exact hS.ver_events_sub u su Eu hu' a ha
    have hcl1 : fullClosureRel (Sal.ConditionedMRDTs.Configuration.core C).vis
        (unionEvents (D := QSig E W hP hC hA) C accS) := by
      rintro a b hab ⟨u, hu, su, Eu, hu', hb⟩
      exact ⟨u, hu, su, Eu, hu', hS.ver_causal u su Eu hu' a b hab hb⟩
    have hjoin := mergedH_of_join H HonJ E W hP hC hA hJoinH
      (Sal.ConditionedMRDTs.Configuration.core C)
      (Sal.ConditionedMRDTs.Configuration.core C).events
      (unionEvents (D := QSig E W hP hC hA) C accS) Em
      (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm
      hHonJ
      (fun hab hbc => hS.vis_trans hab hbc)
      (fun a ha => hS.vis_irrefl a ha)
      hdts
      h1 (hS.ver_events_sub m sm Em hm)
      hcl1
      (fun a b hab hb => hS.ver_causal m sm Em hm a b hab hb)
      hinner hacc (hcanon m sm Em hm)
    -- fold the union back into the grown support and recurse
    have hset : unionEvents (D := QSig E W hP hC hA) C accS ∪ Em
        = unionEvents (D := QSig E W hP hC hA) C (accS ∪ {m}) := by
      rw [Sal.ConditionedMRDTs.unionEvents_union,
        Sal.ConditionedMRDTs.unionEvents_singleton hm]
    rw [hset] at hjoin
    have hstep := ih (accS ∪ {m})
      ((QSig E W hP hC hA).mergeL (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm)
      (fun x hx => hsub hx) (fun x hx => hpend x (List.mem_cons_of_mem m hx)) hjoin
    have hsets : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hsets] at hstep
    rw [hsd]
    exact hstep

/-- The H-canonicity claim at every measure, by strong induction (mirror of
`Adequacy.vlcaAux_canonical_at`).  The empty antichain returns `σ₀`, whose witness is
`[]` — this is where `H []` (`hHnil`) enters; the singleton antichain is the registered
slot's own H-witness. -/
private theorem vlcaAuxH_canonical_at {C : Configuration (QSig E W hP hC hA)}
    (hSI : StoreInv C.ver C.parents) (hS : GoodConfig3S C)
    (hcanon : ∀ (v : Version) (s : QState D E) (Ev : Set (Op D.AppOp)),
      C.ver v = some (s, Ev) →
      IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C) Ev s)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHonJ : HonJ (Sal.ConditionedMRDTs.Configuration.core C).vis
      (Sal.ConditionedMRDTs.Configuration.core C).events)
    (hHnil : H []) :
    ∀ n, VCanonAtH H E W hP hC hA C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S w sw Ew hmeas hS' hw
    rcases hsort : (mcaFinset C.parents S w).sort (· ≤ ·) with _ | ⟨m₁, ms₁⟩
    · -- empty antichain: covering forces an empty intersection; `σ₀` with witness `[]`
      rw [Sal.ConditionedMRDTs.vlcaAux_of_sort_nil C.ver C.parents C.parents_lt hsort]
      have hM : mcaFinset C.parents S w = ∅ := by
        rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
        rfl
      have hcov := Sal.ConditionedMRDTs.mcaFinset_unionEvents hSI hS' hw
      rw [hM, Sal.ConditionedMRDTs.unionEvents_empty] at hcov
      rw [← hcov]
      exact ⟨D.init, hP.inv_init, rfl,
        [], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, hHnil,
        E.equiv.refl _⟩
    · have hm₁M : m₁ ∈ mcaFinset C.parents S w := by
        rw [← Finset.mem_sort (· ≤ ·), hsort]
        exact List.mem_cons_self
      have hm₁alloc : (C.ver m₁).isSome :=
        Sal.ConditionedMRDTs.reaches_alloc hSI
          (Sal.ConditionedMRDTs.mcaFinset_isMCA C.parents hm₁M).1.2 (by rw [hw]; rfl)
      obtain ⟨⟨sm₁, Em₁⟩, hm₁⟩ := Option.isSome_iff_exists.mp hm₁alloc
      have hsd₁ : stateD C.ver m₁ = sm₁ := by simp [stateD, hm₁]
      have hcov := Sal.ConditionedMRDTs.mcaFinset_unionEvents hSI hS' hw
      rw [Sal.ConditionedMRDTs.vlcaAux_of_sort_cons C.ver C.parents C.parents_lt hsort]
      rcases ms₁ with _ | ⟨m₂, ms₂⟩
      · -- singleton antichain: the registered slot's own H-witness
        rw [Sal.ConditionedMRDTs.vfoldAux_nil, hsd₁]
        have hM : mcaFinset C.parents S w = {m₁} := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          rfl
        rw [hM, Sal.ConditionedMRDTs.unionEvents_singleton hm₁] at hcov
        rw [← hcov]
        exact hcanon m₁ sm₁ Em₁ hm₁
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
            (Sal.ConditionedMRDTs.supportOf_mca_ssubset C.parents C.parents_lt
              hm₁M hm₂M hne)
        have hfold := vfold_canonicalH H HonJ E W hP hC hA hSI hS hcanon hJoinH hHonJ
          IH (by rw [hw]; rfl) hstrict
          (m₂ :: ms₂) {m₁} (stateD C.ver m₁)
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)
          (by rw [Sal.ConditionedMRDTs.unionEvents_singleton hm₁, hsd₁]
              exact hcanon m₁ sm₁ Em₁ hm₁)
        have hMset : ({m₁} ∪ (m₂ :: ms₂).toFinset : Finset Version)
            = mcaFinset C.parents S w := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
            List.mem_cons]
        rw [hMset, hcov] at hfold
        exact hfold

/-- **The head-pair corollary**: at any configuration carrying `StoreInv` + the
H-invariant + the datatype's `≈`-Join and its ambient join context, the recursive
antichain merge of a head pair is `H`-canonical for the pair's event-set
intersection — exactly what the merge step demanded of a registered LCA. -/
theorem virtualLCAState_canonicalH {C : Configuration (QSig E W hP hC hA)}
    (hSI : StoreInv C.ver C.parents)
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHonJ : HonJ (Sal.ConditionedMRDTs.Configuration.core C).vis
      (Sal.ConditionedMRDTs.Configuration.core C).events)
    (hHnil : H [])
    (h : GoodConfig3H H E W hP hC hA C)
    {v₁ v₂ : Version} {s₁ s₂ : QState D E} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalStateH H E W hP hC hA (Sal.ConditionedMRDTs.Configuration.core C)
      (ev₁ ∩ ev₂) (virtualLCAState C v₁ v₂) := by
  have hres := vlcaAuxH_canonical_at H HonJ E W hP hC hA hSI h.1 h.2 hJoinH hHonJ hHnil _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [Sal.ConditionedMRDTs.unionEvents_singleton h_ver₁] at hres
  exact hres

/-! ## §2  The virtual merge preserves the H-invariant -/

/-- **`goodConfig3H_merge` with the registered LCA slot replaced by the recursive
antichain merge**: the slot's H-canonicity for the intersection is re-supplied by
`virtualLCAState_canonicalH` (in place of `lca_events` + the registered slot's witness);
the rest is verbatim.  The extra `StoreInv` hypothesis is what widened reachability
carries (`storeInv_stepV`/`storeInv_reachableV`). -/
theorem goodConfig3H_mergeVirtual
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    {C C' : Configuration (QSig E W hP hC hA)}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version}
    {s₁ s₂ : QState D E} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some ((QSig E W hP hC hA).mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂)
      else C.ver w)
    (hHnil : H [])
    (hHonJ : HonJ (Sal.ConditionedMRDTs.Configuration.core C).vis
      (Sal.ConditionedMRDTs.Configuration.core C).events)
    (h : GoodConfig3H H E W hP hC hA C) :
    GoodConfig3H H E W hP hC hA C' := by
  have hcTH : IsCanonicalStateH H E W hP hC hA (C.core) (ev₁ ∩ ev₂)
      (virtualLCAState C v₁ v₂) :=
    virtualLCAState_canonicalH H HonJ E W hP hC hA hSI hJoinH hHonJ hHnil h
      h_ver₁ h_ver₂
  have hcl₁f : fullClosureRel (C.core).vis ev₁ :=
    fun a b hab hb => h.1.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb
  have hcl₂f : fullClosureRel (C.core).vis ev₂ :=
    fun a b hab hb => h.1.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb
  have hsub₁ : ∀ a ∈ ev₁, a ∈ (C.core).events := h.1.ver_events_sub v₁ s₁ ev₁ h_ver₁
  have hsub₂ : ∀ a ∈ ev₂, a ∈ (C.core).events := h.1.ver_events_sub v₂ s₂ ev₂ h_ver₂
  have hdts : ∀ a b : Op D.AppOp,
      a ∈ (C.core).events → b ∈ (C.core).events → a ≠ b → a.1 ≠ b.1 := by
    intro a b ha hb hne
    obtain ⟨r, s, hLr, hsa⟩ := ha
    obtain ⟨r', s', hLr', hsb⟩ := hb
    exact (C.core).timestamps_distinct hLr hsa hLr' hsb hne
  have h_mergedH := mergedH_of_join H HonJ E W hP hC hA hJoinH (C.core) (C.core).events
    ev₁ ev₂ (virtualLCAState C v₁ v₂) s₁ s₂ hHonJ
    (fun hab hbc => h.1.vis_trans hab hbc) (fun a ha => h.1.vis_irrefl a ha) hdts
    hsub₁ hsub₂ hcl₁f hcl₂f hcTH (h.2 v₁ s₁ ev₁ h_ver₁) (h.2 v₂ s₂ ev₂ h_ver₂)
  refine ⟨goodConfig3S_merge h_head₁ h_ver₁ h_ver₂ hL hvis hver h.1, ?_⟩
  have hver_new : C'.ver vm
      = some ((QSig E W hP hC hA).mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_sameH : ∀ (E' : Set (Op D.AppOp)) (s' : QState D E),
      IsCanonicalStateH H E W hP hC hA (C.core) E' s' →
      IsCanonicalStateH H E W hP hC hA (C'.core) E' s' :=
    fun E' s' hcs => isCanonicalStateH_congr H E W hP hC hA
      (fun a _ b _ => by rw [core_vis, core_vis, hvis]) hcs
  intro w s' E' hw
  by_cases hwn : w = vm
  · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
    rw [← hw.1, ← hw.2]
    exact h_sameH _ _ h_mergedH
  · rw [hver_old w hwn] at hw
    exact h_sameH E' s' (h.2 w s' E' hw)

/-! ## §3  The widened reachability induction and the RAW-≈ metatheorem over `Step3V` -/

open LabeledTS in
/-- **`GoodConfig3H` at every `Step3V`-reachable configuration** — `StoreInv` is carried
alongside (the virtual case reads it); every gated case is the existing per-step lemma;
the honest premises (`hHon`/`hHext`/`hBA`) are the gated theorem's, quantified over
widened reachability. -/
theorem goodConfig3H_of_reachV
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    GoodConfig3H H E W hP hC hA C := by
  have hpair : StoreInv C.ver C.parents ∧ GoodConfig3H H E W hP hC hA C := by
    induction hReach with
    | refl => exact ⟨storeInv_init trivial, goodConfig3H_init H E W hP hC hA hHnil⟩
    | tail hprev hs ih =>
      obtain ⟨ℓ, hstep⟩ := hs
      refine ⟨storeInv_stepV hstep ih.1, ?_⟩
      cases hstep with
      | base hstep' =>
        have hkeep := hstep'
        cases hstep' with
        | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
          exact goodConfig3H_createReplica H E W hP hC hA h_fresh hL hvis hver ih.2
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hN hL hvis hver hhead hparents =>
          obtain ⟨hqapp, hgw⟩ := hBA hprev hkeep h_head h_ver
          exact goodConfig3H_apply H E W hP hC hA hInvCong hgw
            h_head h_ver h_fresh_t h_vnew hL hvis hver hqapp
            (fun ρ hρp hH happ => hHext hprev hkeep h_head h_ver ρ hρp hH happ) ih.2
        | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂
            C' hN hL hvis hver hhead hparents =>
          exact goodConfig3H_merge H HonJ E W hP hC hA hJoinH h_head₁ h_ver₁ h_ver₂
            h_lca h_verT hL hvis hver (hHon hprev) ih.2
        | query h_s h_val => exact ih.2
      | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3H_mergeVirtual H HonJ E W hP hC hA hJoinH ih.1
          h_head₁ h_ver₁ h_ver₂ hL hvis hver hHnil (hHon hprev) ih.2
  exact hpair.2

open LabeledTS in
/-- **The RAW-≈ metatheorem over the widened LTS** (`RA_linearizable_up_to_eq_H` with the
criss-cross gate lifted): a `Step3V`-reachable `QSig`-configuration under the
born-applicable discipline is per-version RA-linearizable in the paper's sense — raw
datatype folds, up to `≈` — from the SAME per-datatype hypotheses (`EqJoinLemma3C_H`
already quantifies over arbitrary closed event-set pairs, so the intermediate antichain
unions are covered by the hook as-is). -/
theorem RA_linearizable_up_to_eq_H_V
    (hInvCong : ∀ {s s' : D.State}, E.eqv s s' → D.Inv s → D.Inv s')
    (hJoinH : EqJoinLemma3C_H D E W H HonJ)
    (hHon : ∀ {C₀ : Configuration (QSig E W hP hC hA)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      HonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hHnil : H [])
    (hHext : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      ∀ ρ : List (Op D.AppOp), listPermOf ρ evh → H ρ →
        D.applicable (t, r, o) (applySeq D.toCRDTSig D.init ρ) → H (ρ ++ [(t, r, o)]))
    (hBA : ∀ {C₀ C₁ : Configuration (QSig E W hP hC hA)}
      {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {sh : QState D E} {evh : Set (Op D.AppOp)},
      (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C₀ →
      Step3 (QSig E W hP hC hA) C₀ (Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable E W hA (t, r, o) sh ∧
        (∀ s', D.applicable (t, r, o) s' → W (t, r, o) s'))
    (C : Configuration (QSig E W hP hC hA))
    (hReach : (labeledTS3V (QSig E W hP hC hA)).ReachableFrom
        (initConfig (QSig E W hP hC hA) trivial) C) :
    IsRALinearizable3Eq E W hP hC hA C :=
  isRALinearizable3Eq_of_goodH H E W hP hC hA C
    (goodConfig3H_of_reachV H HonJ E W hP hC hA hInvCong hJoinH hHon hHnil hHext hBA
      C hReach)

/-! ## Axiom audit -/

#print axioms virtualLCAState_canonicalH
#print axioms goodConfig3H_mergeVirtual
#print axioms goodConfig3H_of_reachV
#print axioms RA_linearizable_up_to_eq_H_V

end Sal.ConditionedMRDTs.GoodConfig3H
