import Artifact.MRDTs.Metatheory.AdequacyResult
import Artifact.MRDTs.Metatheory.CertifiedAdequacy
import Artifact.MRDTs.Metatheory.VirtualAdequacy
import LeanProofs.Implementations.MVRegister.Definition

/-!
# The multivalue register: clause 1

Convergence, by the same route the efficient OR-set takes and for a sharper
reason. Whether two writes commute depends on their **timestamps**, not on
their payloads, so no relation over operations can order them and no replay
contract holding at every state is available.

`Represents` relates a compact state to the writes that produced it. This
file shows it survives `update`, `merge` and a virtual merge base, then that
a represented state is the canonical state of its event set, which is all
`ReplayAdequacyCertificate` needs. The issuance guard `canIssue` is what
makes the represented states the only reachable ones.
-/

namespace LeanProofs.Implementations.MVRegister

open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical
local instance : EventOrder D.toUpdateSig := replayOrder
set_option maxHeartbeats 1000000

private theorem merge_logic (bl ba bb dl da db : Prop)
    (bi : bl ↔ ba ∧ bb) (d1 : dl → da) (d2 : dl → db)
    (a1 : bb → da → ba) (a2 : ba → db → bb) :
    (bl ∧ ¬dl ∧ ba ∧ ¬da ∧ bb ∧ ¬db) ∨
      (ba ∧ ¬da ∧ ¬(bl ∧ ¬dl)) ∨ (bb ∧ ¬db ∧ ¬(bl ∧ ¬dl)) ↔
      (ba ∨ bb) ∧ ¬(da ∨ db) := by tauto

def Represents (E : Set Event) (s : State) : Prop :=
  ∀ p, p ∈ s ↔ (∃ e ∈ E, (e.1, MVR.writeValue e) = p) ∧
    ¬ ∃ e ∈ E, p.1 ∈ MVR.overwrites e

theorem represents_empty : Represents ∅ ∅ := by simp [Represents]

theorem fold_born (ops : List Event) (p : ℕ × ℕ)
    (hp : p ∈ ops.foldl update ∅) :
    ∃ e ∈ ops, (e.1, MVR.writeValue e) = p := by
  induction ops using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton ops e ih =>
    rw [List.foldl_append] at hp
    change p ∈ insert (e.1,MVR.writeValue e)
      ((ops.foldl update ∅).filter _) at hp
    rcases Finset.mem_insert.mp hp with he | ho
    · exact ⟨e,by simp,he.symm⟩
    · obtain ⟨a,ha,hp⟩ := ih (Finset.mem_filter.mp ho).1
      exact ⟨a,List.mem_append_left _ ha,hp⟩

theorem issued_overwrite {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {b : Event}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ MVR.overwrites b) :
    ∃ a ∈ C.events, C.vis a b ∧ a.1 = n := by
  obtain ⟨ops,hp,_,hg⟩ := mint b hb
  have heq := hg.2
  have hm : n ∈ (MVR.overwrites b).toFinset := List.mem_toFinset.mpr hn
  rw [heq] at hm
  obtain ⟨p,hps,ht⟩ := Finset.mem_image.mp hm
  obtain ⟨a,ha,hpair⟩ := fold_born ops p hps
  exact ⟨a,((hp.2 a).mp ha).1,((hp.2 a).mp ha).2,
    (congrArg (fun p : ℕ × ℕ => p.1) hpair).trans ht⟩

theorem issued_overwrite_lt {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {b : Event}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ MVR.overwrites b) : n < b.1 := by
  obtain ⟨a,_,hv,ht⟩ := issued_overwrite mint hb hn
  simpa [ht] using C.causal_mono hv

theorem represents_merge (C : Configuration D)
    (mint : MintHonest D issuance.CanIssue C) (A B : Set Event)
    (supA : A ⊆ C.events) (supB : B ⊆ C.events)
    (closedA : ∀ a b, C.vis a b → b ∈ A → a ∈ A)
    (closedB : ∀ a b, C.vis a b → b ∈ B → a ∈ B)
    {l a b : State} (hl : Represents (A ∩ B) l)
    (ha : Represents A a) (hb : Represents B b) :
    Represents (A ∪ B) (merge l a b) := by
  intro p
  let born := fun E : Set Event => ∃ e ∈ E, (e.1,MVR.writeValue e) = p
  let dead := fun E : Set Event => ∃ e ∈ E, p.1 ∈ MVR.overwrites e
  have bi : born (A ∩ B) ↔ born A ∧ born B := by
    constructor
    · rintro ⟨e,⟨heA,heB⟩,hp⟩; exact ⟨⟨e,heA,hp⟩,⟨e,heB,hp⟩⟩
    · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
      have heq := C.replayContext.ts_unique (supA hx) (supB hy)
        (congrArg (fun p : ℕ × ℕ => p.1) (hxp.trans hyp.symm))
      subst y
      exact ⟨x,⟨hx,hy⟩,hxp⟩
  have dl : dead (A ∩ B) → dead A := by rintro ⟨e,he,hn⟩; exact ⟨e,he.1,hn⟩
  have dr : dead (A ∩ B) → dead B := by rintro ⟨e,he,hn⟩; exact ⟨e,he.2,hn⟩
  have al : born B → dead A → born A := by
    rintro ⟨x,hx,hp⟩ ⟨e,he,hn⟩
    obtain ⟨birth,hm,hv,ht⟩ := issued_overwrite mint (supA he) hn
    have heq := C.replayContext.ts_unique hm (supB hx)
      (ht.trans (congrArg (fun p : ℕ × ℕ => p.1) hp).symm)
    exact ⟨x,closedA x e (heq ▸ hv) he,hp⟩
  have ar : born A → dead B → born B := by
    rintro ⟨x,hx,hp⟩ ⟨e,he,hn⟩
    obtain ⟨birth,hm,hv,ht⟩ := issued_overwrite mint (supB he) hn
    have heq := C.replayContext.ts_unique hm (supA hx)
      (ht.trans (congrArg (fun p : ℕ × ℕ => p.1) hp).symm)
    exact ⟨x,closedB x e (heq ▸ hv) he,hp⟩
  have bu : born (A ∪ B) ↔ born A ∨ born B := by
    simp [born, Set.mem_union, or_and_right, exists_or]
  have du : dead (A ∪ B) ↔ dead A ∨ dead B := by
    simp [dead, Set.mem_union, or_and_right, exists_or]
  change _ ↔ born (A ∪ B) ∧ ¬ dead (A ∪ B)
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
    hl p,ha p,hb p]
  simp only [and_assoc,or_assoc]
  change (born (A ∩ B) ∧ ¬dead (A ∩ B) ∧ born A ∧ ¬dead A ∧
      born B ∧ ¬dead B) ∨
    (born A ∧ ¬dead A ∧ ¬(born (A ∩ B) ∧ ¬dead (A ∩ B))) ∨
    (born B ∧ ¬dead B ∧ ¬(born (A ∩ B) ∧ ¬dead (A ∩ B))) ↔ _
  rw [bu,du]
  exact merge_logic _ _ _ _ _ _ bi dl dr al ar

theorem represents_update {E : Set Event} {s : State} (e : Event)
    (hs : Represents E s)
    (fresh : ∀ b ∈ E, e.1 ∉ MVR.overwrites b)
    (self : e.1 ∉ MVR.overwrites e) :
    Represents (E ∪ {e}) (update s e) := by
  intro p
  simp only [update, MVR.clientStep, Finset.mem_insert, Finset.mem_filter,hs p]
  by_cases hp : p = (e.1,MVR.writeValue e)
  · subst p
    simp only [Set.mem_union,Set.mem_singleton_iff,or_and_right,
      exists_or,exists_eq_left]
    simp [self]
    exact Or.inr (fun t r o h => fresh (t,r,o) h)
  · simp only [Set.mem_union, Set.mem_singleton_iff, or_and_right,
      exists_or, exists_eq_left]
    have hp' := Ne.symm hp
    simp [hp,hp',and_comm,and_left_comm]

theorem canonical_of_represents (C : Configuration D)
    (mint : MintHonest D issuance.CanIssue C) (E : Set Event)
    (sup : E ⊆ C.events) (ops : List Event) (hp : listPermOf ops E)
    {s : State} (hs : Represents E s) :
    IsCanonicalState C.replayContext E s := by
  let sorted := MVR.chronological ops
  have hperm : listPermOf sorted E :=
    ⟨(MVR.chronological_perm ops).symm.nodup hp.1,
      fun a => (MVR.chronological_perm ops).mem_iff.trans (hp.2 a)⟩
  refine ⟨sorted,hperm,?_,?_⟩
  · apply (MVR.chronological_sorted ops).imp
    intro a b hab hlo
    rcases hlo with hv | hr
    · exact (not_lt_of_ge hab) (C.causal_mono hv.1)
    · exact (not_lt_of_ge hab) ((MVR.replayOrder_before_iff b a).mp hr.2.2.1).1
  · rw [fold_live sorted (MVR.chronological_sorted ops)
      (fun e he n hn => issued_overwrite_lt mint (sup ((hperm.2 e).mp he)) hn)]
    apply Finset.ext
    intro p
    rw [mem_live,hs p]
    simp only [Born,Dead,List.mem_toFinset,hperm.2]

def RepConfig (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → Represents E s

open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical
local instance : EventOrder D.toUpdateSig := replayOrder

private def VRepAt (C : Configuration D) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : State) (Ew : Set (Event)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    Represents
      (unionEvents C S ∩ Ew) (virtualBaseAux C.ver C.parents C.parents_lt S w)

/-- Each scratch state represents its union history. The outer induction
supplies the sub-pair's intersection history for the three-way merge. -/
private theorem vfold_represents {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C) (mint : MintHonest D issuance.CanIssue C)
    {n : ℕ} (IH : ∀ k, k < n → VRepAt C k)
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
    have hjoin := represents_merge C mint (unionEvents C accS) Em
      hsup1 (fun e he => hG.version_events_supported m sm Em hm e he)
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
private theorem virtualBaseAux_represents_at {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C) (hR : RepConfig C) (mint : MintHonest D issuance.CanIssue C) :
    ∀ n, VRepAt C n := by
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
        have hfold := vfold_represents hSI hG hR mint IH (by rw [hw]; rfl) hstrict
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
theorem virtualMergeBaseState_represents {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : CanonicalConfig C)
    (hR : RepConfig C) (mint : MintHonest D issuance.CanIssue C)
    {v₁ v₂ : Version} {s₁ s₂ : State} {ev₁ ev₂ : Set (Event)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    Represents (ev₁ ∩ ev₂)
      (virtualMergeBaseState C v₁ v₂) := by
  have h := virtualBaseAux_represents_at hSI hG hR mint _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical
local instance : EventOrder D.toUpdateSig := replayOrder
set_option maxHeartbeats 1000000

theorem repConfig_init : RepConfig (initConfig D) := by
  intro v s E hv
  change (if v = 0 then some (D.init,∅) else none) = some (s,E) at hv
  split at hv
  · cases Option.some.inj hv
    exact represents_empty
  · cases hv

theorem repConfig_store {C C' : Configuration D}
    {v : Version} {s : State} {E : Set Event}
    (hver : C'.ver = fun w => if w = v then some (s,E) else C.ver w)
    (hR : RepConfig C) (hs : Represents E s) : RepConfig C' := by
  intro w sw Ew hw
  rw [hver] at hw
  dsimp only at hw
  split at hw
  · cases Option.some.inj hw
    exact hs
  · exact hR w sw Ew hw

theorem repConfig_apply {C C' : Configuration D}
    {e : Event} {v vnew : Version} {s : State} {E : Set Event}
    (hver : C.ver v = some (s,E))
    (hstore : C'.ver = fun w => if w = vnew then some (update s e,E ∪ {e}) else C.ver w)
    (hfresh : ∀ a ∈ C.events, a.1 ≠ e.1)
    (hG : CanonicalConfig C) (hG' : CanonicalConfig C')
    (mint : MintHonest D issuance.CanIssue C)
    (after : MintHonest D issuance.CanIssue C') (hR : RepConfig C) : RepConfig C' := by
  apply repConfig_store hstore hR
  apply represents_update e (hR v s E hver)
  · intro b hb hn
    obtain ⟨a,ha,_,ht⟩ := issued_overwrite mint
      (hG.version_events_supported v s E hver b hb) hn
    exact hfresh a ha ht
  · intro hn
    have hvnew : C'.ver vnew = some (update s e,E ∪ {e}) := by rw [hstore]; simp
    have he := hG'.version_events_supported vnew _ _ hvnew e (by simp)
    exact (Nat.lt_irrefl _) (issued_overwrite_lt after he hn)

theorem canonical_union {C : Configuration D}
    (hG : CanonicalConfig C) (mint : MintHonest D issuance.CanIssue C)
    {v₁ v₂ : Version} {s₁ s₂ s : State} {E₁ E₂ : Set Event}
    (hv₁ : C.ver v₁ = some (s₁,E₁)) (hv₂ : C.ver v₂ = some (s₂,E₂))
    (hs : Represents (E₁ ∪ E₂) s) :
    IsCanonicalState C.replayContext (E₁ ∪ E₂) s := by
  obtain ⟨ops₁,hp₁,_⟩ := hG.canonical v₁ s₁ E₁ hv₁
  obtain ⟨ops₂,hp₂,_⟩ := hG.canonical v₂ s₂ E₂ hv₂
  apply canonical_of_represents C mint (E₁ ∪ E₂) _ (ops₁ ++ ops₂).dedup _ hs
  · intro e he
    rcases he with he | he
    · exact hG.version_events_supported v₁ s₁ E₁ hv₁ e he
    · exact hG.version_events_supported v₂ s₂ E₂ hv₂ e he
  · exact ⟨List.nodup_dedup _,fun a => by simp [hp₁.2 a,hp₂.2 a]⟩

theorem represented_of_mintCertifiedV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  induction reach with
  | init => exact ⟨storeInv_init,canonicalConfig_init,repConfig_init⟩
  | @step C C' l _ mint step after ih =>
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
        have hm := represents_merge C mint _ _
          (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
          (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := virtualMergeBaseState_represents hSI hG hR mint hv₁ hv₂
      have hm := represents_merge C mint _ _
        (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
        (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩

noncomputable def replayAdequacy : @ReplayAdequacyCertificate D issuance replayOrder where
  soundV reach := hasReplayWitness_of_canonical (represented_of_mintCertifiedV reach).2.1

theorem represented_of_execution {C : Configuration D}
    (exec : CertifiedExecution D issuance C) : CanonicalConfig C ∧ RepConfig C := by
  cases exec with
  | ordinary h => exact (represented_of_mintCertifiedV h.toV).2
  | virtual h => exact (represented_of_mintCertifiedV h).2

end LeanProofs.Implementations.MVRegister
