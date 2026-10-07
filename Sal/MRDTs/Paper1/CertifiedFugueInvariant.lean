import Sal.MRDTs.Paper1.CertifiedFugueVCExecution
import Sal.MRDTs.Paper1.InvariantOrder

namespace Sal.MRDTs.Paper1.CertifiedFugueInvariant
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

def Valid (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig) (s : State) : Prop :=
  SSorted s.live ∧
    (∀ p ∈ s.live, ∃ e ∈ C.events, mIsIns (recordOf e) = true ∧ p = written Γ e) ∧
    (∀ g ∈ s.births, ∃ e ∈ C.events, recordOf e = g ∧ mIsIns g = true)

theorem empty_valid (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig) :
    Valid Γ C (datatype Γ).init := by
  constructor
  · simp [datatype,SSorted]
  · constructor <;> simp [datatype]

theorem represented_valid (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : CertifiedFugueVCReplay.representation Γ C H s) :
    Valid Γ C s := by
  refine ⟨CertifiedFugueVCAlgebra.sorted Γ C H s rep,?_,?_⟩
  · intro p hp
    obtain ⟨⟨e,he,ins,eq⟩,_⟩ := (CertifiedFugueVCAlgebra.membership Γ C H s rep p).mp hp
    exact ⟨e,rep.2.2.2.1 he,ins,eq⟩
  · intro g hg
    obtain ⟨e,he,eq,ins⟩ := (CertifiedFugueVCAlgebra.births_membership Γ C H s rep g).mp hg
    exact ⟨e,rep.2.2.2.1 he,eq,ins⟩

theorem keys_compatible (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {s t : State} (hs : Valid Γ C.replayContext s) (ht : Valid Γ C.replayContext t) :
    ∀ x ∈ s.live, ∀ y ∈ t.live, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨a,ha,ia,rx⟩ := hs.2.1 x hx
  obtain ⟨b,hb,ib,ry⟩ := ht.2.1 y hy
  have same := same_written_of_key C mint trans ha hb ia ib (by simpa only [rx,ry] using keys)
  simpa only [rx,ry,same]

theorem update_valid (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {s : State} (hs : Valid Γ C.replayContext s) (e : Op Payload) (he : e ∈ C.events) :
    Valid Γ C.replayContext (rawUpdate Γ s e) := by
  rcases e with ⟨ts,r,⟨op,lo,ro,chain⟩⟩
  cases op with
  | del target =>
    refine ⟨List.Pairwise.filter _ hs.1,?_,?_⟩
    · intro p hp
      exact hs.2.1 p (List.mem_filter.mp hp).1
    · exact hs.2.2
  | ins parent side =>
    have birth : mIsIns (recordOf (ts,r,⟨.ins parent side,lo,ro,chain⟩)) = true := rfl
    by_cases present : ts ∈ sIds s.live
    · refine ⟨?_,?_,?_⟩
      · simpa only [rawUpdate,mStep,recordOf,if_pos present] using hs.1
      · simpa only [rawUpdate,mStep,recordOf,if_pos present] using hs.2.1
      · intro g hg
        rcases Finset.mem_insert.mp hg with eq | hg
        · exact ⟨(ts,r,⟨.ins parent side,lo,ro,chain⟩),he,eq.symm,eq ▸ birth⟩
        · exact hs.2.2 g hg
    have fresh : ∀ p ∈ s.live, sKey p.2.2 ≠ sKey (fmCoordOf Γ chain) := by
      intro p hp keyeq
      obtain ⟨a,ha,ia,rec⟩ := hs.2.1 p hp
      have same := same_written_of_key C mint trans ha he ia birth
        (by simpa only [rec,written] using keyeq)
      apply present
      exact List.mem_map.mpr ⟨p,hp,by simp only [rec,written,same]⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [rawUpdate,mStep,recordOf,if_neg present] using
        (sInsert_sorted (r := (ts,ts,fmCoordOf Γ chain)) hs.1 fresh)
    · intro p hp
      simp only [rawUpdate,mStep,recordOf,if_neg present] at hp
      rcases mem_sInsert.mp (show p ∈ sInsert (ts,ts,fmCoordOf Γ chain) s.live from hp) with old | eq
      · exact hs.2.1 p old
      · exact ⟨(ts,r,⟨.ins parent side,lo,ro,chain⟩),he,birth,eq⟩
    · intro g hg
      rcases Finset.mem_insert.mp hg with eq | hg
      · exact ⟨(ts,r,⟨.ins parent side,lo,ro,chain⟩),he,eq.symm,eq ▸ birth⟩
      · exact hs.2.2 g hg

theorem merge_valid (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {l a b : State} (ha : Valid Γ C.replayContext a) (hb : Valid Γ C.replayContext b) :
    Valid Γ C.replayContext (rawMerge l a b) := by
  refine ⟨sMerge_sorted ha.1 hb.1 (keys_compatible Γ C mint trans ha hb),?_,?_⟩
  · intro p hp
    simp only [rawMerge,sMerge,mem_sMerge2,List.mem_filter] at hp
    rcases hp with ⟨hp,_⟩ | ⟨hp,_⟩
    · exact ha.2.1 p hp
    · exact hb.2.1 p hp
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact ha.2.2 g hg
    · exact hb.2.2 g hg

theorem closed (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis) :
    InvariantOrder.Closed (datatype Γ) C.replayContext (Valid Γ C.replayContext) :=
  ⟨empty_valid Γ C.replayContext,fun _ hs e he => update_valid Γ C mint trans hs e he,
    fun _ _ _ _ ha hb => merge_valid Γ C mint trans ha hb⟩
theorem update_membership (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    {s : State} (hs : Valid Γ C.replayContext s) (e : Op Payload) (he : e ∈ C.events)
    (p : SRec) : p ∈ (rawUpdate Γ s e).live ↔
      match e.2.2.op with
      | .ins _ _ => p ∈ s.live ∨ p = written Γ e
      | .del target => p ∈ s.live ∧ p.1 ≠ target := by
  rcases e with ⟨ts,r,⟨op,lo,ro,chain⟩⟩
  cases op with
  | del target => simp [rawUpdate,mStep,recordOf]
  | ins parent side =>
    by_cases present : ts ∈ sIds s.live
    · obtain ⟨q,hq,id⟩ := List.mem_map.mp present
      obtain ⟨a,ha,_,rec⟩ := hs.2.1 q hq
      have same := C.replayContext.ts_unique ha he (by simpa only [rec,written] using id)
      have born : written Γ (ts,r,⟨.ins parent side,lo,ro,chain⟩) ∈ s.live := by
        simpa only [rec,same] using hq
      simp only [rawUpdate,mStep,recordOf,if_pos
        (show ts ∈ sIds s.live from List.mem_map.mpr ⟨q,hq,id⟩)]
      constructor
      · exact Or.inl
      · rintro (hp | rfl)
        · exact hp
        · exact born
    · simp only [rawUpdate,mStep,recordOf,if_neg present,mem_sInsert,written]

def SemanticCommutes (a b : Op Payload) : Prop :=
  match a.2.2.op,b.2.2.op with
  | .ins _ _, .ins _ _ => True
  | .ins _ _, .del target => a.1 ≠ target
  | .del target, .ins _ _ => b.1 ≠ target
  | .del _, .del _ => True

private theorem state_ext {s t : State} (live : s.live = t.live) (births : s.births = t.births) : s=t := by
  cases s; cases t; cases live; cases births; rfl

theorem semantic_commutes (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis) (a b : Op (Payload))
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (semantic : SemanticCommutes a b) :
    ∀ s, Valid Γ C.replayContext s →
      rawUpdate Γ (rawUpdate Γ s a) b = rawUpdate Γ (rawUpdate Γ s b) a := by
  intro s hs
  have hsa := update_valid Γ C mint trans hs a ha
  have hsb := update_valid Γ C mint trans hs b hb
  apply state_ext
  · apply ssorted_ext (update_valid Γ C mint trans hsa b hb).1
      (update_valid Γ C mint trans hsb a ha).1
    intro p
    rw [update_membership Γ C hsa b hb p,update_membership Γ C hsb a ha p]
    rcases a with ⟨ats,ar,⟨ao,al,aro,ac⟩⟩
    rcases b with ⟨bt,br,⟨bo,bl,bro,bc⟩⟩
    cases ao <;> cases bo <;>
      simp only [SemanticCommutes] at semantic
    all_goals
      simp only [update_membership Γ C hs _ ha p,update_membership Γ C hs _ hb p]
    · tauto
    · constructor
      · rintro ⟨hp,np⟩
        rcases hp with hp | eq
        · exact Or.inl ⟨hp,np⟩
        · exact Or.inr eq
      · rintro (⟨hp,np⟩ | eq)
        · exact ⟨Or.inl hp,np⟩
        · exact ⟨Or.inr eq,by simpa only [eq,written] using semantic⟩
    · constructor
      · rintro (⟨hp,np⟩ | eq)
        · exact ⟨Or.inl hp,np⟩
        · exact ⟨Or.inr eq,by simpa only [eq,written] using semantic⟩
      · rintro ⟨hp,np⟩
        rcases hp with hp | eq
        · exact Or.inl ⟨hp,np⟩
        · exact Or.inr eq
    · tauto

  · rcases a with ⟨ats,ar,⟨ao,al,aro,ac⟩⟩
    rcases b with ⟨bts,br,⟨bo,bl,bro,bc⟩⟩
    cases ao <;> cases bo <;> simp [rawUpdate,recordOf,mIsIns,Finset.insert_comm]

theorem birth_delete_noncommutes (Γ : OrderedPrefixCode)
    (C : ReplayContext (datatype Γ).toUpdateSig)
    (ts r parent : Nat) (side : Side) (lo : Nat) (ro : Option Nat) (chain : FMChain)
    (dts dr dlo : Nat) (dro : Option Nat) (dc : FMChain) :
    ¬ InvariantOrder.Commutes (datatype Γ).toUpdateSig (Valid Γ C)
      (ts,r,⟨.ins parent side,lo,ro,chain⟩) (dts,dr,⟨.del ts,dlo,dro,dc⟩) := by
  intro commute
  have eq := congrArg State.live (commute (datatype Γ).init (empty_valid Γ C))
  simp [datatype,rawUpdate,mStep,recordOf,sIds,sInsert] at eq

theorem invariant_commutes_iff (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (a b : Op Payload) (ha : a ∈ C.events) (hb : b ∈ C.events) :
    InvariantOrder.Commutes (datatype Γ).toUpdateSig (Valid Γ C.replayContext) a b ↔ SemanticCommutes a b := by
  constructor
  · intro commute
    rcases a with ⟨ats,ar,⟨ao,al,aro,ac⟩⟩
    rcases b with ⟨bts,br,⟨bo,bl,bro,bc⟩⟩
    cases ao <;> cases bo <;> simp only [SemanticCommutes]
    · intro eq
      subst eq
      exact birth_delete_noncommutes Γ C.replayContext _ _ _ _ _ _ _ _ _ _ _ _ commute
    · intro eq
      subst eq
      exact birth_delete_noncommutes Γ C.replayContext _ _ _ _ _ _ _ _ _ _ _ _
        (InvariantOrder.commutes_symm commute)
  · exact semantic_commutes Γ C mint trans a b ha hb

theorem stored_valid (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v : Version} {s : State} {H : Set (Op Payload)} (hv : C.ver v = some (s,H)) :
    Valid Γ C.replayContext s :=
  represented_valid Γ C.replayContext H s (CertifiedFugueVCExecution.representedVersions Γ execution hv)

theorem closed_of_execution (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C) :
    InvariantOrder.Closed (datatype Γ) C.replayContext (Valid Γ C.replayContext) := by
  have good := CertifiedFugueVCExecution.canonicalConfig Γ execution
  exact closed Γ C execution.mintHonest (fun _ _ _ h k => good.vis_trans h k)

/-- The original recursive merge-base algorithm remains in this domain. -/
theorem virtual_base_valid (Γ : OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (FugueMax.generation Γ) C)
    {v₁ v₂ : Version} {s₁ s₂ : State} {H₁ H₂ : Set (Op Payload)}
    (left : C.ver v₁ = some (s₁,H₁)) (right : C.ver v₂ = some (s₂,H₂)) :
    Valid Γ C.replayContext (virtualMergeBaseState C v₁ v₂) := by
  have store : StoreInv C.ver C.parents := by
    cases execution with
    | ordinary reach => exact storeInv_reachable reach.toReachable
    | virtual reach => exact storeInv_reachableV reach.toReachable
  have good := CertifiedFugueVCExecution.canonicalConfig Γ execution
  have base := CertifiedClosedExecution.virtualMergeBaseState_canonical store good
    (CertifiedFugueVCExecution.closedJoinAt Γ C execution.mintHonest) left right
  have rep := CertifiedFugueVCExecution.represented_of_canonical Γ C execution.mintHonest
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl (H₁ ∩ H₂)
    (virtualMergeBaseState C v₁ v₂)
    (fun e he => good.version_events_supported v₁ s₁ H₁ left e he.1) base
  exact represented_valid Γ C.replayContext _ _ rep

#print axioms closed
#print axioms invariant_commutes_iff
#print axioms stored_valid
end Sal.MRDTs.Paper1.CertifiedFugueInvariant
