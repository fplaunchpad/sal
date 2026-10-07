import Sal.MRDTs.Paper1.CertifiedRGASidedVCAlgebra
import Sal.MRDTs.Paper1.InvariantOrder

namespace Sal.MRDTs.Paper1.CertifiedSidedInvariant
open Foundation Sal.EmbedRGA Instances.SidedEmbedRGA

def Valid (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (s : SState) : Prop :=
  SSorted s ∧ ∀ p ∈ s, ∃ o ∈ C.events, sIsIns o = true ∧ p = sRecOf Γ o

theorem empty_valid (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig) :
    Valid Γ C [] := by
  constructor <;> simp [SSorted]

theorem represented_valid (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op SOp)) (s : SState)
    (h : CertifiedRGAVCReplay.Sided.representation Γ C H s) : Valid Γ C s := by
  refine ⟨CertifiedRGAVCAlgebra.Sided.sorted Γ C H s h, ?_⟩
  intro p hp
  obtain ⟨o,ho,ins,eq⟩ := CertifiedRGAVCAlgebra.Sided.provenance Γ C H s h p hp
  exact ⟨o,h.2.2.2.1 ho,ins,eq⟩

theorem compatible (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    {s t : SState} (hs : Valid Γ C s) (ht : Valid Γ C t) :
    ∀ x ∈ s, ∀ y ∈ t, x.1 = y.1 → x = y := by
  intro x hx y hy ids
  obtain ⟨a,ha,_,rx⟩ := hs.2 x hx
  obtain ⟨b,hb,_,ry⟩ := ht.2 y hy
  have stamps : a.1 = b.1 := by simpa only [rx,ry,sRecOf] using ids
  simpa only [rx,ry,C.ts_unique ha hb stamps]

theorem keys_compatible (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) {s t : SState} (hs : Valid Γ C s) (ht : Valid Γ C t) :
    ∀ x ∈ s, ∀ y ∈ t, sKey x.2.2 = sKey y.2.2 → x = y := by
  intro x hx y hy keys
  obtain ⟨a,ha,ia,rx⟩ := hs.2 x hx
  obtain ⟨b,hb,ib,ry⟩ := ht.2 y hy
  have ids : a.1 = b.1 := by
    by_contra ne
    exact s_keys_inj_events honest a ha b hb ia ib ne
      (by simpa only [rx,ry,sRecOf] using keys)
  simpa only [rx,ry,C.ts_unique ha hb ids]

theorem update_valid (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) {s : SState} (hs : Valid Γ C s)
    (o : Op SOp) (ho : o ∈ C.events) : Valid Γ C (sUpdate Γ s o) := by
  rcases o with ⟨ts,r,op⟩
  cases op with
  | del target =>
    refine ⟨List.Pairwise.filter _ hs.1,?_⟩
    intro p hp
    exact hs.2 p (List.mem_filter.mp hp).1
  | ins el pref anchor side =>
    by_cases present : ts ∈ sIds s
    · simpa only [sUpdate,if_pos present] using hs
    have fresh : ∀ p ∈ s, sKey p.2.2 ≠ sKey (pref ++ sBlock Γ (side,ts-anchor)) := by
      intro p hp eq
      obtain ⟨a,ha,ia,rec⟩ := hs.2 p hp
      have ne : a.1 ≠ ts := by
        intro equal
        exact present (List.mem_map.mpr ⟨p,hp,by simpa only [rec,sRecOf] using equal⟩)
      exact s_keys_inj_events honest a ha (ts,r,.ins el pref anchor side) ho ia rfl ne
        (by simpa only [rec,sRecOf] using eq)
    simp only [sUpdate,if_neg present]
    refine ⟨sInsert_sorted hs.1 fresh,?_⟩
    intro p hp
    rcases mem_sInsert.mp hp with old | eq
    · exact hs.2 p old
    · exact ⟨(ts,r,.ins el pref anchor side),ho,rfl,eq⟩

theorem merge_valid (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) {l a b : SState}
    (ha : Valid Γ C a) (hb : Valid Γ C b) : Valid Γ C (sMerge l a b) := by
  refine ⟨sMerge_sorted ha.1 hb.1 (keys_compatible Γ C honest ha hb),?_⟩
  intro p hp
  simp only [sMerge,mem_sMerge2,List.mem_filter] at hp
  rcases hp with ⟨hp,_⟩ | ⟨hp,_⟩
  · exact ha.2 p hp
  · exact hb.2 p hp

/-- On coherent states the implementation's present-id shortcut is exactly
ordinary immutable-record insertion, including repeated applications. -/
theorem update_membership (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    {s : SState} (hs : Valid Γ C s) (o : Op SOp) (ho : o ∈ C.events)
    (p : SRec) : p ∈ sUpdate Γ s o ↔
      match o.2.2 with
      | .ins _ _ _ _ => p ∈ s ∨ p = sRecOf Γ o
      | .del target => p ∈ s ∧ p.1 ≠ target := by
  rcases o with ⟨ts,r,op⟩
  cases op with
  | del target => simp [sUpdate]
  | ins el pref anchor side =>
    by_cases present : ts ∈ sIds s
    · obtain ⟨q,hq,id⟩ := List.mem_map.mp present
      obtain ⟨a,ha,_,rec⟩ := hs.2 q hq
      have same := C.ts_unique ha ho (by simpa only [rec,sRecOf] using id)
      have born : sRecOf Γ (ts,r,SOp.ins el pref anchor side) ∈ s := by
        simpa only [rec,same] using hq
      simp only [sUpdate,if_pos (show ts ∈ sIds s from List.mem_map.mpr ⟨q,hq,id⟩)]
      constructor
      · exact Or.inl
      · rintro (hp | rfl)
        · exact hp
        · exact born
    · simp only [sUpdate,if_neg present,mem_sInsert,sRecOf,sCoord]


/-- This quantifies over every valid carrier, without readiness, freshness,
visibility, or reissuability premises. -/
theorem semantic_commutes (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (a b : Op SOp)
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (semantic : Instances.ProductionRGA.sidedSemanticCommutes a b) :
    ∀ s, Valid Γ C s →
      sUpdate Γ (sUpdate Γ s a) b = sUpdate Γ (sUpdate Γ s b) a := by
  intro s hs
  have hsa := update_valid Γ C honest hs a ha
  have hsb := update_valid Γ C honest hs b hb
  apply ssorted_ext (update_valid Γ C honest hsa b hb).1
    (update_valid Γ C honest hsb a ha).1
  intro p
  rw [update_membership Γ C hsa b hb p,update_membership Γ C hsb a ha p]
  rcases a with ⟨ats,ar,ao⟩
  rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;>
    simp only [Instances.ProductionRGA.sidedSemanticCommutes] at semantic
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
      · exact ⟨Or.inr eq,by simpa only [eq,sRecOf] using semantic⟩
  · constructor
    · rintro (⟨hp,np⟩ | eq)
      · exact ⟨Or.inl hp,np⟩
      · exact ⟨Or.inr eq,by simpa only [eq,sRecOf] using semantic⟩
    · rintro ⟨hp,np⟩
      rcases hp with hp | eq
      · exact Or.inl ⟨hp,np⟩
      · exact Or.inr eq
  · tauto

/-- The domain is nonempty, and a birth and its own removal remain genuinely
noncommuting: the empty valid state witnesses the distinction. -/
theorem birth_delete_noncommutes (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig)
    (ts r : Nat) (el : Nat) (pref : List Nat) (anchor dts dr : Nat) (side : Side) :
    ¬ (∀ s, Valid Γ C s →
      sUpdate Γ (sUpdate Γ s (ts,r,.ins el pref anchor side)) (dts,dr,.del ts) =
      sUpdate Γ (sUpdate Γ s (dts,dr,.del ts)) (ts,r,.ins el pref anchor side)) := by
  intro comm
  have eq := comm [] (empty_valid Γ C)
  simp [sUpdate,sIds,sInsert] at eq

theorem commutes_iff_semantic (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (a b : Op SOp) (ha : a ∈ C.events) (hb : b ∈ C.events) :
    (∀ s, Valid Γ C s → sUpdate Γ (sUpdate Γ s a) b =
      sUpdate Γ (sUpdate Γ s b) a) ↔ Instances.ProductionRGA.sidedSemanticCommutes a b := by
  constructor
  · intro comm
    rcases a with ⟨ats,ar,ao⟩
    rcases b with ⟨bts,br,bo⟩
    cases ao <;> cases bo <;> simp only [Instances.ProductionRGA.sidedSemanticCommutes]
    · intro eq
      subst eq
      exact birth_delete_noncommutes Γ C _ _ _ _ _ _ _ _ comm
    · intro eq
      subst eq
      exact birth_delete_noncommutes Γ C _ _ _ _ _ _ _ _ (fun s hs => (comm s hs).symm)
  · exact semantic_commutes Γ C honest a b ha hb

theorem closed (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) : InvariantOrder.Closed (S Γ) C (Valid Γ C) := by
  refine ⟨empty_valid Γ C, ?_, ?_⟩
  · intro s hs e he
    exact update_valid Γ C honest hs e he
  · intro l a b _ ha hb
    exact merge_valid Γ C honest ha hb

theorem invariant_commutes_iff (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (a b : Op SOp) (ha : a ∈ C.events) (hb : b ∈ C.events) :
    InvariantOrder.Commutes (S Γ).toUpdateSig (Valid Γ C) a b ↔
      Instances.ProductionRGA.sidedSemanticCommutes a b := by
  simpa only [InvariantOrder.Commutes,S_core_update] using
    commutes_iff_semantic Γ C honest a b ha hb

#print axioms closed
#print axioms invariant_commutes_iff
#print axioms update_valid
#print axioms merge_valid
#print axioms semantic_commutes
#print axioms birth_delete_noncommutes
#print axioms commutes_iff_semantic

end Sal.MRDTs.Paper1.CertifiedSidedInvariant
