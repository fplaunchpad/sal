import Sal.MRDTs.Paper1.CertifiedRGACoreVC

namespace Sal.MRDTs.Paper1.CertifiedRGACoreAlgebra
open Foundation Classical Sal.EmbedRGA Instances.SidedPeritext Instances.SidedEmbedRGA
open CertifiedRGACoreVC
noncomputable section
abbrev FiniteState := Finset SRec × Finset Nat × Finset MarkEvent

def normalize {Γ : OrderedPrefixCode} (s : (Core Γ).State) : FiniteState :=
  ((show SState from s.1).toFinset,s.2)
def unite (s t : FiniteState) : FiniteState := (s.1 ∪ t.1,s.2.1 ∪ t.2.1,s.2.2 ∪ t.2.2)

theorem normalize_merge (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (L A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (hl : representation Γ C L l) (ha : representation Γ C A a) (hb : representation Γ C B b)
    (left : L ⊆ A) (right : L ⊆ B) :
    normalize ((Core Γ).merge l a b) = unite (normalize a) (normalize b) := by
  apply Prod.ext
  · exact text_merge_union Γ C L A B l a b hl ha hb left right
  · rfl

theorem eq_of_normalize (Γ : OrderedPrefixCode) (s t : (Core Γ).State)
    (hs : SSorted s.1) (ht : SSorted t.1) (eq : normalize s = normalize t) : s=t := by
  apply Prod.ext
  · exact CertifiedRGAVCAlgebra.Sided.eq_of_toFinset hs ht (congrArg Prod.fst eq)
  · exact congrArg (fun z : FiniteState => z.2) eq

theorem normalized_mono (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H K : Set (Op (Core Γ).AppOp)) (s t : (Core Γ).State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) (subset : H ⊆ K) :
    (normalize s).1 ⊆ (normalize t).1 ∧ (normalize s).2.1 ⊆ (normalize t).2.1 ∧
      (normalize s).2.2 ⊆ (normalize t).2.2 := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact List.mem_toFinset.mpr (text_mono Γ C H K s t hs ht subset p (List.mem_toFinset.mp hp))
  · intro p hp
    obtain ⟨e,he,rfl⟩ := (delete_store_membership Γ C H s hs p).mp hp
    exact (delete_store_membership Γ C K t ht e.2.2).mpr ⟨e,subset he,rfl⟩
  · intro p hp
    obtain ⟨e,he,rfl⟩ := (mark_store_membership Γ C H s hs p).mp hp
    exact (mark_store_membership Γ C K t ht e.2.2).mpr ⟨e,subset he,rfl⟩

def step (Γ : OrderedPrefixCode) (s : FiniteState) (e : Op (Core Γ).AppOp) : FiniteState :=
  match e.2.2 with
  | .inl op => (CertifiedRGAVCAlgebra.Sided.recordStep Γ (e.1,e.2.1,op) s.1,s.2)
  | .inr (.inl p) => (s.1,insert p s.2.1,s.2.2)
  | .inr (.inr p) => (s.1,s.2.1,insert p s.2.2)

theorem normalize_update (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s)
    (e : Op (Core Γ).AppOp) (eligible : e ∈ C.events) (absent : e ∉ H) :
    normalize ((Core Γ).update s e) = step Γ (normalize s) e := by
  rcases e with ⟨t,r,op|op⟩
  · apply Prod.ext
    · exact CertifiedRGAVCAlgebra.Sided.update_toFinset Γ (projReplayContext₁ C) _ _
        (represented_text Γ C H s rep) (t,r,op)
        (mem_projReplayContext₁_events.mpr eligible) absent
    · rfl
  · cases op <;> rfl

theorem step_union (Γ : OrderedPrefixCode) (s b : FiniteState) (e : Op (Core Γ).AppOp)
    (sub : b.1 ⊆ s.1 ∧ b.2.1 ⊆ s.2.1 ∧ b.2.2 ⊆ s.2.2)
    (native : ∀target, e.2.2 ≠ Sum.inl (SOp.del target)) :
    unite s (step Γ b e) = step Γ s e := by
  rcases e with ⟨t,r,op|op⟩
  · cases op with
    | del target => exact False.elim (native target rfl)
    | ins el pref anchor side =>
      apply Prod.ext
      · apply Finset.ext; intro p
        have h : p ∈ b.1 → p ∈ s.1 := fun h => sub.1 h
        simp only [unite,step,CertifiedRGAVCAlgebra.Sided.recordStep,Finset.mem_union,Finset.mem_insert]
        tauto
      · apply Prod.ext
        · exact Finset.union_eq_left.mpr sub.2.1
        · exact Finset.union_eq_left.mpr sub.2.2
  · cases op with
    | inl p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext
      · apply Finset.ext; intro x
        have h : x ∈ b.2.1 → x ∈ s.2.1 := fun h => sub.2.1 h
        simp only [unite,step,Finset.mem_union,Finset.mem_insert]
        tauto
      · exact Finset.union_eq_left.mpr sub.2.2
    | inr p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext (Finset.union_eq_left.mpr sub.2.1)
      apply Finset.ext; intro x
      have h : x ∈ b.2.2 → x ∈ s.2.2 := fun h => sub.2.2 h
      simp only [unite,step,Finset.mem_union,Finset.mem_insert]
      tauto

#print axioms normalize_merge
#print axioms normalize_update
end
end Sal.MRDTs.Paper1.CertifiedRGACoreAlgebra
