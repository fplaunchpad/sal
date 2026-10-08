import CertifiedReplayExpansion
import CertifiedExpansion
import Sal.MRDTs.Paper1.CertifiedFugueVCReplay

namespace NeemExpansion.CertifiedFugue
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay

def Born (Γ : OrderedPrefixCode) (e : Op Payload) (p : SRec) :=
  mIsIns (recordOf e) = true ∧ p = (e.1,e.1,fmCoordOf Γ e.2.2.chain)
def Kill (e : Op Payload) (p : SRec) := e.2.2.op = .del p.1

theorem update_provenance (Γ : OrderedPrefixCode) (s : State) (e : Op Payload) (p : SRec) :
    p ∈ (rawUpdate Γ s e).live → Born Γ e p ∨ p ∈ s.live := by
  rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
  cases op with
  | del x => simp only [rawUpdate,mStep,recordOf,List.mem_filter]; tauto
  | ins a sd =>
    simp only [rawUpdate,mStep,recordOf]
    split
    · exact Or.inr
    · rw [mem_sInsert]
      intro h
      exact h.elim Or.inr (fun h => Or.inl ⟨rfl,h⟩)

theorem provenance (Γ : OrderedPrefixCode) (xs : List (Op Payload)) (p : SRec) :
    p ∈ (xs.foldl (rawUpdate Γ) ⟨[],∅⟩).live → ∃e∈xs,Born Γ e p :=
  CertifiedReplay.provenance (rawUpdate Γ) ⟨[],∅⟩ (fun p s => p ∈ s.live) (Born Γ)
    (by simp) (update_provenance Γ) xs p

theorem births (Γ : OrderedPrefixCode) (xs : List (Op Payload)) (g : MRec) :
    g ∈ (xs.foldl (rawUpdate Γ) ⟨[],∅⟩).births ↔
      ∃e∈xs,recordOf e = g ∧ mIsIns g = true := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs e ih =>
    rw [List.foldl_append]
    change g ∈ (rawUpdate Γ _ e).births ↔ _
    simp only [rawUpdate]
    split
    · simp only [Finset.mem_insert,ih,List.mem_append,List.mem_singleton]
      constructor
      · rintro (rfl | ⟨q,hq,eq,ins⟩)
        · exact ⟨e,Or.inr rfl,rfl,by assumption⟩
        · exact ⟨q,Or.inl hq,eq,ins⟩
      · rintro ⟨q,hq,eq,ins⟩
        rcases hq with hq | rfl
        · exact Or.inr ⟨q,hq,eq,ins⟩
        · exact Or.inl eq.symm
    · rw [ih]
      simp only [List.mem_append,List.mem_singleton]
      constructor
      · rintro ⟨q,hq,eq,ins⟩; exact ⟨q,Or.inl hq,eq,ins⟩
      · rintro ⟨q,hq,eq,ins⟩
        rcases hq with hq | rfl
        · exact ⟨q,hq,eq,ins⟩
        · subst g; contradiction

theorem represented_births (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) (g : MRec) :
    g ∈ s.births ↔ ∃e∈H,recordOf e = g ∧ mIsIns g = true := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2
  rw [←fold]
  change g ∈ (xs.foldl (rawUpdate Γ) ⟨[],∅⟩).births ↔ _
  rw [births]
  simp only [perm.2]

/-- Exact birth-store causal inclusion follows from actual metadata closure. -/
theorem past_births_subset (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (U : Set (Op Payload)) (a B : State) (e : Op Payload)
    (closed : (scheme Γ C).Closed U) (member : e∈U)
    (ha : representation Γ C (U \ {e}) a)
    (hB : representation Γ C ((scheme Γ C).Past e \ {e}) B) : B.births ⊆ a.births := by
  intro g hg
  obtain ⟨o,ho,eq,ins⟩ := (represented_births Γ C _ B hB g).mp hg
  exact (represented_births Γ C _ a ha g).mpr
    ⟨o,⟨(scheme Γ C).past_subset U e closed member ho.1,ho.2⟩,eq,ins⟩

/-- Only the chain facts consumed by the finite record bridge. -/
def ChainFacts (g : MRec) : Prop :=
  0 < g.ts ∧ (mIsIns g = true → PosFMChain g.chain ∧ TagsOK g.chain ∧
    (g.chain.map fmδ).sum = g.ts)

theorem lookup_chain (K : KnowM) (facts : ∀g∈K, ChainFacts g)
    (x : ℕ) (hx : x=0 ∨ x∈mMintedIds K) :
    PosFMChain (mChainOf K x) ∧ TagsOK (mChainOf K x) ∧
      ((mChainOf K x).map fmδ).sum = x := by
  rcases hx with rfl | hx
  · rw [mChainOf_zero (fun g hg => Nat.succ_le_of_lt (facts g hg).1)]
    exact ⟨by simp [PosFMChain],by simp [TagsOK],rfl⟩
  · obtain ⟨g,lookup,mem,ins,time⟩ := mRecOfId_of_minted hx
    rw [mChainOf_eq_of_rec lookup,←time]
    exact (facts g mem).2 ins

theorem generated_chain (Γ : OrderedPrefixCode) (K : KnowM)
    (facts : ∀g∈K, ChainFacts g) (rep t a : ℕ) (positive : 0<t)
    (newer : ∀g∈K,g.ts<t) (anchor : a=0 ∨ a∈mMintedIds K) :
    ChainFacts (mGenInsAfter Γ K rep t a) := by
  have late : ∀x∈mMintedIds K,x<t := by
    intro x hx
    obtain ⟨g,_,mem,_,time⟩ := mRecOfId_of_minted hx
    rw [←time]; exact newer g mem
  have alt : a<t := anchor.elim (fun h => h ▸ positive) (late a)
  have wa := lookup_chain K facts a anchor
  cases hs : succOfM Γ K a with
  | none =>
    rw [mGenInsAfter_none hs]
    refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
    · intro ent he
      rcases List.mem_append.mp he with he | he
      · exact wa.1 ent he
      · simp only [List.mem_singleton] at he; subst ent
        change 1≤t-a; omega
    · intro ent he
      rcases List.mem_append.mp he with he | he
      · exact wa.2.1 ent he
      · simp only [List.mem_singleton] at he; subst ent
        exact Or.inl rfl
    · simp only [List.map_append,List.sum_append,wa.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      change a+(t-a+0)=t; omega
  | some n =>
    have hn := succOfM_mem hs
    have wn := lookup_chain K facts n (Or.inr hn)
    have nlt := late n hn
    have npos : 0<n := by
      obtain ⟨g,_,mem,_,time⟩ := mRecOfId_of_minted hn
      rw [←time]; exact (facts g mem).1
    cases hr : hasRChildM K a with
    | true =>
      rw [mGenInsAfter_someTrue hs hr]
      refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wn.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          change 1≤t-n; omega
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wn.2.1 ent he
        · simp only [List.mem_singleton] at he; subst ent; exact trivial
      · simp only [List.map_append,List.sum_append,wn.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        change n+(t-n+0)=t; omega
    | false =>
      rw [mGenInsAfter_someFalse hs hr]
      refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wa.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          change 1≤t-a; omega
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wa.2.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          apply tagOK_key Γ wn.1 wn.2.1
          intro empty
          simp [empty] at wn
          omega
      · simp only [List.map_append,List.sum_append,wa.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        change a+(t-a+0)=t; omega
end NeemExpansion.CertifiedFugue
