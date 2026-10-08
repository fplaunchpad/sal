import CertifiedFugueExpansion

namespace NeemExpansion.CertifiedFugue
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

theorem chain_of_mint {Γ : OrderedPrefixCode} (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C)
    (_trans : Transitive C.vis) (e : Op Payload) (eligible : e ∈ C.events) :
    ChainFacts (recordOf e) := by
  have main : ∀ t, ∀ e : Op Payload, e.1 = t → e ∈ C.events → ChainFacts (recordOf e) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro e time eligible
      obtain ⟨π,perm,_,guard⟩ := mint e eligible
      obtain ⟨K, Kset, issued⟩ := guard
      change K.toFinset = (π.foldl (rawUpdate Γ) ⟨[],∅⟩).births at Kset
      change canIssue Γ ⟨(π.foldl (rawUpdate Γ) ⟨[],∅⟩).live,K⟩ (recordOf e) = true at issued
      have facts : ∀ g ∈ K, ChainFacts g := by
        intro g hg
        have mem : g ∈ (π.foldl (rawUpdate Γ) ⟨[],∅⟩).births := by
          rw [← Kset]; exact List.mem_toFinset.mpr hg
        obtain ⟨q,hq,record,ins⟩ := (births Γ π g).mp mem
        have prior := (perm.2 q).mp hq
        rw [← record]
        exact ih q.1 (by rw [← time]; exact C.causal_mono prior.2) q rfl prior.1
      have liveAnchor : ∀ a ∈ sIds (π.foldl (rawUpdate Γ) ⟨[],∅⟩).live,
          a ∈ mMintedIds K := by
        intro a ha
        obtain ⟨p,hp,id⟩ := List.mem_map.mp ha
        obtain ⟨q,hq,born⟩ := provenance Γ π p hp
        have recordMem : recordOf q ∈ K := by
          apply List.mem_toFinset.mp
          rw [Kset]
          exact (births Γ π _).mpr ⟨q,hq,rfl,born.1⟩
        apply List.mem_map.mpr
        refine ⟨recordOf q,List.mem_filter.mpr ⟨recordMem,born.1⟩,?_⟩
        simpa only [Born] using (congrArg Prod.fst born.2).symm.trans id
      by_cases ins : mIsIns (recordOf e) = true
      · obtain ⟨positive,newer,i,shape⟩ := (canIssue_insert_iff Γ _ _ ins).mp issued
        rw [shape]
        apply generated_chain Γ K facts _ _ _ positive newer
        by_cases iz : i = 0
        · simp [iz]
        · simp only [if_neg iz]
          by_cases bound : i - 1 < (sIds (π.foldl (rawUpdate Γ) ⟨[],∅⟩).live).length
          · right
            apply liveAnchor
            rw [List.getD_eq_getElem _ _ bound]
            exact List.getElem_mem bound
          · left
            exact List.getD_eq_default _ _ (Nat.le_of_not_lt bound)
      · have no : mIsIns (recordOf e) = false := by cases h : mIsIns (recordOf e) <;> simp_all
        obtain ⟨positive,_,_⟩ := (canIssue_delete_iff Γ _ _ no).mp issued
        exact ⟨positive,fun h => False.elim (ins h)⟩
  exact main e.1 e rfl eligible

theorem delete_birth_of_mint {Γ : OrderedPrefixCode} (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C)
    (_trans : Transitive C.vis) (e : Op Payload) (eligible : e ∈ C.events)
    (x : ℕ) (shape : e.2.2.op = .del x) :
    x = 0 ∨ ∃ a ∈ C.events, C.vis a e ∧ mIsIns (recordOf a) = true ∧ a.1 = x := by
  by_cases zero : x = 0
  · exact Or.inl zero
  right
  obtain ⟨π,perm,_,guard⟩ := mint e eligible
  obtain ⟨K,_,issued⟩ := guard
  have no : mIsIns (recordOf e) = false := by simp [mIsIns,recordOf,shape]
  obtain ⟨_,i,eq⟩ := (canIssue_delete_iff Γ _ _ no).mp issued
  have target : x = (sIds (π.foldl (rawUpdate Γ) ⟨[],∅⟩).live).getD i 0 := by
    have h := congrArg MRec.op eq
    change e.2.2.op = .del _ at h
    rw [shape] at h
    exact MOp.del.inj h
  have member : x ∈ sIds (π.foldl (rawUpdate Γ) ⟨[],∅⟩).live := by
    by_cases bound : i < (sIds (π.foldl (rawUpdate Γ) ⟨[],∅⟩).live).length
    · rw [List.getD_eq_getElem _ _ bound] at target
      rw [target]; exact List.getElem_mem bound
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt bound)] at target
      exact False.elim (zero target)
  obtain ⟨p,hp,id⟩ := List.mem_map.mp member
  obtain ⟨a,ha,birth⟩ := provenance Γ π p hp
  have prior := (perm.2 a).mp ha
  exact ⟨a,prior.1,prior.2,birth.1,(congrArg Prod.fst birth.2).symm.trans id⟩

#print axioms chain_of_mint
#print axioms delete_birth_of_mint
end NeemExpansion.CertifiedFugue
