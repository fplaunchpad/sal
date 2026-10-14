import Sal.MRDTs.Paper1.FugueMaxPhysicalClientRefinement

namespace Sal.MRDTs.Paper1.FugueMaxHonestPhysicalRefinement
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxClientCandidate
open FugueMaxSourceRepresentation
open FugueMaxPhysicalClientRefinement

theorem generated_origins {Γ : Sal.EmbedRGA.OrderedPrefixCode} {K : KnowM}
    {rep stamp index id : Nat} {g : MRec}
    (generated : Generates Γ (summarize Γ K) rep stamp (.insert index id) g) :
    g.lo = (if index = 0 then 0 else (mView Γ K).getD (index - 1) 0) ∧
      g.ro = succOfM Γ K g.lo := by
  rw [generated.2.2,prepareInsert_exact]
  unfold mGenInsAt mAnchorAt mGenInsAfter
  split <;> simp_all

theorem source_physical_insert_refinement {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf))
    {rep stamp index id : Nat} {g : MRec}
    (generated : Generates Γ (summarize Γ (ops.map recordOf)) rep stamp (.insert index id) g)
    (issued : canIssue Γ (summarize Γ (ops.map recordOf)) g = true)
    (augInv : KInv Γ (ops.map recordOf ++ [g]))
    (slc : ∀ b ∈ ops.map recordOf ++ [g], SLC Γ (ops.map recordOf ++ [g]) b)
    (bk : ∀ b ∈ ops.map recordOf ++ [g], RBk Γ (ops.map recordOf ++ [g]) b) :
    sIds (update Γ (summarize Γ (ops.map recordOf)) g).live =
      clientStep (sIds (summarize Γ (ops.map recordOf)).live) (.insert index id) := by
  let K := ops.map recordOf
  let D := K.filter (fun g => !mIsIns g)
  have nodup : K.Nodup := enumerates.1.map_on (by
    intro a ha b hb same
    have eq := congrArg eventOf same
    simpa using eq)
  obtain ⟨L,births,construction⟩ := exists_chain_construction (mMinted K)
  have sub : ∀ g ∈ L, g ∈ K ∧ mIsIns g = true :=
    fun g member => List.mem_filter.mp (births.mem_iff.mpr member)
  obtain ⟨sorted,_⟩ := births_refine inv sub (births.nodup (nodup.filter _)) construction
    (birth_parents_of_construction inv births construction)
  have shape : ∀ r ∈ buildNodes Γ K L,
      r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K) := by
    intro r member
    rcases (buildNodes_mem Γ K L r).mp member with rfl | ⟨g,hg,rfl⟩
    · exact ⟨rfl,Or.inl rfl⟩
    · exact ⟨rfl,Or.inr (List.mem_map.mpr ⟨g,births.mem_iff.mpr hg,rfl⟩)⟩
  have liveEq : (summarize Γ K).live = (buildNodes Γ K L).filter
      (fun r => decide (r.1 ≠ 0 ∧ r.1 ∉ deletedTargets D)) := by
    have finalEq := finalNodes_eq_live C mint trans enumerates supported ordered inv births sorted
    rw [finalNodes,eraseNodes_filter] at finalEq
    exact finalEq.symm
  obtain ⟨inserted,same⟩ := FugueMaxClientRefinement.generated_insert_facts generated
  obtain ⟨positive,freshIDs,_⟩ := (canIssue_insert_exact Γ K g inserted).mp issued
  have fresh : ∀ r ∈ buildNodes Γ K L, r.1 ≠ g.ts := by
    intro r hr equal
    rcases (shape r hr).2 with zero | minted
    · omega
    · have smaller := freshIDs r.1 minted
      omega
  have undeleted : g.ts ∉ deletedTargets D := by
    intro deleted
    rcases honest_deletedTargets C mint trans enumerates supported closed deleted with zero | minted
    · omega
    · have smaller := freshIDs g.ts minted
      omega
  obtain ⟨leftEq,rightEq⟩ := generated_origins generated
  have leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K := by
    by_cases zero : index = 0
    · exact Or.inl (by simpa [zero] using leftEq)
    · have view := sourceBuffer_matches_issuer C mint trans enumerates supported ordered inv births sorted
      have bound : index - 1 < (mView Γ K).length := by
        have requestBound := generated.1
        change index ≤ (summarize Γ K).live.length at requestBound
        dsimp only [summarize] at requestBound
        simp only [mView,sIds,List.length_map]
        omega
      rw [if_neg zero,List.getD_eq_getElem _ _ bound] at leftEq
      have visibleMember : (mView Γ K)[index - 1] ∈ visible (sourceBuffer Γ K L D) := by
        rw [view]
        exact List.getElem_mem bound
      have orderMember := List.mem_of_mem_filter visibleMember
      obtain ⟨r,hr,equal⟩ := List.mem_map.mp orderMember
      exact (equal.trans leftEq.symm) ▸ (shape r hr).2
  have anchor : node Γ K g.lo ∈ buildNodes Γ K L := by
    apply (buildNodes_mem Γ K L _).mpr
    rcases leftKnown with zero | minted
    · exact Or.inl (by rw [zero])
    · obtain ⟨record,member,equal⟩ := List.mem_map.mp minted
      exact Or.inr ⟨record,births.mem_iff.mp member,by rw [equal]⟩
  obtain ⟨tail,first⟩ := sorted_root_first inv sorted shape
    ((buildNodes_mem Γ K L _).mpr (Or.inl rfl))
  apply physical_insert_refines_positional generated inv augInv slc bk leftKnown rightEq
    sorted shape anchor fresh undeleted liveEq
  · exact ⟨tail.map Prod.fst,by rw [sIds,first]; rfl⟩
  · exact sourceBuffer_nodup (D := D) sorted (fun r hr => (shape r hr).1)

theorem honest_physical_insert_refinement {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    {rep stamp index id : Nat} {g : MRec}
    (eventPresent : eventOf g ∈ C.events)
    (sourceExact : ∀ e, e ∈ E ↔ C.vis e (eventOf g))
    (generated : Generates Γ (summarize Γ (ops.map recordOf)) rep stamp (.insert index id) g)
    (issued : canIssue Γ (summarize Γ (ops.map recordOf)) g = true) :
    sIds (update Γ (summarize Γ (ops.map recordOf)) g).live =
      clientStep (sIds (summarize Γ (ops.map recordOf)).live) (.insert index id) := by
  have closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E := by
    intro a b ab member
    exact (sourceExact a).mpr (trans ab ((sourceExact b).mp member))
  have oldClosed : ∀ a b, C.vis a b → b ∈ ops → a ∈ ops := by
    intro a b ab member
    exact (enumerates.2 a).mpr (closed a b ab ((enumerates.2 b).mp member))
  obtain ⟨inv,_,_⟩ := invariants_of_mint C mint trans irrefl ops enumerates.1
    (fun e he => supported e ((enumerates.2 e).mp he)) oldClosed
  have notPast : eventOf g ∉ ops := by
    intro member
    exact irrefl (eventOf g) ((sourceExact (eventOf g)).mp ((enumerates.2 _).mp member))
  have augmentedNodup : (ops ++ [eventOf g]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨enumerates.1,by simp,?_⟩
    intro a ha b hb equal
    have same := List.mem_singleton.mp hb
    subst b
    apply notPast
    rw [← same]
    exact ha
  have augmentedSupported : ∀ e ∈ ops ++ [eventOf g], e ∈ C.events := by
    intro e member
    rcases List.mem_append.mp member with old | new
    · exact supported e ((enumerates.2 e).mp old)
    · exact (List.mem_singleton.mp new).symm ▸ eventPresent
  have augmentedClosed : ∀ a b, C.vis a b → b ∈ ops ++ [eventOf g] → a ∈ ops ++ [eventOf g] := by
    intro a b ab member
    apply List.mem_append_left
    rcases List.mem_append.mp member with old | new
    · exact oldClosed a b ab old
    · have equal := List.mem_singleton.mp new
      subst b
      exact (enumerates.2 a).mpr ((sourceExact a).mpr ab)
  obtain ⟨augInv,slc,bk⟩ := invariants_of_mint C mint trans irrefl (ops ++ [eventOf g])
    augmentedNodup augmentedSupported augmentedClosed
  simp only [List.map_append,List.map_singleton,recordOf_eventOf] at augInv slc bk
  exact source_physical_insert_refinement C mint trans enumerates supported closed ordered inv
    generated issued augInv slc bk

theorem honest_physical_delete_refinement {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    {rep stamp index : Nat} {g : MRec}
    (generated : Generates Γ (summarize Γ (ops.map recordOf)) rep stamp (.delete index) g) :
    sIds (update Γ (summarize Γ (ops.map recordOf)) g).live =
      clientStep (sIds (summarize Γ (ops.map recordOf)).live) (.delete index) := by
  obtain ⟨inv,_,_⟩ := invariants_of_mint C mint trans irrefl ops enumerates.1
    (fun e he => supported e ((enumerates.2 e).mp he))
    (fun a b ab hb => (enumerates.2 a).mpr (closed a b ab ((enumerates.2 b).mp hb)))
  obtain ⟨source,_,unique,view,_⟩ :=
    honest_source_representation C mint trans enumerates supported ordered inv
  apply physical_delete_refines_positional generated
  · rw [← view]
    exact List.Nodup.filter _ unique
  · rw [← view]
    simp [visible,visiblePart]

#print axioms source_physical_insert_refinement
#print axioms honest_physical_insert_refinement
#print axioms honest_physical_delete_refinement
end Sal.MRDTs.Paper1.FugueMaxHonestPhysicalRefinement
