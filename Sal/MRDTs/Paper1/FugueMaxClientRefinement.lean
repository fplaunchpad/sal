import Sal.MRDTs.Paper1.FugueMaxSourceRepresentation

/-! Source-local honest positional-client refinement to the origin-only
natural machine. The source buffer is derived from the complete birth set,
including tombstones. No global natural replay witness is assumed. -/
namespace Sal.MRDTs.Paper1.FugueMaxClientRefinement
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxClientCandidate
open FugueMaxNaturalSequence
open FugueMaxSourceRepresentation

theorem generated_insert_facts {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {issuer : IssuerState} {rep stamp index id : Nat} {message : MRec}
    (generated : Generates Γ issuer rep stamp (.insert index id) message) :
    mIsIns message = true ∧ message.ts = id := by
  obtain ⟨_,same,exact⟩ := generated
  rw [exact]
  unfold prepareInsert mGenInsAfter
  split <;> simp [mIsIns,same]

theorem honest_insert_client_refinement {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf))
    {rep stamp index id : Nat} {message : MRec}
    (generated : Generates Γ (summarize Γ (ops.map recordOf)) rep stamp (.insert index id) message)
    (issued : canIssue Γ (summarize Γ (ops.map recordOf)) message = true) :
    ∃ L : KnowM, (mMinted (ops.map recordOf)).Perm L ∧
      let source := sourceBuffer Γ (ops.map recordOf) L
        ((ops.map recordOf).filter (fun g => !mIsIns g))
      legal source (ofMessage message) ∧ visible (step source (ofMessage message)) =
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
  have parents := birth_parents_of_construction inv births construction
  obtain ⟨sorted,_⟩ := births_refine inv sub (births.nodup (nodup.filter _)) construction parents
  have shape : ∀ r ∈ buildNodes Γ K L,
      r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K) := by
    intro r member
    rcases (buildNodes_mem Γ K L r).mp member with rfl | ⟨g,hg,rfl⟩
    · exact ⟨rfl,Or.inl rfl⟩
    · exact ⟨rfl,Or.inr (List.mem_map.mpr ⟨g,births.mem_iff.mpr hg,rfl⟩)⟩
  obtain ⟨tail,first⟩ := sorted_root_first inv sorted shape
    ((buildNodes_mem Γ K L _).mpr (Or.inl rfl))
  have root : (sourceBuffer Γ K L D).order = 0 :: tail.map Prod.fst := by
    change (buildNodes Γ K L).map Prod.fst = _
    rw [first]
    rfl
  obtain ⟨inserted,same⟩ := generated_insert_facts generated
  obtain ⟨positive,fresh,_⟩ := (canIssue_insert_exact Γ K message inserted).mp issued
  rw [same] at positive fresh
  have undeleted : id ∉ (sourceBuffer Γ K L D).deleted := by
    intro deleted
    rcases honest_deletedTargets C mint trans enumerates supported closed deleted with zero | old
    · omega
    · have impossible := fresh id old
      omega
  have view := sourceBuffer_matches_issuer C mint trans enumerates supported ordered inv births sorted
  refine ⟨L,births,?_,?_⟩
  · rw [generates_insert_action generated]
    refine ⟨by omega,?_,?_⟩
    · intro member
      obtain ⟨r,hr,sameID⟩ := List.mem_map.mp member
      have known := sameID ▸ (shape r hr).2
      rcases known with zero | old
      · omega
      · have impossible := fresh id old
        omega
    · by_cases zero : index = 0
      · simp only [zero,if_pos rfl]
        change 0 ∈ (buildNodes Γ K L).map Prod.fst
        exact List.mem_map.mpr ⟨node Γ K 0,(buildNodes_mem Γ K L _).mpr (Or.inl rfl),rfl⟩
      · simp only [if_neg zero]
        rw [← view]
        have bound : index - 1 < (visible (sourceBuffer Γ K L D)).length := by
          rw [view]
          have lengthEq : (sIds (summarize Γ K).live).length = (summarize Γ K).live.length := by simp [sIds]
          rw [lengthEq]
          have requestBound := generated.1
          change index ≤ (summarize Γ K).live.length at requestBound
          omega
        rw [List.getD_eq_getElem _ _ bound]
        exact List.mem_of_mem_filter (List.getElem_mem bound)
  · exact generated_insert_refines_source generated view
      root (sourceBuffer_nodup sorted (fun r hr => (shape r hr).1))
      (by omega) undeleted

theorem honest_delete_client_refinement {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf))
    {rep stamp index : Nat} {message : MRec}
    (generated : Generates Γ (summarize Γ (ops.map recordOf)) rep stamp (.delete index) message) :
    ∃ source : FugueMaxClientCandidate.Buffer,
      (∀ id, id ∈ source.order ↔ id = 0 ∨ id ∈ mMintedIds (ops.map recordOf)) ∧
      visible source = sIds (summarize Γ (ops.map recordOf)).live ∧
      legal source (ofMessage message) ∧
      visible (step source (ofMessage message)) =
        clientStep (sIds (summarize Γ (ops.map recordOf)).live) (.delete index) := by
  obtain ⟨source,_,unique,view,allBorn⟩ :=
    honest_source_representation C mint trans enumerates supported ordered inv
  refine ⟨source,allBorn,view,?_,generated_delete_refines_source generated view unique⟩
  rw [generates_delete_action generated]
  change (sIds (summarize Γ (ops.map recordOf)).live).getD index 0 ∈ source.order
  rw [← view]
  have bound : index < (visible source).length := by
    rw [view]
    simpa [sIds] using generated.1
  rw [List.getD_eq_getElem _ _ bound]
  exact List.mem_of_mem_filter (List.getElem_mem bound)

#print axioms honest_insert_client_refinement
#print axioms honest_delete_client_refinement
end Sal.MRDTs.Paper1.FugueMaxClientRefinement
