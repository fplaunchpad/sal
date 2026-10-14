import Sal.MRDTs.Instances.FugueMaxContract
import Sal.MRDTs.Instances.FugueMaxOriginSplice
import Sal.MRDTs.Paper1.FugueMaxNaturalSequence

/-! Proof-side permanent-list representation of an issuer view. Structural
construction is used only to enumerate the sorted birth coordinates here;
it is not a witness schedule for the natural origin-based specification. -/
namespace Sal.MRDTs.Paper1.FugueMaxSourceRepresentation
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxClientCandidate

def deletedTargets : KnowM → Finset Nat
  | [] => ∅
  | g :: rest => match g.op with
      | .ins _ _ => deletedTargets rest
      | .del id => insert id (deletedTargets rest)

theorem mem_deletedTargets (D : KnowM) (id : Nat) :
    id ∈ deletedTargets D ↔ ∃ g ∈ D, g.op = .del id := by
  induction D with
  | nil => simp [deletedTargets]
  | cons g D ih =>
    cases operation : g.op with
    | ins p side => simp [deletedTargets,operation,ih]
    | del target => simp [deletedTargets,operation,ih]; grind

theorem honest_deletedTargets {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {id : Nat} (deleted : id ∈ deletedTargets
      ((ops.map recordOf).filter (fun g => !mIsIns g))) :
    id = 0 ∨ id ∈ mMintedIds (ops.map recordOf) := by
  obtain ⟨g,member,operation⟩ := (mem_deletedTargets _ _).mp deleted
  have recordMember := (List.mem_filter.mp member).1
  obtain ⟨e,eventMember,rfl⟩ := List.mem_map.mp recordMember
  have inE := (enumerates.2 e).mp eventMember
  rcases delete_birth_of_mint C mint trans e (supported e inE) id operation with
    zero | ⟨birth,_,visible,inserted,same⟩
  · exact Or.inl zero
  · have birthMember := (enumerates.2 birth).mpr (closed birth e visible inE)
    exact Or.inr (List.mem_map.mpr ⟨recordOf birth,
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨birth,birthMember,rfl⟩,inserted⟩,same⟩)

theorem eraseNodes_filter (s : SState) (D : KnowM) :
    (eraseNodes s D).filter (fun r => r.1 != 0) =
      s.filter (fun r => decide (r.1 ≠ 0 ∧ r.1 ∉ deletedTargets D)) := by
  induction D generalizing s with
  | nil =>
    apply List.filter_congr
    intro r hr
    apply Bool.eq_iff_iff.mpr
    simp [deletedTargets,bne_iff_ne]
  | cons g D ih =>
    cases operation : g.op with
    | ins p side => simpa [eraseNodes,deletedTargets,operation] using ih s
    | del id =>
      by_cases zero : id = 0
      · subst id
        simp only [eraseNodes,operation]
        rw [ih]
        apply List.filter_congr
        intro r hr
        simp [deletedTargets,operation]
      · simp only [eraseNodes,operation,if_neg zero]
        rw [ih,List.filter_filter]
        apply List.filter_congr
        intro r hr
        apply Bool.eq_iff_iff.mpr
        simp [deletedTargets,operation,bne_iff_ne]
        tauto

def sourceBuffer (Γ : Sal.EmbedRGA.OrderedPrefixCode) (K L D : KnowM) : Buffer :=
  ⟨(buildNodes Γ K L).map Prod.fst,deletedTargets D⟩

theorem sourceBuffer_visible (Γ : Sal.EmbedRGA.OrderedPrefixCode) (K L D : KnowM) :
    visible (sourceBuffer Γ K L D) = sIds (finalNodes Γ K L D) := by
  unfold visible sourceBuffer visiblePart finalNodes sIds
  rw [eraseNodes_filter]
  exact List.filter_map ..

theorem sourceBuffer_matches_issuer {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf)) {L : KnowM}
    (births : (mMinted (ops.map recordOf)).Perm L)
    (sorted : SSorted (buildNodes Γ (ops.map recordOf) L)) :
    visible (sourceBuffer Γ (ops.map recordOf) L
      ((ops.map recordOf).filter (fun g => !mIsIns g))) =
      sIds (summarize Γ (ops.map recordOf)).live := by
  rw [sourceBuffer_visible,finalNodes_eq_live C mint trans enumerates supported ordered inv births sorted]
  rfl

theorem sourceBuffer_nodup {Γ : Sal.EmbedRGA.OrderedPrefixCode} {K L D : KnowM}
    (sorted : SSorted (buildNodes Γ K L))
    (shape : ∀ r ∈ buildNodes Γ K L, r = node Γ K r.1) :
    (sourceBuffer Γ K L D).order.Nodup := by
  unfold sourceBuffer
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  apply sorted.imp_of_mem
  intro a b ha hb before same
  have equal : a = b := by rw [shape a ha,shape b hb,same]
  subst b
  exact Bool.noConfusion ((Sal.EmbedRGA.keyLt_irrefl _).symm.trans before)

theorem sorted_root_first {Γ : Sal.EmbedRGA.OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {s : SState} (sorted : SSorted s)
    (shape : ∀ r ∈ s, r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K))
    (root : node Γ K 0 ∈ s) : ∃ tail, s = node Γ K 0 :: tail := by
  cases s with
  | nil => simp at root
  | cons head tail =>
    have headShape := shape head (by simp)
    by_cases zero : head.1 = 0
    · exact ⟨tail,by rw [headShape.1,zero]⟩
    · have minted := headShape.2.resolve_left zero
      have afterRoot := minted_after_root inv minted
      have beforeRoot : Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey (node Γ K 0).2.2)
          (Sal.EmbedRGA.sKey head.2.2) = true := by
        have inTail : node Γ K 0 ∈ tail := by
          rcases List.mem_cons.mp root with eq | member
          · exact False.elim (zero (congrArg Prod.fst eq.symm))
          · exact member
        exact (List.pairwise_cons.mp sorted).1 _ inTail
      have coordinates := congrArg (fun r : SRec => r.2.2) headShape.1
      dsimp only at coordinates
      rw [coordinates] at beforeRoot
      change Sal.EmbedRGA.keyLt (mKey Γ K 0) (mKey Γ K head.1) = true at beforeRoot
      have contradiction := Sal.EmbedRGA.keyLt_asymm afterRoot
      rw [beforeRoot] at contradiction
      contradiction

theorem honest_source_representation {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf)) :
    ∃ s : Buffer, (∃ tail, s.order = 0 :: tail) ∧ s.order.Nodup ∧
      visible s = sIds (summarize Γ (ops.map recordOf)).live ∧
      (∀ id, id ∈ s.order ↔ id = 0 ∨ id ∈ mMintedIds (ops.map recordOf)) := by
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
  have root : node Γ K 0 ∈ buildNodes Γ K L :=
    (buildNodes_mem Γ K L _).mpr (Or.inl rfl)
  obtain ⟨tail,first⟩ := sorted_root_first inv sorted shape root
  refine ⟨sourceBuffer Γ K L D,⟨tail.map Prod.fst,?_,⟩,?_,?_,?_⟩
  · change (buildNodes Γ K L).map Prod.fst = _
    rw [first]
    rfl
  · exact sourceBuffer_nodup sorted (fun r hr => (shape r hr).1)
  · exact sourceBuffer_matches_issuer C mint trans enumerates supported ordered inv births sorted
  · intro id
    change id ∈ (buildNodes Γ K L).map Prod.fst ↔ _
    constructor
    · intro member
      obtain ⟨r,hr,same⟩ := List.mem_map.mp member
      exact same ▸ (shape r hr).2
    · intro known
      apply List.mem_map.mpr
      refine ⟨node Γ K id,?_,rfl⟩
      apply (buildNodes_mem Γ K L _).mpr
      rcases known with zero | minted
      · exact Or.inl (by rw [zero])
      · obtain ⟨g,hg,same⟩ := List.mem_map.mp minted
        exact Or.inr ⟨g,births.mem_iff.mp hg,by rw [same]⟩

#print axioms sourceBuffer_visible
#print axioms sourceBuffer_matches_issuer
#print axioms honest_source_representation
end Sal.MRDTs.Paper1.FugueMaxSourceRepresentation
