import Sal.MRDTs.Paper1.FugueMaxProjectedVisibility
import Sal.MRDTs.Paper1.FugueMaxOriginEventWitness
import Sal.MRDTs.Paper1.FugueMaxNaturalReplay
import Sal.MRDTs.Paper1.OriginPlanOrder
import Sal.MRDTs.Paper1.CertifiedFugueVCReplay

namespace Sal.MRDTs.Paper1.FugueMaxNaturalHistory
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxNaturalSequence
open FugueMaxSourceRepresentation
open FugueMaxOriginForest
open FugueMaxOriginEventWitness
open FugueMaxOriginTreeWitness
open FugueMaxProjectedVisibility

def target (e : Op Payload) : Nat := match e.op.op with
  | .del id => id
  | .ins _ _ => 0

theorem deletion_mask (deletions : List (Op Payload))
    (deleted : ∀ e ∈ deletions, mIsIns (recordOf e) = false) :
    deletedTargets (deletions.map recordOf) = (deletions.map target).toFinset := by
  induction deletions with
  | nil => rfl
  | cons e rest ih =>
    have tail := ih (fun d hd => deleted d (by simp [hd]))
    have this := deleted e (by simp)
    cases operation : (recordOf e).op with
    | ins p side => simp [mIsIns,operation] at this
    | del id =>
      have targetEq : target e = id := by
        unfold target
        change e.op.op = .del id at operation
        rw [operation]
      simp [deletedTargets,operation,targetEq,tail]

theorem projected_insert_labels (insertions : List (Op Payload))
    (inserted : ∀ e ∈ insertions, mIsIns (recordOf e) = true)
    (pairs : List (Nat × Nat))
    (pairMap : insertions.map (fun e => (e.time,(recordOf e).lo)) = pairs) :
    projectedLabels (D := datatype Γ) (fun e => ofMessage (recordOf e)) insertions = labels pairs := by
  rw [← pairMap]
  simp only [projectedLabels,labels,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e member
  obtain ⟨parent,side,operation⟩ := mIsIns_shape (inserted e member)
  simp only [ofMessage,operation]
  rfl

theorem projected_delete_labels (deletions : List (Op Payload))
    (deleted : ∀ e ∈ deletions, mIsIns (recordOf e) = false) :
    projectedLabels (D := datatype Γ) (fun e => ofMessage (recordOf e)) deletions =
      FugueMaxNaturalReplay.deleteLabels (deletions.map target) := by
  simp only [projectedLabels,FugueMaxNaturalReplay.deleteLabels,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e member
  have this := deleted e member
  cases operation : (recordOf e).op with
  | ins parent side => simp [mIsIns,operation] at this
  | del id =>
    have targetEq : target e = id := by
      unfold target
      change e.op.op = .del id at operation
      rw [operation]
    simp [ofMessage,operation,targetEq]

theorem insertion_order {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (events insertions : List (Op Payload)) (inv : KInv Γ (events.map recordOf))
    (sub : ∀ e ∈ insertions, e ∈ events)
    (inserted : ∀ e ∈ insertions, mIsIns (recordOf e) = true)
    (pairs : List (Nat × Nat))
    (pairMap : insertions.map (fun e => (e.time,(recordOf e).lo)) = pairs)
    (ordered : pairs.Pairwise (fun a b => a.2 ≠ b.1 ∧
      (a.2 = b.2 → mBefore Γ (events.map recordOf) b.1 a.1))) :
    insertions.Pairwise ParentsFirst ∧ insertions.Pairwise (SiblingsReverse Γ) := by
  rw [← pairMap,List.pairwise_map] at ordered
  constructor
  · exact ordered.imp (fun h _ _ => h.1)
  · apply ordered.imp_of_mem
    intro a b ha hb h _ _ same
    have before := h.2 same
    unfold mBefore mKey at before
    change Sal.EmbedRGA.keyLt
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ (mChainOf (events.map recordOf) (recordOf a).ts)))
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ (mChainOf (events.map recordOf) (recordOf b).ts))) = true at before
    rw [mChainOf_of_mem inv (List.mem_map.mpr ⟨a,sub a ha,rfl⟩) (inserted a ha),
      mChainOf_of_mem inv (List.mem_map.mpr ⟨b,sub b hb,rfl⟩) (inserted b hb)] at before
    exact before

theorem pairwise_from_membership {α : Type} (L : List α) {R : α → α → Prop}
    (proof : ∀ a ∈ L, ∀ b ∈ L, R a b) : L.Pairwise R := by
  have trivial : L.Pairwise (fun _ _ => True) := List.pairwise_of_forall (fun _ _ => True.intro)
  apply trivial.imp_of_mem
  intro a b ha hb _
  exact proof a ha b hb

theorem natural_witness {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e)
    (ops : List (Op Payload)) (E : Set (Op Payload))
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E)) :
    ∃ π : List (Op Payload), listPermOf π E ∧ π.Pairwise BirthsFirst ∧
      respects π (projectedSpecVisibility (fun e => ofMessage (recordOf e)) spec C.replayContext) ∧
      spec.admits (projectedLabels (D := datatype Γ) (fun e => ofMessage (recordOf e)) π ++
        [.query () (mView Γ (ops.map recordOf))]) := by
  let K := ops.map recordOf
  let D := ops.filter (fun e => !mIsIns (recordOf e))
  have sourceSupport : ∀ e ∈ ops, e ∈ C.events := fun e he => supported e ((enumerates.2 e).mp he)
  have sourceClosed : ∀ a b, C.vis a b → b ∈ ops → a ∈ ops :=
    fun a b ab hb => (enumerates.2 a).mpr (closed a b ab ((enumerates.2 b).mp hb))
  obtain ⟨inv,slc,_⟩ := invariants_of_mint C mint trans irrefl ops enumerates.1 sourceSupport sourceClosed
  obtain ⟨source,⟨ids,root⟩,unique,view,allBorn,sorted,mask⟩ :=
    honest_source_ordered_representation C mint trans enumerates supported ordered inv
  rw [root] at unique allBorn sorted
  have idsSorted := (List.pairwise_cons.mp sorted).2
  obtain ⟨pairs,plan,pairShape⟩ := source_forest_exists inv slc ids unique allBorn idsSorted
  have idsEnumeration : ∀ id, id ∈ ids ↔ id ∈ mMintedIds K := by
    intro id
    have nonzero : id ∈ ids → id ≠ 0 := fun member same =>
      (List.nodup_cons.mp unique).1 (same ▸ member)
    constructor
    · intro member
      exact ((allBorn id).mp (by simp [member])).resolve_left (nonzero member)
    · intro member
      have positive : id ≠ 0 := by
        obtain ⟨g,hg,same⟩ := List.mem_map.mp member
        have pos := inv.pos g (List.mem_filter.mp hg).1
        omega
      exact (List.mem_cons.mp ((allBorn id).mpr (Or.inr member))).resolve_left positive
  have idsPerm := source_ids_permutation ops inv enumerates.1 ids
    (List.nodup_cons.mp unique).2 idsEnumeration
  obtain ⟨I,insertPerm,pairMap⟩ := source_insertion_permutation ops inv pairs
    ((ids_perm plan).trans idsPerm) pairShape
  have insertSub : ∀ e ∈ I, e ∈ ops := fun e he => (List.mem_filter.mp (insertPerm.mem_iff.mp he)).1
  have inserted : ∀ e ∈ I, mIsIns (recordOf e) = true :=
    fun e he => (List.mem_filter.mp (insertPerm.mem_iff.mp he)).2
  have deleted : ∀ e ∈ D, mIsIns (recordOf e) = false := by
    intro e he
    simpa using (List.mem_filter.mp he).2
  have fullPerm : (I ++ D).Perm ops :=
    (insertPerm.append_right D).trans (List.filter_append_perm (fun e => mIsIns (recordOf e)) ops)
  have fullEnumeration : listPermOf (I ++ D) E :=
    ⟨fullPerm.symm.nodup enumerates.1,fun e => fullPerm.mem_iff.trans (enumerates.2 e)⟩
  have fullSupport : ∀ e ∈ I ++ D, e ∈ C.events := fun e he => sourceSupport e (fullPerm.mem_iff.mp he)
  have fullClosed : ∀ a b, C.vis a b → b ∈ I ++ D → a ∈ I ++ D :=
    fun a b ab hb => fullPerm.mem_iff.mpr (sourceClosed a b ab (fullPerm.mem_iff.mp hb))
  obtain ⟨fullInv,_,_⟩ := invariants_of_mint C mint trans irrefl (I ++ D)
    fullEnumeration.1 fullSupport fullClosed
  obtain ⟨parentsI,siblingsI⟩ := insertion_order ops I inv insertSub inserted pairs pairMap
    (OriginPlanOrder.replay_order plan unique (mBefore Γ K) idsSorted)
  have parents : (I ++ D).Pairwise ParentsFirst := by
    apply List.pairwise_append.mpr
    refine ⟨parentsI,?_,?_⟩
    · apply pairwise_from_membership D
      intro a ha b hb _ ins
      exact False.elim (Bool.noConfusion ((deleted b hb).symm.trans ins))
    · intro a ha b hb _ ins
      exact False.elim (Bool.noConfusion ((deleted b hb).symm.trans ins))
  have siblings : (I ++ D).Pairwise (SiblingsReverse Γ) := by
    apply List.pairwise_append.mpr
    refine ⟨siblingsI,?_,?_⟩
    · apply pairwise_from_membership D
      intro a ha b hb _ ins
      exact False.elim (Bool.noConfusion ((deleted b hb).symm.trans ins))
    · intro a ha b hb _ ins
      exact False.elim (Bool.noConfusion ((deleted b hb).symm.trans ins))
  have births : (I ++ D).Pairwise BirthsFirst := by
    apply List.pairwise_append.mpr
    refine ⟨?_,?_,?_⟩
    · apply pairwise_from_membership I
      intro a ha b hb no
      exact False.elim (Bool.noConfusion ((inserted a ha).symm.trans no))
    · apply pairwise_from_membership D
      intro a ha b hb _
      exact deleted b hb
    · intro a ha b hb _
      exact deleted b hb
  have targetMask : deletedTargets (K.filter (fun g => !mIsIns g)) = (D.map target).toFinset := by
    have records : K.filter (fun g => !mIsIns g) = D.map recordOf := by
      simp [K,D,List.filter_map,Function.comp_def]
    rw [records,deletion_mask D deleted]
  have born : ∀ id ∈ D.map target, id ∈ 0 :: ids := by
    intro id member
    have inMask : id ∈ deletedTargets (K.filter (fun g => !mIsIns g)) := by
      rw [targetMask]
      exact List.mem_toFinset.mpr member
    exact (allBorn id).mpr (honest_deletedTargets C mint trans enumerates supported closed inMask)
  have answer : mView Γ K = ids.filter (fun id => decide (id ∉ D.map target)) := by
    change sIds (summarize Γ (ops.map recordOf)).live = _
    rw [← view]
    unfold FugueMaxClientCandidate.visible FugueMaxClientCandidate.visiblePart
    rw [root,mask,targetMask]
    simp only [List.filter_cons,ne_eq,not_true_eq_false,false_and,decide_false,Bool.false_eq_true,if_false]
    apply List.filter_congr
    intro id member
    have nonzero : id ≠ 0 := fun same => (List.nodup_cons.mp unique).1 (same ▸ member)
    simp [nonzero]
  refine ⟨I ++ D,fullEnumeration,births,
    respects_projected_visibility C mint trans irrefl (I ++ D) fullSupport fullInv parents siblings births,?_⟩
  have admitted := FugueMaxNaturalReplay.plan_admits plan unique (D.map target) born
  rw [← answer,← projected_insert_labels (Γ := Γ) I inserted pairs pairMap,
    ← projected_delete_labels (Γ := Γ) D deleted] at admitted
  simpa only [projectedLabels,List.map_append,List.append_assoc] using admitted

#print axioms natural_witness
end Sal.MRDTs.Paper1.FugueMaxNaturalHistory
