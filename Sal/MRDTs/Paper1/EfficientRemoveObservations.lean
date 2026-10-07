import Sal.MRDTs.Paper1.EfficientAddObservations

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

theorem remove_raw_conflict (et er : Nat) (x : α) (b : Event α)
    (nc : ¬ (D α).toUpdateSig.commutes (et,er,.remove x) b) :
    ¬ AbstractMRDT.Commutes (model (α := α)) (et,er,.remove x) b := by
  rcases b with ⟨bt,br,op⟩
  cases op with
  | add y =>
    have same := EventSpec.noncomm_same_element (et,er,.remove x) (bt,br,.add y) nc
    change x = y at same
    subst y
    exact (laws.noncomm_exact _ _).mpr (Or.inl ⟨x,rfl,rfl⟩)
  | remove y =>
    apply False.elim
    apply nc
    intro s
    change update (update s (et,er,.remove x)) (bt,br,.remove y) =
      update (update s (bt,br,.remove y)) (et,er,.remove x)
    apply Finset.ext
    intro p
    simp [update,and_comm,and_left_comm,and_assoc]

theorem remove_past_subset (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (et er : Nat) (x : α) (member : (et,er,.remove x) ∈ U)
    (trans : Transitive C.vis) (closed : AbstractMRDT.ConflictClosed (model (α := α)) C U) :
    (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past (et,er,.remove x) ⊆ U := by
  let M := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  have pathVis : ∀ {a b}, Relation.TransGen M.before a b → C.vis a b := by
    intro a b h
    induction h with
    | single edge => exact edge.1
    | tail _ edge ih => exact trans ih edge.1
  have pathElement : ∀ {a b}, Relation.TransGen M.before a b → element a = element b := by
    intro a b h
    induction h with
    | single edge => exact EventSpec.noncomm_same_element _ _ edge.2
    | tail _ edge ih => exact ih.trans (EventSpec.noncomm_same_element _ _ edge.2)
  rintro a (equal | path)
  · exact equal ▸ member
  · induction path using Relation.TransGen.head_induction_on with
    | single edge =>
      exact closed _ _ edge.1
        (fun commute => remove_raw_conflict et er x _
          (fun raw => edge.2 (Foundation.commutes_symm raw))
          (fun s => (commute s).symm)) member
    | @head a b edge rest ih =>
      rcases a with ⟨ta,ar,op⟩
      cases op with
      | remove y => exact closed _ _ edge.1 (remove_raw_conflict ta ar y b edge.2) ih
      | add y =>
        have full : Relation.TransGen M.before (ta,ar,.add y) (et,er,.remove x) :=
          Relation.TransGen.trans (.single edge) rest
        have same := pathElement full
        change y = x at same
        subst y
        exact closed _ _ (pathVis full) ((laws.noncomm_exact _ _).mpr (Or.inr ⟨x,rfl,rfl⟩)) member

theorem local_remove_eq (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Event α)) (l B t s : State α) (et er : Nat) (x : α)
    (trans : Transitive C.vis) (member : (et,er,.remove x) ∈ E₁)
    (closed : AbstractMRDT.ConflictClosed (model (α := α)) C E₁)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (past : Represents C.vis
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past (et,er,.remove x) \
        {(et,er,.remove x)}) B) (other : Represents C.vis E₂ s) :
    merge l (merge B t (update B (et,er,.remove x))) s =
      merge B (merge l t s) (update B (et,er,.remove x)) := by
  apply SetMergeAlgebra.local_redistribute
  · intro p inPast lost inOther
    have elem : p.2.2 = x := by
      by_contra ne
      exact lost (by simp [update,inPast,ne])
    have hp := (past p).mp inPast
    have hs := (other p).mp inOther
    have vis := (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).past_vis
      trans hp.1.1 hp.1.2
    have birth₁ := closed _ _ vis ((laws.noncomm_exact _ _).mpr (Or.inr ⟨x,rfl,by simp [Op.op,elem]⟩)) member
    apply (base p).mpr
    refine ⟨⟨birth₁,hs.1⟩,?_⟩
    exact fun deadBase => hs.2 (dead_mono C.vis Set.inter_subset_right deadBase)
  · intro p notPast updated
    exact False.elim (notPast (Finset.mem_filter.mp updated).1)

theorem causal_remove_eq (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (A B : State α) (et er : Nat) (x : α)
    (trans : Transitive C.vis) (member : (et,er,.remove x) ∈ U)
    (supported : AbstractMRDT.Supported C U)
    (closed : AbstractMRDT.ConflictClosed (model (α := α)) C U)
    (maximal : ∀ z ∈ U, z ≠ (et,er,.remove x) →
      ¬ AbstractMRDT.order (model (α := α)) (EventSpec.conflict α) C U (et,er,.remove x) z)
    (pre : Represents C.vis (U \ {(et,er,.remove x)}) A)
    (past : Represents C.vis
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past (et,er,.remove x) \
        {(et,er,.remove x)}) B) :
    merge B A (update B (et,er,.remove x)) = update A (et,er,.remove x) := by
  let e : Event α := (et,er,.remove x)
  let M := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  have pastSub := remove_past_subset C U et er x member trans closed
  have metadata : ∀ z ∈ U, z ≠ e → ¬ M.before e z := by
    intro z hz ne edge
    exact maximal z hz ne (Or.inl ⟨edge.1,remove_raw_conflict et er x z edge.2⟩)
  apply merge_update_eq
  · intro p impossible
    cases impossible
  · intro p mem kill
    have live := (pre p).mp mem
    have vis := live_killed_before C U e member supported maximal metadata p live kill
    apply (past p).mpr
    refine ⟨⟨Or.inr (.single ⟨vis,kills_noncomm p e kill live.1.2⟩),live.1.2⟩,?_⟩
    intro killed
    have subset : M.Past e \ {e} ⊆ U \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    exact live.2 (dead_mono C.vis subset killed)

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
