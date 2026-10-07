import Sal.MRDTs.Paper1.MetadataMaximal

/-! Reconstruction obligations are independent of merge Join. Metadata pasts
are causally closed under their dependency relation; exact OR-set replay can
choose and reattach a common maximum using only replay laws. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

/-- Reattachment is semantic replay reasoning. It does not imply that the
result's hidden metadata represents the history. -/
theorem canonical_snoc {A : Model D} {P : OperationPolicy D.AppOp}
    (laws : Laws A P) {C : ReplayContext D.toUpdateSig}
    {U : Set (Op D.AppOp)} {s : D.State} {e : Op D.AppOp}
    (member : e ∈ U) (maximal : ∀ x ∈ U, x ≠ e → ¬ order A P C U e x)
    (canonical : Canonical A P C (U \ {e}) s) :
    Canonical A P C U (D.update s e) := by
  letI : ReplayPolicy (algebra A) := P.lift
  apply isCanonicalState_snoc member _ canonical
  intro x hx ne edge
  apply maximal x hx ne
  exact (order_eq A P C U e x).mpr
    ((paperOrder_iff_loOn laws.toRestricted (context A C) U e x).mpr edge)

theorem enumeration_subset {β : Type} {π : List β} {U E : Set β}
    (perm : listPermOf π U) (subset : E ⊆ U) : ∃ xs, listPermOf xs E := by
  classical
  refine ⟨π.filter (fun x => decide (x ∈ E)),perm.1.filter _,fun x => ?_⟩
  rw [List.mem_filter]
  constructor
  · exact fun h => of_decide_eq_true h.2
  · exact fun h => ⟨(perm.2 x).mpr (subset h),decide_eq_true h⟩

namespace MetadataDependencies
theorem past_closed {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (e : Op D.AppOp) : M.Closed (M.Past e) := by
  rintro a b edge (rfl | path)
  · exact Or.inr (.single edge)
  · exact Or.inr (Relation.TransGen.trans (.single edge) path)

theorem past_vis {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (trans : Transitive C.vis)
    {x e : Op D.AppOp} (mem : x ∈ M.Past e) (ne : x ≠ e) : C.vis x e := by
  rcases mem with equal | path
  · exact False.elim (ne equal)
  · have causalPath : ∀ {a b}, Relation.TransGen M.before a b → C.vis a b := by
      intro a b h
      induction h with
      | single edge => exact M.causal _ _ edge
      | tail _ edge ih => exact trans ih (M.causal _ _ edge)
    exact causalPath path

theorem past_semantic_maximal {A : Model D} {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies A C) (P : OperationPolicy D.AppOp)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) (e : Op D.AppOp) :
    ∀ x ∈ M.Past e, x ≠ e → ¬ order A P C (M.Past e) e x := by
  intro x mem ne edge
  have vis := M.past_vis trans mem ne
  rcases edge with causal | concurrent
  · exact irrefl e (trans causal.1 vis)
  · exact concurrent.2.1 vis

end MetadataDependencies
end Sal.MRDTs.Paper1.AbstractMRDT

namespace Sal.MRDTs.Paper1.ORSet.AbstractSpec
open Foundation
variable {α : Type} [DecidableEq α]

private theorem raw_maximal (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (e : Op (Update α))
    (maximal : ∀ x ∈ E, x ≠ e →
      ¬ AbstractMRDT.order (model (α := α)) (conflict α) C E e x) :
    ∀ x ∈ E, x ≠ e → ¬ @loOn (D α).toUpdateSig (conflict α).lift C E e x := by
  intro x hx ne edge
  apply maximal x hx ne
  have paper := (paperOrder_iff_loOn restrictedLaws C E e x).mpr edge
  have commutation : ∀ a b, AbstractMRDT.Commutes (model (α := α)) a b ↔
      (D α).toUpdateSig.commutes a b := fun a b =>
    (AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).trans
      (QuerySpec.commutes_iff_concrete a b)
  simpa only [AbstractMRDT.order,paperOrder,commutation] using paper

/-- Produces the complete represented peel data without invoking merge or
representation Join. -/
theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (s : (D α).State)
    (rep : representation C U s) (nonempty : U.Nonempty)
    (supported : AbstractMRDT.Supported C U)
    (closed : (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (AbstractMRDT.DependencyPeelChoice (model (α := α)) (conflict α)
      representation C (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) U) := by
  classical
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  let M := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  obtain ⟨e,he,semantic,metadata⟩ := joint_maximal C U s rep nonempty
  obtain ⟨π,hp,_,_⟩ := rep
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed he
  obtain ⟨pre,hpre⟩ := AbstractMRDT.enumeration_subset hp
    (show U \ {e} ⊆ U from fun _ h => h.1)
  obtain ⟨past,hpast⟩ := AbstractMRDT.enumeration_subset hp
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨a,ha⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpre (fun x h => supported x h.1)
  obtain ⟨b,hb⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpast (fun x h => supported x (pastSub h.1))
  refine ⟨⟨e,he,semantic,metadata,a,b,⟨representsCanonical C _ a ha,ha⟩,
    ⟨representsCanonical C _ b hb,hb⟩,?_,?_⟩⟩
  · exact isCanonicalState_snoc (Or.inl rfl)
      (raw_maximal C _ e (M.past_semantic_maximal (conflict α) trans irrefl e)) hb
  · exact isCanonicalState_snoc he (raw_maximal C U e semantic) ha

end Sal.MRDTs.Paper1.ORSet.AbstractSpec
