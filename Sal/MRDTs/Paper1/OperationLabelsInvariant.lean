import Sal.MRDTs.Paper1.OperationLabels
import Sal.MRDTs.Paper1.InvariantOrder

/-!
# Pointwise operation labels for the invariant-scoped criterion

The invariant, concrete states, and operation policy are retained. The result
concerns the mapped configuration; it does not assert execution transport for
arbitrary labels of the enlarged operation alphabet.
-/
namespace Sal.MRDTs.Paper1.OperationLabelsInvariant
open Foundation
open OperationLabels

variable {D : MRDTSig} {U : Type} [DecidableEq U]

@[simp] theorem commutes_issue (args : Op D.AppOp → U)
    (Inv : D.State → Prop) (a b : Op D.AppOp) :
    InvariantOrder.Commutes (datatype D U).toUpdateSig Inv (issue args a) (issue args b) ↔
      InvariantOrder.Commutes D.toUpdateSig Inv a b := Iff.rfl

theorem order_issue (args : Op D.AppOp → U) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) (C : Configuration D)
    (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    InvariantOrder.order Inv (policy P) (configuration args C).replayContext
      (issue args '' E) (issue args a) (issue args b) ↔
    InvariantOrder.order Inv P C.replayContext E a b := by
  simp only [InvariantOrder.order, Configuration.replayContext,
    visibility_issue, commutes_issue]
  have absorb : (∃ c ∈ issue args '' E, (configuration args C).vis (issue args b) c ∧
      ¬ InvariantOrder.Commutes (datatype D U).toUpdateSig Inv (issue args b) c) ↔
      ∃ c ∈ E, C.vis b c ∧ ¬ InvariantOrder.Commutes D.toUpdateSig Inv b c := by
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, hv, hn⟩
      exact ⟨c, hc, (visibility_issue args C b c).mp hv, hn⟩
    · rintro ⟨c, hc, hv, hn⟩
      exact ⟨issue args c, ⟨c, hc, rfl⟩, (visibility_issue args C b c).mpr hv, hn⟩
  constructor
  · rintro (h | ⟨ha,hb,hp,hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha,hb,hp,fun hc => hn (absorb.mpr hc)⟩
  · rintro (h | ⟨ha,hb,hp,hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha,hb,hp,fun hc => hn (absorb.mp hc)⟩

/-- All allocated versions, using literal operation-field projection and the
same invariant in the causal and absorber clauses. -/
def VersionsRA (D : MRDTSig) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp)
    (S : HistorySpec D.AppOp D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (InvariantOrder.order Inv P C.replayContext E) ∧
    respects π (specVisibility S C.replayContext) ∧
    S.admits (projectedUpdates π ++ [.query q (D.query s q)])

/-- The source witness criterion for any fixed prepared-argument alphabet. -/
def ProjectedVersionsRA (D : MRDTSig) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) {U : Type} (args : Op D.AppOp → U)
    (S : HistorySpec U D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → ∀ q, ∃ π : List (Op D.AppOp),
    listPermOf π E ∧ respects π (InvariantOrder.order Inv P C.replayContext E) ∧
    respects π (projectedSpecVisibility args S C.replayContext) ∧
    S.admits (projectedLabels args π ++ [.query q (D.query s q)])

/-- Prepared arguments, including identified actions or atomic command groups,
can be carried directly in the operation field without changing the invariant. -/
theorem projectedVersionsRA (args : Op D.AppOp → U)
    {Inv : D.State → Prop} {P : OperationPolicy D.AppOp}
    {S : HistorySpec U D.Query D.Value} {C : Configuration D}
    (h : ProjectedVersionsRA D Inv P args S C) :
    VersionsRA (datatype D U) Inv (policy P) (specification S)
      (configuration args C) := by
  intro v s E hv q
  obtain ⟨⟨s',F⟩,hF,eq⟩ := Option.map_eq_some_iff.mp hv
  cases eq
  obtain ⟨π,hπ,ho,hs,ha⟩ := h v s' F hF q
  refine ⟨π.map (issue args), permutation_issue args hπ, ?_,
    respects_specification_issue args S C hs,
    (labels_issue args S π q (D.query s' q)).mpr ha⟩
  rw [respects, List.pairwise_map]
  exact ho.imp (fun {a b} hab hnew => hab ((order_issue args Inv P C F b a).mp hnew))

/-- A full-event invariant proof is the special case carrying the original
event among the operation arguments. -/
theorem versionsRA {Inv : D.State → Prop} {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (h : InvariantOrder.VersionsRA D Inv P S C) :
    VersionsRA (datatype D (Op D.AppOp)) Inv (policy P) (specification S)
      (configuration id C) :=
  projectedVersionsRA id h

#print axioms projectedVersionsRA
#print axioms versionsRA

end Sal.MRDTs.Paper1.OperationLabelsInvariant
