import Sal.MRDTs.Paper1.ConcreteFormalism

/-! Metadata dependencies are causal event relations used for reconstruction.
They cover concrete causal conflicts and may additionally
retain commuting predecessors whose tags affect reconstruction. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

structure MetadataDependencies (C : ReplayContext D.toUpdateSig) where
  before : Op D.AppOp → Op D.AppOp → Prop
  causal : ∀ a b, before a b → C.vis a b
  covers : ∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → before a b

namespace MetadataDependencies

def ofConcrete (C : ReplayContext D.toUpdateSig) : MetadataDependencies C where
  before a b := C.vis a b ∧ ¬ D.toUpdateSig.commutes a b
  causal _ _ h := h.1
  covers _ _ vis nc := ⟨vis,nc⟩

def Closed {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (E : Set (Op D.AppOp)) : Prop :=
  ∀ a b, M.before a b → b ∈ E → a ∈ E

def Past {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (e : Op D.AppOp) : Set (Op D.AppOp) :=
  {x | x = e ∨ Relation.TransGen M.before x e}

theorem past_subset {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (E : Set (Op D.AppOp)) (e : Op D.AppOp)
    (closed : M.Closed E) (mem : e ∈ E) : M.Past e ⊆ E := by
  rintro x (rfl | h)
  · exact mem
  · induction h using Relation.TransGen.head_induction_on with
    | single edge => exact closed _ _ edge mem
    | head edge _ ih => exact closed _ _ edge ih

/-- Removing an event maximal for metadata dependencies preserves the closure
needed by the smaller induction problem. Semantic maximality alone does not. -/
theorem closed_diff_of_max {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (U E : Set (Op D.AppOp)) (e : Op D.AppOp)
    (subset : E ⊆ U) (closed : M.Closed E)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ M.before e x) : M.Closed (E \ {e}) := by
  intro a b edge hb
  refine ⟨closed a b edge hb.1,?_⟩
  intro equal
  change a = e at equal
  subst a
  exact maximal b (subset hb.1) hb.2 edge

end MetadataDependencies
end Sal.MRDTs.Paper1.ConcreteMRDT

namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

theorem enumeration_subset {β : Type} {π : List β} {U E : Set β}
    (perm : listPermOf π U) (subset : E ⊆ U) : ∃ xs, listPermOf xs E := by
  classical
  refine ⟨π.filter (fun x => decide (x ∈ E)),perm.1.filter _,fun x => ?_⟩
  rw [List.mem_filter]
  constructor
  · exact fun h => of_decide_eq_true h.2
  · exact fun h => ⟨(perm.2 x).mpr (subset h),decide_eq_true h⟩

private theorem exists_last {β : Type} (xs : List β) (nonempty : xs ≠ []) :
    ∃ pre e, xs = pre ++ [e] := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton xs e _ => exact ⟨xs,e,rfl⟩

theorem joint_maximal_of_enumeration {β : Type} {R M : β → β → Prop}
    {E : Set β} (π : List β) (perm : listPermOf π E) (nonempty : E.Nonempty)
    (semantic : respects π R) (metadata : respects π M) :
    ∃ e ∈ E, (∀ x ∈ E, x ≠ e → ¬ R e x) ∧ (∀ x ∈ E, x ≠ e → ¬ M e x) := by
  have hn : π ≠ [] := by
    intro h
    obtain ⟨e,he⟩ := nonempty
    have mem := (perm.2 e).mpr he
    simp [h] at mem
  obtain ⟨pre,e,hπ⟩ := exists_last π hn
  subst π
  refine ⟨e,(perm.2 e).mp (by simp),?_,?_⟩
  · intro x hx ne
    have mem : x ∈ pre := by
      simpa [ne] using (perm.2 x).mpr hx
    exact (List.pairwise_append.mp semantic).2.2 x mem e (by simp)
  · intro x hx ne
    have mem : x ∈ pre := by
      simpa [ne] using (perm.2 x).mpr hx
    exact (List.pairwise_append.mp metadata).2.2 x mem e (by simp)

namespace MetadataDependencies
theorem past_closed {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (e : Op D.AppOp) : M.Closed (M.Past e) := by
  rintro a b edge (rfl | path)
  · exact Or.inr (.single edge)
  · exact Or.inr (Relation.TransGen.trans (.single edge) path)

theorem past_vis {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (trans : Transitive C.vis)
    {x e : Op D.AppOp} (mem : x ∈ M.Past e) (ne : x ≠ e) : C.vis x e := by
  rcases mem with equal | path
  · exact False.elim (ne equal)
  · have causalPath : ∀ {a b}, Relation.TransGen M.before a b → C.vis a b := by
      intro a b h
      induction h with
      | single edge => exact M.causal _ _ edge
      | tail _ edge ih => exact trans ih (M.causal _ _ edge)
    exact causalPath path

theorem past_semantic_maximal {C : ReplayContext D.toUpdateSig}
    (M : MetadataDependencies C) (P : OperationPolicy D.AppOp)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) (e : Op D.AppOp) :
    ∀ x ∈ M.Past e, x ≠ e → ¬ paperOrder P C (M.Past e) e x := by
  intro x mem ne edge
  have vis := M.past_vis trans mem ne
  rcases edge with causal | concurrent
  · exact irrefl e (trans causal.1 vis)
  · exact concurrent.2.1 vis

end MetadataDependencies
end Sal.MRDTs.Paper1.ConcreteMRDT
