import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Paper1.ConcreteJoin

/-! A checked residual for the tempting local-VC shortcut. Removing an
absorber can restore an ordering edge; union maximality cannot justify
replacing a nested causal reconstruction by a last update on each side. -/
namespace Sal.MRDTs.Paper1.NeemResidual
open Foundation ConcreteMRDT

/-- The two scope-dependent verdicts are proved against the actual paperOrder.
The represented-history bridge must preserve this change of verdict. -/
theorem absorber_scope_change {D : UpdateSig} (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) (E U : Set (Op D.AppOp)) (e p c : Op D.AppOp)
    (ep : ¬ C.vis e p) (pe : ¬ C.vis p e) (policy : P.before e.op p.op)
    (member : c ∈ U) (edge : C.vis p c) (nc : ¬ D.commutes p c)
    (absent : ¬ ∃ z ∈ E, C.vis p z ∧ ¬ D.commutes p z) :
    paperOrder P C E e p ∧ ¬ paperOrder P C U e p := by
  refine ⟨Or.inr ⟨ep, pe, policy, absent⟩, ?_⟩
  rintro (⟨vis, _⟩ | ⟨_, _, _, noAbsorber⟩)
  · exact ep vis
  · exact noAbsorber ⟨c, member, edge, nc⟩

open ORSet

/-- Hand-derived PASS+FAIL pin: a concurrent Remove contributes no delta to
an empty past, hence a causal merge preserves the Add; a last update removes
it. This is a shortcut counterexample, not a counterexample to Sal's VC. -/
theorem local_shortcut_state_counterexample :
    let e : Op (Update Nat) := (2, 1, .remove 7)
    let t : State Nat := {(7, 1)}
    merge ∅ t (step ∅ e) = t ∧
    step t e = ∅ ∧
    merge ∅ t (step ∅ e) ≠ step t e := by
  decide

def p : Op (Update Nat) := (1, 0, .add 7)
def e : Op (Update Nat) := (2, 1, .remove 7)
def c : Op (Update Nat) := (3, 0, .remove 7)
def whole : Set (Op (Update Nat)) := {p, e, c}
def left : Set (Op (Update Nat)) := {p, e}

def context : ReplayContext (D Nat).toUpdateSig where
  L := fun _ => some whole
  vis a b := a = p ∧ b = c
  timestamps_distinct := by
    intro a b r s r' s' hs ha ht hb ne
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [p, e, c]
  vis_total_same_replica := by
    intro a b r s r' s' hs ha ht hb ne same
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [p, e, c]

def policy : OperationPolicy (Update Nat) where
  before a b := ∃ x, a = .remove x ∧ b = .add x

theorem concrete_order_changes :
    paperOrder policy context left e p ∧
    ¬ paperOrder policy context whole e p := by
  apply absorber_scope_change policy context left whole e p c
  · simp [context, e, p, c]
  · simp [context, e, p, c]
  · exact ⟨7, rfl, rfl⟩
  · simp [whole]
  · exact ⟨rfl, rfl⟩
  · rw [ORSet.noncomm_iff_rc]
    simp [UpdateSig.rc, ReplayPolicy.Before, ORSet.policy, ORSet.order, p, c]
  · rintro ⟨z, hz, vis, _⟩
    have equal : z = c := vis.2
    subst z
    simp [left, p, e, c] at hz

theorem concrete_union_maximal :
    ∀ z ∈ whole, z ≠ e → ¬ paperOrder policy context whole e z := by
  intro z hz ne
  rcases hz with rfl | rfl | rfl
  · exact concrete_order_changes.2
  · exact False.elim (ne rfl)
  · simp [paperOrder, policy, context, e, p, c, Op.op]

/-- Both observed sides are metadata closed although the left loses the
absorber. This rules out explaining the failed shortcut as malformed scope. -/
theorem concrete_closed_sides :
    (MetadataDependencies.ofConcrete context).Closed left ∧
    (MetadataDependencies.ofConcrete context).Closed ({p, c} : Set _) := by
  constructor
  · intro a b edge hb
    have eq : b = c := edge.1.2
    subst b
    simp [left, p, e, c] at hb
  · intro a b edge _
    have eq : a = p := edge.1.1
    subst a
    simp

def right : Set (Op (Update Nat)) := {p, c}

theorem concrete_context :
    ConcreteMRDT.Raw.Context policy (fun C => MetadataDependencies.ofConcrete C)
      context left right e := by
  have union : left ∪ right = whole := by
    ext z
    simp only [left, right, whole, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  constructor
  · intro a b z hab hbz
    have impossible : c = p := hab.2.symm.trans hbz.1
    simp [p, c] at impossible
  · intro a ha
    have impossible : p = c := ha.1.symm.trans ha.2
    simp [p, c] at impossible
  · intro a ha
    exact ⟨0, whole, rfl, by rw [← union]; exact Or.inl ha⟩
  · intro a ha
    exact ⟨0, whole, rfl, by rw [← union]; exact Or.inr ha⟩
  · exact concrete_closed_sides.1
  · exact concrete_closed_sides.2
  · rw [union]
    exact concrete_union_maximal
  · intro z _ _ h
    have impossible : e = p := h.1.1
    simp [e, p] at impossible

theorem left_canonical :
    Canonical policy context left ({(7, 1)} : State Nat) := by
  refine ⟨[e, p], ?_, ?_, ?_⟩
  · simp [listPermOf, left, e, p, or_comm]
  · simp [respects, paperOrder, policy, context, e, p, c, Op.op]
  · decide

theorem right_canonical :
    Canonical policy context right (∅ : State Nat) := by
  refine ⟨[p, c], ?_, ?_, ?_⟩
  · simp [listPermOf, right, p, c]
  · simp [respects, paperOrder, policy, context, p, c, Op.op]
  · decide

/-- The actual redistribution equation succeeds in the same scenario where
replacing its nested side reconstruction by a last update fails. -/
theorem local_redistribution_still_holds :
    let l : State Nat := {(7, 1)}
    let B : State Nat := ∅
    let t : State Nat := {(7, 1)}
    let b : State Nat := ∅
    merge l (merge B t (step B e)) b = ∅ ∧
    merge B (merge l t b) (step B e) = ∅ ∧
    merge l (merge B t (step B e)) b =
      merge B (merge l t b) (step B e) ∧
    merge B t (step B e) ≠ step t e := by
  decide

end Sal.MRDTs.Paper1.NeemResidual
