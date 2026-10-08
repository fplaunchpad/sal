import Sal.MRDTs.Paper1.ConcreteJoin
import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Instances.EfficientORSet

/-! Closed, individually canonical histories can have cyclic combined orders.
This defeats synchronized last-event peeling; it does not refute merge soundness. -/
set_option linter.unusedSimpArgs false
namespace Sal.MRDTs.Paper1.NeemCycleResidual
open Foundation ConcreteMRDT ORSet

def d : Op (Update Nat) := (1,1,.add 7)
def b : Op (Update Nat) := (2,0,.add 7)
def a : Op (Update Nat) := (3,1,.remove 7)
def c : Op (Update Nat) := (4,0,.remove 7)
def whole : Set (Op (Update Nat)) := {d,b,a,c}
def left : Set (Op (Update Nat)) := {d,a,b}
def right : Set (Op (Update Nat)) := {b,c,d}
def policy : OperationPolicy (Update Nat) where
  before x y := ∃ z, x = .remove z ∧ y = .add z

def context : ReplayContext (D Nat).toUpdateSig where
  L := fun _ => some whole
  vis x y := (x = d ∧ y = a) ∨ (x = b ∧ y = c)
  timestamps_distinct := by
    intro x y r s r' s' hs hx ht hy ne
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> simp_all [d,b,a,c]
  vis_total_same_replica := by
    intro x y r s r' s' hs hx ht hy ne same
    simp only [Option.some.injEq] at hs ht
    subst s; subst s'
    simp only [whole] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> simp_all [d,b,a,c]

-- A payload Remove/Add pair is noncommuting against the actual implementation.
private theorem conflict (x y : Op (Update Nat))
    (h : (∃ z, x.2.2 = .remove z ∧ y.2.2 = .add z) ∨
      (∃ z, y.2.2 = .remove z ∧ x.2.2 = .add z)) :
    ¬ (D Nat).toUpdateSig.commutes x y := by
  rw [ORSet.noncomm_iff_rc]
  simpa only [ORSet.rc_iff] using h

theorem cycle_edges :
    paperOrder policy context left a b ∧
    paperOrder policy context right b c ∧
    paperOrder policy context right c d ∧
    paperOrder policy context left d a := by
  have bcn : ¬ (D Nat).toUpdateSig.commutes b c := conflict b c (Or.inr ⟨7,rfl,rfl⟩)
  have dan : ¬ (D Nat).toUpdateSig.commutes d a := conflict d a (Or.inr ⟨7,rfl,rfl⟩)
  simp [b,c] at bcn
  simp [d,a] at dan
  simp [paperOrder,context,policy,left,right,a,b,c,d,Op.op,bcn,dan]

theorem closed_sides :
    (MetadataDependencies.ofConcrete context).Closed left ∧
    (MetadataDependencies.ofConcrete context).Closed right := by
  constructor <;> intro x y edge hy
  · rcases edge.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [left]
    · simp [left,a,b,c,d] at hy
  · rcases edge.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [right,a,b,c,d] at hy
    · simp [right]

theorem left_canonical : Canonical policy context left ({(7,2)} : State Nat) := by
  refine ⟨[d,a,b],?_,?_,?_⟩
  · simp [listPermOf,left,d,a,b,c]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

theorem right_canonical : Canonical policy context right ({(7,1)} : State Nat) := by
  refine ⟨[b,c,d],?_,?_,?_⟩
  · simp [listPermOf,right,d,a,b,c,or_comm]
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

theorem common_canonical : Canonical policy context (left ∩ right)
    ({(7,1),(7,2)} : State Nat) := by
  refine ⟨[d,b],?_,?_,?_⟩
  · simp [listPermOf,left,right,d,a,b,c]
    aesop
  · simp [respects,paperOrder,context,policy,d,a,b,c,Op.op]
  · decide

theorem union_canonical : Canonical policy context (left ∪ right) (∅ : State Nat) := by
  refine ⟨[d,b,a,c],?_,?_,?_⟩
  · simp [listPermOf,left,right,d,a,b,c]
    aesop
  · simp [respects,paperOrder,context,policy,left,right,d,a,b,c,Op.op,
      ORSet.noncomm_iff_rc,ORSet.rc_iff,
      UpdateSig.rc,ReplayPolicy.Before,ORSet.policy,ORSet.order]
  · decide

/-- Hand-derived value: each side retains a different Add tag; both shared
births are removed in the union. Merge cannot project either nonempty side. -/
theorem merge_positive_and_negative :
    merge ({(7,1),(7,2)} : State Nat) {(7,2)} {(7,1)} = ∅ ∧
    merge ({(7,1),(7,2)} : State Nat) {(7,2)} {(7,1)} ≠ {(7,2)} ∧
    merge ({(7,1),(7,2)} : State Nat) {(7,2)} {(7,1)} ≠ {(7,1)} := by
  decide

def combined (x y : Op (Update Nat)) : Prop :=
  (x ∈ left ∧ y ∈ left ∧ paperOrder policy context left x y) ∨
  (x ∈ right ∧ y ∈ right ∧ paperOrder policy context right x y)

/-- There is no union enumeration whose projections respect both side orders.
This uses only the four concrete edges and generic list position reasoning. -/
theorem no_joint_replay : ¬ ∃ π : List (Op (Update Nat)),
    listPermOf π whole ∧ respects π combined := by
  rintro ⟨π,perm,hr⟩
  have edgeIndex : ∀ x y, x ∈ whole → y ∈ whole → x ≠ y → combined x y →
      π.idxOf x < π.idxOf y := by
    intro x y hx hy ne edge
    have ix := List.idxOf_lt_length_iff.mpr ((perm.2 x).mpr hx)
    have iy := List.idxOf_lt_length_iff.mpr ((perm.2 y).mpr hy)
    by_contra hn
    have le : π.idxOf y ≤ π.idxOf x := by omega
    rcases Nat.eq_or_lt_of_le le with eq | lt
    · have same : x = y := by
        have gx := List.getElem_idxOf ix
        have gy := List.getElem_idxOf iy
        have gy' : π[π.idxOf x] = y := by simpa only [eq] using gy
        exact gx.symm.trans gy'
      exact ne same
    · have no := List.pairwise_iff_getElem.mp hr _ _ iy ix lt
      rw [List.getElem_idxOf iy, List.getElem_idxOf ix] at no
      exact no edge
  obtain ⟨ab,bc,cd,da⟩ := cycle_edges
  have hab := edgeIndex a b (by simp [whole]) (by simp [whole])
    (by simp [a,b]) (Or.inl ⟨by simp [left],by simp [left],ab⟩)
  have hbc := edgeIndex b c (by simp [whole]) (by simp [whole])
    (by simp [b,c]) (Or.inr ⟨by simp [right],by simp [right],bc⟩)
  have hcd := edgeIndex c d (by simp [whole]) (by simp [whole])
    (by simp [c,d]) (Or.inr ⟨by simp [right],by simp [right],cd⟩)
  have hda := edgeIndex d a (by simp [whole]) (by simp [whole])
    (by simp [d,a]) (Or.inl ⟨by simp [left],by simp [left],da⟩)
  omega


/-- A crossed common-order square. It is a finite implementation theorem,
not claimed to be a consequence of Neem's 21 aligned-common schemata. It
covers the cycle's two incompatible common-event projections. -/
theorem crossed_square_exact (z : State Nat) (x ti th tr ts ri rh rr rs : Nat)
    (tags : ti ≠ th) :
    let i : Op (Update Nat) := (ti,ri,.add x)
    let h : Op (Update Nat) := (th,rh,.add x)
    let r : Op (Update Nat) := (tr,rr,.remove x)
    let s : Op (Update Nat) := (ts,rs,.remove x)
    merge (step (step z i) h)
      (step (step (step z i) r) h) (step (step (step z h) s) i) =
      step (step (step (step z i) h) r) s := by
  dsimp
  ext p
  simp [merge,step] at *
  grind

open Sal.MRDTs.Instances in
/-- The same finite crossed square respects efficient Add's overwrite rule. -/
theorem crossed_square_efficient (z : EfficientORSet.State Nat)
    (x ti th tr ts ri rh rr rs : Nat) (tags : ti ≠ th) (replicas : ri ≠ rh) :
    let i : Op (EfficientORSet.SetOp Nat) := (ti,ri,.add x)
    let h : Op (EfficientORSet.SetOp Nat) := (th,rh,.add x)
    let r : Op (EfficientORSet.SetOp Nat) := (tr,rr,.remove x)
    let s : Op (EfficientORSet.SetOp Nat) := (ts,rs,.remove x)
    EfficientORSet.merge (EfficientORSet.update (EfficientORSet.update z i) h)
      (EfficientORSet.update (EfficientORSet.update (EfficientORSet.update z i) r) h)
      (EfficientORSet.update (EfficientORSet.update (EfficientORSet.update z h) s) i) =
      EfficientORSet.update (EfficientORSet.update
        (EfficientORSet.update (EfficientORSet.update z i) h) r) s := by
  dsimp
  ext p
  simp [EfficientORSet.merge,EfficientORSet.update] at *
  grind

/-- The concrete cycle's merge equality follows from the crossed finite law,
without calculating the merge result using decide. -/
theorem cycle_via_crossed_square :
    merge (step (step ∅ d) b) (step (step (step ∅ d) a) b)
      (step (step (step ∅ b) c) d) = step (step (step (step ∅ d) b) a) c := by
  exact crossed_square_exact ∅ 7 1 2 3 4 1 0 1 0 (by decide)

end Sal.MRDTs.Paper1.NeemCycleResidual
