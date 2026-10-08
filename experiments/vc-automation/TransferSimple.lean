import ExpandedVCs
import Sal.MRDTs.Paper1.SimpleConcretePorts

/-! Transfer to the unchanged four commuting production families. Empty metadata
past expands to the empty replay, so the causal induction has only its seed.
All datatype equations below are newly checked directly from definitions. -/
namespace NeemExpansion.TransferSimple
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Classical

structure EmptyPastKernels (D : MRDTSig) : Prop where
  comm : ∀ l a b, D.merge l a b = D.merge l b a
  initial : ∀ s, D.merge D.init D.init s = s
  causalSeed : ∀ s e, D.merge D.init s (D.update D.init e) = D.update s e
  localEquation : ∀ l B t b e, D.merge l (D.merge B t (D.update B e)) b =
    D.merge B (D.merge l t b) (D.update B e)
  shared : ∀ B t₀ t₁ t₂ e,
    D.merge (D.merge B t₀ (D.update B e))
      (D.merge B t₁ (D.update B e)) (D.merge B t₂ (D.update B e)) =
    D.merge B (D.merge t₀ t₁ t₂) (D.update B e)

/-- Empty metadata coverage reduces the causal VC to the finite seed equation.
No existing VC, Join, state invariant, merge-law or delta-law proof is used. -/
theorem assemble (D : MRDTSig) (commute : ∀ a b, D.toUpdateSig.commutes a b)
    (kernels : EmptyPastKernels D) :
    Raw.MergeVCs (commutingPolicy D.AppOp) (CommutingPort.representation D)
      (CommutingPort.scheme commute) := by
  constructor
  · intros; apply kernels.comm
  · intros; apply kernels.initial
  · intro C U s B e _ _ _ _ _ _ _ _ hB _ _
    have past : (CommutingPort.scheme commute C).Past e \ {e} = ∅ := by
      rw [CommutingPort.past_eq, Set.diff_self]
    obtain ⟨_, π, perm, replay⟩ := hB
    rw [past] at perm
    have nil : π = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x member
      exact (perm.2 x).mp member
    subst π
    change D.init = B at replay
    rw [← replay]
    exact kernels.causalSeed s e
  · intros; apply kernels.localEquation
  · intros; apply kernels.shared

variable {A : Type} [DecidableEq A]

namespace Add
open Instances.AddStore
 theorem kernels : EmptyPastKernels (D A) := by
  constructor
  · intros; apply Set.ext; intro x; simp [D, or_comm]
  · intros; apply Set.ext; intro x; simp [D]
  · intros; apply Set.ext; intro x; simp [D]
  · intros; apply Set.ext; intro x; simp [D, or_assoc, or_comm]
  · intros; apply Set.ext; intro x; simp [D, or_assoc, or_left_comm, or_comm]
 theorem expanded_vcs : Raw.MergeVCs (commutingPolicy A)
    (CommutingPort.representation (D A)) (CommutingPort.scheme (all_comm (α := A))) :=
  assemble (D A) all_comm kernels
end Add

namespace Finite
open Instances.FinsetStore
 theorem kernels : EmptyPastKernels (D A) := by
  constructor
  · intros; apply Finset.ext; intro x; simp [D, or_comm]
  · intros; apply Finset.ext; intro x; simp [D]
  · intros; apply Finset.ext; intro x; simp [D]
  · intros; apply Finset.ext; intro x; simp [D, or_left_comm, or_comm]
  · intros; apply Finset.ext; intro x; simp [D, or_left_comm, or_comm]
 theorem expanded_vcs : Raw.MergeVCs (commutingPolicy A)
    (CommutingPort.representation (D A)) (CommutingPort.scheme (all_comm (α := A))) :=
  assemble (D A) all_comm kernels
end Finite

namespace Delta
open Instances.FlatCounters
 theorem kernels (delta : A → Int) : EmptyPastKernels (D A delta) := by
  constructor <;> intros <;> simp only [D] <;> omega
 theorem expanded_vcs (delta : A → Int) : Raw.MergeVCs (commutingPolicy A)
    (CommutingPort.representation (D A delta)) (CommutingPort.scheme (all_comm delta)) :=
  assemble (D A delta) (all_comm delta) (kernels delta)
end Delta

namespace Boolean
private theorem or_idem (a b : Bool) : (a || (a || b)) = (a || b) := by cases a <;> rfl
open Instances.FlatGrowOnly
 theorem kernels : EmptyPastKernels (D A) := by
  constructor <;> intros <;> funext x <;> simp only [D]
  all_goals simp only [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm, Bool.false_or, Bool.or_self, or_idem]
 theorem expanded_vcs : Raw.MergeVCs (commutingPolicy A)
    (CommutingPort.representation (D A)) (CommutingPort.scheme (all_comm (A := A))) :=
  assemble (D A) all_comm kernels
end Boolean

abbrev gset := Add.expanded_vcs (A := Nat)
abbrev addStore := Add.expanded_vcs (A := Nat)
abbrev finiteAdd := Finite.expanded_vcs (A := Nat)
abbrev counter := Delta.expanded_vcs (A := Unit) (fun _ => 1)
abbrev ioc := Delta.expanded_vcs (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev pn := Delta.expanded_vcs Instances.FlatCounters.pnDelta
abbrev booleanSet := Boolean.expanded_vcs (A := Nat)
abbrev booleanMap := Boolean.expanded_vcs (A := Nat × Nat)

#print axioms Add.expanded_vcs
#print axioms Finite.expanded_vcs
#print axioms Delta.expanded_vcs
#print axioms Boolean.expanded_vcs
end NeemExpansion.TransferSimple
