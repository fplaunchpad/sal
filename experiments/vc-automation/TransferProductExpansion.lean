import TransferSimple
import CertifiedExpansion
import Sal.MRDTs.Paper1.RGAConcretePort

/-! Product expansion: finite record text merge cells and monotone evidence-store
cells compose componentwise. Native tombstone RGA also has an empty-past route
because its representation effectors commute, despite guarded issuance. -/
namespace NeemExpansion.TransferProduct
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

def mixedMerge {T K M : Type} [DecidableEq T] [DecidableEq K] [DecidableEq M]
    (l a b : Finset T × (Finset K × Finset M)) :=
  (Certified.merge l.1 a.1 b.1, a.2.1 ∪ b.2.1, a.2.2 ∪ b.2.2)

theorem mixed_local {T K M : Type} [DecidableEq T] [DecidableEq K] [DecidableEq M]
    (l B t b d : Finset T × (Finset K × Finset M))
    (evidence : Certified.LocalEvidence l.1 B.1 b.1 d.1) :
    mixedMerge l (mixedMerge B t d) b = mixedMerge B (mixedMerge l t b) d := by
  apply Prod.ext
  · exact Certified.local_redistribute _ _ _ _ _ evidence
  · apply Prod.ext <;> apply Finset.ext <;> intro p
    all_goals simp only [mixedMerge, Finset.mem_union]; tauto

theorem mixed_shared {T K M : Type} [DecidableEq T] [DecidableEq K] [DecidableEq M]
    (t₀ t₁ t₂ B d : Finset T × (Finset K × Finset M)) :
    mixedMerge (mixedMerge B t₀ d) (mixedMerge B t₁ d) (mixedMerge B t₂ d) =
    mixedMerge B (mixedMerge t₀ t₁ t₂) d := by
  apply Prod.ext
  · exact Certified.shared _ _ _ _ _
  · apply Prod.ext <;> apply Finset.ext <;> intro p
    all_goals simp only [mixedMerge, Finset.mem_union]; tauto

/-- Product causal certificate: immutable text births/kills plus monotone
store inclusions and unchanged finite birth packets. -/
theorem mixed_causal {T K M : Type} [DecidableEq T] [DecidableEq K] [DecidableEq M]
    (B a d u : Finset T × (Finset K × Finset M))
    (born killed : T → Prop) (text : Certified.DeltaEvidence B.1 a.1 born killed)
    (pastText : ∀ p, p ∈ d.1 ↔ born p ∨ (p ∈ B.1 ∧ ¬ killed p))
    (remainderText : ∀ p, p ∈ u.1 ↔ born p ∨ (p ∈ a.1 ∧ ¬ killed p))
    (newK : Finset K) (newM : Finset M)
    (subK : B.2.1 ⊆ a.2.1) (subM : B.2.2 ⊆ a.2.2)
    (pastK : d.2.1 = B.2.1 ∪ newK) (pastM : d.2.2 = B.2.2 ∪ newM)
    (remK : u.2.1 = a.2.1 ∪ newK) (remM : u.2.2 = a.2.2 ∪ newM) :
    mixedMerge B a d = u := by
  apply Prod.ext
  · exact Certified.causal _ _ _ _ born killed text pastText remainderText
  · apply Prod.ext
    · change a.2.1 ∪ d.2.1 = u.2.1
      rw [pastK, remK, ← Finset.union_assoc, Finset.union_eq_left.mpr subK]
    · change a.2.2 ∪ d.2.2 = u.2.2
      rw [pastM, remM, ← Finset.union_assoc, Finset.union_eq_left.mpr subM]

namespace NativeRGA
open Instances.RGA

theorem kernels : TransferSimple.EmptyPastKernels RGAM := by
  constructor
  · intro l a b
    apply Prod.ext <;> funext x <;> simp [RGAM, Bool.or_comm]
  · intro s
    apply Prod.ext <;> funext x <;> simp [RGAM]
  · intro s e
    rcases e with ⟨t,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_comm]
  · intro l B t b e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  · intro B t₀ t₁ t₂ e
    rcases e with ⟨ts,r,op⟩
    cases op <;> apply Prod.ext <;> funext x <;>
      simp [RGAM, rgaUpdate, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem expanded_vcs : Raw.MergeVCs (commutingPolicy RGAOp)
    (CommutingPort.representation RGAM) (CommutingPort.scheme RGAM_all_comm) :=
  TransferSimple.assemble RGAM RGAM_all_comm kernels
#print axioms expanded_vcs
end NativeRGA
end NeemExpansion.TransferProduct
