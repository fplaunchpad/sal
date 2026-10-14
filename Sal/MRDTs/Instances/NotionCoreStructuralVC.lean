import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Paper1.Automation.TransferSimple
import Sal.MRDTs.Paper1.Automation.CommutingAssembly

/-! Actual five VCs for the directly merged fact carrier. The query parameter
is arbitrary here: document correspondence must be established separately.
Neither the state nor its operational replay holds a transaction archive. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralVC
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreStructuralFacts (Fact State decode)

variable {Q V : Type}
abbrev D (query : State → Q → V) : Sal.MRDTs.MRDTSig where
  State := State
  dec_state := inferInstance
  init := ∅
  AppOp := Transaction
  dec_op := inferInstance
  Query := Q
  Value := V
  update s e := s ∪ decode e.op
  merge _ left right := left ∪ right
  query := query

variable (query : State → Q → V)
theorem all_comm (a b : Op (D query).AppOp) : (D query).toUpdateSig.commutes a b := by
  intro s
  simp [D,Finset.union_assoc,Finset.union_comm,Finset.union_left_comm]

theorem kernels : Automation.TransferSimple.EmptyPastKernels (D query) := by
  constructor
  · intro l a b; simp [D,Finset.union_comm]
  · intro s; simp [D]
  · intro s e; simp [D]
  · intro l B t b e
    simp [D,Finset.union_assoc,Finset.union_comm,Finset.union_left_comm]
  · intro B t₀ t₁ t₂ e
    ext f
    simp
    tauto

abbrev representation : Representation (D query) := CommutingPort.representation (D query)
abbrev scheme (C : ReplayContext (D query).toUpdateSig) : @MetadataDependencies (D query) C :=
  @CommutingPort.scheme (D query) (all_comm query) C

/-- The actual carrier's five VCs, for any eventual structural query. -/
theorem fiveVCs : @Raw.MergeVCs (D query) (commutingPolicy Transaction)
    (representation query) (scheme query) :=
  Automation.TransferSimple.assemble (D query) (all_comm query) (kernels query)

/-- Fold membership exposes the exact decoded-event representation. Updates
may contribute many facts or none; injectivity of decoding is not required. -/
theorem fold_membership (start : State) (events : List (Op Transaction)) (f : Fact) :
    f ∈ applySeq (D query).toUpdateSig start events ↔
      f ∈ start ∨ ∃ e ∈ events, f ∈ decode e.op := by
  induction events generalizing start with
  | nil => simp [applySeq]
  | cons e events ih =>
      change f ∈ applySeq (D query).toUpdateSig (start ∪ decode e.op) events ↔ _
      rw [ih]
      simp only [D,Finset.mem_union,List.mem_cons]
      aesop

/-- Exact represented fact sets, retaining the event-enumeration hypothesis
needed for finite operational replay. No transaction archive is a state field. -/
theorem representation_iff (C : ReplayContext (D query).toUpdateSig)
    (E : Set (Op Transaction)) (state : State) :
    representation query C E state ↔
      Supported C E ∧ (∃ events, listPermOf events E) ∧
        ∀ f, f ∈ state ↔ ∃ e ∈ E, f ∈ decode e.op := by
  constructor
  · rintro ⟨support,events,enumeration,fold⟩
    refine ⟨support,⟨events,enumeration⟩,?_⟩
    intro f
    rw [← fold,fold_membership]
    simp only [Finset.notMem_empty,false_or]
    constructor
    · rintro ⟨e,member,fact⟩
      exact ⟨e,(enumeration.2 e).mp member,fact⟩
    · rintro ⟨e,member,fact⟩
      exact ⟨e,(enumeration.2 e).mpr member,fact⟩
  · rintro ⟨support,⟨events,enumeration⟩,members⟩
    refine ⟨support,events,enumeration,?_⟩
    ext f
    rw [fold_membership,members]
    simp only [Finset.notMem_empty,false_or]
    constructor
    · rintro ⟨e,member,fact⟩
      exact ⟨e,(enumeration.2 e).mp member,fact⟩
    · rintro ⟨e,member,fact⟩
      exact ⟨e,(enumeration.2 e).mpr member,fact⟩

def issuance : Issuance (D query) where
  CanIssue := fun _ _ => True
noncomputable def replayConditions (I : Issuance (D query)) :
    VCReplayConditions (commutingPolicy Transaction) I :=
  CommutingPort.automatedReplayConditions (D := D query) (all_comm query) (fiveVCs query) I

theorem represented_versions {I : Issuance (D query)} {C : Configuration (D query)}
    (reachable : MintCertifiedReachV (D query) (canonicalVirtualMergeBase (D query)) I C)
    (version : Version) (state : State) (events : Set (Op Transaction))
    (registered : C.ver version = some (state,events)) :
    representation query C.replayContext events state :=
  (replayConditions query I).representedVersions C reachable version state events registered

#print axioms fiveVCs
#print axioms representation_iff
#print axioms represented_versions
end Sal.MRDTs.Instances.NotionCoreStructuralVC
