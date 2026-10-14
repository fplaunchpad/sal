import Sal.MRDTs.Instances.NotionCoreIncrementalReplay
import Sal.MRDTs.Instances.NotionCoreMRDTArchive
import Sal.MRDTs.Paper1.Automation.TransferSimple

/-! Invariant-restricted incremental replay MRDT. Proof fields certify the full
checkpoint sequence; ordinary Lean equality is retained. Its ordered Finset
boundary inherits the reference's noncomputability, while the replay engine is
executable. This baseline is not a direct structural merge implementation. -/
namespace Sal.MRDTs.Instances.NotionCoreIncrementalMRDT
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCoreIncrementalReplay

structure Maintained where
  archive : Finset Transaction
  cache : Cache
  valid : Valid cache
  ordered : transactions cache = NotionCoreMRDT.transactions archive
  deriving DecidableEq

/-- Archive projection is injective because *every* stored checkpoint is
certified, not just the final observation. Equality remains concrete equality. -/
theorem Maintained.ext {a b : Maintained} (same : a.archive = b.archive) : a = b := by
  have cached : a.cache = b.cache := by
    rw [valid_canonical a.valid,valid_canonical b.valid,a.ordered,b.ordered,same]
  cases a
  cases b
  simp_all

noncomputable def initial : Maintained :=
  ⟨∅,NotionCoreIncrementalReplay.initial,.nil _,by simp [transactions,NotionCoreMRDT.transactions,NotionCoreIncrementalReplay.initial]⟩

/-- Update/merge retain old checkpoints and invoke the dirty-suffix engine.
The proof does not change the computation into a full reconstruction. -/
noncomputable def refreshArchive (old : Maintained) (archive : Finset Transaction) : Maintained :=
  let new := NotionCoreMRDT.transactions archive
  ⟨archive,(updateTo old.cache new).cache,updateTo_valid old.valid new,
    refresh_transactions _ _ new⟩

noncomputable def D : Sal.MRDTs.MRDTSig where
  State := Maintained
  dec_state := inferInstance
  init := initial
  AppOp := Transaction
  dec_op := inferInstance
  Query := Unit
  Value := Option NotionCoreHistory.View
  update state event := refreshArchive state (insert event.2.2 state.archive)
  merge _ left right := refreshArchive left (left.archive ∪ right.archive)
  query state _ := query state.cache

@[simp] theorem init_archive : D.init.archive = ∅ := rfl
@[simp] theorem update_archive (state : Maintained) (event : Op Transaction) :
    (D.update state event).archive = insert event.2.2 state.archive := rfl
@[simp] theorem merge_archive (base left right : Maintained) :
    (D.merge base left right).archive = left.archive ∪ right.archive := rfl

theorem query_reference (state : Maintained) :
    D.query state () = NotionCoreMRDT.observe state.archive := by
  change query state.cache = _
  rw [query_eq_replay state.valid,state.ordered]
  rfl

theorem all_comm (a b : Op D.AppOp) : D.toUpdateSig.commutes a b := by
  intro state
  apply Maintained.ext
  simp [Finset.insert_comm]

/-- All hypotheses needed for the five-VC assembly are proved on the restricted
state type. No cache well-formedness assumption is dropped or deferred to callers. -/
theorem kernels : Automation.TransferSimple.EmptyPastKernels D := by
  constructor
  · intro l a b; apply Maintained.ext; simp [Finset.union_comm]
  · intro state; apply Maintained.ext; simp
  · intro state event; apply Maintained.ext; simp
  · intro l B t b event; apply Maintained.ext
    simp [Finset.union_comm,Finset.union_left_comm]
  · intro B t₀ t₁ t₂ event; apply Maintained.ext
    ext x
    simp
    tauto

abbrev representation : Representation D := CommutingPort.representation D
abbrev scheme (C : ReplayContext D.toUpdateSig) : @MetadataDependencies D C :=
  @CommutingPort.scheme D all_comm C

theorem fiveVCs : @Raw.MergeVCs D (commutingPolicy Transaction) representation scheme :=
  Automation.TransferSimple.assemble D all_comm kernels

def issuance : Issuance D where
  CanIssue := fun _ _ => True

noncomputable def replayConditions (I : Issuance D) : VCReplayConditions (commutingPolicy Transaction) I :=
  CommutingPort.automatedReplayConditions (D := D) all_comm fiveVCs I

/-- The actual cache carrier's representation supply includes canonical
recursive virtual merge bases; this is not merely observational convergence. -/
theorem represented_versions {I : Issuance D} {C : Configuration D}
    (reachable : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C)
    (version : Version) (state : Maintained) (events : Set (Op Transaction))
    (registered : C.ver version = some (state,events)) :
    representation C.replayContext events state :=
  (replayConditions I).representedVersions C reachable version state events registered

/-- Explicit sequential transport scope: an honest archive, a closed version,
and exact archive projection are required. No desired answer or replay success
is a hypothesis. This does not itself derive protocol/archive coupling. -/
theorem honest_history_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (state : Maintained) (coupled : state.archive = NotionCoreMRDTArchive.carrierFor network version)
    (lift : Transaction → Op Transaction)
    (payload : ∀ tx ∈ NotionCoreReconstruction.transactionsFor network version, (lift tx).op = tx) :
    ∃ answer, D.query state () = some answer ∧
      NotionCoreMRDT.spec.admits
        ((NotionCoreMRDTArchive.eventHistory (NotionCoreReconstruction.transactionsFor network version)
          lift answer).map NotionCoreMRDT.someLabel) := by
  rw [query_reference,coupled]
  exact NotionCoreMRDTArchive.honest_carrier_history network reachable version closed lift payload

#print axioms represented_versions
#print axioms honest_history_version
#print axioms query_reference
#print axioms fiveVCs
end Sal.MRDTs.Instances.NotionCoreIncrementalMRDT
