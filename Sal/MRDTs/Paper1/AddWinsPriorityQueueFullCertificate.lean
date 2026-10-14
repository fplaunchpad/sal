import Sal.MRDTs.Paper1.AddWinsPriorityQueueCertificate
import Sal.MRDTs.Paper1.AddWinsPriorityQueueFullSpec

/-! All four observable queries share the existing operational five equations.
The query-only lift preserves carrier, updates, merge and replay policy. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full
open Foundation Instances.AddWinsPriorityQueue ConcreteMRDT
open Classical
noncomputable local instance : EventOrder FullD.toUpdateSig := (conflict Nat).lift

abbrev representation : Representation FullD := AddWinsPriorityQueue.representation (α := Nat)

abbrev scheme (C : ReplayContext FullD.toUpdateSig) : @MetadataDependencies FullD C :=
  Automation.QueryLift.scheme (D Nat) FullQuery Answer Instances.AddWinsPriorityQueue.read AddWinsPriorityQueue.scheme C

theorem fiveVC : @Raw.MergeVCs FullD (conflict Nat) representation scheme :=
  Automation.QueryLift.transport (D Nat) FullQuery Answer Instances.AddWinsPriorityQueue.read (conflict Nat)
    AddWinsPriorityQueue.representation AddWinsPriorityQueue.scheme AddWinsPriorityQueue.fiveVC

/-- Query-only transport of replay supply rebuilds the two nominal record
wrappers; every event, represented state and dependency edge is unchanged. -/
def replaySupply (C : ReplayContext FullD.toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) :
    @Raw.ReplaySupply FullD (conflict Nat) representation scheme C := by
  let old := AddWinsPriorityQueue.replaySupply C trans irr
  refine ⟨old.represented,?_⟩
  intro E s represented supported nonempty closed
  obtain ⟨choice⟩ := old.peel E s represented supported nonempty closed
  exact ⟨⟨choice.event,choice.member,choice.semantic_maximal,choice.metadata_maximal,
    choice.remainder,choice.past,choice.remainder_rep,choice.past_rep,
    choice.reconstructed_past,choice.reconstructed_union⟩⟩

theorem representationJoin : RepresentationJoin representation := by
  apply Raw.representationJoin_of_vcs fiveVC AddWinsPriorityQueue.unique
    (fun C _ _ _ => initial_rep C) AddWinsPriorityQueue.finite
  intro C _ _ _ _ trans irr _ _ _ _
  exact replaySupply C trans irr

def generation : Issuance FullD where
  CanIssue _ _ := True

theorem vcJoinAt (C : ReplayContext FullD.toUpdateSig) :
    CertifiedClosedExecution.ClosedJoinAt FullD C := by
  intro E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  exact (representationJoin C E₁ E₂ l a b (fun _ _ _ => trans) irr
    sup₁ sup₂ closed₁ closed₂ ⟨hl,fun e he => sup₁ e he.1⟩ ⟨ha,sup₁⟩ ⟨hb,sup₂⟩).1

theorem canonicalConfig {C : Configuration FullD}
    (reach : MintCertifiedReachV FullD (canonicalVirtualMergeBase FullD) generation C) :
    CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => vcJoinAt C.replayContext) reach

def replayConditions : VCReplayConditions (conflict Nat) generation where
  representation := representation
  scheme := scheme
  laws := (splitLaws (α := Nat)).toGuarded
  vcs := fiveVC
  unique := AddWinsPriorityQueue.unique
  initial := fun C _ _ _ => initial_rep C
  finite := AddWinsPriorityQueue.finite
  canonical := AddWinsPriorityQueue.canonical
  supported := fun _ _ _ h => h.2
  replaySupply := fun C _ _ _ _ trans irr _ _ _ _ => replaySupply C trans irr
  representedVersions := by
    intro C reach v s E hv
    have good := canonicalConfig reach
    exact ⟨good.canonical v s E hv,good.version_events_supported v s E hv⟩

def conditions : VCConditions (conflict Nat) spec generation where
  toVCReplayConditions := replayConditions
  compatibility := compatible
  historySound := historySound

theorem certifiedV : EventCertifiedSpecificationRAV FullD (conflict Nat) spec generation := by
  intro C reach
  exact conditions.versionsV reach

theorem certified : EventCertifiedSpecificationRA FullD (conflict Nat) spec generation :=
  certifiedV.ordinary

theorem executions (trace : List (Label FullD × Configuration FullD))
    (execution : (certifiedTS FullD generation).Execution (initConfig FullD) trace) :
    ExecutionCorrect (conflict Nat) spec trace := conditions.executions trace execution

theorem executionsV (trace : List (Label FullD × Configuration FullD))
    (execution : (certifiedTSV FullD generation).Execution (initConfig FullD) trace) :
    ExecutionCorrect (conflict Nat) spec trace := conditions.executionsV trace execution

#print axioms fiveVC
#print axioms certifiedV
#print axioms executions
#print axioms executionsV
end Sal.MRDTs.Paper1.AddWinsPriorityQueue.Full
