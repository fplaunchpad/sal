import Sal.MRDTs.Paper1.AddWinsPriorityQueueVC
import Sal.MRDTs.Paper1.AddWinsPriorityQueueSpec
import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.CertifiedClosedExecution

/-! Source-faithful priority queue with retained historical increments.
The concrete certificate consumes the five equations and common finite merge
induction, and covers stored ancestors and recursive virtual merge bases. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue
open Foundation Instances.AddWinsPriorityQueue ConcreteMRDT
open Classical
variable {α : Type} [DecidableEq α]
noncomputable local instance : EventOrder (D α).toUpdateSig := (conflict α).lift

/-- No state-dependent operation guard. Globally fresh timestamps, honest
minting, causally closed event histories, and valid stored or recursively
computed virtual ancestors are enforced by certified execution. -/
def generation (α : Type) [DecidableEq α] : Issuance (D α) where
  CanIssue _ _ := True

/-- Join on the source issuance domain follows from the five-VC induction. -/
theorem vcJoinAt (C : ReplayContext (D α).toUpdateSig) :
    CertifiedClosedExecution.ClosedJoinAt (D α) C := by
  intro E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have joined := representationJoin C E₁ E₂ l a b (fun _ _ _ => trans) irr
    sup₁ sup₂ closed₁ closed₂
    ⟨hl,(fun e he => sup₁ e he.1)⟩ ⟨ha,sup₁⟩ ⟨hb,sup₂⟩
  exact joined.1

theorem canonicalConfig {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (generation α) C) :
    CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => vcJoinAt C.replayContext) reach

theorem representedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (generation α) C)
    (v : Version) (s : State α) (E : Set (Op (Update α))) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s := by
  have good := canonicalConfig reach
  exact ⟨good.canonical v s E hv,good.version_events_supported v s E hv⟩

def replayConditions : VCReplayConditions (conflict α) (generation α) where
  representation := representation
  scheme := scheme
  laws := splitLaws.toGuarded
  vcs := fiveVC
  unique := unique
  initial := fun C _ _ _ => initial_rep C
  finite := finite
  canonical := canonical
  supported := fun _ _ _ h => h.2
  replaySupply := fun C _ _ _ _ trans irr _ _ _ _ => replaySupply C trans irr
  representedVersions := fun _ reach v s E hv => representedVersions reach v s E hv

def conditions : VCConditions (conflict α) (spec α) (generation α) where
  toVCReplayConditions := replayConditions
  compatibility := compatible
  historySound := historySound

theorem certifiedV : EventCertifiedSpecificationRAV (D α) (conflict α) (spec α) (generation α) := by
  intro C reach
  exact conditions.versionsV reach

theorem certified : EventCertifiedSpecificationRA (D α) (conflict α) (spec α) (generation α) :=
  certifiedV.ordinary

theorem executions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) (generation α)).Execution (initConfig (D α)) trace) :
    ExecutionCorrect (conflict α) (spec α) trace := conditions.executions trace execution

theorem executionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) (generation α)).Execution (initConfig (D α)) trace) :
    ExecutionCorrect (conflict α) (spec α) trace := conditions.executionsV trace execution

#print axioms certifiedV
#print axioms executions
#print axioms executionsV
end Sal.MRDTs.Paper1.AddWinsPriorityQueue
