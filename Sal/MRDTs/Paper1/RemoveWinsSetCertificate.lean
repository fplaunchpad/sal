import Sal.MRDTs.Paper1.RemoveWinsSetVC
import Sal.MRDTs.Paper1.RemoveWinsSetEvent
import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.CertifiedClosedExecution

/-! Source-faithful removal-tag set, with timestamp zero reserved for genesis.
The concrete certificate consumes the five equations and common finite merge
induction, and covers stored ancestors and recursive virtual merge bases. -/
namespace Sal.MRDTs.Paper1.RemoveWinsSet
open Foundation Instances.RemoveWinsSet ConcreteMRDT
open Classical
variable {α : Type} [DecidableEq α] [Fintype α]
noncomputable local instance : EventOrder (D α).toUpdateSig := (conflict α).lift

/-- The source's initial zero tags reserve that timestamp for genesis. -/
def generation (α : Type) [DecidableEq α] [Fintype α] : Issuance (D α) where
  CanIssue e _ := 0 < e.time

private theorem positive_of_mint {C : Configuration (D α)}
    (mint : MintHonest (D α) (generation α).CanIssue C) : Positive C.replayContext := by
  intro e he
  obtain ⟨π,hp,hr,issued⟩ := mint e he
  exact issued

/-- Join on the source issuance domain follows from the five-VC induction. -/
theorem vcJoinAt (C : ReplayContext (D α).toUpdateSig) (positive : Positive C) :
    CertifiedClosedExecution.ClosedJoinAt (D α) C := by
  intro E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have joined := representationJoin C E₁ E₂ l a b (fun _ _ _ => trans) irr
    sup₁ sup₂ closed₁ closed₂
    ⟨hl,(fun e he => sup₁ e he.1),positive⟩ ⟨ha,sup₁,positive⟩ ⟨hb,sup₂,positive⟩
  exact joined.1

theorem canonicalConfig {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (generation α) C) :
    CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C mint => vcJoinAt C.replayContext (positive_of_mint mint)) reach

theorem representedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) (generation α) C)
    (v : Version) (s : State α) (E : Set (Op (Update α))) (hv : C.ver v = some (s,E)) :
    representation C.replayContext E s := by
  have good := canonicalConfig reach
  exact ⟨good.canonical v s E hv,good.version_events_supported v s E hv,
    positive_of_mint reach.mintHonest⟩

def replayConditions : VCReplayConditions (conflict α) (generation α) where
  representation := representation
  scheme := scheme
  laws := splitLaws.toGuarded
  vcs := fiveVC
  unique := unique
  initial := fun C E s h => initial_rep C h.2.2
  finite := finite
  canonical := canonical
  supported := fun _ _ _ h => h.2.1
  replaySupply := fun C _ _ _ _ trans irr _ _ ha _ => replaySupply C ha.2.2 trans irr
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
end Sal.MRDTs.Paper1.RemoveWinsSet
