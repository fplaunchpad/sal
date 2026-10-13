import Sal.MRDTs.Paper1.DisableWinsFlagEvent

/-! Hand-derived PASS+FAIL controls for the source's row counters, initial
polarity, concurrent winner and observed reset. Distinct replicas model
concurrent requests; physical winning/reset labels have source aliases. -/
namespace Sal.MRDTs.Paper1.DisableWinsFlagSPOT
open Foundation Instances.DisableWinsFlag
open Classical

private theorem enabled_of_clear {s : State} (clear : ∀ r, (s r).2 = false) :
    query s () = true := by simp [query,Instances.NeemFlag.active,clear]
private theorem disabled_of_bit {s : State} {r : Nat} (bit : (s r).2 = true) :
    query s () = false := by
  have active : Instances.NeemFlag.active s = true :=
    (Instances.NeemFlag.active_true_iff s).mpr ⟨r,bit⟩
  simp [query,active]

/-- Source const has universal domain, so the initial row 99 is true too. -/
theorem initial_control : initial 0 = (0,true) ∧ initial 99 = (0,true) ∧
    query initial () = false ∧ query initial () ≠ true := by
  simp [initial,Instances.NeemFlag.initial]

def enabledRoot : State := update initial (1,0,enable)
def concurrent : State := merge enabledRoot
  (update enabledRoot (2,0,enable)) (update enabledRoot (3,1,disable))

theorem concurrent_disable_wins : query concurrent () = false ∧ query concurrent () ≠ true ∧
    concurrent 1 = (1,true) ∧ concurrent 0 = (0,false) := by
  have row : concurrent 1 = (1,true) := by
    norm_num [concurrent,enabledRoot,initial,update,merge,enable,disable,
      Instances.NeemFlag.initial,Instances.NeemFlag.update,Instances.NeemFlag.merge,
      Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,Op.op]
  have value := disabled_of_bit (r := 1) (s := concurrent) (by rw [row])
  refine ⟨value,by simp [value],row,?_⟩
  norm_num [concurrent,enabledRoot,initial,update,merge,enable,disable,
    Instances.NeemFlag.initial,Instances.NeemFlag.update,Instances.NeemFlag.merge,
    Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,Op.op]

theorem sequential_enable_clears : query (update concurrent (4,1,enable)) () = true ∧
    query (update concurrent (4,1,enable)) () ≠ false := by
  have hv := query_enable concurrent (4,1,enable) (by rfl)
  exact ⟨hv,by simp [hv]⟩

/-- The source's all-present-row reset includes remotely created rows. -/
def observed : State := update enabledRoot (2,1,disable)
def observedReset : State := merge observed (update observed (3,0,enable)) observed

theorem observed_enable_suppresses : query observedReset () = true ∧
    query observedReset () ≠ false ∧ observedReset 1 = (1,false) := by
  have clear : ∀ r, (observedReset r).2 = false := by
    intro r
    by_cases hr : r = 1 <;>
      simp [observedReset,observed,enabledRoot,initial,update,merge,enable,disable,
        Instances.NeemFlag.initial,Instances.NeemFlag.update,Instances.NeemFlag.merge,
        Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,Op.op,hr]
  have value := enabled_of_clear clear
  refine ⟨value,by simp [value],?_⟩
  norm_num [observedReset,observed,enabledRoot,initial,update,merge,enable,disable,
    Instances.NeemFlag.initial,Instances.NeemFlag.update,Instances.NeemFlag.merge,
    Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,Op.op]

/-- Two source counters prevent the stale winner that a scalar counter admits.
The final merge ancestor is the observed replica-1 disable, not initial. -/
def localReset : State := update (update initial (1,0,disable)) (2,0,enable)
def remoteDisable : State := update initial (3,1,disable)
def delivered : State := merge initial localReset remoteDisable
def crossReplicaReset : State := merge remoteDisable
  (update remoteDisable (4,1,enable)) delivered

theorem cross_replica_reset_control : query crossReplicaReset () = true ∧
    query crossReplicaReset () ≠ false ∧ crossReplicaReset 0 = (1,false) ∧
    crossReplicaReset 1 = (1,false) ∧ crossReplicaReset 99 = (0,false) := by
  have clear : ∀ r, (crossReplicaReset r).2 = false := by
    intro r
    by_cases h0 : r = 0 <;> by_cases h1 : r = 1
    all_goals simp [crossReplicaReset,delivered,remoteDisable,localReset,initial,
      update,merge,enable,disable,Instances.NeemFlag.initial,Instances.NeemFlag.update,
      Instances.NeemFlag.merge,Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,
      Op.op,h0,h1]
  have value := enabled_of_clear clear
  refine ⟨value,by simp [value],?_,?_,?_⟩
  all_goals norm_num [crossReplicaReset,delivered,remoteDisable,localReset,initial,
    update,merge,enable,disable,Instances.NeemFlag.initial,Instances.NeemFlag.update,
    Instances.NeemFlag.merge,Instances.NeemFlag.mergeCell,Instances.NeemFlag.mergeFlag,Op.op]

#print axioms concurrent_disable_wins
#print axioms observed_enable_suppresses
end Sal.MRDTs.Paper1.DisableWinsFlagSPOT
