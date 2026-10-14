import Sal.MRDTs.Paper1.SplitPolicy
import Sal.MRDTs.Instances.BalegasBoundedCounter
import Sal.MRDTs.Paper1.Automation.CommutingInputs
import Sal.MRDTs.Paper1.Automation.SimpleInputs
import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Paper1.NeemScope
import Sal.MRDTs.Paper1.CertifiedMVRReplay

/-! Raw same-payload audit. Quantification includes arbitrary concrete states.
Named commuting families account for twelve cases in the automation roster.
The compact live MVR is distinguished from the historical tombstone MVR. -/
namespace Sal.MRDTs.Paper1.SelfCommutationInstances
open Foundation

def Unrestricted (D : UpdateSig) : Prop :=
  ∀ a b : Op D.AppOp, a.op = b.op → D.commutes a b

theorem unrestricted_of_all {D : UpdateSig}
    (all : ∀ a b : Op D.AppOp, D.commutes a b) : Unrestricted D :=
  fun a b _ => all a b

theorem guarded_of_unrestricted {D : UpdateSig} (h : Unrestricted D) :
    SplitPolicy.EqualOperationCommutes D := fun a b _ _ same => h a b same

section Commuting
variable {A : Type} [DecidableEq A]
theorem add : Unrestricted (Instances.AddStore.D A).toUpdateSig :=
  unrestricted_of_all Instances.AddStore.all_comm
theorem finite : Unrestricted (Instances.FinsetStore.D A).toUpdateSig :=
  unrestricted_of_all Instances.FinsetStore.all_comm
theorem delta (change : A → Int) : Unrestricted (Instances.FlatCounters.D A change).toUpdateSig :=
  unrestricted_of_all (Instances.FlatCounters.all_comm change)
theorem boolean : Unrestricted (Instances.FlatGrowOnly.D A).toUpdateSig :=
  unrestricted_of_all Instances.FlatGrowOnly.all_comm
theorem lww : Unrestricted Instances.LWWRegister.D.toUpdateSig :=
  unrestricted_of_all Instances.LWWRegister.all_comm
theorem rga : Unrestricted Instances.RGA.RGAM.toUpdateSig :=
  unrestricted_of_all Instances.RGA.RGAM_all_comm
theorem balegasBounded (n : Nat) (K : Int) :
    Unrestricted (Instances.BalegasBoundedCounter.D n K).toUpdateSig :=
  unrestricted_of_all (Instances.BalegasBoundedCounter.all_comm n K)
theorem tree : Unrestricted Instances.TreeMove.D.toUpdateSig :=
  unrestricted_of_all Instances.TreeMove.all_comm
theorem aegis : Unrestricted Instances.AegisSheet.D.toUpdateSig :=
  unrestricted_of_all Instances.AegisSheet.all_comm
end Commuting

theorem ordinary_or_set {A : Type} [DecidableEq A] :
    Unrestricted (ORSet.D A).toUpdateSig := by
  intro a b same
  apply ORSet.commute_of_no_conflict
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  change ao = bo at same
  subst bo
  cases ao <;> simp [UpdateSig.replayBefore, EventOrder.Before, ORSet.policy, ORSet.order]

theorem efficient_guarded {A : Type} [DecidableEq A] :
    SplitPolicy.EqualOperationCommutes (Instances.EfficientORSet.D A).toUpdateSig :=
by
  intro a b _ replicas same
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  change ao = bo at same
  subst bo
  cases ao with
  | add x => exact EfficientORSet.NeemScope.adds_commute_of_replica_ne ta ra tb rb x x replicas
  | remove x => exact EfficientORSet.NeemScope.removes_commute ta ra tb rb x x

theorem efficient_not_unrestricted :
    ¬ Unrestricted (Instances.EfficientORSet.D Nat).toUpdateSig := by
  intro h
  exact EfficientORSet.EventSpec.same_replica_adds_noncomm 7 (h (1,0,.add 7) (2,0,.add 7) rfl)

/-- PASS: distinct replicas really retain both birth records. -/
theorem efficient_remote_control :
    Instances.EfficientORSet.update
      (Instances.EfficientORSet.update (∅ : Instances.EfficientORSet.State Nat) (1,0,.add 7))
      (2,1,.add 7) = {(0,1,7), (1,2,7)} := by decide
/-- FAIL companion: the second remote add is not a replacement of the first. -/
theorem efficient_remote_not_projection :
    Instances.EfficientORSet.update
      (Instances.EfficientORSet.update (∅ : Instances.EfficientORSet.State Nat) (1,0,.add 7))
      (2,1,.add 7) ≠ {(1,2,7)} := by decide

/-- Arbitrary overwrite payloads can erase one of the two equal-payload writes. -/
theorem mvr_not_guarded :
    ¬ SplitPolicy.EqualOperationCommutes Instances.MVRLive.D.toUpdateSig := by
  intro h
  have eq := h (1,0,.write 7 [1]) (2,1,.write 7 [1]) (by change (1 : Nat) ≠ 2; decide) (by decide) rfl (∅ : Instances.MVRLive.State)
  have ne : Instances.MVRLive.update
      (Instances.MVRLive.update ∅ (1,0,.write 7 [1])) (2,1,.write 7 [1]) ≠
    Instances.MVRLive.update
      (Instances.MVRLive.update ∅ (2,1,.write 7 [1])) (1,0,.write 7 [1]) := by decide
  exact ne eq

theorem mvr_not_unrestricted : ¬ Unrestricted Instances.MVRLive.D.toUpdateSig :=
  fun h => mvr_not_guarded (guarded_of_unrestricted h)

/-- The raw failing write cannot be honestly minted at any origin state. -/
theorem mvr_self_overwrite_rejected (s : Instances.MVRLive.State) :
    ¬ Instances.MVRLive.canIssue (1,0,.write 7 [1]) s := by
  rintro ⟨fresh,overwrite⟩
  have member : (1 : Nat) ∈ s.image Prod.fst := by
    rw [← overwrite]
    simp [Instances.MVR.overwrites]
  obtain ⟨p,hp,equal⟩ := Finset.mem_image.mp member
  exact fresh p hp equal

/-- Nearby PASS control excludes constant output and universal failure. -/
theorem mvr_empty_overwrite_control :
    Instances.MVRLive.update (Instances.MVRLive.update ∅ (1,0,.write 7 [])) (2,1,.write 7 []) =
      {(1,7),(2,7)} := by decide
theorem mvr_empty_overwrite_not_projection :
    Instances.MVRLive.update (Instances.MVRLive.update ∅ (1,0,.write 7 [])) (2,1,.write 7 []) ≠
      {(2,7)} := by decide
#print axioms add
#print axioms finite
#print axioms delta
#print axioms boolean
#print axioms lww
#print axioms rga
#print axioms balegasBounded
#print axioms tree
#print axioms aegis
#print axioms ordinary_or_set
#print axioms efficient_guarded
#print axioms efficient_not_unrestricted
#print axioms mvr_not_guarded
#print axioms mvr_not_unrestricted
#print axioms mvr_self_overwrite_rejected
end Sal.MRDTs.Paper1.SelfCommutationInstances
