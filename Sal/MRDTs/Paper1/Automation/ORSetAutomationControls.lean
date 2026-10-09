import Sal.MRDTs.Paper1.Automation.ORSetInputs

/-! Independent PASS/FAIL controls for the OR-set author interface.
The broken merge's expected verdict follows from hand-chosen unequal branches.
These controls do not supply registered proofs to either production instance. -/
namespace Sal.MRDTs.Paper1.Automation.ORSetAutomationControls
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open CommonVerification InputDerivation

example : Raw.MergeVCs (ORSet.conflict Nat)
    (ORSet.RawReplay.representation (α := Nat)) (ORSet.RawReplay.scheme (α := Nat)) := by
  mrdt_verify

example : Raw.MergeVCs (EfficientORSet.EventSpec.conflict Nat)
    (EfficientORSet.RawReplay.representation (α := Nat))
    (EfficientORSet.RawReplay.scheme (α := Nat)) := by
  mrdt_verify

/- Construct a fresh ordinary input from raw definitions and comparison data;
do not use its registered input or any cached finite-law declaration. -/
namespace FreshOrdinary
variable {α : Type} [DecidableEq α]
local instance policyData : PolicyData (ORSet.D α) := ⟨ORSet.order⟩
attribute [local policy_expansion_simps] policyData ORSet.D LocalAssembly.ofMRDT
  ORSet.step ORSet.merge ORSet.order ORSet.conflict Op.op Op.rep Op.time
attribute [local mrdt_implementation] ORSet.RawReplay.representation ORSet.ConcreteRep.representation
set_option maxHeartbeats 4000000 in
example : Input (ORSet.D α) (ORSet.conflict α)
    (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α)) := by
  derive_mrdt_input
end FreshOrdinary

/- The new Type-valued mask kit retains the original four semantic maps.
Proof fields may change; these data projections remain definitionally equal. -/
example : (AutomatedEfficientORSet.maskKit (α := Nat)).carrier = id := by rfl
example : (AutomatedEfficientORSet.maskKit (α := Nat)).step =
    Instances.EfficientORSet.update := by rfl
example : (AutomatedEfficientORSet.maskKit (α := Nat)).birth =
    AutomatedEfficientORSet.birth := by rfl
example : (AutomatedEfficientORSet.maskKit (α := Nat)).kill =
    (fun p e => Instances.EfficientORSet.kills p.1 p.2.2 e) := by rfl

def unannotatedMerge (l a b : ORSet.State Nat) : ORSet.State Nat := ORSet.merge l a b

example : True := by
  fail_if_success have unannotated (l a b : ORSet.State Nat) :
      unannotatedMerge l a b = unannotatedMerge l b a := by policy_finite
  trivial

attribute [local policy_expansion_simps] unannotatedMerge ORSet.merge
example (l a b : ORSet.State Nat) :
    unannotatedMerge l a b = unannotatedMerge l b a := by policy_finite

/-- A merge projection of the left branch violates the first finite obligation. -/
def broken : MRDTSig := { ORSet.D Nat with merge := fun _ a _ => a }

abbrev brokenRepresentation : Representation broken := ORSet.RawReplay.representation (α := Nat)
def brokenScheme (C : ReplayContext broken.toUpdateSig) : MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

/- Missing comparison data is rejected before finite proof search. -/
/--
error: derive_mrdt_input needs a PolicyData annotation for the event comparison
-/
#guard_msgs in
example : Input broken (ORSet.conflict Nat) brokenRepresentation brokenScheme := by
  derive_mrdt_input

local instance brokenPolicyData : PolicyData broken := ⟨ORSet.order⟩
attribute [local policy_expansion_simps] brokenPolicyData broken ORSet.D
  ORSet.step ORSet.merge ORSet.order ORSet.conflict Op.op Op.rep Op.time

/- With data present the false finite merge law still blocks derivation. -/
example : True := by
  fail_if_success have falseInput : (Input broken (ORSet.conflict Nat) brokenRepresentation brokenScheme) := by derive_mrdt_input
  trivial

theorem broken_merge_counterexample :
    broken.merge (∅ : ORSet.State Nat) (∅ : ORSet.State Nat) ({(0, 0)} : ORSet.State Nat) ≠
    broken.merge (∅ : ORSet.State Nat) ({(0, 0)} : ORSet.State Nat) (∅ : ORSet.State Nat) := by
  change (∅ : ORSet.State Nat) ≠ {(0, 0)}
  intro eq
  have member : (0, 0) ∈ (∅ : ORSet.State Nat) := by rw [eq]; simp
  simpa using member

theorem broken_has_no_policy_kit :
    ¬ PolicyExpansion.Kit broken (ORSet.conflict Nat) ORSet.order := by
  intro kit
  exact broken_merge_counterexample (kit.comm (∅ : ORSet.State Nat) (∅ : ORSet.State Nat) ({(0, 0)} : ORSet.State Nat))

def counterEvent : Op (ORSet.Update Nat) := (0,0,.add 0)
def counterContext : ReplayContext broken.toUpdateSig where
 L := fun _ => some {counterEvent}
 vis := fun _ _ => False
 timestamps_distinct := by
  intro a b r s r' s' hl ha hl' hb ne
  cases Option.some.inj hl
  cases Option.some.inj hl'
  simp only [Set.mem_singleton_iff] at ha hb
  exact False.elim (ne (ha.trans hb.symm))
 vis_total_same_replica := by
  intro a b r s r' s' hl ha hl' hb ne _
  cases Option.some.inj hl
  cases Option.some.inj hl'
  simp only [Set.mem_singleton_iff] at ha hb
  exact False.elim (ne (ha.trans hb.symm))
theorem broken_has_false_vcs : ¬Raw.MergeVCs (ORSet.conflict Nat) brokenRepresentation brokenScheme := by
 intro vc
 have supported : Supported counterContext {counterEvent} := by
  intro e member
  exact ⟨0,{counterEvent},rfl,member⟩
 have represented : brokenRepresentation counterContext {counterEvent} ({(0,0)} : ORSet.State Nat) := by
  refine ⟨⟨[counterEvent],?_,?_,?_⟩,supported⟩
  · simp [listPermOf]
  · simp [respects]
  · simp [applySeq,counterEvent,ORSet.D,ORSet.step]
 have wrong := vc.init counterContext {counterEvent} ({(0,0)} : ORSet.State Nat) supported
  (by intros a b h; exact h.elim) represented
 change (∅ : ORSet.State Nat) = {(0,0)} at wrong
 have member : (0,0) ∈ (∅ : ORSet.State Nat) := by rw [wrong]; simp
 simpa using member

example : True := by
  fail_if_success have wrong :
      broken.merge (∅ : ORSet.State Nat) (∅ : ORSet.State Nat) ({(0, 0)} : ORSet.State Nat) =
      broken.merge (∅ : ORSet.State Nat) ({(0, 0)} : ORSet.State Nat) (∅ : ORSet.State Nat) := by policy_finite
  trivial

/- Completed production VC proofs cannot enter instance search. -/
/--
error: register_mrdt_input requires CommonVerification.Input; completed VC theorems cannot be registered
-/
#guard_msgs in
register_mrdt_input Sal.MRDTs.Paper1.Automation.CommonVerification.verify

end Sal.MRDTs.Paper1.Automation.ORSetAutomationControls
