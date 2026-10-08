import CommonInstances

/-! PASS/FAIL controls for finite helper selection, registration boundaries and
precise missing annotations. Expected values are hand-derived. -/
namespace NeemExpansion.CommonVerificationControls
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 ConcreteMRDT
open CommonVerification

example (a b : Nat) : max a (max a b) = max a b := by mrdt_finite
example : True := by
  fail_if_success have wrong : max (0 : Nat) 1 = 0 := by mrdt_finite
  trivial

/-- A raw carrier whose shared equation fails: merge ignores its ancestor,
and adding the last event separately to both branches duplicates the delta. -/
def D : MRDTSig where
  State := Nat
  dec_state := inferInstance
  init := 0
  AppOp := Unit
  dec_op := inferInstance
  Query := Unit
  Value := Nat
  update := fun s _ => s+1
  query := fun s _ => s
  merge := fun _ a b => a+b

theorem commute (a b : Op Unit) : D.toUpdateSig.commutes a b := by intro s; rfl
abbrev P := commutingPolicy Unit
abbrev R := CommutingPort.representation D
abbrev M := CommutingPort.scheme (D := D) commute

/--
error: tactic 'aesop' failed, made no progress
Initial goal:
  case input
  ⊢ Input D P R M
-/
#guard_msgs in
example : Raw.MergeVCs P R M := by mrdt_obligations

abbrev Shared := ∀ B t₀ t₁ t₂ e,
  D.merge (D.merge B t₀ (D.update B e))
    (D.merge B t₁ (D.update B e)) (D.merge B t₂ (D.update B e)) =
  D.merge B (D.merge t₀ t₁ t₂) (D.update B e)

def incomplete (shared : Shared) : Input D P R M :=
  .commuting commute {
    comm := by intros; simp only [D]; omega
    initial := by intros; simp [D]
    causalSeed := by intros; rfl
    localEquation := by intros; simp only [D]; omega
    shared := shared } rfl rfl rfl
register_mrdt_input incomplete

/--
error: unsolved goals
case input
⊢ Shared
-/
#guard_msgs in
example : Raw.MergeVCs P R M := by mrdt_obligations

example : ¬Shared := by
  intro shared
  have wrong := shared (0 : Nat) (0 : Nat) (0 : Nat) (0 : Nat) ((0,0,()) : Op Unit)
  change (2 : Nat) = 1 at wrong
  omega
example : True := by
  fail_if_success have falseVC : Raw.MergeVCs P R M := by mrdt_verify
  trivial

/--
error: register_mrdt_input requires CommonVerification.Input; completed VC theorems cannot be registered
-/
#guard_msgs in
register_mrdt_input NeemExpansion.CommonInstances.lww

def fromCorrectness (_vc : Raw.MergeVCs P R M) (shared : Shared) : Input D P R M :=
  incomplete shared
/--
error: register_mrdt_input rejects a completed correctness premise
-/
#guard_msgs in
register_mrdt_input fromCorrectness
abbrev Completed := Raw.MergeVCs P R M
def fromAlias (_vc : Completed) (shared : Shared) : Input D P R M := incomplete shared
/--
error: register_mrdt_input rejects a completed correctness premise
-/
#guard_msgs in
register_mrdt_input fromAlias
end NeemExpansion.CommonVerificationControls
