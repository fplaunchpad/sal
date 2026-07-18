import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3H_V

/-!
# The flat identity-Eq capstone over the widened LTS `Step3V` (task #90)

*Additive; modifies no existing file; 0 `sorry`.*

`flat_ra_linearizable3_eq` re-derived at every configuration reachable in the ternary
system **with the criss-cross gate lifted** (`labeledTS3V`): every flat MRDT with a
closure-indexed Join Lemma inherits `IsRALinearizable3Eq` over `Step3V`,
unconditionally.  Nothing per-datatype moves: the flat join context (`flatHonJ`) is a
STRUCTURAL field of every configuration (no reachability induction), the witness
discipline is `⊤`, and `qapplicable` is the lift of `⊤` — so the honest premises of
`RA_linearizable_up_to_eq_H_V` are exactly as trivial as the gated theorem's.
-/

namespace Sal.ConditionedMRDTs.FlatGeneric

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs (Configuration initConfig labeledTS3V JoinLemma3C fullClosure)

variable {D : ConditionedMRDTSig}

/-- **The flat capstone over `Step3V`** — every flat MRDT with a closure-indexed Join
Lemma is per-version RA-linearizable (at the identity `≈`) at every configuration
reachable with virtual-LCA merges enabled; the honest-execution premises are trivial or
structural, exactly as in the gated `flat_ra_linearizable3_eq`. -/
theorem flat_ra_linearizable3_eq_V
    (hInvT : ∀ s : D.State, D.Inv s)
    (hAppT : ∀ (o : Op D.AppOp) (s : D.State), D.applicable o s)
    (hJoin : JoinLemma3C D (fullClosure D.toCRDTSig))
    (C : Configuration (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
      (congVCEq D) (invInvVCTop D)))
    (hReach : (labeledTS3V (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
        (congVCEq D) (invInvVCTop D))).ReachableFrom
      (initConfig (QSig (eqOfEq D) (WTop D) (invPresTop hInvT)
        (congVCEq D) (invInvVCTop D)) trivial) C) :
    IsRALinearizable3Eq (eqOfEq D) (WTop D) (invPresTop hInvT)
      (congVCEq D) (invInvVCTop D) C :=
  RA_linearizable_up_to_eq_H_V (H := fun _ => True) (flatHonJ D) (eqOfEq D) (WTop D)
    (invPresTop hInvT) (congVCEq D) (invInvVCTop D)
    (fun {_ s'} _ _ => hInvT s')
    (eqJoinH_of_joinC hInvT hJoin)
    (fun {C₀} _ => flatHonJ_of_config hInvT C₀)
    trivial
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => ⟨qapplicable_top hAppT _ _, fun _ _ => trivial⟩)
    C hReach

/-! ## Axiom audit -/

#print axioms flat_ra_linearizable3_eq_V

end Sal.ConditionedMRDTs.FlatGeneric
