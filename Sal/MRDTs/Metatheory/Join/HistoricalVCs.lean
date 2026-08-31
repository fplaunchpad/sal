import Sal.MRDTs.Metatheory.Adequacy
import Sal.MRDTs.Metatheory.Join.Assoc_CounterModel

/-!
# The historical 24-VC route

This file tests the conjecture that the 24 verification conditions used by
the original bottom-up linearization argument imply the corrected,
set-relative ternary Join lemma.

The declarations below transcribe the ternary VC statements from the Sal
MRDT artifact (`papoc2026`, `CaseStudies/Fstar_like_implementations/MRDTs/SAL`).
They deliberately exclude the later binary-emulation additions
`rc_non_comm_directional`, `cond_comm_lift`, `merge_init`,
`merge_peel_comm`, and `shared_peel_1op`.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

section

variable (D : MRDTSig) [ReplayPolicy D.toUpdateSig]

abbrev historicalDistinct (o₁ o₂ : Op D.AppOp) : Prop :=
  @distinctOps D.toUpdateSig o₁ o₂

abbrev historicalDifferentReplicas (o₁ o₂ : Op D.AppOp) : Prop :=
  @differentReplicas D.toUpdateSig o₁ o₂

/-- The 24 conditions in the historical ternary MRDT artifact: three
update/order conditions, two merge laws, and nineteen base/inductive
instances of the BottomUp template. -/
structure HistoricalVCs24 : Prop where
  rc_non_comm :
    ∀ o₁ o₂ : Op D.AppOp,
      historicalDistinct D o₁ o₂ → historicalDifferentReplicas D o₁ o₂ →
      (D.toUpdateSig.replayOrder o₁ o₂ = RcRes.Either ↔
        D.toUpdateSig.commutes o₁ o₂)
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      historicalDistinct D o₁ o₂ → historicalDistinct D o₂ o₃ →
      ¬ (D.toUpdateSig.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∧
         D.toUpdateSig.replayOrder o₂ o₃ = RcRes.Fst_then_snd)
  cond_comm_base :
    ∀ (s : D.State) (o₁ o₂ o₃ : Op D.AppOp),
      historicalDistinct D o₁ o₂ → historicalDistinct D o₂ o₃ → historicalDistinct D o₁ o₃ →
      D.toUpdateSig.replayOrder o₁ o₂ = RcRes.Fst_then_snd →
      D.toUpdateSig.replayOrder o₂ o₃ ≠ RcRes.Either →
      D.update (D.update (D.update s o₁) o₂) o₃ =
        D.update (D.update (D.update s o₂) o₁) o₃
  merge_comm :
    ∀ l a b : D.State, D.merge l a b = D.merge l b a
  merge_idem :
    ∀ s : D.State, D.merge s s s = s

  base_2op :
    ∀ o₁ o₂ : Op D.AppOp,
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ → historicalDistinct D o₁ o₂ →
      D.merge D.init (D.update D.init o₁) (D.update D.init o₂) =
        D.update (D.merge D.init D.init (D.update D.init o₂)) o₁
  ind_base_2op :
    ∀ (l : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ol → historicalDistinct D o₂ ol →
      D.merge (D.update l ol) (D.update (D.update l ol) o₁) (D.update l ol) =
        D.update (D.merge (D.update l ol) (D.update l ol) (D.update l ol)) o₁ →
      D.merge l (D.update l o₁) (D.update l o₂) =
        D.update (D.merge l l (D.update l o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update l ol) o₁)
          (D.update (D.update l ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update l ol)
          (D.update (D.update l ol) o₂)) o₁
  inter_right_base_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ →
      D.toUpdateSig.replayOrder ob o₁ = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ob → historicalDistinct D o₁ ol →
      historicalDistinct D o₂ ob → historicalDistinct D o₂ ol → historicalDistinct D ob ol →
      D.merge l (D.update a o₁) (D.update b o₂) =
        D.update (D.merge l a (D.update b o₂)) o₁ →
      D.merge l (D.update a o₁) (D.update (D.update b ob) o₂) =
        D.update (D.merge l a (D.update (D.update b ob) o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update (D.update b ob) ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update (D.update b ob) ol) o₂)) o₁
  inter_left_base_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D o₂ o₁ → historicalDifferentReplicas D ob ol →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ob → historicalDistinct D o₁ ol →
      historicalDistinct D o₂ ob → historicalDistinct D o₂ ol → historicalDistinct D ob ol →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update (D.update a ob) ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update (D.update a ob) ol)
          (D.update (D.update b ol) o₂)) o₁
  inter_right_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ →
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      (D.toUpdateSig.replayOrder o ob ≠ RcRes.Either ∨
       D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ob → historicalDistinct D o₁ ol →
      historicalDistinct D o₁ o → historicalDistinct D o₂ ob → historicalDistinct D o₂ ol →
      historicalDistinct D o₂ o → historicalDistinct D ob ol → historicalDistinct D ob o →
      historicalDistinct D ol o → historicalDifferentReplicas D o ol →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update (D.update b ob) ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update (D.update b ob) ol) o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update (D.update (D.update b o) ob) ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update (D.update (D.update b o) ob) ol) o₂)) o₁
  inter_left_2op :
    ∀ (l a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D o₂ o₁ → historicalDifferentReplicas D ob ol →
      (D.toUpdateSig.replayOrder o ob ≠ RcRes.Either ∨
       D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ob → historicalDistinct D o₁ ol →
      historicalDistinct D o₁ o → historicalDistinct D o₂ ob → historicalDistinct D o₂ ol →
      historicalDistinct D o₂ o → historicalDistinct D ob ol → historicalDistinct D ob o →
      historicalDistinct D ol o → historicalDifferentReplicas D o ol →
      D.merge (D.update l ol) (D.update (D.update (D.update a ob) ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update (D.update a ob) ol)
          (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update l ol)
          (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol)
          (D.update (D.update (D.update a o) ob) ol)
          (D.update (D.update b ol) o₂)) o₁
  inter_base_2op :
    ∀ (l a b : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ ol → historicalDistinct D o₂ ol →
      (∃ o, D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update a ol) (D.update b ol)) o₁ →
      D.merge l (D.update a o₁) (D.update b o₂) =
        D.update (D.merge l a (D.update b o₂)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update b ol) o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update b ol) o₂)) o₁
  ind_right_2op :
    ∀ (l a b : D.State) (o₁ o₂ o₂' : Op D.AppOp),
      D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      historicalDifferentReplicas D o₁ o₂ →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ o₂' → historicalDistinct D o₂ o₂' →
      D.merge l (D.update a o₁) (D.update b o₂) =
        D.update (D.merge l a (D.update b o₂)) o₁ →
      D.merge l (D.update a o₁) (D.update (D.update b o₂') o₂) =
        D.update (D.merge l a (D.update (D.update b o₂') o₂)) o₁
  ind_left_2op :
    ∀ (l a b : D.State) (o₁ o₂ o₁' : Op D.AppOp),
      (D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨
       D.toUpdateSig.replayOrder o₂ o₁ = RcRes.Either) →
      historicalDifferentReplicas D o₁ o₂ →
      historicalDistinct D o₁ o₂ → historicalDistinct D o₁ o₁' → historicalDistinct D o₂ o₁' →
      D.merge l (D.update a o₁) (D.update b o₂) =
        D.update (D.merge l a (D.update b o₂)) o₁ →
      D.merge l (D.update (D.update a o₁') o₁) (D.update b o₂) =
        D.update (D.merge l (D.update a o₁') (D.update b o₂)) o₁

  base_1op :
    ∀ o₁ : Op D.AppOp,
      D.merge D.init (D.update D.init o₁) D.init =
        D.update (D.merge D.init D.init D.init) o₁
  ind_base_1op :
    ∀ (l : D.State) (o₁ ol : Op D.AppOp),
      historicalDistinct D o₁ ol →
      (historicalDifferentReplicas D o₁ ol ∨ ol.time < o₁.time) →
      D.merge l (D.update l o₁) l = D.update (D.merge l l l) o₁ →
      D.merge (D.update l ol) (D.update (D.update l ol) o₁) (D.update l ol) =
        D.update (D.merge (D.update l ol) (D.update l ol) (D.update l ol)) o₁
  inter_right_base_1op :
    ∀ (l a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      historicalDistinct D o₁ ob → historicalDistinct D o₁ ol → historicalDistinct D ob ol →
      (D.toUpdateSig.replayOrder ob o₁ = RcRes.Fst_then_snd →
        D.merge l (D.update a o₁) (D.update b ob) =
          D.update (D.merge l a (D.update b ob)) o₁) →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update b ob) ol) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update b ob) ol)) o₁
  inter_left_base_1op :
    ∀ (l a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      historicalDistinct D o₁ ob → historicalDistinct D o₁ ol → historicalDistinct D ob ol →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update l ol) (D.update (D.update (D.update a ob) ol) o₁)
          (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update (D.update a ob) ol)
          (D.update b ol)) o₁
  inter_right_1op :
    ∀ (l a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      (D.toUpdateSig.replayOrder o ob ≠ RcRes.Either ∨
       D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      historicalDistinct D o₁ ob → historicalDistinct D o₁ ol → historicalDistinct D o₁ o →
      historicalDistinct D ob ol → historicalDistinct D ob o → historicalDistinct D ol o →
      historicalDifferentReplicas D o ol →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update b ob) ol) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update b ob) ol)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁)
          (D.update (D.update (D.update b o) ob) ol) =
        D.update (D.merge (D.update l ol) (D.update a ol)
          (D.update (D.update (D.update b o) ob) ol)) o₁
  inter_left_1op :
    ∀ (l a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.toUpdateSig.replayOrder ob ol = RcRes.Fst_then_snd →
      historicalDifferentReplicas D ob ol →
      (D.toUpdateSig.replayOrder o ob ≠ RcRes.Either ∨
       D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      historicalDistinct D o₁ ob → historicalDistinct D o₁ ol → historicalDistinct D o₁ o →
      historicalDistinct D ob ol → historicalDistinct D ob o → historicalDistinct D ol o →
      historicalDifferentReplicas D o ol →
      D.merge (D.update l ol) (D.update (D.update (D.update a ob) ol) o₁)
          (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update (D.update a ob) ol)
          (D.update b ol)) o₁ →
      D.merge (D.update l ol)
          (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
          (D.update b ol) =
        D.update (D.merge (D.update l ol)
          (D.update (D.update (D.update a o) ob) ol) (D.update b ol)) o₁
  inter_base_1op :
    ∀ (l a b : D.State) (o₁ ol oi : Op D.AppOp),
      historicalDistinct D o₁ ol → historicalDistinct D o₁ oi → historicalDistinct D ol oi →
      (∃ o, D.toUpdateSig.replayOrder o ol = RcRes.Fst_then_snd) →
      (∃ o, D.toUpdateSig.replayOrder o oi = RcRes.Fst_then_snd) →
      D.merge (D.update l oi) (D.update (D.update a oi) o₁) (D.update b oi) =
        D.update (D.merge (D.update l oi) (D.update a oi) (D.update b oi)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a ol) o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update (D.update l oi) ol)
          (D.update (D.update (D.update a oi) ol) o₁)
          (D.update (D.update b oi) ol) =
        D.update (D.merge (D.update (D.update l oi) ol)
          (D.update (D.update a oi) ol) (D.update (D.update b oi) ol)) o₁
  ind_left_1op :
    ∀ (l a b : D.State) (o₁ o₁' ol : Op D.AppOp),
      historicalDistinct D o₁ o₁' → historicalDistinct D o₁ ol → historicalDistinct D o₁' ol →
      D.merge (D.update l ol) (D.update a o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) a (D.update b ol)) o₁ →
      D.merge (D.update l ol) (D.update (D.update a o₁') o₁) (D.update b ol) =
        D.update (D.merge (D.update l ol) (D.update a o₁') (D.update b ol)) o₁
  ind_right_1op :
    ∀ (l a b : D.State) (o₂ o₂' ol : Op D.AppOp),
      historicalDistinct D o₂ o₂' → historicalDistinct D o₂ ol → historicalDistinct D o₂' ol →
      D.merge (D.update l ol) (D.update a ol) (D.update b o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol) b) o₂ →
      D.merge (D.update l ol) (D.update a ol) (D.update (D.update b o₂') o₂) =
        D.update (D.merge (D.update l ol) (D.update a ol) (D.update b o₂')) o₂
  lem_0op :
    ∀ (l a b : D.State) (ol : Op D.AppOp),
      D.merge (D.update l ol) (D.update a ol) (D.update b ol) =
        D.update (D.merge l a b) ol

end

/-- `Join` with the replay-policy dictionary made explicit. The current
framework declaration has type `MRDTSig → Prop`: its section-local policy was
resolved to the default instance while elaborating the body. This formulation
states the intended comparison with the *same* policy on both sides. -/
def JoinWithPolicy (D : MRDTSig)
    (P : ReplayPolicy D.toUpdateSig) : Prop :=
  ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    @IsCanonicalState D.toUpdateSig P C (ev₁ ∩ ev₂) s₀ →
    @IsCanonicalState D.toUpdateSig P C ev₁ s₁ →
    @IsCanonicalState D.toUpdateSig P C ev₂ s₂ →
    @IsCanonicalState D.toUpdateSig P C (ev₁ ∪ ev₂) (D.merge s₀ s₁ s₂)

/-! ## Falsification model

The state remembers only whether the last update was `add` (`true`) or `rem`
(`false`). Ternary merge ignores its GCA and joins the two branch bits with
Boolean disjunction. This is the flag projection of `AWSetF`, isolated so the
historical VCs are finite and executable.
-/

noncomputable def HistoricalFlag : MRDTSig where
  State := Bool
  dec_state := inferInstance
  init := false
  AppOp := AWOp
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := fun _ e => awFlag e
  merge := fun _ a b => a || b
  query := fun s _ => s

instance : ReplayPolicy HistoricalFlag.toUpdateSig where
  order := awRc

@[simp] theorem HistoricalFlag_update (s : HistoricalFlag.State)
    (e : Op HistoricalFlag.AppOp) :
    HistoricalFlag.update s e = awFlag e := rfl

@[simp] theorem HistoricalFlag_merge (l a b : HistoricalFlag.State) :
    HistoricalFlag.merge l a b = (a || b) := rfl

@[simp] theorem HistoricalFlag_replayOrder :
    HistoricalFlag.toUpdateSig.replayOrder = awRc := rfl

def historicalFlagAdd : Op HistoricalFlag.AppOp := (0, 0, AWOp.add)
def historicalFlagRem : Op HistoricalFlag.AppOp := (1, 0, AWOp.rem)

/-- **Negative control:** the historical GCA-induction VC rejects the
last-writer flag countermodel. The shared `add` is in the GCA and the local
`rem` is peeled from one branch; the VC's premise holds at `false`, while its
conclusion would equate `true` and `false`. -/
theorem HistoricalFlag_not_historicalVCs24 :
    ¬ HistoricalVCs24 HistoricalFlag := by
  intro h
  have bad := h.ind_base_1op false historicalFlagRem historicalFlagAdd
    (by simp [historicalDistinct, distinctOps, historicalFlagRem,
      historicalFlagAdd, Op.time])
    (Or.inr (by simp [historicalFlagRem, historicalFlagAdd, Op.time]))
    (by simp [HistoricalFlag, historicalFlagRem, awFlag])
  simp [HistoricalFlag, historicalFlagAdd, historicalFlagRem, awFlag] at bad

/-! A degenerate unit-state MRDT is the positive harness control: all 24 VCs
hold and Join is non-vacuously inhabited for every supported finite event set.
-/

noncomputable def HistoricalUnit : MRDTSig where
  State := Unit
  dec_state := inferInstance
  init := ()
  AppOp := Unit
  dec_op := inferInstance
  Query := Unit
  Value := Unit
  update := fun _ _ => ()
  merge := fun _ _ _ => ()
  query := fun _ _ => ()

noncomputable instance : ReplayPolicy HistoricalUnit.toUpdateSig :=
  ReplayPolicy.unconstrained _

@[simp] theorem HistoricalUnit_replayOrder
    (o₁ o₂ : Op HistoricalUnit.AppOp) :
    HistoricalUnit.toUpdateSig.replayOrder o₁ o₂ = RcRes.Either := rfl

theorem HistoricalUnit_historicalVCs24 : HistoricalVCs24 HistoricalUnit := by
  constructor
  case rc_non_comm =>
    intro o₁ o₂ _ _
    rw [HistoricalUnit_replayOrder]
    constructor
    · intro _ _
      rfl
    · intro _
      rfl
  case no_rc_chain =>
    intros
    simp [HistoricalUnit_replayOrder]
  case merge_idem =>
    intro s
    cases s
    rfl
  all_goals
    intros
    simp_all [HistoricalUnit, historicalDistinct,
      historicalDifferentReplicas, distinctOps, differentReplicas]

/-- **Positive control:** the same unit model satisfies the target Join lemma. -/
theorem HistoricalUnit_join : Join HistoricalUnit := by
  intro C ev₁ ev₂ s₀ s₁ s₂ _ _ _ _ _ _ _ hc₁ hc₂
  obtain ⟨π₁, hp₁, _, _⟩ := hc₁
  obtain ⟨π₂, hp₂, _, _⟩ := hc₂
  let π := π₁ ++ π₂.filter (fun a => decide (a ∉ π₁))
  have hp : listPermOf π (ev₁ ∪ ev₂) := listPermOf_union hp₁ hp₂
  refine ⟨π, hp, ?_, ?_⟩
  · unfold respects
    induction π with
    | nil => exact List.Pairwise.nil
    | cons x xs ih =>
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro y _ hlo
      rcases hlo with ⟨_, hnc⟩ | ⟨_, _, hrc, _⟩
      · exact hnc (fun _ => rfl)
      · rw [HistoricalUnit_replayOrder] at hrc
        contradiction
  · have unit_state : ∀ s : HistoricalUnit.State,
        s = HistoricalUnit.init := by
      intro s
      cases s
      rfl
    exact (unit_state _).trans (unit_state _).symm

/-! ## Resolver-coherence falsification gate -/

inductive HistoricalGapState where
  | initial
  | add
  | rem
  | conflict
  deriving DecidableEq

def historicalGapUpdate (_ : HistoricalGapState) (e : Op AWOp) :
    HistoricalGapState :=
  match e.op with
  | .add => .add
  | .rem => .rem

/-- A symmetric three-way merge. An unchanged branch contributes the other
branch; two distinct changes produce a state that no update produces. -/
def historicalGapMerge (l a b : HistoricalGapState) : HistoricalGapState :=
  if a = l then b
  else if b = l then a
  else if a = b then a
  else .conflict

/-- Deliberately incoherent: both directions of a conflicting pair return
`Snd_then_fst`; no pair ever returns `Fst_then_snd`. -/
def historicalGapRc (e₁ e₂ : Op AWOp) : RcRes :=
  if e₁.op = e₂.op then .Either else .Snd_then_fst

noncomputable def HistoricalGap : MRDTSig where
  State := HistoricalGapState
  dec_state := inferInstance
  init := .initial
  AppOp := AWOp
  dec_op := inferInstance
  Query := Unit
  Value := HistoricalGapState
  update := historicalGapUpdate
  merge := historicalGapMerge
  query := fun s _ => s

instance : ReplayPolicy HistoricalGap.toUpdateSig where
  order := historicalGapRc

@[simp] theorem HistoricalGap_update (s : HistoricalGap.State)
    (e : Op HistoricalGap.AppOp) :
    HistoricalGap.update s e = historicalGapUpdate s e := rfl

@[simp] theorem HistoricalGap_merge (l a b : HistoricalGap.State) :
    HistoricalGap.merge l a b = historicalGapMerge l a b := rfl

@[simp] theorem HistoricalGap_replayOrder
    (e₁ e₂ : Op HistoricalGap.AppOp) :
    HistoricalGap.toUpdateSig.replayOrder e₁ e₂ = historicalGapRc e₁ e₂ := rfl

theorem historicalGapRc_ne_fst (e₁ e₂ : Op AWOp) :
    historicalGapRc e₁ e₂ ≠ RcRes.Fst_then_snd := by
  simp only [historicalGapRc]
  split <;> simp

theorem historicalGapMerge_comm (l a b : HistoricalGapState) :
    historicalGapMerge l a b = historicalGapMerge l b a := by
  cases l <;> cases a <;> cases b <;> decide

theorem historicalGapMerge_idem (s : HistoricalGapState) :
    historicalGapMerge s s s = s := by
  cases s <;> decide

/-- The incoherent finite model passes the exact historical bundle. -/
theorem HistoricalGap_historicalVCs24 : HistoricalVCs24 HistoricalGap := by
  constructor
  case rc_non_comm =>
    rintro ⟨t₁, r₁, k₁⟩ ⟨t₂, r₂, k₂⟩ _ _
    rw [HistoricalGap_replayOrder]
    cases k₁ <;> cases k₂ <;>
      simp [historicalGapRc, HistoricalGap,
        UpdateSig.commutes, historicalGapUpdate, Op.op] <;>
      exact ⟨HistoricalGapState.initial⟩
  case no_rc_chain =>
    intro o₁ o₂ o₃ _ _ h
    rw [HistoricalGap_replayOrder] at h
    exact historicalGapRc_ne_fst o₁ o₂ h.1
  case cond_comm_base =>
    intro s o₁ o₂ o₃ _ _ _ h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o₁ o₂ h)
  case merge_comm =>
    exact historicalGapMerge_comm
  case merge_idem =>
    exact historicalGapMerge_idem
  case base_2op =>
    rintro ⟨t₁, r₁, k₁⟩ ⟨t₂, r₂, k₂⟩ h _ _
    rw [HistoricalGap_replayOrder] at h
    cases k₁ <;> cases k₂ <;>
      simp_all [historicalGapRc, HistoricalGap,
        historicalGapUpdate, historicalGapMerge, Op.op]
  case ind_base_2op =>
    rintro l ⟨t₁, r₁, k₁⟩ ⟨t₂, r₂, k₂⟩ ⟨tl, rl, kl⟩ h _ _ _ _ _ ih
    rw [HistoricalGap_replayOrder] at h
    cases l <;> cases k₁ <;> cases k₂ <;> cases kl <;>
      simp_all [historicalGapRc, HistoricalGap,
        historicalGapUpdate, historicalGapMerge, Op.op]
  case inter_right_base_2op =>
    intro l a b o₁ o₂ ob ol _ _ h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob o₁ h)
  case inter_left_base_2op =>
    intro l a b o₁ o₂ ob ol h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o₂ o₁ h)
  case inter_right_2op =>
    intro l a b o₁ o₂ ob ol o _ _ h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob ol h)
  case inter_left_2op =>
    intro l a b o₁ o₂ ob ol o h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o₂ o₁ h)
  case inter_base_2op =>
    intro l a b o₁ o₂ ol _ _ _ _ _ hex
    obtain ⟨o, h⟩ := hex
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o ol h)
  case ind_right_2op =>
    intro l a b o₁ o₂ o₂' h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o₂ o₁ h)
  case ind_left_2op =>
    rintro l a b ⟨t₁, r₁, k₁⟩ ⟨t₂, r₂, k₂⟩ ⟨t₁', r₁', k₁'⟩ h _ _ _ _ ih
    rw [HistoricalGap_replayOrder] at h
    cases l <;> cases a <;> cases b <;> cases k₁ <;> cases k₂ <;> cases k₁' <;>
      simp_all [historicalGapRc, HistoricalGap,
        historicalGapUpdate, historicalGapMerge, Op.op]
  case base_1op =>
    rintro ⟨t₁, r₁, k₁⟩
    cases k₁ <;>
      simp [HistoricalGap, historicalGapUpdate, historicalGapMerge, Op.op]
  case ind_base_1op =>
    rintro l ⟨t₁, r₁, k₁⟩ ⟨tl, rl, kl⟩ _ _ ih
    cases l <;> cases k₁ <;> cases kl <;>
      simp_all [HistoricalGap, historicalGapUpdate, historicalGapMerge, Op.op]
  case inter_right_base_1op =>
    intro l a b o₁ ob ol h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob ol h)
  case inter_left_base_1op =>
    intro l a b o₁ ob ol h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob ol h)
  case inter_right_1op =>
    intro l a b o₁ ob ol o h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob ol h)
  case inter_left_1op =>
    intro l a b o₁ ob ol o h
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst ob ol h)
  case inter_base_1op =>
    intro l a b o₁ ol oi _ _ _ hex
    obtain ⟨o, h⟩ := hex
    rw [HistoricalGap_replayOrder] at h
    exact False.elim (historicalGapRc_ne_fst o ol h)
  case ind_left_1op =>
    rintro l a b ⟨t₁, r₁, k₁⟩ ⟨t₁', r₁', k₁'⟩ ⟨tl, rl, kl⟩ _ _ _ ih
    cases l <;> cases a <;> cases b <;> cases k₁ <;> cases k₁' <;> cases kl <;>
      simp_all [HistoricalGap, historicalGapUpdate, historicalGapMerge, Op.op]
  case ind_right_1op =>
    rintro l a b ⟨t₂, r₂, k₂⟩ ⟨t₂', r₂', k₂'⟩ ⟨tl, rl, kl⟩ _ _ _ ih
    cases l <;> cases a <;> cases b <;> cases k₂ <;> cases k₂' <;> cases kl <;>
      simp_all [HistoricalGap, historicalGapUpdate, historicalGapMerge, Op.op]
  case lem_0op =>
    rintro l a b ⟨tl, rl, kl⟩
    cases l <;> cases a <;> cases b <;> cases kl <;>
      simp [HistoricalGap, historicalGapUpdate, historicalGapMerge, Op.op]

/-! ### Failure of the set-relative ternary Join lemma -/

def historicalGapAdd : Op HistoricalGap.AppOp := (0, 0, .add)
def historicalGapRem : Op HistoricalGap.AppOp := (1, 1, .rem)

def historicalGapEv₁ : Set (Op HistoricalGap.AppOp) := {historicalGapAdd}
def historicalGapEv₂ : Set (Op HistoricalGap.AppOp) := {historicalGapRem}

private theorem historicalGap_L_cases (r : Replica)
    (s : Set (Op HistoricalGap.AppOp))
    (hL : (if r = 0 then some historicalGapEv₁
      else if r = 1 then some historicalGapEv₂ else none) = some s) :
    ∀ x ∈ s, x = historicalGapAdd ∨ x = historicalGapRem := by
  intro x hx
  by_cases h₀ : r = 0
  · rw [if_pos h₀, Option.some.injEq] at hL
    rw [← hL] at hx
    exact Or.inl hx
  · by_cases h₁ : r = 1
    · rw [if_neg h₀, if_pos h₁, Option.some.injEq] at hL
      rw [← hL] at hx
      exact Or.inr hx
    · rw [if_neg h₀, if_neg h₁] at hL
      contradiction

noncomputable def historicalGapConfig :
    Sal.MRDTs.Foundation.ReplayContext HistoricalGap.toUpdateSig where
  L := fun r =>
    if r = 0 then some historicalGapEv₁
    else if r = 1 then some historicalGapEv₂
    else none
  vis := fun _ _ => False
  timestamps_distinct := by
    intro a b r s r' s' hL ha hL' hb hne
    rcases historicalGap_L_cases r s hL a ha with rfl | rfl <;>
      rcases historicalGap_L_cases r' s' hL' b hb with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [historicalGapAdd, historicalGapRem]
  vis_total_same_replica := by
    intro a b r s r' s' hL ha hL' hb hne hrep
    rcases historicalGap_L_cases r s hL a ha with rfl | rfl <;>
      rcases historicalGap_L_cases r' s' hL' b hb with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | simp [historicalGapAdd, historicalGapRem] at hrep

private theorem historicalGap_in₁ :
    ∀ x ∈ historicalGapEv₁, x ∈ historicalGapConfig.events := by
  intro x hx
  exact ⟨0, historicalGapEv₁, by simp [historicalGapConfig], hx⟩

private theorem historicalGap_in₂ :
    ∀ x ∈ historicalGapEv₂, x ∈ historicalGapConfig.events := by
  intro x hx
  exact ⟨1, historicalGapEv₂, by simp [historicalGapConfig], hx⟩

private theorem historicalGap_canonical₀
    (P : ReplayPolicy HistoricalGap.toUpdateSig) :
    @IsCanonicalState HistoricalGap.toUpdateSig P historicalGapConfig
      (historicalGapEv₁ ∩ historicalGapEv₂) HistoricalGapState.initial := by
  refine ⟨[], ⟨List.nodup_nil, ?_⟩, List.Pairwise.nil, rfl⟩
  intro x
  constructor
  · simp
  · rintro ⟨h₁, h₂⟩
    have hx₁ : x = historicalGapAdd := h₁
    have hx₂ : x = historicalGapRem := h₂
    exact absurd (hx₁.symm.trans hx₂) (by
      simp [historicalGapAdd, historicalGapRem])

private theorem historicalGap_canonical₁
    (P : ReplayPolicy HistoricalGap.toUpdateSig) :
    @IsCanonicalState HistoricalGap.toUpdateSig P historicalGapConfig
      historicalGapEv₁ HistoricalGapState.add := by
  refine ⟨[historicalGapAdd],
    ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, ?_⟩
  · simp [historicalGapEv₁]
  · simp [applySeq, HistoricalGap, historicalGapAdd,
      historicalGapUpdate, Op.op]

private theorem historicalGap_canonical₂
    (P : ReplayPolicy HistoricalGap.toUpdateSig) :
    @IsCanonicalState HistoricalGap.toUpdateSig P historicalGapConfig
      historicalGapEv₂ HistoricalGapState.rem := by
  refine ⟨[historicalGapRem],
    ⟨List.nodup_singleton _, fun x => ?_⟩,
    List.pairwise_singleton _ _, ?_⟩
  · simp [historicalGapEv₂]
  · simp [applySeq, HistoricalGap, historicalGapRem,
      historicalGapUpdate, Op.op]

/-- **Counterexample:** the exact historical bundle does not imply the
corrected ternary Join lemma. The old conditions allow a replay policy that
returns `Snd_then_fst` in both directions. On two concurrent conflicting
updates, both branch states are canonical, but ternary merge produces
`conflict`, a state no sequential fold can produce. -/
theorem HistoricalGap_not_joinWithPolicy
    (P : ReplayPolicy HistoricalGap.toUpdateSig) :
    ¬ JoinWithPolicy HistoricalGap P := by
  intro hJoin
  have h := hJoin historicalGapConfig historicalGapEv₁ historicalGapEv₂
    HistoricalGapState.initial HistoricalGapState.add HistoricalGapState.rem
    (fun h => h.elim) (fun _ h => h.elim)
    historicalGap_in₁ historicalGap_in₂
    (fun _ _ h => h.elim) (fun _ _ h => h.elim)
    (historicalGap_canonical₀ P) (historicalGap_canonical₁ P)
    (historicalGap_canonical₂ P)
  obtain ⟨ρ, hp, _, hf⟩ := h
  have hpair : listPermOf [historicalGapAdd, historicalGapRem]
      (historicalGapEv₁ ∪ historicalGapEv₂) := by
    constructor
    · simp [historicalGapAdd, historicalGapRem]
    · intro x
      simp [historicalGapEv₁, historicalGapEv₂, or_comm]
  have hlen := listPermOf_length_eq hp hpair
  obtain ⟨x, y, rfl⟩ : ∃ x y, ρ = [x, y] := by
    rcases ρ with _ | ⟨x, _ | ⟨y, _ | ⟨z, tail⟩⟩⟩
    · exact absurd hlen (by simp)
    · exact absurd hlen (by simp)
    · exact ⟨x, y, rfl⟩
    · exact absurd hlen (by simp)
  have hcases : ∀ z, z ∈ historicalGapEv₁ ∪ historicalGapEv₂ →
      z = historicalGapAdd ∨ z = historicalGapRem := by
    intro z hz
    rcases hz with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr h₂
  have hx := hcases x ((hp.2 x).mp List.mem_cons_self)
  have hy := hcases y ((hp.2 y).mp
    (List.mem_cons_of_mem _ List.mem_cons_self))
  have hxy : x ≠ y := by
    intro hEq
    have hnd := hp.1
    rw [hEq, List.nodup_cons] at hnd
    exact hnd.1 List.mem_cons_self
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · simp [applySeq, HistoricalGap, historicalGapAdd, historicalGapRem,
      historicalGapUpdate, historicalGapMerge, Op.op] at hf
  · simp [applySeq, HistoricalGap, historicalGapAdd, historicalGapRem,
      historicalGapUpdate, historicalGapMerge, Op.op] at hf
  · exact absurd rfl hxy

theorem HistoricalVCs24_not_imply_JoinWithPolicy :
    ¬ (∀ (D : MRDTSig) (P : ReplayPolicy D.toUpdateSig),
      @HistoricalVCs24 D P → JoinWithPolicy D P) := by
  intro implication
  exact HistoricalGap_not_joinWithPolicy
    instReplayPolicyToUpdateSigHistoricalGap
    (implication HistoricalGap instReplayPolicyToUpdateSigHistoricalGap
      HistoricalGap_historicalVCs24)

/-- The implication also fails for the framework's current, policy-erased
`Join`. This statement matches the declaration that exists today; the
explicit-policy theorem above is the stronger and conceptually intended test. -/
theorem HistoricalVCs24_not_imply_join :
    ¬ (∀ (D : MRDTSig) (P : ReplayPolicy D.toUpdateSig),
      @HistoricalVCs24 D P → Join D) := by
  intro implication
  have hCurrent := implication HistoricalGap
    instReplayPolicyToUpdateSigHistoricalGap HistoricalGap_historicalVCs24
  change JoinWithPolicy HistoricalGap
    (ReplayPolicy.default HistoricalGap.toUpdateSig) at hCurrent
  exact HistoricalGap_not_joinWithPolicy
    (ReplayPolicy.default HistoricalGap.toUpdateSig) hCurrent

end Sal.MRDTs
