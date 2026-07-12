import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Sal.ConditionedMRDTs.Metatheory.WitnessClass
import Sal.ConditionedMRDTs.Metatheory.WitnessCoherence
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Evolution
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Replay
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_EffFold

/-! # Shesha — the conditioned signature, honesty contract, witness class

The definitional layer of the Shesha instance (split out of
`Shesha_Cond.lean` so the join-hook proof machinery can consume it):
the `ConditionedMRDTSig` instance (`SheshaD`, timestamp-as-id), the
honesty contract (`SheshaHonest` = `GenHonest` at the generation guard),
the witness class (`SheshaEff` — effective enumerations) with its two
bookkeeping facts, and the op-level bridge (`toSOp`/`applySeq_toSOp`).
The capstone and its single owed hook live in `Shesha_Cond.lean`. -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- Shesha application payloads. The node id is NOT in the payload: it is
the op's Lamport timestamp. -/
inductive SAppOp where
  | insA (a : Nat)
  | delA (d : Nat)
deriving DecidableEq

/-- The framework update: timestamp-as-id. -/
def sUpdate (s : Shesha.St) (o : Op SAppOp) : Shesha.St :=
  match o.2.2 with
  | .insA a => Shesha.insert s o.1 a
  | .delA d => Shesha.delete s d

/-- Generation-time guard: fresh nonzero ids, live anchors, live delete
targets. -/
def sGuard (o : Op SAppOp) (s : Shesha.St) : Prop :=
  match o.2.2 with
  | .insA a => o.1 ∉ Shesha.read s ∧ o.1 ≠ 0 ∧
      (a = 0 ∨ a ∈ Shesha.read s)
  | .delA d => d ∈ Shesha.read s

/-- **The Shesha conditioned instance.** -/
def SheshaD : ConditionedMRDTSig where
  State := Shesha.St
  dec_state := inferInstance
  init := ([] : Shesha.St)
  AppOp := SAppOp
  dec_op := inferInstance
  Query := Unit
  Value := List Nat
  update := sUpdate
  merge := fun a b => Shesha.merge [] a b
  query := fun s _ => Shesha.read s
  rc := fun _ _ => RcRes.Either
  mergeL := Shesha.merge
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := sGuard

/-- The honesty contract: every event satisfies the generation guard at
the fold of (any enumeration of) its causal past. -/
def SheshaHonest (C : Configuration SheshaD) : Prop :=
  GenHonest SheshaD sGuard C

/-! ## The witness class: effective enumerations

An **effective** enumeration never no-ops an insert: at each insert's point
in the fold, its anchor is live (or the root). Deletes are unconstrained —
a delete of an absent id is a harmless identity (two replicas may honestly
issue concurrent deletes of the same node; any enumeration no-ops the
second). Real executions produce exactly this class: ops apply once, at
their issuer, where the generation guard held. -/

/-- One effective step. -/
def effStep (s : Shesha.St) (o : Op SAppOp) : Prop :=
  match o.2.2 with
  | .insA a => a = 0 ∨ a ∈ Shesha.read s
  | .delA _ => True

/-- Effectiveness of an enumeration, from a start state. -/
def EffFrom : Shesha.St → List (Op SAppOp) → Prop
  | _, [] => True
  | s, o :: ρ => effStep s o ∧ EffFrom (sUpdate s o) ρ

/-- The Shesha witness class: effective from the empty document. -/
def SheshaEff (ρ : List (Op SAppOp)) : Prop := EffFrom ([] : Shesha.St) ρ

theorem sheshaEff_init : SheshaEff [] := trivial

theorem effFrom_append :
    ∀ (ρ : List (Op SAppOp)) (s : Shesha.St) (e : Op SAppOp),
      EffFrom s ρ → effStep (ρ.foldl sUpdate s) e → EffFrom s (ρ ++ [e])
  | [], s, e, _, he => ⟨he, trivial⟩
  | o :: ρ, s, e, h, he => by
      refine ⟨h.1, ?_⟩
      exact effFrom_append ρ (sUpdate s o) e h.2 he

/-- The generation guard implies the effective step. -/
theorem sGuard_effStep {e : Op SAppOp} {s : Shesha.St}
    (h : sGuard e s) : effStep s e := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | insA a => exact h.2.2
  | delA d => trivial

/-- The `W`-extension fact the metatheorem consumes: an honest fresh event
extends an effective enumeration effectively. -/
theorem sheshaEff_step (e : Op SAppOp) (ρ : List (Op SAppOp)) (s : Shesha.St)
    (hW : SheshaEff ρ) (hfold : applySeq SheshaD.toCRDTSig SheshaD.init ρ = s)
    (hP : sGuard e s) : SheshaEff (ρ ++ [e]) := by
  refine effFrom_append ρ ([] : Shesha.St) e hW ?_
  have hs : ρ.foldl sUpdate ([] : Shesha.St) = s := hfold
  rw [hs]
  exact sGuard_effStep hP

/-! ## The op-level bridge

The replay layers (`Shesha_Replay.lean`) are stated over `Shesha.Op`; the
framework folds `Op SAppOp` events through `sUpdate`. The translation is a
`map`, and the folds agree pointwise. -/

/-- Translate a framework event to the datatype op (timestamp-as-id). -/
def toSOp (o : Op SAppOp) : Shesha.Op :=
  match o.2.2 with
  | .insA a => .ins o.1 a
  | .delA d => .del d

theorem sUpdate_toSOp (s : Shesha.St) (o : Op SAppOp) :
    sUpdate s o = Shesha.applyOp s (toSOp o) := by
  rcases o with ⟨t, r, op⟩
  cases op <;> rfl

/-- The framework fold is the datatype fold of the translated ops. -/
theorem applySeq_toSOp :
    ∀ (ρ : List (Op SAppOp)) (s : Shesha.St),
      applySeq SheshaD.toCRDTSig s ρ = Shesha.steps s (ρ.map toSOp)
  | [], _ => rfl
  | o :: ρ, s => by
      rw [List.map_cons,
        show applySeq SheshaD.toCRDTSig s (o :: ρ)
          = applySeq SheshaD.toCRDTSig (sUpdate s o) ρ from rfl,
        show Shesha.steps s (toSOp o :: ρ.map toSOp)
          = Shesha.steps (Shesha.applyOp s (toSOp o)) (ρ.map toSOp) from rfl,
        sUpdate_toSOp, applySeq_toSOp ρ]

end Sal.ConditionedMRDTs
