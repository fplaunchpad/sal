import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Sal.ConditionedMRDTs.Metatheory.WitnessClass
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Evolution
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Replay

/-! # Shesha — the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness. But the
queue's plain hook (`JoinLemma3At` at every honest configuration) is
**FALSE for Shesha** — machine-checked in `Shesha_Join_Refuted.lean`:
`IsCanonicalState` is existential, Shesha's canonical states are not unique
per event set (a concurrent `(ins x←a, del a)` pair folds to different live
sets under the two enumeration orders), and a misaligned canonical triple
makes the merge emit a node twice. The queue was immune only because its
canonical states are unique.

The corrected route (`WitnessClass.lean`) restricts the witnesses to the
class real executions produce: **effective** enumerations (`SheshaEff` —
every insert applies: its anchor is live, or the root, at its point in the
fold). Effectiveness realigns the three slots of the join: the live set of
an effective fold is determined by the event set alone (inserted minus
deleted), which restores `HonestMerge.fresh`-style membership agreement and
the branch-structure invariants that the M0–M2 layer consumes.

Status:
- the `ConditionedMRDTSig` instance (`SheshaD`) — the op's Lamport
  timestamp *is* the node id, exactly the design's convention;
- the honesty contract (`SheshaHonest`) — generation-honest ops: fresh
  nonzero ids, live anchors, live delete targets at the issuer's causal
  past (the `GenHonest` shape);
- the witness class (`SheshaEff`) with its two bookkeeping facts
  (`sheshaEff_init`, `sheshaEff_step` — the generation guard implies the
  effective step);
- the capstone `shesha_ra_linearizable3`, reduced to the **single owed
  hook** `shesha_join_at_eff` (documented `sorry`): Shesha's merge is the
  fold of some `lo`-respecting *effective* enumeration of the union.
  Its single-merge substance is the M0–M2 layer (well-formedness, the
  survivor-set identity, LCA-order extension — all closed); what remains
  is the replay half: M3 (branch-order extension) and the fold-realization
  of the assembled output — the pen-and-paper Theorem P/D layer of
  `whiteboard/sibling-linked-proof.md`. -/

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

/-- **The owed join hook** (the last obligation): under honest histories,
Shesha's ternary merge is the fold of some `lo`-respecting **effective**
enumeration of the union of the branches' events, given effective
witnesses for the LCA and both branches.

`sorry` — the replay half of phase 2. The witness is
`ρ⋆ = (all inserts of the union, planned over the pre-splice anchored
forest: anchors before children, same-anchor runs right-to-left)
++ (all deletes, ascending timestamps)`. Landed layers it composes
(`Shesha_Replay.lean`, all kernel-clean):
- §1 commutation (`insert_insert_comm`, `delete_insert_comm`) — with
  honesty (which excludes `vis` from a delete into an insert of its own
  target or anchor: the target would be dead at the issuer's causal past)
  this discharges `respects` for the inserts-then-deletes shape;
- §3 realization (`fold_planF` via the §2 graft algebra) — the insert
  phase builds any WF anchored forest exactly; `applySeq_toSOp` bridges
  the framework fold to the datatype fold.
Still owed, in order:
(i) fold theory of effective enumerations: live set = inserted ∖ deleted
    (set-determined — this is what effectiveness buys, and what restores
    `ModelOK`/`LRowsOK` for the M0–M2 layer at misaligned-row inputs);
    parent = lowest live original-anchor ancestor; vis-descending rows;
(ii) the **pre-splice forest**: from the merge output `merge s₀ s₁ s₂`
    and the three effective witnesses, the anchored forest `T` with
    original-anchor parenthood whose delete-collapse is the output —
    the un-spliced `outRows` plus the ghost ids (born-and-died within a
    branch) that the merge never saw; its row orders are read off the
    output rows (M0's `merge_ids`, M2's row characterizations feed this);
(iii) the delete-phase equation: folding the deletes from `T` splices it
    down to the output (iterated `mem_row_delete`-style splice algebra —
    the delete-fold *is* the collapse, so the content is that the
    collapse of `T` computes the output rows). -/
theorem shesha_join_at_eff :
    ∀ C', SheshaHonest C' →
      JoinLemma3AtW SheshaD SheshaEff (Configuration.core C') := by
  sorry

/-- **RA-linearizability of Shesha**: at every honestly-reachable
configuration, every version's state is the raw fold of some
`lo`-respecting linearization of its events. -/
theorem shesha_ra_linearizable3 {C : Configuration SheshaD}
    (hReach : HonestReach SheshaD SheshaHonest trivial C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_genHonest_reachW (P := sGuard)
    sheshaEff_init sheshaEff_step shesha_join_at_eff
    (show HonestReach SheshaD (GenHonest SheshaD sGuard) trivial C from hReach)

end Sal.ConditionedMRDTs

section AxiomAuditCond
/-! Axiom audit: the capstone carries exactly the hook's `sorry`; the
route and the witness-class bookkeeping are kernel-clean. -/
#print axioms Sal.ConditionedMRDTs.shesha_ra_linearizable3
#print axioms Sal.ConditionedMRDTs.sheshaEff_step
#print axioms Sal.ConditionedMRDTs.applySeq_toSOp
end AxiomAuditCond
