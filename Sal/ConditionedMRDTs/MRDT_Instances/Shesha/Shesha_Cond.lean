import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Evolution

/-! # Shesha — the conditioned instance and the RA-linearizability capstone

Shesha enters the one framework by the **mergeable-queue route**: the
ternary merge is exhibited directly as the linearization witness
(`JoinLemma3At`), and `ra_linearizable3_of_honest_reach` turns that single
per-datatype obligation into per-version RA-linearizability, with no
further datatype-specific spec.

Status:
- the `ConditionedMRDTSig` instance (`SheshaD`) — the op's Lamport
  timestamp *is* the node id, exactly the design's convention;
- the honesty contract (`SheshaHonest`) — generation-honest ops: fresh
  nonzero ids, live anchors, live delete targets at the issuer's causal
  past (the `GenHonest` shape; this is what `Shesha_Evolution.lean`'s
  per-branch `HReach` invariants consume);
- the capstone `shesha_ra_linearizable3`, reduced to the **single owed
  hook** `shesha_join_at` (documented `sorry`): Shesha's merge is the fold
  of some causally-ordered enumeration of the union of the branches'
  events. Its single-merge substance is the M0–M2 layer (well-formedness,
  the survivor-set identity, LCA-order extension — all closed); what
  remains is the replay half: M3 (branch-order extension) and the
  fold-realization of the assembled output (runs realized by
  ascending-timestamp insertion, markers by post-hoc deletes) — the
  pen-and-paper Theorem P/D layer of
  `whiteboard/sibling-linked-proof.md`.
-/

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

/-- **The owed join hook** (the last obligation): under honest histories,
Shesha's ternary merge is itself the linearization witness — the fold of
some `lo`-respecting enumeration of the union of the branches' events.

`sorry` — the replay half of phase 2. What is already closed feeds it:
`merge_WF_honest` / `merge_ids_honest` (the output is well-formed and
displays exactly the merge-live ids), `merge_comm_honest` (symmetry), and
`merge_extends_L_honest` (LCA-order extension). Owed: (i) **M3** —
branch-order extension (merge-surviving branch pairs keep the branch's
display order; the analogue of M2 with the branch in place of the LCA,
requiring the branch-evolution invariants of `Shesha_Evolution.lean`
threaded through the run-placement layer); (ii) **fold realization** —
the assembled output is the Shesha-fold of an explicit interleaving:
LCA enumeration, then both branches' born inserts in ascending timestamp
order (same-slot newest-head-first is exactly what head-insertion
realizes), with inserts placed before the concurrent deletes of their
anchors (rehoming = the delete splice, `mem_row_delete`), then the
remaining deletes. -/
theorem shesha_join_at :
    ∀ C', SheshaHonest C' → JoinLemma3At SheshaD (Configuration.core C') := by
  sorry

/-- **RA-linearizability of Shesha**: at every honestly-reachable
configuration, every version's state is the raw fold of some
`lo`-respecting linearization of its events. -/
theorem shesha_ra_linearizable3 {C : Configuration SheshaD}
    (hReach : HonestReach SheshaD SheshaHonest trivial C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reach shesha_join_at hReach

end Sal.ConditionedMRDTs
