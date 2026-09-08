import Sal.MRDTs.Framework.Execution
import Sal.MRDTs.Framework.Base.Replay

/-!
# Implementer-supplied MRDT certificates

The framework defines these interfaces.  A datatype implementation supplies
their inhabitants; none of them changes the raw operational semantics.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation
open Classical

/-- Every event was issuable at a causal enumeration of its
mint-time past. -/
def MintHonest (D : MRDTSig)
    (Guard : Op D.AppOp → D.State → Prop) (C : Configuration D) : Prop :=
  ∀ e, e ∈ C.events →
    ∃ π : List (Op D.AppOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      respects π C.vis ∧
      Guard e (applySeq D.toUpdateSig D.init π)

/-- The only operation-generation premise exposed by the framework.  A
replica may issue `e` from `s` exactly when `CanIssue e s` holds.  Datatypes
may implement this relation with an executable command generator, but the
semantic core does not prescribe a command language. -/
structure Issuance (D : MRDTSig) where
  CanIssue : Op D.AppOp → D.State → Prop

/-- A raw apply is certified only when the operation is issuable at
the materialized head from which it mints.  Other raw steps add no client
premise. -/
inductive IssuedStep (D : MRDTSig) (I : Issuance D) :
    Configuration D → Label D → Configuration D → Prop where
  | nonApply {C C' : Configuration D} {l : Label D} :
      Step D C l C' →
      (∀ t r o, l ≠ .apply t r o) →
      IssuedStep D I C l C'
  | apply {C C' : Configuration D} {t : Timestamp} {r : Replica}
      {o : D.AppOp} {v : Version} {s : D.State}
      (headAt : C.head r = some v)
      (versionAt : (C.ver v).map Prod.fst = some s)
      (guard : I.CanIssue (t, r, o) s)
      (raw : Step D C (.apply t r o) C') :
      IssuedStep D I C (.apply t r o) C'

theorem IssuedStep.toRaw {D : MRDTSig} {I : Issuance D}
    {C C' : Configuration D} {l : Label D}
    (h : IssuedStep D I C l C') : Step D C l C' := by
  cases h with
  | nonApply h _ => exact h
  | apply _ _ _ h => exact h

/-- Issuance-certified execution for the widened semantics. Only apply steps
consult `CanIssue`; ordinary and virtual merges share the non-apply
case. -/
inductive IssuedStepV (D : MRDTSig) (V : VirtualMergeBaseResolver D)
    (I : Issuance D) :
    Configuration D → Label D → Configuration D → Prop where
  | base {C C' : Configuration D} {l : Label D} :
      IssuedStep D I C l C' → IssuedStepV D V I C l C'
  | virtual {C C' : Configuration D} {l : Label D} :
      StepV D V C l C' →
      (Step D C l C' → False) →
      IssuedStepV D V I C l C'

theorem IssuedStepV.toRaw {D : MRDTSig} {V : VirtualMergeBaseResolver D}
    {I : Issuance D} {C C' : Configuration D} {l : Label D}
    (h : IssuedStepV D V I C l C') : StepV D V C l C' := by
  cases h with
  | base h => exact .base h.toRaw
  | virtual h _ => exact h

/-- Certified executions retain mint provenance explicitly because an
ordinary configuration does not retain historical issuer heads. -/
inductive MintCertifiedReach (D : MRDTSig) (I : Issuance D) :
    Configuration D → Prop where
  | init : MintCertifiedReach D I (initConfig D)
  | step {C C' l} :
      MintCertifiedReach D I C →
      MintHonest D I.CanIssue C →
      IssuedStep D I C l C' →
      MintHonest D I.CanIssue C' →
      MintCertifiedReach D I C'

/-- Mint provenance for virtual-merge-base executions. -/
inductive MintCertifiedReachV (D : MRDTSig) (V : VirtualMergeBaseResolver D)
    (I : Issuance D) : Configuration D → Prop where
  | init : MintCertifiedReachV D V I (initConfig D)
  | step {C C' l} :
      MintCertifiedReachV D V I C →
      MintHonest D I.CanIssue C →
      IssuedStepV D V I C l C' →
      MintHonest D I.CanIssue C' →
      MintCertifiedReachV D V I C'

/-- Ordinary certified execution is the base fragment of every widened
virtual-merge-base execution.  Certificates therefore need to store only the widened
case; the ordinary result is derived. -/
theorem MintCertifiedReach.toV {D : MRDTSig} {I : Issuance D}
    {V : VirtualMergeBaseResolver D} {C : Configuration D}
    (h : MintCertifiedReach D I C) : MintCertifiedReachV D V I C := by
  induction h with
  | init => exact .init
  | step _ before one after ih =>
      exact .step ih before (.base one) after

theorem MintCertifiedReach.mintHonest {D : MRDTSig}
    {I : Issuance D} {C : Configuration D}
    (h : MintCertifiedReach D I C) : MintHonest D I.CanIssue C := by
  cases h with
  | init =>
      intro e he
      unfold Configuration.events Configuration.headEvents headEventsFrom at he
      simp only [initConfig] at he
      obtain ⟨r, s, hrs, hse⟩ := he
      by_cases hr : r = 0
      · subst r
        simp at hrs
        subst s
        exact False.elim hse
      · simp [hr] at hrs
  | step _ _ _ after => exact after

theorem MintCertifiedReachV.mintHonest {D : MRDTSig}
    {V : VirtualMergeBaseResolver D} {I : Issuance D}
    {C : Configuration D} (h : MintCertifiedReachV D V I C) :
    MintHonest D I.CanIssue C := by
  cases h with
  | init =>
      intro e he
      unfold Configuration.events Configuration.headEvents headEventsFrom at he
      simp only [initConfig] at he
      obtain ⟨r, s, hrs, hse⟩ := he
      by_cases hr : r = 0
      · subst r
        simp at hrs
        subst s
        exact False.elim hse
      · simp [hr] at hrs
  | step _ _ _ after => exact after

/-- Erase issuance evidence from an ordinary certified execution. -/
theorem MintCertifiedReach.toReachable {D : MRDTSig} {I : Issuance D}
    {C : Configuration D} (h : MintCertifiedReach D I C) :
    (labeledTS D).ReachableFrom (initConfig D) C := by
  induction h with
  | init => exact Relation.ReflTransGen.refl
  | step _ _ one _ ih =>
      exact Relation.ReflTransGen.tail ih ⟨_, one.toRaw⟩

/-- Erase issuance evidence from a widened certified execution. -/
theorem MintCertifiedReachV.toReachable {D : MRDTSig}
    {V : VirtualMergeBaseResolver D} {I : Issuance D}
    {C : Configuration D} (h : MintCertifiedReachV D V I C) :
    (labeledTSV D V).ReachableFrom (initConfig D) C := by
  induction h with
  | init => exact Relation.ReflTransGen.refl
  | step _ _ one _ ih =>
      exact Relation.ReflTransGen.tail ih ⟨_, one.toRaw⟩

/-- Mint-consistent configurations satisfy an issuance-established contextual
merge precondition. The precondition itself remains independent of issuance. -/
def IssuanceEstablishes (D : MRDTSig) (I : Issuance D)
    (Good : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig → Prop) : Prop :=
  ∀ C, MintHonest D I.CanIssue C → Good C.replayContext

def VersionsSatisfy {D : MRDTSig}
    (P : D.State → Prop) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s, E) → P s

/-- Client safety derived from generation-certified execution. -/
structure SafetyCertificate (D : MRDTSig) (V : VirtualMergeBaseResolver D)
    (I : Issuance D) where
  Safe : D.State → Prop
  Observable : D.State → Prop
  preservationV : ∀ {C},
    MintCertifiedReachV D V I C → VersionsSatisfy Safe C
  consequence : ∀ s, Safe s → Observable s

namespace SafetyCertificate

/-- The ordinary safety theorem is derived from the widened theorem. -/
theorem preservation {D : MRDTSig} {V : VirtualMergeBaseResolver D}
    {I : Issuance D} (S : SafetyCertificate D V I)
    {C : Configuration D} (h : MintCertifiedReach D I C) :
    VersionsSatisfy S.Safe C :=
  S.preservationV h.toV

def trivial {D : MRDTSig} {V : VirtualMergeBaseResolver D}
    (I : Issuance D) : SafetyCertificate D V I where
  Safe := fun _ => True
  Observable := fun _ => True
  preservationV := fun _ _ _ _ _ => True.intro
  consequence := fun _ _ => True.intro

end SafetyCertificate

/-- An implementation-independent deterministic sequential machine.  The
replay-only certificate uses this internal component while production
correctness uses `SequentialSpec` below. -/
structure SequentialMachine (Event : Type) where
  State : Type
  init : State
  step : State → Event → State

/-- The public sequential specification.  `Legal` speaks only about the
abstract event history; it does not inspect implementation states. -/
structure SequentialSpec (D : MRDTSig) extends SequentialMachine (Op D.AppOp) where
  Legal : List (Op D.AppOp) → Prop
  query : State → D.Query → D.Value

namespace SequentialMachine

def run {Event : Type} (S : SequentialMachine Event) (ops : List Event) : S.State :=
  ops.foldl S.step S.init

@[simp] theorem run_append_single {Event : Type} (S : SequentialMachine Event)
    (ops : List Event) (e : Event) :
    S.run (ops ++ [e]) = S.step (S.run ops) e := by
  simp [run, List.foldl_append]

end SequentialMachine

namespace SequentialSpec

def run {D : MRDTSig} (S : SequentialSpec D)
    (ops : List (Op D.AppOp)) : S.State :=
  S.toSequentialMachine.run ops

@[simp] theorem run_append_single {D : MRDTSig} (S : SequentialSpec D)
    (ops : List (Op D.AppOp)) (e : Op D.AppOp) :
    S.run (ops ++ [e]) = S.step (S.run ops) e := by
  simp [run, SequentialMachine.run_append_single]

end SequentialSpec

/-- Sequential correctness may require a history discipline stronger than a
single-state predicate. -/
structure SequentialRefinement (D : MRDTSig)
    (S : SequentialMachine (Op D.AppOp)) where
  Honest : List (Op D.AppOp) → Prop
  Rel : D.State → S.State → Prop
  init : Rel D.init S.init
  sound : ∀ ops, Honest ops →
    Rel (applySeq D.toUpdateSig D.init ops) (S.run ops)

/-- A local client's minting discipline includes both origin issuance and a
Lamport-clock premise. This structure belongs to the replay compatibility
layer, not the public sequential specification. -/
structure LinearMintHistory (D : MRDTSig)
    (CanIssue : Op D.AppOp → D.State → Prop)
    (ops : List (Op D.AppOp)) : Prop where
  guarded : ∀ pre e post, ops = pre ++ e :: post →
    CanIssue e (applySeq D.toUpdateSig D.init pre)
  clocked : ∀ pre e post, ops = pre ++ e :: post →
    ∀ old ∈ pre, old.1 < e.1

end Sal.MRDTs
