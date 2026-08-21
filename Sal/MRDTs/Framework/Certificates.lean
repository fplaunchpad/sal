import Sal.MRDTs.Framework.Execution

/-!
# Implementer-supplied MRDT certificates

The framework defines these interfaces.  A datatype implementation supplies
their inhabitants; none of them changes the raw operational semantics.
-/

namespace Sal.MRDTs

open Sal.Emulation
open Classical

/-- Every event passed its issuer guard at a causal enumeration of its
mint-time past. -/
def MintHonest (D : MRDTSig)
    (Guard : Op D.AppOp → D.State → Prop) (C : Configuration D) : Prop :=
  ∀ e, e ∈ C.events →
    ∃ π : List (Op D.AppOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      respects π C.vis ∧
      Guard e (applySeq D.toCRDTSig D.init π)

/-- Issuer policy and the datatype-specific history fact derived from it. -/
structure GenerationContract (D : MRDTSig) where
  Guard : Op D.AppOp → D.State → Prop
  History : Configuration D → Prop
  history_of_mint : ∀ C, MintHonest D Guard C → History C

/-- A raw apply is certified only when its issuer checks the public guard at
the materialized head from which it mints.  Other raw steps add no client
premise. -/
inductive GuardedStep (D : MRDTSig) (G : GenerationContract D) :
    Configuration D → Label D → Configuration D → Prop where
  | nonApply {C C' : Configuration D} {l : Label D} :
      Step D C l C' →
      (∀ t r o, l ≠ .apply t r o) →
      GuardedStep D G C l C'
  | apply {C C' : Configuration D} {t : Timestamp} {r : Replica}
      {o : D.AppOp} {v : Version} {s : D.State}
      (headAt : C.head r = some v)
      (versionAt : (C.ver v).map Prod.fst = some s)
      (guard : G.Guard (t, r, o) s)
      (raw : Step D C (.apply t r o) C') :
      GuardedStep D G C (.apply t r o) C'

theorem GuardedStep.toRaw {D : MRDTSig} {G : GenerationContract D}
    {C C' : Configuration D} {l : Label D}
    (h : GuardedStep D G C l C') : Step D C l C' := by
  cases h with
  | nonApply h _ => exact h
  | apply _ _ _ h => exact h

/-- Guarded execution for the widened semantics.  Only apply steps consult
the generation contract; ordinary and virtual merges share the non-apply
case. -/
inductive GuardedStepV (D : MRDTSig) (V : VirtualLCAResolver D)
    (G : GenerationContract D) :
    Configuration D → Label D → Configuration D → Prop where
  | base {C C' : Configuration D} {l : Label D} :
      GuardedStep D G C l C' → GuardedStepV D V G C l C'
  | virtual {C C' : Configuration D} {l : Label D} :
      StepV D V C l C' →
      (∀ ordinary : Step D C l C', False) →
      GuardedStepV D V G C l C'

theorem GuardedStepV.toRaw {D : MRDTSig} {V : VirtualLCAResolver D}
    {G : GenerationContract D} {C C' : Configuration D} {l : Label D}
    (h : GuardedStepV D V G C l C') : StepV D V C l C' := by
  cases h with
  | base h => exact .base h.toRaw
  | virtual h _ => exact h

/-- Certified executions retain mint provenance explicitly because an
ordinary configuration does not retain historical issuer heads. -/
inductive MintCertifiedReach (D : MRDTSig) (G : GenerationContract D) :
    Configuration D → Prop where
  | init : MintCertifiedReach D G (initConfig D)
  | step {C C' l} :
      MintCertifiedReach D G C →
      MintHonest D G.Guard C →
      GuardedStep D G C l C' →
      MintHonest D G.Guard C' →
      MintCertifiedReach D G C'

/-- Mint provenance for virtual-LCA executions. -/
inductive MintCertifiedReachV (D : MRDTSig) (V : VirtualLCAResolver D)
    (G : GenerationContract D) : Configuration D → Prop where
  | init : MintCertifiedReachV D V G (initConfig D)
  | step {C C' l} :
      MintCertifiedReachV D V G C →
      MintHonest D G.Guard C →
      GuardedStepV D V G C l C' →
      MintHonest D G.Guard C' →
      MintCertifiedReachV D V G C'

def VersionsSatisfy {D : MRDTSig}
    (P : D.State → Prop) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s, E) → P s

/-- Client safety derived from generation-certified execution. -/
structure SafetyCertificate (D : MRDTSig) (V : VirtualLCAResolver D)
    (G : GenerationContract D) where
  Safe : D.State → Prop
  Observable : D.State → Prop
  preservation : ∀ {C},
    MintCertifiedReach D G C → VersionsSatisfy Safe C
  preservationV : ∀ {C},
    MintCertifiedReachV D V G C → VersionsSatisfy Safe C
  consequence : ∀ s, Safe s → Observable s

/-- Independent sequential machine used to state local client intent. -/
structure SequentialSpec (Event : Type) where
  State : Type
  init : State
  step : State → Event → State

namespace SequentialSpec

def run {Event : Type} (S : SequentialSpec Event) (ops : List Event) : S.State :=
  ops.foldl S.step S.init

end SequentialSpec

/-- Sequential correctness may require a history discipline stronger than a
single-state predicate. -/
structure SequentialRefinement (D : MRDTSig)
    (S : SequentialSpec (Op D.AppOp)) where
  Honest : List (Op D.AppOp) → Prop
  Rel : D.State → S.State → Prop
  init : Rel D.init S.init
  sound : ∀ ops, Honest ops →
    Rel (applySeq D.toCRDTSig D.init ops) (S.run ops)

/-- A local client's minting discipline includes both the public generation
guard and a Lamport-clock premise. -/
structure LinearMintHistory (D : MRDTSig)
    (Guard : Op D.AppOp → D.State → Prop)
    (ops : List (Op D.AppOp)) : Prop where
  guarded : ∀ pre e post, ops = pre ++ e :: post →
    Guard e (applySeq D.toCRDTSig D.init pre)
  clocked : ∀ pre e post, ops = pre ++ e :: post →
    ∀ old ∈ pre, old.1 < e.1

end Sal.MRDTs
