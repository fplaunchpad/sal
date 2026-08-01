import Sal.ConditionedMRDTs.Metatheory.JoinKit
import Sal.ConditionedMRDTs.Metatheory.WorldIndexedStability
import Sal.ConditionedMRDTs.Metatheory.Product

/-!
# Packaged MRDT correctness

The repository proves three independent layers: causal-history convergence,
sequential intent, and representation simulation.  This file packages those
layers without forcing datatypes that have no compactor to invent one.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- An independent sequential state machine over timestamped MRDT events. -/
structure SequentialSpec (Event : Type) where
  State : Type
  init : State
  step : State → Event → State

namespace SequentialSpec

def run {Event : Type} (S : SequentialSpec Event) (ops : List Event) : S.State :=
  ops.foldl S.step S.init

/-- Independent sequential product for timestamped sum operations. -/
def prod {A₁ A₂ : Type} (S₁ : SequentialSpec (Op A₁))
    (S₂ : SequentialSpec (Op A₂)) : SequentialSpec (Op (A₁ ⊕ A₂)) where
  State := S₁.State × S₂.State
  init := (S₁.init, S₂.init)
  step s e := match e.2.2 with
    | Sum.inl o => (S₁.step s.1 (e.1, e.2.1, o), s.2)
    | Sum.inr o => (s.1, S₂.step s.2 (e.1, e.2.1, o))

theorem run_append_single {Event : Type} (S : SequentialSpec Event)
    (ops : List Event) (e : Event) :
    S.run (ops ++ [e]) = S.step (S.run ops) e := by
  simp [run, List.foldl_append]

/-- The independent sequential product projects an interleaved history in
the same way as the MRDT product fold. -/
theorem run_prod {A₁ A₂ : Type} (S₁ : SequentialSpec (Op A₁))
    (S₂ : SequentialSpec (Op A₂)) (ops : List (Op (A₁ ⊕ A₂))) :
    (S₁.prod S₂).run ops =
      (S₁.run (projList₁ ops), S₂.run (projList₂ ops)) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      rw [run_append_single, ih]
      rcases e with ⟨t, r, o⟩
      cases o <;>
        simp [run_append_single, projList₁, projList₂, prod,
          oplOp, oprOp, List.filterMap_append]

end SequentialSpec

/-- A local forward simulation from the MRDT update machine to an independent
sequential specification. -/
structure SequentialRefinement (D : ConditionedMRDTSig)
    (S : SequentialSpec (Op D.AppOp)) where
  Rel : D.State → S.State → Prop
  init : Rel D.init S.init
  step : ∀ {s q e}, Rel s q → Rel (D.update s e) (S.step q e)

/-- A sequential refinement whose semantic claim is restricted to a declared
history discipline.  Nontrivial MRDT intent theorems use this form: freshness
and applicability depend on the prefix, not merely on the current visible
state. -/
structure HistorySequentialRefinement (D : ConditionedMRDTSig)
    (S : SequentialSpec (Op D.AppOp)) where
  Honest : List (Op D.AppOp) → Prop
  Rel : D.State → S.State → Prop
  init : Rel D.init S.init
  sound : ∀ ops, Honest ops →
    Rel (applySeq D.toCRDTSig D.init ops) (S.run ops)

/-- Local sequential simulation composes over every operation list. -/
theorem SequentialRefinement.run {D : ConditionedMRDTSig}
    {S : SequentialSpec (Op D.AppOp)} (R : SequentialRefinement D S)
    (ops : List (Op D.AppOp)) :
    R.Rel (applySeq D.toCRDTSig D.init ops) (S.run ops) := by
  induction ops using List.reverseRecOn with
  | nil => exact R.init
  | append_singleton ops e ih =>
    rw [applySeq_append_single]
    simpa [SequentialSpec.run, List.foldl_append] using R.step ih

/-- An unconditional local simulation is a history refinement with the
trivial history discipline. -/
def SequentialRefinement.toHistory {D : ConditionedMRDTSig}
    {S : SequentialSpec (Op D.AppOp)} (R : SequentialRefinement D S) :
    HistorySequentialRefinement D S where
  Honest := fun _ => True
  Rel := R.Rel
  init := R.init
  sound := fun ops _ => R.run ops

/-- Sequential forward simulations compose componentwise. -/
def SequentialRefinement.prod {D₁ D₂ : ConditionedMRDTSig}
    {S₁ : SequentialSpec (Op D₁.AppOp)} {S₂ : SequentialSpec (Op D₂.AppOp)}
    (R₁ : SequentialRefinement D₁ S₁) (R₂ : SequentialRefinement D₂ S₂) :
    SequentialRefinement (prodSig D₁ D₂) (SequentialSpec.prod S₁ S₂) where
  Rel s q := R₁.Rel s.1 q.1 ∧ R₂.Rel s.2 q.2
  init := ⟨R₁.init, R₂.init⟩
  step := by
    intro s q e h
    rcases e with ⟨t, r, o⟩
    cases o with
    | inl o => exact ⟨R₁.step h.1, h.2⟩
    | inr o => exact ⟨h.1, R₂.step h.2⟩

/-- History-conditioned sequential certificates compose by projecting the
mixed history to each component. -/
def HistorySequentialRefinement.prod {D₁ D₂ : ConditionedMRDTSig}
    {S₁ : SequentialSpec (Op D₁.AppOp)} {S₂ : SequentialSpec (Op D₂.AppOp)}
    (R₁ : HistorySequentialRefinement D₁ S₁)
    (R₂ : HistorySequentialRefinement D₂ S₂) :
    HistorySequentialRefinement (prodSig D₁ D₂) (SequentialSpec.prod S₁ S₂) where
  Honest ops := R₁.Honest (projList₁ ops) ∧ R₂.Honest (projList₂ ops)
  Rel s q := R₁.Rel s.1 q.1 ∧ R₂.Rel s.2 q.2
  init := ⟨R₁.init, R₂.init⟩
  sound := by
    intro ops h
    rw [applySeq_prod, SequentialSpec.run_prod]
    exact ⟨R₁.sound _ h.1, R₂.sound _ h.2⟩

/-- The semantic and sequential-intent certificate shared by every fully
verified MRDT.  `join` is exposed through the common doctrine interface while
remaining definitionally consumable by the established adequacy theorem. -/
structure VerifiedMRDT (D : ConditionedMRDTSig) where
  Honest : Sal.Emulation.Configuration D.toCRDTSig → Prop
  initInv : D.Inv D.init
  join : ∀ C, Honest C → JoinKitAt D (plainDoctrine D) C
  Spec : SequentialSpec (Op D.AppOp)
  seq : HistorySequentialRefinement D Spec

namespace VerifiedMRDT

variable {D : ConditionedMRDTSig} (V : VerifiedMRDT D)

/-- Packaged convergence: honest reachability plus the Join certificate gives
per-version RA-linearizability. -/
theorem ra_linearizable {C : Configuration D}
    (hReach : HonestReach D (fun C => V.Honest (Configuration.core C))
      V.initInv C) : IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reach
    (fun C hC => (joinKitAt_plain_iff D (Configuration.core C)).1
      (V.join (Configuration.core C) hC))
    hReach

/-- Packaged convergence for the widened execution model. Virtual-LCA merges
consume the same per-configuration Join certificate as ordinary merges. -/
theorem ra_linearizableV {C : Configuration D}
    (hReach : HonestReachV D (fun C => V.Honest (Configuration.core C))
      V.initInv C) : IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reachV
    (fun C hC => (joinKitAt_plain_iff D (Configuration.core C)).1
      (V.join (Configuration.core C) hC))
    hReach

/-- Packaged single-replica intent refinement for an arbitrary event list. -/
theorem sequential (ops : List (Op D.AppOp)) (hHonest : V.seq.Honest ops) :
    V.seq.Rel (applySeq D.toCRDTSig D.init ops) (V.Spec.run ops) :=
  V.seq.sound ops hHonest

/-- Complete verified packages compose: semantic joins use the existing
product gluing, while intent simulations compose componentwise. -/
def prod {D₁ D₂ : ConditionedMRDTSig}
    (V₁ : VerifiedMRDT D₁) (V₂ : VerifiedMRDT D₂) :
    VerifiedMRDT (prodSig D₁ D₂) where
  Honest C := V₁.Honest (projCore₁ C) ∧ V₂.Honest (projCore₂ C)
  initInv := ⟨V₁.initInv, V₂.initInv⟩
  join C h := (joinKitAt_plain_iff (prodSig D₁ D₂) C).2
    (joinLemma3At_prod
      ((joinKitAt_plain_iff D₁ (projCore₁ C)).1 (V₁.join _ h.1))
      ((joinKitAt_plain_iff D₂ (projCore₂ C)).1 (V₂.join _ h.2)))
  Spec := SequentialSpec.prod V₁.Spec V₂.Spec
  seq := HistorySequentialRefinement.prod V₁.seq V₂.seq

end VerifiedMRDT

/-- A representation-changing runtime callback.  A callback may translate
both the stored state and operations issued against an older representation;
`Admissible` records the cut/domain obligations under which that translation
is sound.  This is deliberately weaker than `StabilityEpochFamily`: the latter
packages a complete DAG simulation, while many concrete compactors first prove
the continuation theorem exposed here. -/
structure RuntimeRecoding (D : ConditionedMRDTSig) (World : Type) where
  Obs : Type
  compact : World → D.State → D.State
  translate : World → Op D.AppOp → Op D.AppOp
  observe : D.State → Obs
  Admissible : World → D.State → List (Op D.AppOp) → Prop
  sound : ∀ w s ops, Admissible w s ops →
    observe (applySeq D.toCRDTSig (compact w s) (ops.map (translate w))) =
      observe (applySeq D.toCRDTSig s ops)

/-- A verified datatype equipped with an executable, continuation-aware
runtime recoding certificate. -/
structure VerifiedRuntimeMRDT (D : ConditionedMRDTSig) (World : Type)
    extends VerifiedMRDT D where
  runtime : RuntimeRecoding D World

namespace VerifiedRuntimeMRDT

variable {D : ConditionedMRDTSig} {World : Type}
  (V : VerifiedRuntimeMRDT D World)

/-- Packaged observational preservation for a compacted state followed by a
translated continuation. -/
theorem compact_continuation (w : World) (s : D.State)
    (ops : List (Op D.AppOp)) (h : V.runtime.Admissible w s ops) :
    V.runtime.observe
        (applySeq D.toCRDTSig (V.runtime.compact w s)
          (ops.map (V.runtime.translate w))) =
      V.runtime.observe (applySeq D.toCRDTSig s ops) :=
  V.runtime.sound w s ops h

end VerifiedRuntimeMRDT

#print axioms SequentialRefinement.run
#print axioms HistorySequentialRefinement.prod
#print axioms VerifiedMRDT.ra_linearizable
#print axioms VerifiedMRDT.ra_linearizableV
#print axioms VerifiedRuntimeMRDT.compact_continuation

end Sal.ConditionedMRDTs
