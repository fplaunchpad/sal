import Sal.MRDTs.GC.Distributed
import Sal.MRDTs.Metatheory.Correctness

/-! # Datatype-rich refinement of distributed commit GC -/

namespace Sal.MRDTs.GC

open Classical Sal.Emulation Sal.MRDTs

variable {D : MRDTSig}

structure Runtime (D : MRDTSig) where
  core : Configuration D
  stores : World

def Runtime.WellFormed (S : Runtime D) : Prop :=
  (∀ r v, v ∈ (S.stores r).commits → (S.core.ver v).isSome) ∧
  (∀ r v, S.core.head r = some v →
    (S.stores r).head = v ∧ v ∈ (S.stores r).commits)

def Available (S : Runtime D) : Label D → Prop
  | .createReplica r => 0 ∈ (S.stores r).commits
  | .apply _ r _ => ∀ v, S.core.head r = some v → v ∈ (S.stores r).commits
  | .merge r₁ r₂ =>
      ∀ v₁ v₂, S.core.head r₁ = some v₁ → S.core.head r₂ = some v₂ →
        v₁ ∈ (S.stores r₁).commits ∧ v₂ ∈ (S.stores r₁).commits ∧
        ∃ vT, IsLCA S.core.parents v₁ v₂ vT ∧ vT ∈ (S.stores r₁).commits
  | .query r _ _ => ∀ v, S.core.head r = some v → v ∈ (S.stores r).commits

def installAuthoredHead (L : Local) (author : Replica) (v : Version) : Local where
  self := L.self
  head := v
  commits := insert v L.commits
  roster := L.roster
  authors := insert author L.authors
  authored := fun r => if r = author then insert v (L.authored r) else L.authored r
  head_present := by change v = v ∨ _; exact Or.inl rfl
  self_registered := L.self_registered
  authored_present := by
    intro r w hw
    by_cases hr : r = author
    · subst r
      simp only [if_pos] at hw
      rcases hw with rfl | hw
      · exact Or.inl rfl
      · change w = v ∨ _; exact Or.inr (L.authored_present author hw)
    · simp only [if_neg hr] at hw
      change w = v ∨ _
      exact Or.inr (L.authored_present r hw)

def StoreEvolution (S S' : Runtime D) : Label D → Prop
  | .createReplica r => S'.core.head r = some 0 ∧
      S'.stores = Function.update S.stores r (installHead (S.stores r) 0)
  | .apply _ r _ => ∃ v, S'.core.head r = some v ∧
      S'.stores = Function.update S.stores r
        (installAuthoredHead (S.stores r) r v)
  | .merge r₁ _ => ∃ v, S'.core.head r₁ = some v ∧
      S'.stores = Function.update S.stores r₁ (installHead (S.stores r₁) v)
  | .query _ _ _ => S'.stores = S.stores

/-- Fetch and collection are silent. Every visible transition contains the
actual semantic derivation; the runtime cannot reconstruct or postulate it. -/
inductive RuntimeStep (D : MRDTSig) :
    Runtime D → Option (Label D) → Runtime D → Prop where
  | fetch (S : Runtime D) (src dst : Replica)
      (wf : S.WellFormed)
      (wf' : (Runtime.mk S.core (Function.update S.stores dst
        (receive (S.stores dst) (advertise (S.stores src))))).WellFormed) :
      RuntimeStep D S none ⟨S.core, Function.update S.stores dst
        (receive (S.stores dst) (advertise (S.stores src)))⟩
  | gc (S : Runtime D) (r : Replica)
      (cert : Certificate S.core.parents (S.stores r))
      (wf : S.WellFormed)
      (wf' : (Runtime.mk S.core (Function.update S.stores r
        (collect S.core.parents (S.stores r) cert))).WellFormed) :
      RuntimeStep D S none ⟨S.core, Function.update S.stores r
        (collect S.core.parents (S.stores r) cert)⟩
  | visible {S S' : Runtime D} {l : Label D}
      (wf : S.WellFormed) (available : Available S l)
      (core : Sal.MRDTs.Step D S.core l S'.core)
      (stores : StoreEvolution S S' l) (wf' : S'.WellFormed) :
      RuntimeStep D S (some l) S'

inductive RuntimeSteps (D : MRDTSig) :
    Runtime D → List (Option (Label D)) → Runtime D → Prop where
  | nil (S) : RuntimeSteps D S [] S
  | cons {S S' S'' l ls} : RuntimeStep D S l S' →
      RuntimeSteps D S' ls S'' → RuntimeSteps D S (l :: ls) S''

inductive CoreSteps (D : MRDTSig) :
    Configuration D → List (Label D) → Configuration D → Prop where
  | nil (C) : CoreSteps D C [] C
  | cons {C C' C'' l ls} : Sal.MRDTs.Step D C l C' →
      CoreSteps D C' ls C'' → CoreSteps D C (l :: ls) C''

def eraseLabels : List (Option (Label D)) → List (Label D) := List.filterMap id

/-- The distributed storage protocol refines the raw no-GC MRDT semantics;
fetch and local GC erase to stuttering. -/
theorem runtime_refines_core {S₀ S₁ : Runtime D} {ls}
    (run : RuntimeSteps D S₀ ls S₁) :
    CoreSteps D S₀.core (eraseLabels ls) S₁.core := by
  induction run with
  | nil => exact .nil _
  | cons one _ ih =>
      cases one with
      | fetch => simpa [eraseLabels] using ih
      | gc => simpa [eraseLabels] using ih
      | visible _ _ core _ _ => simpa [eraseLabels] using CoreSteps.cons core ih

/-- Widened runtime. Availability is parameterized by the exact set of commit
versions read by the framework's virtual-LCA resolver. -/
def AvailableV (reads : Configuration D → Version → Version → Set Version)
    (S : Runtime D) : Label D → Prop
  | .merge r₁ r₂ => ∀ v₁ v₂, S.core.head r₁ = some v₁ →
      S.core.head r₂ = some v₂ →
      v₁ ∈ (S.stores r₁).commits ∧ v₂ ∈ (S.stores r₁).commits ∧
      reads S.core v₁ v₂ ⊆ (S.stores r₁).commits
  | l => Available S l

inductive RuntimeStepV (D : MRDTSig) (V : VirtualLCAResolver D)
    (reads : Configuration D → Version → Version → Set Version) :
    Runtime D → Option (Label D) → Runtime D → Prop where
  | silent {S S'} : RuntimeStep D S none S' → RuntimeStepV D V reads S none S'
  | visible {S S' l} : S.WellFormed → AvailableV reads S l →
      StepV D V S.core l S'.core → StoreEvolution S S' l →
      S'.WellFormed → RuntimeStepV D V reads S (some l) S'

inductive RuntimeStepsV (D : MRDTSig) (V : VirtualLCAResolver D)
    (reads : Configuration D → Version → Version → Set Version) :
    Runtime D → List (Option (Label D)) → Runtime D → Prop where
  | nil (S) : RuntimeStepsV D V reads S [] S
  | cons {S S' S'' l ls} : RuntimeStepV D V reads S l S' →
      RuntimeStepsV D V reads S' ls S'' → RuntimeStepsV D V reads S (l :: ls) S''

inductive CoreStepsV (D : MRDTSig) (V : VirtualLCAResolver D) :
    Configuration D → List (Label D) → Configuration D → Prop where
  | nil (C) : CoreStepsV D V C [] C
  | cons {C C' C'' l ls} : StepV D V C l C' →
      CoreStepsV D V C' ls C'' → CoreStepsV D V C (l :: ls) C''

theorem runtime_refines_coreV {V : VirtualLCAResolver D} {reads}
    {S₀ S₁ : Runtime D} {ls}
    (run : RuntimeStepsV D V reads S₀ ls S₁) :
    CoreStepsV D V S₀.core (eraseLabels ls) S₁.core := by
  induction run with
  | nil => exact .nil _
  | cons one _ ih =>
      cases one with
      | silent raw =>
          cases raw <;> simpa [eraseLabels] using ih
      | visible _ _ core _ _ =>
          simpa [eraseLabels] using CoreStepsV.cons core ih

end Sal.MRDTs.GC
