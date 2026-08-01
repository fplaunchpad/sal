import Sal.Emulation.Weak_Simulation
import Mathlib.Data.Finset.Basic

/-!
# Grow-only-set emulation canary

The two systems deliberately use different label grammars. The op side has
message delivery; the state side has singleton-state merge. Both internal
actions are silent. This is the smallest concrete instance that exercises
label morphisms, both weak simulations, trace equivalence, and representation
independence without hiding the result behind type equality.
-/

namespace Sal.Emulation.Instances.GSetCanary

open Sal.Emulation LabeledTS

inductive OpLabel where
  | add (n : Nat)
  | read (value : Finset Nat)
  | deliver (message : Nat)
deriving DecidableEq

inductive StateLabel where
  | update (n : Nat)
  | query (value : Finset Nat)
  | mergeSingleton (message : Nat)
deriving DecidableEq

def opSilent : OpLabel → Prop
  | .deliver _ => True
  | _ => False

def stateSilent : StateLabel → Prop
  | .mergeSingleton _ => True
  | _ => False

inductive OpStep : Finset Nat → OpLabel → Finset Nat → Prop where
  | add (s) (n) : OpStep s (.add n) (insert n s)
  | read (s) : OpStep s (.read s) s
  | deliver (s) (n) : OpStep s (.deliver n) (insert n s)

inductive StateStep : Finset Nat → StateLabel → Finset Nat → Prop where
  | update (s) (n) : StateStep s (.update n) (insert n s)
  | query (s) : StateStep s (.query s) s
  | mergeSingleton (s) (n) : StateStep s (.mergeSingleton n) (insert n s)

def opTS : LabeledTS where
  State := Finset Nat
  Label := OpLabel
  step := OpStep
  silent := opSilent

def stateTS : LabeledTS where
  State := Finset Nat
  Label := StateLabel
  step := StateStep
  silent := stateSilent

def opToState : LabelMorphism opTS stateTS where
  map
    | .add n => .update n
    | .read v => .query v
    | .deliver n => .mergeSingleton n
  silent_iff := by intro ℓ; cases ℓ <;> simp [opTS, stateTS, opSilent, stateSilent]

def stateToOp : LabelMorphism stateTS opTS where
  map
    | .update n => .add n
    | .query v => .read v
    | .mergeSingleton n => .deliver n
  silent_iff := by intro ℓ; cases ℓ <;> simp [opTS, stateTS, opSilent, stateSilent]

def labels : LabelIso opTS stateTS where
  forward := opToState
  backward := stateToOp
  left_inv := by intro ℓ; cases ℓ <;> rfl
  right_inv := by intro ℓ; cases ℓ <;> rfl

def forward : WeakSimM opTS stateTS labels.forward where
  rel s t := s = t
  step := by
    intro s s' t ℓ hrel hstep
    change Finset Nat at s s' t
    subst t
    cases hstep with
    | add n =>
        exact ⟨(insert n s : Finset Nat), WeakSimM.weakStep_of_step (.update s n), rfl⟩
    | read =>
        exact ⟨s, WeakSimM.weakStep_of_step (.query s), rfl⟩
    | deliver n =>
        exact ⟨(insert n s : Finset Nat),
          WeakSimM.weakStep_of_step (.mergeSingleton s n), rfl⟩

def backward : WeakSimM stateTS opTS labels.backward where
  rel s t := s = t
  step := by
    intro s s' t ℓ hrel hstep
    change Finset Nat at s s' t
    subst t
    cases hstep with
    | update n =>
        exact ⟨(insert n s : Finset Nat), WeakSimM.weakStep_of_step (.add s n), rfl⟩
    | query =>
        exact ⟨s, WeakSimM.weakStep_of_step (.read s), rfl⟩
    | mergeSingleton n =>
        exact ⟨(insert n s : Finset Nat), WeakSimM.weakStep_of_step (.deliver s n), rfl⟩

def emulation : EmulationEquivalence opTS stateTS where
  labels := labels
  forward := forward
  backward := backward

theorem initial_related_forward : forward.rel (∅ : Finset Nat) (∅ : Finset Nat) := rfl
theorem initial_related_backward : backward.rel (∅ : Finset Nat) (∅ : Finset Nat) := rfl

theorem weak_traces_equivalent (trace : List OpLabel) :
    trace ∈ opTS.weakTrace (∅ : Finset Nat) ↔
      trace.map labels.forward.map ∈ stateTS.weakTrace (∅ : Finset Nat) :=
  emulation.trace_iff initial_related_forward initial_related_backward trace

theorem client_representation_independence (P : List OpLabel → Prop) :
    (∀ tr, tr ∈ opTS.weakTrace (∅ : Finset Nat) → P tr) ↔
    (∀ tr, tr ∈ stateTS.weakTrace (∅ : Finset Nat) → P (tr.map labels.backward.map)) :=
  emulation.representation_independence
    initial_related_forward initial_related_backward P

end Sal.Emulation.Instances.GSetCanary
