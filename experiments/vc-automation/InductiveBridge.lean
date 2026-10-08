import Sal.MRDTs.Paper1.ConcreteJoin
import InductiveLeaves

/-!
Generic kernel-checked pieces of the inductive-expansion bridge. These lemmas
are deliberately not a theorem claiming that Neem's interface implies Sal's
five VCs: the compatible-history induction supplying their premises remains
an explicit residual. No production VC, Join theorem, or datatype invariant
is used here.
-/
namespace Sal.MRDTs.Paper1.NeemBridge
open Foundation ConcreteMRDT
variable {D : MRDTSig}

/-- An equation-shaped IH, extended at the last position of a replay.
`Allowed` retains ordering/freshness guards; it must be prefix closed. -/
structure ReplayEquation (D : MRDTSig)
    (Allowed : List (Op D.AppOp) → Prop) (Equation : D.State → Prop) : Prop where
  prefix_closed : ∀ π e, Allowed (π ++ [e]) → Allowed π
  base : Allowed [] → Equation D.init
  step : ∀ π e, Allowed (π ++ [e]) →
    Equation (applySeq D.toUpdateSig D.init π) →
    Equation (D.update (applySeq D.toUpdateSig D.init π) e)

theorem ReplayEquation.sound {Allowed : List (Op D.AppOp) → Prop}
    {Equation : D.State → Prop} (expansion : ReplayEquation D Allowed Equation)
    (π : List (Op D.AppOp)) (allowed : Allowed π) :
    Equation (applySeq D.toUpdateSig D.init π) := by
  induction π using List.reverseRecOn with
  | nil => exact expansion.base allowed
  | append_singleton π e ih =>
      rw [applySeq_append_single]
      exact expansion.step π e allowed (ih (expansion.prefix_closed π e allowed))

/-- Initial VC via replay witnesses; no equality/uniqueness of representations
or merge preservation is assumed. The equation itself is the induction IH. -/
theorem initial_of_expansion {R : Representation D}
    {Allowed : ReplayContext D.toUpdateSig → List (Op D.AppOp) → Prop}
    (replay : ∀ C E s, R C E s → ∃ π,
      Allowed C π ∧ applySeq D.toUpdateSig D.init π = s)
    (expansion : ∀ C, ReplayEquation D (Allowed C)
      (fun s => D.merge D.init D.init s = s)) :
    ∀ C E s, R C E s → D.merge D.init D.init s = s := by
  intro C E s rep
  obtain ⟨π, allowed, rfl⟩ := replay C E s rep
  exact (expansion C).sound π allowed

/-- Causal delta's exact two algebraic residuals. Absorption concerns the
smaller histories `Past e \\ {e}` and `U \\ {e}`; it cannot be silently obtained
from the target Join theorem. -/
theorem causal_delta_of_absorption_transport (B s : D.State) (e : Op D.AppOp)
    (absorption : D.merge B s B = s)
    (transport : D.merge B s (D.update B e) =
      D.update (D.merge B s B) e) :
    D.merge B s (D.update B e) = D.update s e := by
  rw [transport, absorption]

/-- Once the two causal reconstructions are established, local redistribution
is precisely the one-operation equation with the peeled event frozen. -/
theorem local_of_causal_transport (l B t b : D.State) (e : Op D.AppOp)
    (side : D.merge B t (D.update B e) = D.update t e)
    (union : D.merge B (D.merge l t b) (D.update B e) =
      D.update (D.merge l t b) e)
    (transport : D.merge l (D.update t e) b =
      D.update (D.merge l t b) e) :
    D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e) := by
  rw [side, union, transport]

/-- Shared redistribution similarly reduces to the common-event equation
(Q0), after four causal reconstructions. -/
theorem shared_of_causal_transport (B t₀ t₁ t₂ : D.State) (e : Op D.AppOp)
    (side₀ : D.merge B t₀ (D.update B e) = D.update t₀ e)
    (side₁ : D.merge B t₁ (D.update B e) = D.update t₁ e)
    (side₂ : D.merge B t₂ (D.update B e) = D.update t₂ e)
    (union : D.merge B (D.merge t₀ t₁ t₂) (D.update B e) =
      D.update (D.merge t₀ t₁ t₂) e)
    (transport : D.merge (D.update t₀ e) (D.update t₁ e) (D.update t₂ e) =
      D.update (D.merge t₀ t₁ t₂) e) :
    D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
      (D.merge B t₂ (D.update B e)) =
      D.merge B (D.merge t₀ t₁ t₂) (D.update B e) := by
  rw [side₀, side₁, side₂, union, transport]

end Sal.MRDTs.Paper1.NeemBridge

namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

/-- A real arbitrary-length replay, without state/history invariants. -/
def replay (D : Signature) (π : List (Op D.AppOp)) : D.State :=
  π.foldl D.step D.init

theorem replay_append (D : Signature) (π : List (Op D.AppOp)) (h : Op D.AppOp) :
    D.replay (π ++ [h]) = D.step (D.replay π) h := by
  simp [replay, List.foldl_append]

/-- Both frozen-event equations are propagated along the common prefix.
The extra one-op IH in the F* two-op rule is constructed at the extended
prefix, rather than assumed. Every event retains its timestamp/replica guard. -/
theorem common_prefix (D : Signature)
    (b1 : D.base1) (b2 : D.base2) (c1 : D.common1) (c2 : D.common2)
    (p q : Op D.AppOp) (order : D.admissible p q)
    (replicas : p.2.1 ≠ q.2.1) (fresh : D.distinct p q)
    (π : List (Op D.AppOp)) :
    (∀ h ∈ π, D.distinct p h ∧ D.distinct q h ∧
      (p.2.1 ≠ h.2.1 ∨ h.1 < p.1)) →
    D.Q1 (D.replay π) (D.replay π) (D.replay π) p ∧
    D.Q2 (D.replay π) (D.replay π) (D.replay π) p q := by
  induction π using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨b1 p, b2 p q order replicas fresh⟩
  | append_singleton π h ih =>
      intro guards
      have previous := ih (fun x hx => guards x (List.mem_append_left [h] hx))
      have gh := guards h (by simp)
      rw [replay_append]
      have one := c1 (D.replay π) p h gh.1 gh.2.2 previous.1
      exact ⟨one, c2 (D.replay π) p q h order replicas fresh gh.1 gh.2.1
        one previous.2⟩

/-- Unbounded left suffix before the frozen final operation, using the actual
F* suffix equation. The right frozen event and its state stay fixed. -/
theorem left_suffix (D : Signature) (law : D.ind_left_2op)
    (l a b : D.State) (p q : Op D.AppOp) (order : D.admissible p q)
    (replicas : p.2.1 ≠ q.2.1) (fresh : D.distinct p q)
    (base : D.Q2 l a b p q) (π : List (Op D.AppOp)) :
    (∀ h ∈ π, D.distinct p h ∧ D.distinct q h) →
    D.Q2 l (π.foldl D.step a) b p q := by
  induction π using List.reverseRecOn with
  | nil => intro _; exact base
  | append_singleton π h ih =>
      intro guards
      have previous := ih (fun x hx => guards x (List.mem_append_left [h] hx))
      have gh := guards h (by simp)
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact law l (π.foldl D.step a) b p q h
        ⟨order, replicas, fresh, gh.1, gh.2, previous⟩

/-- Mirrored suffix propagation retains F*'s STRICT order guard. -/
theorem right_suffix (D : Signature) (law : D.ind_right_2op)
    (l a b : D.State) (p q : Op D.AppOp) (order : D.order q p = .Fst_then_snd)
    (replicas : p.2.1 ≠ q.2.1) (fresh : D.distinct p q)
    (base : D.Q2 l a b p q) (π : List (Op D.AppOp)) :
    (∀ h ∈ π, D.distinct p h ∧ D.distinct q h) →
    D.Q2 l a (π.foldl D.step b) p q := by
  induction π using List.reverseRecOn with
  | nil => intro _; exact base
  | append_singleton π h ih =>
      intro guards
      have previous := ih (fun x hx => guards x (List.mem_append_left [h] hx))
      have gh := guards h (by simp)
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact law l a (π.foldl D.step b) p q h
        ⟨order, replicas, fresh, gh.1, gh.2, previous⟩

/-- Three complete unbounded phases of Neem's decomposition: common prefix,
then both local suffixes, while p and q remain frozen at their final position.
Intermediate locals-before-common blocks still require the separate coupled
insertion rules; this theorem does not erase that coverage obligation. -/
theorem prefix_and_suffixes (D : Signature)
    (b1 : D.base1) (b2 : D.base2) (c1 : D.common1) (c2 : D.common2)
    (left : D.ind_left_2op) (right : D.ind_right_2op)
    (p q : Op D.AppOp) (order : D.order q p = .Fst_then_snd)
    (replicas : p.2.1 ≠ q.2.1) (fresh : D.distinct p q)
    (common localLeft localRight : List (Op D.AppOp))
    (commonGuards : ∀ h ∈ common, D.distinct p h ∧ D.distinct q h ∧
      (p.2.1 ≠ h.2.1 ∨ h.1 < p.1))
    (leftGuards : ∀ h ∈ localLeft, D.distinct p h ∧ D.distinct q h)
    (rightGuards : ∀ h ∈ localRight, D.distinct p h ∧ D.distinct q h) :
    D.Q2 (D.replay common) (localLeft.foldl D.step (D.replay common))
      (localRight.foldl D.step (D.replay common)) p q := by
  have admissible : D.admissible p q := Or.inl order
  have initial := (D.common_prefix b1 b2 c1 c2 p q admissible replicas fresh
    common commonGuards).2
  have leftEquation := D.left_suffix left _ _ _ p q admissible replicas fresh
    initial localLeft leftGuards
  exact D.right_suffix right _ _ _ p q order replicas fresh
    leftEquation localRight rightGuards

/-- First genuine causal-coverage subcase: a common replay followed by an
arbitrary local block and a frozen final operation q strictly before e.
Only finite leaves, universal diagonal collection algebra, and commutativity
are used. No causal or Join IH and no datatype invariant is supplied. -/
theorem causal_strict_suffix (D : Signature)
    (b1 : D.base1) (b2 : D.base2) (c1 : D.common1) (c2 : D.common2)
    (right : D.ind_right_2op) (comm : D.comm)
    (diagonal : ∀ l a, D.merge l a l = a)
    (e q : Op D.AppOp) (order : D.order q e = .Fst_then_snd)
    (replicas : e.2.1 ≠ q.2.1) (fresh : D.distinct e q)
    (common localOps : List (Op D.AppOp))
    (commonGuards : ∀ h ∈ common, D.distinct e h ∧ D.distinct q h ∧
      (e.2.1 ≠ h.2.1 ∨ h.1 < e.1))
    (localGuards : ∀ h ∈ localOps, D.distinct e h ∧ D.distinct q h) :
    let B := D.replay common
    let s := D.step (localOps.foldl D.step B) q
    D.merge B s (D.step B e) = D.step s e := by
  dsimp only
  have initial := (D.common_prefix b1 b2 c1 c2 e q (Or.inl order)
    replicas fresh common commonGuards).2
  have equation := D.right_suffix right _ _ _ e q order replicas fresh
    initial localOps localGuards
  change D.merge (D.replay common) (D.step (D.replay common) e)
    (D.step (localOps.foldl D.step (D.replay common)) q) =
    D.step (D.merge (D.replay common) (D.replay common)
      (D.step (localOps.foldl D.step (D.replay common)) q)) e at equation
  rw [comm (D.replay common) (D.replay common) _, diagonal] at equation
  rw [comm]
  exact equation

end NeemExpansion.Signature
