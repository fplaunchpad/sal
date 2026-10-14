import Sal.MRDTs.Paper1.SimpleConcretePorts

/-! Generic finite transaction storage shell. The five-VC chain below verifies
set storage only. `render` is arbitrary and is not an independent text spec.
No claim about Notion client issuance, source correspondence, or natural text
history refinement follows from this file.
-/
namespace Sal.MRDTs.Instances.NotionTransactionSet
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

variable {Tx : Type} [DecidableEq Tx]

abbrev D := FinsetStore.D Tx
abbrev issuance : Issuance (D (Tx := Tx)) := FinsetStore.generation

noncomputable def storageConditions := SimplePorts.Finite.conditions (A := Tx)

/-- Actual five-VC bundle, reused from the finite-store port, which constructs
its represented execution states through the five-VC induction. -/
theorem fiveVCs : Raw.MergeVCs (commutingPolicy Tx)
    (CommutingPort.representation (D (Tx := Tx)))
    (CommutingPort.scheme (FinsetStore.all_comm (α := Tx))) :=
  (storageConditions (Tx := Tx)).vcs

/-- Join consumes the bundle together with its representation/replay supply. -/
theorem storageJoin : RepresentationJoin
    (CommutingPort.representation (D (Tx := Tx))) :=
  (storageConditions (Tx := Tx)).toVCReplayConditions.join

/-- Any deterministic renderer agrees on registered versions containing the
same event set. The execution may use ordinary or canonical recursive bases.
This is convergence of observations, not correctness of those observations. -/
theorem same_events_render {View : Type} (render : Finset Tx → View)
    {C : Configuration (D (Tx := Tx))}
    (execution : CertifiedExecution D issuance C)
    {v w : Version} {left right : Finset Tx} {E : Set (Op Tx)}
    (hl : C.ver v = some (left, E)) (hr : C.ver w = some (right, E)) :
    render left = render right := by
  have equal := (storageConditions (Tx := Tx)).toCertificate.convergence execution hl hr
  exact congrArg render equal

/-- The ordinary execution specialization. -/
theorem same_events_render_ordinary {View : Type} (render : Finset Tx → View)
    {C : Configuration (D (Tx := Tx))}
    (execution : MintCertifiedReach D issuance C)
    {v w : Version} {left right : Finset Tx} {E : Set (Op Tx)}
    (hl : C.ver v = some (left, E)) (hr : C.ver w = some (right, E)) :
    render left = render right :=
  same_events_render render (.ordinary execution) hl hr

/-- The canonical recursive-base specialization. -/
theorem same_events_render_recursive {View : Type} (render : Finset Tx → View)
    {C : Configuration (D (Tx := Tx))}
    (execution : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C)
    {v w : Version} {left right : Finset Tx} {E : Set (Op Tx)}
    (hl : C.ver v = some (left, E)) (hr : C.ver w = some (right, E)) :
    render left = render right :=
  same_events_render render (.virtual execution) hl hr

/-- Storage updates deduplicate whole immutable transaction values. -/
theorem repeated_delivery (state : Finset Tx) (tx : Tx) :
    insert tx (insert tx state) = insert tx state := by simp

/-- The adapter includes the base in its union after checking that it is a
payload-preserving subset of each branch. On accepted inputs this equals the
base-ignoring finite-store merge. -/
theorem adapter_union_agrees {base left right : Finset Tx}
    (subset : base ⊆ left) :
    (base ∪ left) ∪ right = (D (Tx := Tx)).merge base left right := by
  rw [Finset.union_eq_right.mpr subset]
  rfl

/-- The adapter's transaction-key guard is an additional property. Whole-value
set union alone does not rule out two different payloads sharing a key. -/
def Consistent {Key : Type} (key : Tx → Key) (state : Finset Tx) : Prop :=
  ∀ a ∈ state, ∀ b ∈ state, key a = key b → a = b

theorem consistent_insert {Key : Type} {key : Tx → Key} {state : Finset Tx}
    {tx : Tx} (h : Consistent key state)
    (fresh : ∀ old ∈ state, key old = key tx → old = tx) :
    Consistent key (insert tx state) := by
  intro a ha b hb eq
  simp only [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · rfl
    · exact (fresh b hb eq.symm).symm
  · rcases hb with rfl | hb
    · exact fresh a ha eq
    · exact h a ha b hb eq

theorem consistent_union {Key : Type} {key : Tx → Key}
    {left right : Finset Tx} (hl : Consistent key left) (hr : Consistent key right)
    (cross : ∀ a ∈ left, ∀ b ∈ right, key a = key b → a = b) :
    Consistent key (left ∪ right) := by
  intro a ha b hb eq
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp hb with hb | hb
    · exact hl a ha b hb eq
    · exact cross a ha b hb eq
  · rcases Finset.mem_union.mp hb with hb | hb
    · exact (cross b hb a ha eq.symm).symm
    · exact hr a ha b hb eq

/-- PASS+FAIL: individually consistent branches can conflict at merge. This
pins the reason the JavaScript adapter checks identity/payload agreement. -/
theorem identity_collision_control :
    Consistent (fun n : Nat => n % 2) ({0} : Finset Nat) ∧
    Consistent (fun n : Nat => n % 2) ({2} : Finset Nat) ∧
    ¬ Consistent (fun n : Nat => n % 2) (({0} : Finset Nat) ∪ {2}) := by
  refine ⟨by simp [Consistent], by simp [Consistent], ?_⟩
  intro h
  have impossible := h 0 (by simp) 2 (by simp) (by decide)
  omega

#print axioms fiveVCs
#print axioms storageJoin
#print axioms same_events_render_recursive
end Sal.MRDTs.Instances.NotionTransactionSet
