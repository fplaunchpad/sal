import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Instances.EfficientORSetCertified

/-! An independent ordinary-set history bridge for the production efficient
OR-set. Its existing causal execution certificate supplies the history model.
This is an explicit exception to the restricted-policy proof framework:
same-replica adds with identical application operations can fail to commute,
so no operation-only policy satisfies exact noncommutation and no-chain. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.EventSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

def model (α : Type) [DecidableEq α] : DeterministicSpec (Op (SetOp α)) α Bool where
  State := Finset α
  initial := ∅
  update := setStep
  query s x := decide (x ∈ s)

def spec (α : Type) [DecidableEq α] : HistorySpec (Op (SetOp α)) α Bool := (model α).toSpec

def conflict (α : Type) : OperationPolicy (SetOp α) where
  before a b := ∃ x, a = .remove x ∧ b = .add x

omit [DecidableEq α] in
theorem no_chain (a b c : SetOp α) :
    ¬ ((conflict α).before a b ∧ (conflict α).before b c) := by
  rintro ⟨⟨x, _, h⟩, ⟨y, k, _⟩⟩
  rw [h] at k
  cases k

/-- The policy retains the production remove-before-add rule exactly. -/
theorem conflict_lift_eq : (conflict α).lift = (rc : ReplayPolicy (D α).toUpdateSig) := by
  unfold OperationPolicy.lift rc
  congr 1
  funext a b
  rcases a with ⟨ta, ra, oa⟩
  rcases b with ⟨tb, rb, ob⟩
  cases oa <;> cases ob <;> simp [conflict, Op.op, eq_comm]

theorem commutationCompatibility : CommutationCompatibility (D α) id (spec α) := by
  intro a b hc
  apply DeterministicSpec.language_commutes
  intro s
  let repr : State α := s.image (fun x => (0, 0, x))
  have hv : elements repr = s := by
    simp [repr, elements, Finset.image_image, Function.comp_def]
  have h := congrArg (elements : State α → Finset α) (hc repr)
  change elements (update (update repr a) b) = elements (update (update repr b) a) at h
  simpa only [elements_update, hv] using h

theorem history_bridge (ops : List (Op (SetOp α))) (x : α) :
    (spec α).admits (projectedLabels (D := D α) id ops ++
      [.query x ((D α).query (applySeq (D α).toUpdateSig (D α).init ops) x)]) := by
  apply (model α).updates_query_iff ops x _ |>.mpr
  change decide (x ∈ elements (ops.foldl update ∅)) =
    decide (x ∈ ops.foldl setStep ∅)
  rw [elements_fold]
  rfl


def simulation : EventSequentialSimulation (D α) (model α) where
  Rel s a := elements s = a
  initial := by simp [D, model, elements]
  update s a h e := by
    change elements (update s e) = setStep a e
    rw [elements_update, h]
  observes s a h q := by
    change Finset α at a
    change α at q
    change decide (q ∈ elements s) = decide (q ∈ a)
    rw [h]

theorem foldHistorySound : EventFoldHistorySound (D α) (spec α) := simulation.sound

/-- Updates on different elements commute on every concrete state. -/
theorem different_elements_commute (a b : Event α)
    (hne : element a ≠ element b) : (D α).toUpdateSig.commutes a b := by
  intro s
  change update (update s a) b = update (update s b) a
  rcases a with ⟨ta, ra, oa⟩
  rcases b with ⟨tb, rb, ob⟩
  cases oa <;> cases ob <;>
    ext p <;> rcases p with ⟨r, t, x⟩ <;>
    simp only [update, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq] <;>
    simp only [element] at hne <;> grind

theorem noncomm_same_element (a b : Event α)
    (h : ¬ (D α).toUpdateSig.commutes a b) : element a = element b := by
  by_contra ne
  exact h (different_elements_commute a b ne)

theorem add_remove_noncomm (ta ra tr rr : Nat) (x : α) :
    ¬ (D α).toUpdateSig.commutes (ta, ra, .add x) (tr, rr, .remove x) := by
  intro h
  have bad := h (∅ : State α)
  change update (update ∅ (ta, ra, .add x)) (tr, rr, .remove x) =
    update (update ∅ (tr, rr, .remove x)) (ta, ra, .add x) at bad
  have mem : (ra, ta, x) ∈ update (update ∅ (tr, rr, .remove x)) (ta, ra, .add x) := by
    simp [update]
  rw [← bad] at mem
  simp [D, update] at mem

/-- Identical application adds can overwrite one another's per-replica tag. -/
theorem same_replica_adds_noncomm (x : α) :
    ¬ (D α).toUpdateSig.commutes (1, 0, .add x) (2, 0, .add x) := by
  intro h
  have bad := h (∅ : State α)
  change update (update ∅ (1, 0, .add x)) (2, 0, .add x) =
    update (update ∅ (2, 0, .add x)) (1, 0, .add x) at bad
  have mem : (0, 1, x) ∈ update (update ∅ (2, 0, .add x)) (1, 0, .add x) := by
    simp [update]
  rw [← bad] at mem
  simp [update] at mem

/-- The same application add pair commutes when its event replicas differ. -/
theorem distinct_replicas_adds_commute (x : α) :
    (D α).toUpdateSig.commutes (1, 0, .add x) (2, 1, .add x) := by
  intro s
  change update (update s (1, 0, .add x)) (2, 1, .add x) =
    update (update s (2, 1, .add x)) (1, 0, .add x)
  ext p
  rcases p with ⟨r, t, y⟩
  simp only [update, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq]
  grind

/-- Concrete noncommutation cannot factor through application operations at
all: changing event replicas changes commutation of the same application pair. -/
theorem noncommutation_does_not_factor (x : α) :
    ¬ ∃ R : SetOp α → SetOp α → Prop, ∀ a b : Event α,
      ¬ (D α).toUpdateSig.commutes a b ↔ R a.op b.op := by
  rintro ⟨R, equivalent⟩
  have edge : R (.add x) (.add x) :=
    (equivalent (1, 0, .add x) (2, 0, .add x)).mp (same_replica_adds_noncomm x)
  exact (equivalent (1, 0, .add x) (2, 1, .add x)).mpr edge
    (distinct_replicas_adds_commute x)

/-- This excludes ANY operation-only policy, not merely the existing resolver.
Exact coverage of the identical application pair forces a self edge, which
immediately contradicts no-chain. -/
theorem restrictedLaws_impossible (x : α) (P : OperationPolicy (SetOp α)) :
    ¬ RestrictedLaws (D α).toUpdateSig P := by
  intro laws
  have edge : P.before (.add x) (.add x) := by
    have covered := (laws.noncomm_exact (1, 0, .add x) (2, 0, .add x)).mp
      (same_replica_adds_noncomm x)
    simpa only [Op.op, or_self] using covered
  exact laws.no_chain (.add x) (.add x) (.add x) ⟨edge, edge⟩

/-- A finite event-input witness preserving both the literal paper relation
and independent specification-conflict visibility. -/
theorem versions_of_execution {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ∀ v s E, C.ver v = some (s, E) → ∀ q,
      ∃ π : List (Event α), listPermOf π E ∧
        respects π (paperOrder (conflict α) C.replayContext E) ∧
        respects π (projectedSpecVisibility id (spec α) C.replayContext) ∧
        (spec α).admits (projectedLabels (D := D α) id π ++ [.query q ((D α).query s q)]) := by
  obtain ⟨_, good, represented⟩ := represented_of_mintCertifiedV reach
  intro v s E hv q
  obtain ⟨ops, hp, _, _⟩ := good.canonical v s E hv
  obtain ⟨sorted, hperm, hsort⟩ := exists_sorted C.vis E ops hp
  have support := good.version_events_supported v s E hv
  have ht : Transitive C.vis := fun _ _ _ hab hbc => good.vis_trans hab hbc
  have hm : ∀ a b, C.vis a b → a.time < b.time := fun _ _ h => C.causal_mono h
  have total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a := by
    intro a ha b hb hne hr
    obtain ⟨r, er, hhead, hea⟩ := support a ha
    obtain ⟨r', er', hhead', heb⟩ := support b hb
    exact C.vis_total_same_replica hhead hea hhead' heb hne hr
  have state : applySeq (D α).toUpdateSig (D α).init sorted = s := by
    apply Finset.ext
    intro p
    exact (represents_sorted_fold C.vis E ht hm total sorted hperm hsort p).trans
      (represented v s E hv p).symm
  have order : respects sorted (paperOrder (conflict α) C.replayContext E) := by
    apply hsort.imp_of_mem
    intro a b ha hb hn hedge
    apply hn
    rcases hedge with ⟨vis, noncomm⟩ | ⟨_, _, hrc, noAbsorber⟩
    · exact before_of_vis C.vis E ht hm ((hperm.2 a).mp ha) vis
        (noncomm_same_element _ _ noncomm)
    · obtain ⟨x, hremove, hadd⟩ := hrc
      change b.2.2 = .remove x at hremove
      change a.2.2 = .add x at hadd
      have early : Early C.vis E b := Or.inl ⟨x, hremove⟩
      have late : ¬ Early C.vis E a := by
        rintro (⟨y, hy⟩ | ⟨z, hz, hvis, hzop⟩)
        · rw [hadd] at hy
          cases hy
        · apply noAbsorber ⟨z, hz, hvis, ?_⟩
          rcases a with ⟨ats, ar, aop⟩
          rcases z with ⟨zt, zr, zop⟩
          change aop = .add x at hadd
          simp only at hzop
          subst aop
          simp only [element] at hzop
          subst zop
          exact add_remove_noncomm _ _ _ _ x
      simp [Before, rank, early, late]
  refine ⟨sorted, hperm, order, ?_, ?_⟩
  · exact order.imp (fun {_ _} h => h ∘
      projectedSpecVisibility_sub_paperOrder commutationCompatibility C.replayContext E _ _)
  · simpa [state] using history_bridge sorted q

theorem certifiedRA (C : Configuration (D α))
    (reach : MintCertifiedReach (D α) issuance C) :
    EventSpecificationRALinearizable (D α) (conflict α) (spec α) C := by
  intro r v s E _ hv q
  exact versions_of_execution reach.toV v s E hv q

theorem certifiedRAV (C : Configuration (D α))
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    EventSpecificationRALinearizable (D α) (conflict α) (spec α) C := by
  intro r v s E _ hv q
  exact versions_of_execution reach v s E hv q

theorem certifiedVersionsRAV :
    EventCertifiedSpecificationRAV (D α) (conflict α) (spec α) issuance :=
  fun _ reach => versions_of_execution reach

theorem certifiedVersionsRA :
    EventCertifiedSpecificationRA (D α) (conflict α) (spec α) issuance :=
  certifiedVersionsRAV.ordinary

theorem certifiedLiteralRA (C : Configuration (D α))
    (reach : MintCertifiedReach (D α) issuance C) :
    EventRALinearizable (D α) (conflict α) (spec α) C := (certifiedRA C reach).active

theorem certifiedLiteralRAV (C : Configuration (D α))
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    EventRALinearizable (D α) (conflict α) (spec α) C := (certifiedRAV C reach).active

theorem certifiedExecutions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) issuance).Execution (initConfig (D α)) trace) :
    ProjectedSpecificationExecution (D α) (conflict α) id (spec α) (initConfig (D α)) trace :=
  projected_certified_executions certifiedRA trace execution

theorem certifiedExecutionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) issuance).Execution (initConfig (D α)) trace) :
    ProjectedSpecificationExecution (D α) (conflict α) id (spec α) (initConfig (D α)) trace :=
  projected_certified_executionsV certifiedRAV trace execution

/-- PASS+FAIL: supplied metadata need not increase in the independent history;
the ordinary set answers true after adds and false after physical removal. -/
example : (spec Nat).admits [.update (8, 0, .add 7), .update (3, 0, .add 7),
      .query 7 true] ∧
    ¬ (spec Nat).admits [.update (8, 0, .add 7), .update (3, 0, .add 7),
      .query 7 false] ∧
    (spec Nat).admits [.update (8, 0, .add 7), .update (3, 0, .remove 7),
      .query 7 false] ∧
    ¬ (spec Nat).admits [.update (8, 0, .add 7), .update (3, 0, .remove 7),
      .query 7 true] := by
  change (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(8, 0, SetOp.add 7), (3, 0, SetOp.add 7)] ++
        [.query 7 true]) ∧
    ¬ (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(8, 0, SetOp.add 7), (3, 0, SetOp.add 7)] ++
        [.query 7 false]) ∧
    (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(8, 0, SetOp.add 7), (3, 0, SetOp.remove 7)] ++
        [.query 7 false]) ∧
    ¬ (model Nat).toSpec.admits
      (DeterministicSpec.updateLabels [(8, 0, SetOp.add 7), (3, 0, SetOp.remove 7)] ++
        [.query 7 true])
  simp only [DeterministicSpec.updates_query_iff]
  simp [model, setStep]

#print axioms noncommutation_does_not_factor
#print axioms restrictedLaws_impossible
#print axioms commutationCompatibility
#print axioms simulation
#print axioms certifiedVersionsRA
#print axioms certifiedVersionsRAV
#print axioms certifiedExecutions
#print axioms certifiedExecutionsV
end Sal.MRDTs.Paper1.EfficientORSet.EventSpec
