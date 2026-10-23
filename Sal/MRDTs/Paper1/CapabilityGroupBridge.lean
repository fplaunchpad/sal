import Sal.MRDTs.Paper1.CapabilityGroupSpec
import Sal.MRDTs.Paper1.HistoryInputs
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-! The literal Sal criterion and the stronger specification-visibility
criterion differ on a checked owner-equivocation boundary. The source accepts
the log; this is not an honest single-owner-replica execution theorem.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Sal.MRDTs.Paper1.CapabilityGroupBridge
open Foundation
open Sal.MRDTs.Instances.CapabilityGroup

abbrev datatype (owner : Actor) : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ∅
  AppOp := Event
  dec_op := inferInstance
  Query := Unit
  Value := Finset Name
  update s e := step s e.op
  merge := merge
  query s _ := names owner s

def policy : OperationPolicy Event := ⟨fun _ _ => False⟩
def project (e : Op Event) : CapabilityGroupSpec.Input := CapabilityGroupSpec.project e.op

def grant : Event := ⟨1, 0, ∅, .grant 1⟩
def left : Event := ⟨2, 1, {1}, .assign 1 7⟩
def right : Event := ⟨3, 1, {1}, .assign 1 8⟩
def revokeLeft : Event := ⟨4, 0, {1, 2}, .revoke 1⟩
def revokeRight : Event := ⟨5, 0, {1, 3}, .revoke 1⟩
def concurrentRevoke : Event := ⟨4, 0, {1}, .revoke 1⟩

/-- Device/replica identity is deliberately separate from authenticated actor.
The concurrent owner revocations use distinct replicas. -/
def wrap (e : Event) : Op Event := (e.id, e.id, e)
def allEvents : List (Op Event) :=
  [wrap grant, wrap left, wrap right, wrap revokeLeft, wrap revokeRight]
def log : State := {grant, left, right, revokeLeft, revokeRight}
def eventSet : Set (Op Event) := { e | e ∈ allEvents }

theorem source_empty : names 0 log = ∅ := by decide
theorem source_nontrivial : names 0 {grant, left} = {7} ∧
    names 0 {grant, left} ≠ ∅ := by decide
theorem source_admitted : ∀ e ∈ log, admitted 0 log e := by decide
theorem source_wellFormed : WellFormed log := by constructor <;> decide
theorem owner_equivocates : ¬ OwnerOrdered 0 log := by decide

/-- A concrete source issue/delivery schedule: two replicas receive the grant,
issue the two writes, and distinct owner devices receive one write each before
issuing their revocations. Every issuance is locally authorized. Finally the
two branches reconcile by the source union merge. This is source-level
reachability evidence, not a Sal certified-network execution theorem. -/
theorem source_issue_delivery_schedule :
    admitted 0 ∅ grant ∧
    admitted 0 (step ∅ grant) left ∧
    admitted 0 (step ∅ grant) right ∧
    admitted 0 (step (step ∅ grant) left) revokeLeft ∧
    admitted 0 (step (step ∅ grant) right) revokeRight ∧
    merge {grant}
      (step (step (step ∅ grant) left) revokeLeft)
      (step (step (step ∅ grant) right) revokeRight) = log := by decide

/-- The same local steps meet the source issuance contract, including the
exact full-local-state timestamp and fresh ranked event identity. -/
theorem source_fresh_issue_schedule :
    CanIssue 0 ∅ grant ∧
    CanIssue 0 (step ∅ grant) left ∧
    CanIssue 0 (step ∅ grant) right ∧
    CanIssue 0 (step (step ∅ grant) left) revokeLeft ∧
    CanIssue 0 (step (step ∅ grant) right) revokeRight := by decide

/-- A minimal source protocol: replicas can issue at their complete local cut
and reconcile compatible logs. Authentication is supplied by the actor field.
This protocol is deliberately separate from Sal's version-DAG network. -/
inductive SourceReach (owner : Actor) : State → Prop where
  | empty : SourceReach owner ∅
  | issue {s e} : SourceReach owner s → CanIssue owner s e →
      SourceReach owner (step s e)
  | reconcile {s t} : SourceReach owner s → SourceReach owner t →
      (∀ a ∈ s, ∀ b ∈ t, a.id = b.id → a = b) → SourceReach owner (s ∪ t)

/-- Both validity and immutable admission are preserved by every source
protocol execution, including compatible reconciliation. -/
theorem SourceReach.valid {owner : Actor} {s : State} (h : SourceReach owner s) :
    WellFormed s ∧ LocallyAdmitted owner s := by
  induction h with
  | empty => exact ⟨wellFormed_empty, by intro e he; exact (Finset.notMem_empty e he).elim⟩
  | issue _ hc ih =>
      exact ⟨wellFormed_step ih.1 hc.1, locallyAdmitted_step ih.1 ih.2 hc⟩
  | reconcile _ _ hc ihs iht =>
      exact ⟨wellFormed_union ihs.1 iht.1 hc,
        locallyAdmitted_union ihs.1 iht.1 hc ihs.2 iht.2⟩

theorem source_reachable : SourceReach 0 log := by
  have hgrant : SourceReach 0 (step ∅ grant) := .issue .empty (by decide)
  have hleft : SourceReach 0 (step (step (step ∅ grant) left) revokeLeft) :=
    .issue (.issue hgrant (by decide)) (by decide)
  have hright : SourceReach 0 (step (step (step ∅ grant) right) revokeRight) :=
    .issue (.issue hgrant (by decide)) (by decide)
  have h := SourceReach.reconcile hleft hright (by decide)
  have heq : (step (step (step ∅ grant) left) revokeLeft) ∪
      (step (step (step ∅ grant) right) revokeRight) = log := by decide
  exact heq ▸ h

theorem source_reachable_valid : WellFormed log ∧ LocallyAdmitted 0 log :=
  source_reachable.valid

/-- Honest owner-chain controls pin the intended sequential contract without
assuming that a revocation retracts its causal predecessor's write. -/
theorem honest_precursor_control :
    OwnerOrdered 0 {grant, left, revokeLeft} ∧
    names 0 {grant, left, revokeLeft} = {7} ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, left, revokeLeft].map CapabilityGroupSpec.project)) = {7} ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, left, revokeLeft].map CapabilityGroupSpec.project)) ≠ ∅ := by decide

theorem honest_concurrent_control :
    OwnerOrdered 0 {grant, left, concurrentRevoke} ∧
    names 0 {grant, left, concurrentRevoke} = ∅ ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, concurrentRevoke, left].map CapabilityGroupSpec.project)) = ∅ ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, left, concurrentRevoke].map CapabilityGroupSpec.project)) ≠ ∅ := by decide

theorem honest_controls_wellFormed :
    WellFormed {grant, left, revokeLeft} ∧
    WellFormed {grant, left, concurrentRevoke} := by
  constructor <;> constructor <;> decide

/-- Explicit observed overwrite IDs permit concurrent names; the independent
specification therefore avoids the unrelated scalar-register obstruction. -/
theorem multivalue_control :
    names 0 {grant, left, right} = {7,8} ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, left, right].map CapabilityGroupSpec.project)) = {7,8} ∧
    CapabilityGroupSpec.names (CapabilityGroupSpec.run 0
      ([grant, left, right].map CapabilityGroupSpec.project)) ≠ {8} := by decide

def required (a b : Op Event) : Prop :=
  (a = wrap grant ∧ (b = wrap left ∨ b = wrap right)) ∨
  (a = wrap left ∧ b = wrap revokeLeft) ∨
  (a = wrap right ∧ b = wrap revokeRight)

instance requiredDecidable : DecidableRel required := fun _ _ => by unfold required; infer_instance

instance respectsRequiredDecidable (π : List (Op Event)) : Decidable (respects π required) := by
  unfold respects
  infer_instance

/-- All 120 event orders are checked. Four unavoidable specification conflict
edges force one write to precede the first revocation. Revocation then preserves
that accepted name. The expected empty source result is hand-derived. -/
theorem all_permutations_nonempty :
    ∀ π ∈ allEvents.permutations', respects π required →
      CapabilityGroupSpec.names (CapabilityGroupSpec.run 0 (π.map project)) ≠ ∅ := by decide

theorem grant_left_conflict :
    ¬ (CapabilityGroupSpec.spec 0).Commutes (project (wrap grant)) (project (wrap left)) := by
  intro h
  have hp : (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap left))] ++
        [.query () {7}]) := by
    apply (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap left)] {7}).mpr
    decide
  have hn : ¬ (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap left)), .update (project (wrap grant))] ++
        [.query () {7}]) := by
    intro hn
    have hh := (CapabilityGroupSpec.accepts_iff 0 [project (wrap left), project (wrap grant)] {7}).mp hn
    exact (by decide : ({7} : Finset Name) ≠ ∅) hh
  exact hn ((h [] [.query () {7}]).mp hp)

theorem grant_right_conflict :
    ¬ (CapabilityGroupSpec.spec 0).Commutes (project (wrap grant)) (project (wrap right)) := by
  intro h
  have hp : (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap right))] ++
        [.query () {8}]) := by
    apply (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap right)] {8}).mpr
    decide
  have hn : ¬ (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap right)), .update (project (wrap grant))] ++
        [.query () {8}]) := by
    intro hn
    have hh := (CapabilityGroupSpec.accepts_iff 0 [project (wrap right), project (wrap grant)] {8}).mp hn
    exact (by decide : ({8} : Finset Name) ≠ ∅) hh
  exact hn ((h [] [.query () {8}]).mp hp)

theorem left_revoke_conflict :
    ¬ (CapabilityGroupSpec.spec 0).Commutes (project (wrap left)) (project (wrap revokeLeft)) := by
  intro h
  have hp : (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap left)),
         .update (project (wrap revokeLeft))] ++ [.query () {7}]) := by
    apply (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap left), project (wrap revokeLeft)] {7}).mpr
    decide
  have hn : ¬ (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap revokeLeft)),
         .update (project (wrap left))] ++ [.query () {7}]) := by
    intro hn
    have hh := (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap revokeLeft), project (wrap left)] {7}).mp hn
    exact (by decide : ({7} : Finset Name) ≠ ∅) hh
  exact hn ((h [.update (project (wrap grant))] [.query () {7}]).mp hp)

theorem right_revoke_conflict :
    ¬ (CapabilityGroupSpec.spec 0).Commutes (project (wrap right)) (project (wrap revokeRight)) := by
  intro h
  have hp : (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap right)),
         .update (project (wrap revokeRight))] ++ [.query () {8}]) := by
    apply (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap right), project (wrap revokeRight)] {8}).mpr
    decide
  have hn : ¬ (CapabilityGroupSpec.spec 0).admits
      ([.update (project (wrap grant)), .update (project (wrap revokeRight)),
         .update (project (wrap right))] ++ [.query () {8}]) := by
    intro hn
    have hh := (CapabilityGroupSpec.accepts_iff 0 [project (wrap grant), project (wrap revokeRight), project (wrap right)] {8}).mp hn
    exact (by decide : ({8} : Finset Name) ≠ ∅) hh
  exact hn ((h [.update (project (wrap grant))] [.query () {8}]).mp hp)

private def versions (v : Version) : Option ((datatype 0).State × Set (Op Event)) :=
  if v = 0 then some (∅, ∅) else if v = 1 then some (log, eventSet) else none
private def heads (r : Replica) : Option Version := if r ≤ 5 then some 1 else none
private def parents (v : Version) : List Version := if v = 1 then [0] else []
private def visibility (a b : Op Event) : Prop :=
  a ∈ allEvents ∧ b ∈ allEvents ∧ before a.op b.op

private theorem heads_events {r : Replica} {E : Set (Op Event)}
    (h : headEventsFrom versions heads r = some E) : E = eventSet := by
  by_cases hr : r ≤ 5
  · simpa [headEventsFrom, versions, heads, hr] using h.symm
  · simp [headEventsFrom, heads, hr] at h

private theorem versions_cases {v : Version} {s : (datatype 0).State}
    {E : Set (Op Event)} (h : versions v = some (s,E)) :
    (v = 0 ∧ s = ∅ ∧ E = ∅) ∨ (v = 1 ∧ s = log ∧ E = eventSet) := by
  by_cases h0 : v = 0
  · simp [versions, h0] at h; exact .inl ⟨h0,h.1.symm,h.2.symm⟩
  · by_cases h1 : v = 1
    · simp [versions, h1] at h; exact .inr ⟨h1,h.1.symm,h.2.symm⟩
    · simp [versions, h0, h1] at h

private theorem parents_rank : ∀ v p, p ∈ parents v → p < v := by
  intro v p h
  simp [parents] at h
  rcases h with ⟨rfl,rfl⟩
  decide

/-- An actual Sal configuration satisfying every operational coherence field.
It is not claimed reachable under an actor=replica or single-owner certificate.
-/
def config : Configuration (datatype 0) where
  vis := visibility
  ver := versions
  head := heads
  parents := parents
  parents_lt := parents_rank
  ver_init := rfl
  head_alloc := by
    intro r v h
    by_cases hr : r ≤ 5
    · simp [heads, hr] at h; subst v; simp [versions]
    · simp [heads, hr] at h
  vis_src := by
    intro a b h
    exact ⟨0, eventSet, rfl, h.1⟩
  vis_tgt := by
    intro a b h
    exact ⟨0, eventSet, rfl, h.2.1⟩
  vis_causal := by
    intro a b r E h he _
    rw [heads_events he]
    exact h.1
  timestamps_distinct := by
    intro a b r E r' E' he ha he' hb hn
    change a ∈ E at ha
    change b ∈ E' at hb
    rw [heads_events he] at ha
    rw [heads_events he'] at hb
    simp only [eventSet, Set.mem_setOf_eq, allEvents, List.mem_cons,
      List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first | exact (hn rfl).elim | decide
  causal_mono := by
    intro a b h
    rcases h with ⟨ha,hb,h⟩
    simp only [allEvents, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first | decide | exact False.elim (by simp [wrap, Op.op, before, grant,
          left, right, revokeLeft, revokeRight] at h)
  vis_total_same_replica := by
    intro a b r E r' E' he ha he' hb hn hr
    change a ∈ E at ha
    change b ∈ E' at hb
    rw [heads_events he] at ha
    rw [heads_events he'] at hb
    simp only [eventSet, Set.mem_setOf_eq, allEvents, List.mem_cons,
      List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first | exact (hn rfl).elim | exact False.elim (by simp [wrap, grant,
        left, right, revokeLeft, revokeRight] at hr)
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET hg hv1 hv2 hvT
    rcases versions_cases hv1 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
      rcases versions_cases hv2 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
      rcases versions_cases hvT with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
    all_goals first
      | solve | simp
      | solve | have hh := reaches_le parents_rank hg.1; norm_num at hh
      | solve | have hh := reaches_le parents_rank hg.2.1; norm_num at hh
      | solve | have hh := reaches_le parents_rank
                  (hg.2.2 1 .refl .refl); norm_num at hh

private theorem required_specVisibility {a b : Op Event} (h : required a b) :
    projectedSpecVisibility project (CapabilityGroupSpec.spec 0) config.replayContext a b := by
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨by change visibility _ _; unfold visibility; decide, grant_left_conflict⟩
  · exact ⟨by change visibility _ _; unfold visibility; decide, grant_right_conflict⟩
  · exact ⟨by change visibility _ _; unfold visibility; decide, left_revoke_conflict⟩
  · exact ⟨by change visibility _ _; unfold visibility; decide, right_revoke_conflict⟩

private theorem permutation_of_enumeration {π : List (Op Event)}
    (h : listPermOf π eventSet) : π.Perm allEvents := by
  apply (List.perm_ext_iff_of_nodup h.1 (by decide)).mpr
  exact h.2

/-- The stronger criterion fails for every possible sequential witness,
despite using an observed-overwrite MVR rather than a single-name register.
-/
theorem not_specificationRA :
    ¬ ProjectedSpecificationRALinearizable (datatype 0) policy project
      (CapabilityGroupSpec.spec 0) config := by
  intro h
  obtain ⟨π,hp,_,hs,ha⟩ := h 0 1 log eventSet rfl rfl ()
  have order : respects π required := hs.imp (by
    intro a b hn hreq
    exact hn (required_specVisibility hreq))
  have neq := all_permutations_nonempty π
    (List.mem_permutations'.mpr (permutation_of_enumeration hp)) order
  have answer : (CapabilityGroupSpec.spec 0).admits
      ((π.map project).map SeqLabel.update ++ [.query () (names 0 log)]) := by
    simpa only [projectedLabels, List.map_map, datatype] using ha
  exact neq (((CapabilityGroupSpec.accepts_iff 0 (π.map project) (names 0 log)).mp
    answer).symm.trans source_empty)

theorem raw_updates_commute (a b : Op Event) :
    (datatype 0).toUpdateSig.commutes a b := by
  intro s
  exact Finset.insert_comm _ _ _

private theorem no_paper_order (a b : Op Event) :
    ¬ paperOrder policy config.replayContext eventSet a b := by
  rintro (⟨_,hn⟩ | ⟨_,_,hp,_⟩)
  · exact hn (raw_updates_commute a b)
  · exact hp

def literalWitness : List (Op Event) :=
  [wrap grant, wrap revokeLeft, wrap revokeRight, wrap left, wrap right]

/-- Actual literal Sal RA succeeds: commuting raw insertion removes all
visibility edges from paperOrder. It places both revokes before the writes.
This is a checked classification of the criterion, not a failure theorem.
-/
theorem literalRA :
    EventRALinearizable (datatype 0) policy
      ((CapabilityGroupSpec.spec 0).withInputs project) config := by
  intro r v s E _ hv q
  rcases versions_cases hv with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨[], ⟨by simp, by simp⟩, by simp [respects], by
      cases q
      change (CapabilityGroupSpec.spec 0).admits [.query () (names 0 ∅)]
      exact (CapabilityGroupSpec.accepts_iff 0 [] ∅).mpr (by decide)⟩
  · refine ⟨literalWitness, ?_, ?_, ?_⟩
    · constructor
      · decide
      · intro e
        simp [literalWitness, eventSet, allEvents, or_comm, or_left_comm, or_assoc]
    · exact List.pairwise_of_forall (fun a b => no_paper_order b a)
    · cases q
      change (CapabilityGroupSpec.spec 0).admits
        ((literalWitness.map project).map SeqLabel.update ++ [.query () (names 0 log)])
      apply (CapabilityGroupSpec.accepts_iff 0 (literalWitness.map project) _).mpr
      decide

/-- The same witness also inhabits the repository's original operation-label
`RALinearizable` definition, using the explicit application-input projection.
-/
theorem literal_operationRA :
    RALinearizable (datatype 0) policy
      ((CapabilityGroupSpec.spec 0).withInputs CapabilityGroupSpec.project) config := by
  intro r v s E hh hv q
  obtain ⟨π,hp,ho,ha⟩ := literalRA r v s E hh hv q
  refine ⟨π,hp,ho,?_⟩
  simpa only [HistorySpec.withInputs, projectedLabels, projectedUpdates,
    List.map_append, List.map_cons, List.map_nil, List.map_map,
    SeqLabel.mapUpdate, project] using ha

/-- PASS+FAIL: the same source snapshot passes the literal criterion and
fails its stronger specification-conflict variant. -/
theorem criterion_boundary :
    RALinearizable (datatype 0) policy
      ((CapabilityGroupSpec.spec 0).withInputs CapabilityGroupSpec.project) config ∧
    ¬ ProjectedSpecificationRALinearizable (datatype 0) policy project
      (CapabilityGroupSpec.spec 0) config := ⟨literal_operationRA, not_specificationRA⟩

#print axioms criterion_boundary

end Sal.MRDTs.Paper1.CapabilityGroupBridge
