import Sal.MRDTs.Instances.CapabilityGroupProtocol
import Sal.MRDTs.Instances.CapabilityGroupOwnerRefinement
import Sal.MRDTs.Paper1.ProjectedCriterion
import Sal.MRDTs.Paper1.SplitSoundness

namespace Sal.MRDTs.Instances.CapabilityGroup.Certificate
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open OwnerLinearization OwnerRefinement

abbrev project (event : Op Event) : CapabilityGroupSpec.Input := CapabilityGroupSpec.project event.op

/-- The full concrete-event alphabet drives the same independent ordinary ACL;
framework timestamp/replica metadata has no abstract ACL meaning. -/
def eventMachine (owner : Actor) : DeterministicSpec (Op Event) Unit (Finset Name) where
  State := CapabilityGroupSpec.Store
  initial := {}
  update store event := CapabilityGroupSpec.update owner store (project event)
  query store _ := CapabilityGroupSpec.names store

def eventSpec (owner : Actor) := (eventMachine owner).toSpec

def projectLabel : SeqLabel (Op Event) Unit (Finset Name) →
    SeqLabel CapabilityGroupSpec.Input Unit (Finset Name)
  | .update event => .update (project event)
  | .query query answer => .query query answer

/-- Equivalence holds for arbitrary interleaved sequential histories, not only
for the update-prefix/query shape used by the RA theorem. -/
theorem runs_projected (owner : Actor) (labels : List (SeqLabel (Op Event) Unit (Finset Name)))
    (start finish : CapabilityGroupSpec.Store) :
    Runs (eventMachine owner).machine.transition start labels finish ↔
      Runs (CapabilityGroupSpec.machine owner).machine.transition start (labels.map projectLabel) finish := by
  induction labels generalizing start with
  | nil => constructor <;> intro h <;> cases h <;> exact .nil _
  | cons label labels ih =>
    constructor
    · intro h
      cases h with
      | cons hstep htail =>
        apply Runs.cons (m := _)
        · cases label <;> exact hstep
        · exact (ih _).mp htail
    · intro h
      cases h with
      | cons hstep htail =>
        apply Runs.cons (m := _)
        · cases label <;> exact hstep
        · exact (ih _).mpr htail

theorem event_spec_projects (owner : Actor) (labels : List (SeqLabel (Op Event) Unit (Finset Name))) :
    (eventSpec owner).admits labels ↔
      (CapabilityGroupSpec.spec owner).admits (labels.map projectLabel) := by
  change (∃ finish, Runs (eventMachine owner).machine.transition {} labels finish) ↔
    ∃ finish, Runs (CapabilityGroupSpec.machine owner).machine.transition {} (labels.map projectLabel) finish
  exact exists_congr fun finish => runs_projected owner labels {} finish

/-- Lift a payload enumeration through an injective concrete representation.
The chosen concrete events, not newly invented wrappers, enumerate E. -/
theorem lift_enumeration {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (E : Set α) (π : List β) (hn : π.Nodup)
    (hm : ∀ b, b ∈ π ↔ ∃ a ∈ E, f a = b)
    (hi : ∀ a ∈ E, ∀ b ∈ E, f a = f b → a = b) :
    ∃ ρ : List α, listPermOf ρ E ∧ ρ.map f = π := by
  classical
  let choose (b : {b // b ∈ π}) : α := Classical.choose ((hm b.val).mp b.property)
  have chosen : ∀ b, choose b ∈ E ∧ f (choose b) = b.val :=
    fun b => Classical.choose_spec ((hm b.val).mp b.property)
  refine ⟨π.attach.map choose,⟨?_,?_⟩,?_⟩
  · apply hn.attach.map
    intro a b hab
    apply Subtype.ext
    exact (chosen a).2.symm.trans ((congrArg f hab).trans (chosen b).2)
  · intro a
    constructor
    · intro ha
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
      exact (chosen b).1
    · intro ha
      have hm' : f a ∈ π := (hm (f a)).mpr ⟨a,ha,rfl⟩
      let b : {b // b ∈ π} := ⟨f a,hm'⟩
      have hsame : choose b = a := hi _ (chosen b).1 a ha (chosen b).2
      exact List.mem_map.mpr ⟨b,by simp,hsame⟩
  · rw [List.map_map]
    have hmaps : (f ∘ choose) = Subtype.val := by
      funext b
      exact (chosen b).2
    rw [hmaps,List.attach_map_subtype_val]

/-- The source's strict-index form entails the framework's no-backward-edge
form. Duplicate-free coverage is retained explicitly. -/
theorem respects_of_indices {α : Type} [DecidableEq α] {π : List α}
    (hn : π.Nodup) {R : α → α → Prop}
    (hr : ∀ a ∈ π, ∀ b ∈ π, R a b → π.idxOf a < π.idxOf b) : respects π R := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij hback
  have hbad := hr π[j] (List.getElem_mem hj) π[i] (List.getElem_mem hi) hback
  rw [hn.idxOf_getElem j hj,hn.idxOf_getElem i hi] at hbad
  omega

theorem payload_injective {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    (C : Configuration (Protocol.D owner))
    (honest : MintHonest (Protocol.D owner) (Protocol.issuance owner principal ownerReplica).CanIssue C)
    {a b : Op Event} (ha : a ∈ C.events) (hb : b ∈ C.events) (same : a.op = b.op) : a = b := by
  apply Protocol.event_time_injective owner C ha hb
  rw [← (Protocol.event_guard C honest ha).1,← (Protocol.event_guard C honest hb).1,same]

theorem fold_eq_represented {owner : Actor} (C : Configuration (Protocol.D owner))
    {E : Set (Op Event)} {state : State}
    (hrep : Protocol.representation owner C.replayContext E state)
    {ρ : List (Op Event)} (hρ : listPermOf ρ E) :
    applySeq (Protocol.D owner).toUpdateSig (Protocol.D owner).init ρ = state := by
  ext payload
  rw [Protocol.fold_mem,Protocol.represented_mem owner C.replayContext E state hrep]
  exact exists_congr fun event => and_congr (hρ.2 event) Iff.rfl

/-- The same concrete-event witness preserves full visibility and produces
exactly the independent ordinary ACL answer. -/
theorem represented_witness {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    (C : Configuration (Protocol.D owner))
    (honest : MintHonest (Protocol.D owner) (Protocol.issuance owner principal ownerReplica).CanIssue C)
    {E : Set (Op Event)} {state : State}
    (hrep : Protocol.representation owner C.replayContext E state)
    (hs : WellFormed state) (hl : LocallyAdmitted owner state) (ho : OwnerOrdered owner state) :
    ∃ ρ : List (Op Event), listPermOf ρ E ∧ respects ρ C.vis ∧
      applySeq (Protocol.D owner).toUpdateSig (Protocol.D owner).init ρ = state ∧
      CapabilityGroupSpec.names (CapabilityGroupSpec.run owner (ρ.map project)) = names owner state := by
  have hmem : ∀ p, p ∈ canonical owner state ↔ ∃ e ∈ E, e.op = p := by
    intro p
    rw [mem_canonical,Protocol.represented_mem owner C.replayContext E state hrep]
  obtain ⟨ρ,hρ,hmap⟩ := lift_enumeration Op.op E (canonical owner state)
    (canonical_nodup owner state) hmem
    (fun a ha b hb hab => payload_injective C honest (hrep.1 a ha) (hrep.1 b hb) hab)
  have hsource := respects_of_indices (canonical_nodup owner state) (canonical_respects hs hl ho)
  have hlift : respects ρ (fun a b => before a.op b.op) := by
    have hh : (ρ.map Op.op).Pairwise (fun a b => ¬ before b a) := by
      rw [hmap]
      exact hsource
    exact List.pairwise_map.mp hh
  have hvis : respects ρ C.vis := hlift.imp_of_mem (by
    intro a b ha hb hno hv
    exact hno ((Protocol.before_iff_visibility C honest
      (hrep.1 b ((hρ.2 b).mp hb)) (hrep.1 a ((hρ.2 a).mp ha))).mpr hv))
  refine ⟨ρ,hρ,hvis,fold_eq_represented C hrep hρ,?_⟩
  have hnames := run_names_eq_source hs hl (canonical_perm owner state)
    (canonical_respects hs hl ho) (canonical_adminPrefix hs hl ho)
  have hproj : ρ.map project = (canonical owner state).map CapabilityGroupSpec.project := by
    calc
      _ = (ρ.map Op.op).map CapabilityGroupSpec.project := by simp only [List.map_map]; rfl
      _ = _ := by rw [hmap]
  rw [hproj]
  exact hnames

theorem projected_admits_iff (owner : Actor) (ρ : List (Op Event)) (answer : Finset Name) :
    (CapabilityGroupSpec.spec owner).admits
      (projectedLabels (D := Protocol.D owner) project ρ ++ [.query () answer]) ↔
      answer = CapabilityGroupSpec.names (CapabilityGroupSpec.run owner (ρ.map project)) := by
  simpa only [projectedLabels,List.map_map,Function.comp_def] using
    CapabilityGroupSpec.accepts_iff owner (ρ.map project) answer

theorem event_admits_iff (owner : Actor) (ρ : List (Op Event)) (answer : Finset Name) :
    (eventSpec owner).admits
      (projectedLabels (D := Protocol.D owner) id ρ ++ [.query () answer]) ↔
      answer = CapabilityGroupSpec.names (CapabilityGroupSpec.run owner (ρ.map project)) := by
  change (eventMachine owner).toSpec.admits
    (DeterministicSpec.updateLabels ρ ++ [.query () answer]) ↔ _
  rw [(eventMachine owner).updates_query_iff]
  simp only [eventMachine,CapabilityGroupSpec.run,List.foldl_map]

theorem version_witnessV {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C)
    {v : Version} {state : State} {E : Set (Op Event)}
    (registered : C.ver v = some (state,E)) :
    ∃ ρ : List (Op Event), listPermOf ρ E ∧ respects ρ C.vis ∧
      applySeq (Protocol.D owner).toUpdateSig (Protocol.D owner).init ρ = state ∧
      CapabilityGroupSpec.names (CapabilityGroupSpec.run owner (ρ.map project)) = names owner state := by
  have hrep := (Protocol.replayConditions owner (Protocol.issuance owner principal ownerReplica)).representedVersions
    C reach v state E registered
  obtain ⟨hs,hl,ho⟩ := Protocol.registered_source C reach v state E registered
  exact represented_witness C reach.mintHonest hrep hs hl ho

/-- Every allocated version has one concrete witness preserving the paper order
and all visibility edges, hence independent specification-conflict visibility. -/
theorem projected_versionsV {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C) :
    ∀ v state E, C.ver v = some (state,E) → ∀ q,
      ∃ ρ : List (Op Event), listPermOf ρ E ∧
        respects ρ (paperOrder (commutingPolicy Event) C.replayContext E) ∧
        respects ρ (projectedSpecVisibility project (CapabilityGroupSpec.spec owner) C.replayContext) ∧
        (CapabilityGroupSpec.spec owner).admits
          (projectedLabels (D := Protocol.D owner) project ρ ++ [.query q ((Protocol.D owner).query state q)]) := by
  intro v state E hv q
  cases q
  obtain ⟨ρ,hp,hvis,_,hnames⟩ := version_witnessV reach hv
  refine ⟨ρ,hp,?_,?_,?_⟩
  · exact hvis.imp (fun {_ _} _ => paperOrder_false_of_all_commute (Protocol.all_comm owner) _ _ _ _)
  · exact hvis.imp (fun {_ _} hno edge => hno edge.1)
  · exact (projected_admits_iff owner ρ _).mpr hnames.symm

/-- The certificate retains full concrete-event inputs while consulting the
same independent ordinary ACL semantics through project. -/
theorem event_versionsV {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C) :
    ConcreteMRDT.VersionsWitness (commutingPolicy Event) (eventSpec owner) C := by
  intro v state E hv q
  cases q
  obtain ⟨ρ,hp,hvis,_,hnames⟩ := version_witnessV reach hv
  refine ⟨ρ,hp,?_,?_,?_⟩
  · exact hvis.imp (fun {_ _} _ => paperOrder_false_of_all_commute (Protocol.all_comm owner) _ _ _ _)
  · exact hvis.imp (fun {_ _} hno edge => hno edge.1)
  · exact (event_admits_iff owner ρ _).mpr hnames.symm

theorem projectedRAV {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C) :
    ProjectedSpecificationRALinearizable (Protocol.D owner) (commutingPolicy Event)
      project (CapabilityGroupSpec.spec owner) C := by
  intro r v state E _ hv q
  exact projected_versionsV reach v state E hv q

theorem projectedRA {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReach (Protocol.D owner) (Protocol.issuance owner principal ownerReplica) C) :
    ProjectedSpecificationRALinearizable (Protocol.D owner) (commutingPolicy Event)
      project (CapabilityGroupSpec.spec owner) C := projectedRAV reach.toV

theorem projectedExecutions (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica)
    (trace : List (Label (Protocol.D owner) × Configuration (Protocol.D owner)))
    (execution : (certifiedTS (Protocol.D owner) (Protocol.issuance owner principal ownerReplica)).Execution
      (initConfig (Protocol.D owner)) trace) :
    ProjectedSpecificationExecution (Protocol.D owner) (commutingPolicy Event)
      project (CapabilityGroupSpec.spec owner) (initConfig (Protocol.D owner)) trace :=
  projected_certified_executions (fun _ reach => projectedRA reach) trace execution

theorem projectedExecutionsV (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica)
    (trace : List (Label (Protocol.D owner) × Configuration (Protocol.D owner)))
    (execution : (certifiedTSV (Protocol.D owner) (Protocol.issuance owner principal ownerReplica)).Execution
      (initConfig (Protocol.D owner)) trace) :
    ProjectedSpecificationExecution (Protocol.D owner) (commutingPolicy Event)
      project (CapabilityGroupSpec.spec owner) (initConfig (Protocol.D owner)) trace :=
  projected_certified_executionsV (fun _ reach => projectedRAV reach) trace execution

private theorem toVirtual {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (execution : CertifiedExecution (Protocol.D owner) (Protocol.issuance owner principal ownerReplica) C) :
    MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C := by
  cases execution with
  | ordinary reach => exact reach.toV
  | virtual reach => exact reach

/-- Actual five-VC package plus an execution-scoped independent history bridge.
No global implementation/specification conflict-covering assumption is used. -/
noncomputable def conditions (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica) :
    ConcreteMRDT.ScopedVCConditions (commutingPolicy Event) (eventSpec owner)
      (Protocol.issuance owner principal ownerReplica) where
  toVCReplayConditions := Protocol.replayConditions owner (Protocol.issuance owner principal ownerReplica)
  history := by
    intro C execution v state E hv q
    have reach := toVirtual execution
    obtain ⟨ρ,hp,horder,hspec,hadmit⟩ := event_versionsV reach v state E hv q
    have hrep := (Protocol.replayConditions owner (Protocol.issuance owner principal ownerReplica)).representedVersions
      C reach v state E hv
    have hfold := fold_eq_represented C hrep hp
    exact ⟨ρ,hp,horder,hspec,by simpa only [hfold] using hadmit⟩

theorem eventRA {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReach (Protocol.D owner) (Protocol.issuance owner principal ownerReplica) C) :
    EventSpecificationRALinearizable (Protocol.D owner) (commutingPolicy Event) (eventSpec owner) C :=
  (event_versionsV reach.toV).heads

theorem eventRAV {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    {C : Configuration (Protocol.D owner)}
    (reach : MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C) :
    EventSpecificationRALinearizable (Protocol.D owner) (commutingPolicy Event) (eventSpec owner) C :=
  (event_versionsV reach).heads

theorem executions (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica)
    (trace : List (Label (Protocol.D owner) × Configuration (Protocol.D owner)))
    (execution : (certifiedTS (Protocol.D owner) (Protocol.issuance owner principal ownerReplica)).Execution
      (initConfig (Protocol.D owner)) trace) :
    ConcreteMRDT.ExecutionCorrect (commutingPolicy Event) (eventSpec owner) trace :=
  (conditions owner principal ownerReplica).executions trace execution

theorem executionsV (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica)
    (trace : List (Label (Protocol.D owner) × Configuration (Protocol.D owner)))
    (execution : (certifiedTSV (Protocol.D owner) (Protocol.issuance owner principal ownerReplica)).Execution
      (initConfig (Protocol.D owner)) trace) :
    ConcreteMRDT.ExecutionCorrect (commutingPolicy Event) (eventSpec owner) trace :=
  (conditions owner principal ownerReplica).executionsV trace execution

#print axioms conditions
#print axioms projectedRAV
#print axioms projectedExecutionsV
#print axioms executionsV

end Sal.MRDTs.Instances.CapabilityGroup.Certificate
