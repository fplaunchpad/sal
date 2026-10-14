import Sal.MRDTs.Paper1.CertifiedFugueInvariantReplay
import Sal.MRDTs.Paper1.SplitPolicy
import Sal.MRDTs.Paper1.FugueMaxNaturalHistory
import Sal.MRDTs.Paper1.HistoryInputs
import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Paper1.FugueMaxNaturalOrder

set_option maxHeartbeats 2000000

/-! The unchanged FugueMax implementation satisfies the independent guarded
origin-list language. Its stored-version reconstruction uses the five VCs and
the common merge induction. Concrete commutation uses the existing independently
closed representation domain, rather than arbitrary malformed lists. Its client history is a permutation of original
events interpreted as stable left-origin insertions and named deletions. -/
namespace Sal.MRDTs.Paper1.FugueMaxNaturalCertificate
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxNaturalSequence
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.replayOrder

abbrev policy := CertifiedFugueInvariantReplay.policy

def invariant (Γ : Sal.EmbedRGA.OrderedPrefixCode) (C : Configuration (datatype Γ)) : State → Prop :=
  CertifiedFugueInvariant.Valid Γ C.replayContext

def project (e : Op Payload) : Action := ofMessage (recordOf e)

/-- The natural Action language remains public; the event language is its
exact pullback along the message's client intent, with no concrete replay. -/
def eventSpec : HistorySpec (Op Payload) Unit (List Nat) := spec.withInputs project

theorem project_surjective : Function.Surjective project := by
  intro action
  cases action with
  | insertAfter id left => exact ⟨(id,0,⟨.ins 0 .R,left,none,[]⟩),rfl⟩
  | deleteID id => exact ⟨(0,0,⟨.del id,0,none,[]⟩),rfl⟩

theorem commutes_iff (a b : Op Payload) :
    eventSpec.Commutes a b ↔ spec.Commutes (project a) (project b) :=
  HistorySpec.withInputs_commutes_iff spec project project_surjective a b

theorem version_witness_noninterleaving (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (generation Γ) C)
    {v : Version} {state : State} {events : Set (Op Payload)}
    (version : C.ver v = some (state,events)) (q : Unit) :
    ∃ replay : List (Op Payload), listPermOf replay events ∧
      respects replay (InvariantOrder.order (invariant Γ C) policy C.replayContext events) ∧
      respects replay (projectedSpecVisibility project spec C.replayContext) ∧
      spec.admits (projectedLabels (D := datatype Γ) project replay ++ [.query q ((datatype Γ).query state q)]) ∧
      MaxNonInterleavingM Γ (replay.map recordOf) := by
  have good := CertifiedFugueVCExecution.canonicalConfig Γ execution
  obtain ⟨ops,enumerates,ordered,fold⟩ := good.canonical v state events version
  have support := good.version_events_supported v state events version
  have closed := good.version_events_causal v state events version
  obtain ⟨replay,perm,births,visibility,accepted⟩ :=
    FugueMaxNaturalHistory.natural_witness C execution.mintHonest
      (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl
      ops events enumerates support closed ordered
  have replaySupported : ∀ e ∈ replay, e ∈ C.events :=
    fun e member => support e ((perm.2 e).mp member)
  have replayClosed : ∀ a b, C.vis a b → b ∈ replay → a ∈ replay := by
    intro a b ab member
    exact (perm.2 a).mpr (closed a b ab ((perm.2 b).mp member))
  obtain ⟨inv,slc,bk⟩ := invariants_of_mint C execution.mintHonest
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl replay perm.1 replaySupported replayClosed
  have order := FugueMaxNaturalOrder.respects_order C execution.mintHonest
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl replay replaySupported inv births events
  refine ⟨replay,perm,order,visibility,?_,
    forwardNIM_of_inv inv slc,backwardNIM_of_inv inv slc bk,sameOriginLowFirst_of_KInv inv⟩
  cases q
  rw [← fold,rawFold_records]
  exact accepted

theorem version_witness (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (generation Γ) C)
    {v : Version} {state : State} {events : Set (Op Payload)}
    (version : C.ver v = some (state,events)) (q : Unit) :
    ∃ replay : List (Op Payload), listPermOf replay events ∧
      respects replay (InvariantOrder.order (invariant Γ C) policy C.replayContext events) ∧
      respects replay (projectedSpecVisibility project spec C.replayContext) ∧
      spec.admits (projectedLabels (D := datatype Γ) project replay ++ [.query q ((datatype Γ).query state q)]) := by
  obtain ⟨replay,perm,order,visibility,accepted,_⟩ :=
    version_witness_noninterleaving Γ execution version q
  exact ⟨replay,perm,order,visibility,accepted⟩

theorem versions (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (generation Γ) C) :
    InvariantOrder.VersionsRA (datatype Γ) (invariant Γ C) policy eventSpec C := by
  intro v state events version q
  obtain ⟨replay,perm,order,visibility,accepted⟩ := version_witness Γ execution version q
  refine ⟨replay,perm,order,?_,?_⟩
  · apply visibility.imp
    intro a b noedge edge
    apply noedge
    exact ⟨edge.1,(commutes_iff b a).not.mp edge.2⟩
  · simpa only [eventSpec,HistorySpec.withInputs,projectedLabels,List.map_append,
      List.map_cons,List.map_nil,List.map_map,SeqLabel.mapUpdate,Function.comp_def] using accepted

/-- The existing nonvacuous source domain and implementation replay laws are
part of the package; natural history soundness does not redefine validity. -/
structure Correct (Γ : Sal.EmbedRGA.OrderedPrefixCode) (C : Configuration (datatype Γ)) : Prop where
  closed : InvariantOrder.Closed (datatype Γ) C.replayContext (invariant Γ C)
  stored_valid : ∀ v state events, C.ver v = some (state,events) → invariant Γ C state
  replay : ∀ v state events, C.ver v = some (state,events) →
    SplitPolicy.Invariant.RestrictedLaws (CertifiedFugueInvariantReplay.scope Γ C events)
      (invariant Γ C) policy ∧
    InvariantReplay.Canonical (CertifiedFugueInvariantReplay.scope Γ C events)
      (invariant Γ C) policy (datatype Γ).init state
  versions : InvariantOrder.VersionsRA (datatype Γ) (invariant Γ C) policy eventSpec C

theorem correct (Γ : Sal.EmbedRGA.OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (execution : CertifiedExecution (datatype Γ) (generation Γ) C) : Correct Γ C :=
  ⟨CertifiedFugueInvariant.closed_of_execution Γ execution,
    fun _ _ _ stored => CertifiedFugueInvariant.stored_valid Γ execution stored,
    fun _ _ _ stored =>
      ⟨SplitPolicy.Invariant.RestrictedLaws.ofExisting (CertifiedFugueInvariantReplay.laws Γ execution stored),
        CertifiedFugueInvariantReplay.storedCanonical Γ execution stored⟩,
    versions Γ execution⟩

theorem correctV (Γ : Sal.EmbedRGA.OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (reach : MintCertifiedReachV (datatype Γ) (canonicalVirtualMergeBase (datatype Γ)) (generation Γ) C) :
    Correct Γ C := correct Γ (.virtual reach)

theorem virtual_base_valid (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    {C : Configuration (datatype Γ)} (execution : CertifiedExecution (datatype Γ) (generation Γ) C)
    {v₁ v₂ : Version} {s₁ s₂ : State} {E₁ E₂ : Set (Op Payload)}
    (left : C.ver v₁ = some (s₁,E₁)) (right : C.ver v₂ = some (s₂,E₂)) :
    invariant Γ C (virtualMergeBaseState C v₁ v₂) :=
  CertifiedFugueInvariant.virtual_base_valid Γ execution left right

theorem certifiedV (Γ : Sal.EmbedRGA.OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (reach : MintCertifiedReachV (datatype Γ) (canonicalVirtualMergeBase (datatype Γ)) (generation Γ) C) :
    InvariantOrder.VersionsRA (datatype Γ) (invariant Γ C) policy eventSpec C :=
  (correctV Γ reach).versions

theorem certified (Γ : Sal.EmbedRGA.OrderedPrefixCode) {C : Configuration (datatype Γ)}
    (reach : MintCertifiedReach (datatype Γ) (generation Γ) C) :
    InvariantOrder.VersionsRA (datatype Γ) (invariant Γ C) policy eventSpec C :=
  (correct Γ (.ordinary reach)).versions

theorem executions (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (trace : List (Label (datatype Γ) × Configuration (datatype Γ)))
    (execution : (certifiedTS (datatype Γ) (generation Γ)).Execution (initConfig (datatype Γ)) trace) :
    Correct Γ (initConfig (datatype Γ)) ∧ ∀ entry ∈ trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited (Good := MintCertifiedReach (datatype Γ) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨correct Γ (.ordinary .init),fun entry member => correct Γ (.ordinary (reached entry member))⟩

theorem executionsV (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (trace : List (Label (datatype Γ) × Configuration (datatype Γ)))
    (execution : (certifiedTSV (datatype Γ) (generation Γ)).Execution (initConfig (datatype Γ)) trace) :
    Correct Γ (initConfig (datatype Γ)) ∧ ∀ entry ∈ trace, Correct Γ entry.2 := by
  have reached := ExecutionTrace.visited
    (Good := MintCertifiedReachV (datatype Γ) (canonicalVirtualMergeBase (datatype Γ)) (generation Γ))
    (fun _ _ _ pre step => .step pre step.1 step.2.1 step.2.2) execution .init
  exact ⟨correct Γ (.virtual .init),fun entry member => correct Γ (.virtual (reached entry member))⟩

#print axioms versions
#print axioms version_witness_noninterleaving
#print axioms correctV
#print axioms executionsV
end Sal.MRDTs.Paper1.FugueMaxNaturalCertificate

open Lean Elab Command in
elab "audit_fugue_natural_certificate" : command => do
  let env ← getEnv
  for root in [``Sal.MRDTs.Paper1.FugueMaxNaturalCertificate.correctV,
      ``Sal.MRDTs.Paper1.FugueMaxNaturalCertificate.certifiedV,
      ``Sal.MRDTs.Paper1.FugueMaxNaturalCertificate.executionsV] do
    let mut seen : NameSet := {}
    let mut pending := [root]
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      unless seen.contains name do
        seen := seen.insert name
        if name.toString.startsWith "Sal." || name.toString.startsWith "_private.Sal." then
          if let some info := env.find? name then
            pending := info.getUsedConstantsAsSet.toList ++ pending
    for required in [``Sal.MRDTs.Paper1.CertifiedFugueVC.mergeVCs,
        ``Sal.MRDTs.Paper1.ConcreteMRDT.Raw.join_at_sizes,
        ``Sal.MRDTs.Paper1.FugueMaxOriginForest.source_forest_exists,
        ``Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness.legal_run,
        ``Sal.MRDTs.Paper1.FugueMaxOriginEventWitness.source_insertion_permutation,
        ``Sal.MRDTs.Paper1.FugueMaxProjectedVisibility.respects_projected_visibility] do
      unless seen.contains required do
        throwError "{root} does not consume {required}"
    let axioms ← liftCoreM <| Lean.collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
  logInfo "FugueMax natural certificates consume the five VCs, common merge induction, source forest and legal replay; only standard logical axioms."

audit_fugue_natural_certificate
