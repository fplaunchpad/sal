import Sal.MRDTs.Instances.NotionCoreMRDTArchive
import Sal.MRDTs.Instances.NotionCoreArchiveEvents

/-! Conditional Sal version witnesses using one honest archive and the same
source-sorted event list for carrier, visibility and independent query history.
Maintaining the archive coupling through arbitrary Sal issuance is not assumed
proved by this certificate. VC representation derives registered carrier equality. -/
namespace Sal.MRDTs.Instances.NotionCoreArchiveCertificate
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCorePayload (Transaction)
open NotionCorePayloadNetwork (State)
open NotionCoreMRDT (D)
open NotionCoreArchiveEvents (Event Coupling version witness)

/-- A single selected closed event set has one witness satisfying all the
public obligations, including the implementation's actual Option query. -/
theorem selected_witness (network : State) (reachable : NotionCoreMachineNetwork.Reach network)
    (C : ReplayContext D.toUpdateSig) (events : Set Event) (lift : Transaction → Event)
    (coupled : Coupling network C.events C.vis lift)
    (supported : events ⊆ C.events)
    (closed : ∀ left right, C.vis left right → right ∈ events → left ∈ events)
    (state : Finset Transaction)
    (stateImage : state = NotionCoreMRDTArchive.carrierFor network (version network events lift))
    (query : Unit) :
    ∃ history : List Event, listPermOf history events ∧
      respects history (paperOrder (commutingPolicy Transaction) C events) ∧
      respects history (projectedSpecVisibility id NotionCoreMRDT.spec C) ∧
      NotionCoreMRDT.spec.admits
        (projectedLabels (D := D) id history ++ [.query query (D.query state query)]) := by
  have archiveReach := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable reachable)
  have versionClosed := NotionCoreArchiveEvents.version_closed network archiveReach C.events events C.vis lift
    coupled closed
  obtain ⟨answer,observed,accepted⟩ := NotionCoreMRDTArchive.honest_carrier_history network reachable
    (version network events lift) versionClosed lift (by
      intro tx member
      obtain ⟨entry,entryMember,txEq,_⟩ := NotionCoreReconstruction.transactionsFor_received network _ tx member
      exact coupled.payload tx (List.mem_map.mpr ⟨entry,entryMember,txEq⟩))
  have visible := NotionCoreArchiveEvents.witness_respects network archiveReach C.events events C.vis lift coupled supported
  refine ⟨witness network events lift,
    NotionCoreArchiveEvents.witness_enumerates network archiveReach C.events events C.vis lift coupled supported,?_,?_,?_⟩
  · apply List.pairwise_of_forall
    intro a b
    exact paperOrder_false_of_all_commute NotionCoreMRDT.all_comm C events b a
  · exact visible.imp (fun {_ _} before edge => before edge.1)
  · cases query
    rw [stateImage,NotionCoreMRDT.query_observe,observed]
    simpa [NotionCoreMRDTArchive.eventHistory,NotionCoreMRDT.someLabel,
      projectedLabels,witness,List.map_append,List.map_map,Function.comp_def] using accepted

local instance : Membership Transaction D.toUpdateSig.State :=
  inferInstanceAs (Membership Transaction (Finset Transaction))
local instance : Insert Transaction D.toUpdateSig.State :=
  inferInstanceAs (Insert Transaction (Finset Transaction))

private theorem applySeq_member (initial : Finset Transaction) (history : List Event) (tx : Transaction) :
    tx ∈ (applySeq D.toUpdateSig initial history : Finset Transaction) ↔
      tx ∈ initial ∨ ∃ event ∈ history, event.op = tx := by
  induction history generalizing initial with
  | nil => simp [applySeq]
  | cons head rest ih =>
    change tx ∈ (applySeq D.toUpdateSig (insert head.op initial : Finset Transaction) rest : Finset Transaction) ↔ _
    rw [ih]
    simp only [Finset.mem_insert]
    constructor
    · rintro ((same | old) | ⟨event,member,payload⟩)
      · exact Or.inr ⟨head,by simp,same.symm⟩
      · exact Or.inl old
      · exact Or.inr ⟨event,List.mem_cons_of_mem _ member,payload⟩
    · rintro (old | ⟨event,member,payload⟩)
      · exact Or.inl (Or.inr old)
      · rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl (Or.inl payload.symm)
        · exact Or.inr ⟨event,member,payload⟩

/-- The VC-derived carrier representation and archive event bijection force
its finite state to be exactly the selected archive image. This removes a
state-output equality premise from the public certified version theorem. -/
theorem represented_state_image (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (C : ReplayContext D.toUpdateSig) (events : Set Event) (lift : Transaction → Event)
    (coupled : Coupling network C.events C.vis lift) (state : Finset Transaction)
    (represented : NotionCoreMRDT.representation C events state) :
    state = NotionCoreMRDTArchive.carrierFor network (version network events lift) := by
  obtain ⟨supported,history,enumerated,replayed⟩ := represented
  apply Finset.ext
  intro tx
  have stored : tx ∈ state ↔ ∃ event ∈ events, event.op = tx := by
    rw [← replayed,applySeq_member]
    have empty : D.init = (∅ : Finset Transaction) := rfl
    rw [empty]
    simp only [Finset.notMem_empty,false_or]
    constructor
    · rintro ⟨event,member,payload⟩
      exact ⟨event,(enumerated.2 event).mp member,payload⟩
    · rintro ⟨event,member,payload⟩
      exact ⟨event,(enumerated.2 event).mpr member,payload⟩
  rw [stored]
  change _ ↔ tx ∈ (NotionCoreReconstruction.transactionsFor network (version network events lift)).toFinset
  rw [List.mem_toFinset,NotionCoreArchiveEvents.selected_transactions network reachable events lift tx]
  constructor
  · rintro ⟨event,member,payload⟩
    have archived := NotionCoreArchiveEvents.event_payload network C.events C.vis lift coupled event
      (supported event member)
    exact ⟨payload ▸ archived.1,by rw [← payload,archived.2]; exact member⟩
  · rintro ⟨archived,member⟩
    exact ⟨lift tx,member,coupled.payload tx archived⟩

#print axioms represented_state_image

/-- Every registered version has the public Sal witness when its actual
carrier is the corresponding common-archive image. Metadata validity supplies
support and causal closure; no natural-history condition is a premise. -/
theorem versions_witness_of_states (network : State) (reachable : NotionCoreMachineNetwork.Reach network)
    (C : Configuration D) (metadata : CanonicalConfig C) (lift : Transaction → Event)
    (coupled : Coupling network C.events C.vis lift)
    (states : ∀ v state events, C.ver v = some (state,events) →
      state = NotionCoreMRDTArchive.carrierFor network (version network events lift)) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec C := by
  intro v state events registered query
  exact selected_witness network reachable C.replayContext events lift coupled
    (metadata.version_events_supported v state events registered)
    (metadata.version_events_causal v state events registered)
    state (states v state events registered) query

/-- Carrier VC induction supplies metadata validity for ordinary or canonical
recursive-base Sal executions. Common-archive coupling/state correspondence
are still explicit obligations, not consequences of the finite-store VCs. -/
theorem certified_versions_witness_of_states (network : State) (reachable : NotionCoreMachineNetwork.Reach network)
    {I : Issuance D} {C : Configuration D} (execution : CertifiedExecution D I C)
    (lift : Transaction → Event) (coupled : Coupling network C.events C.vis lift)
    (states : ∀ v state events, C.ver v = some (state,events) →
      state = NotionCoreMRDTArchive.carrierFor network (version network events lift)) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec C := by
  have metadata : CanonicalConfig C := execution.canonicalConfig
    (fun C _ => CommutingPort.automatedJoinAt (D := D) NotionCoreMRDT.all_comm NotionCoreMRDT.fiveVCs C.replayContext)
  exact versions_witness_of_states network reachable C metadata lift coupled states

/-- Public conditional certificate: finite-store VC representation derives
all registered state images, so the only source-specific input is one honest
archive coupled to the actual Sal events/visibility. This does not claim that
arbitrary local issuance preserves or constructs that coupling. -/
theorem certified_versions_witness (network : State) (reachable : NotionCoreMachineNetwork.Reach network)
    {I : Issuance D} {C : Configuration D} (execution : CertifiedExecution D I C)
    (lift : Transaction → Event) (coupled : Coupling network C.events C.vis lift) :
    VersionsWitness (commutingPolicy Transaction) NotionCoreMRDT.spec C := by
  have virtual : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C := by
    cases execution with
    | ordinary reachable => exact reachable.toV
    | virtual reachable => exact reachable
  apply certified_versions_witness_of_states network reachable execution lift coupled
  intro v state events registered
  exact represented_state_image network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    C.replayContext events lift coupled state
    (NotionCoreMRDT.represented_versions virtual v state events registered)

#print axioms selected_witness
#print axioms versions_witness_of_states
#print axioms certified_versions_witness
end Sal.MRDTs.Instances.NotionCoreArchiveCertificate
