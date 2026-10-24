import Sal.MRDTs.Instances.NotionCoreRichSequentialRelation
import Sal.MRDTs.Instances.NotionCoreRichSequentialInputs
import Sal.MRDTs.Instances.NotionCoreRichProtocolTransport
import Sal.MRDTs.Instances.NotionCoreRichSequentialRefinement
import Sal.MRDTs.Instances.NotionCoreRichCanonicalIntegrity
import Sal.MRDTs.Instances.NotionCoreRichSequentialCoreErase

/-!
Complete rich-history refinement on the one selected canonical sequence.
The per-step simulations are derived from the actual source issuer and
captured version closure. Composition then yields independent direct-state
execution and actual query agreement, with no residual simulation premise.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichCanonicalHistory
open NotionCoreRichPayload (Transaction)
open NotionCoreRichSequential.Refinement (Related)
open NotionCoreRichSequential.Refinement

private theorem plain_replayed (pre : List Transaction) (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual) :
    NotionCoreMachine.replay {} (NotionCoreRichCoreProjection.edits pre) = some actual.core := by
  have projected := NotionCoreAtomicFormattingMachine.replay_core_projection {} pre
  simpa only [replayed,Option.map_some,NotionCoreRichPlainReach.eraseFormats_eq] using projected.symm

private theorem plain_edit_position (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (runs : List NotionRunAllocation.Run)
    (pre post : List Transaction) (transaction : Transaction) (payload : NotionCorePayload.Payload)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ transaction :: post)
    (isEdit : transaction.payload = .edit payload) :
    NotionCoreReconstruction.transactionsFor (NotionCoreRichPlainNetwork.erase network)
      (runs.filter (NotionCoreRichPlainNetwork.keep network)) =
        NotionCoreRichCoreProjection.edits pre ++ ⟨transaction.id,payload⟩ ::
          NotionCoreRichCoreProjection.edits post := by
  rw [NotionCoreRichPlainReach.transactionsFor_eq network reachable runs,position,
    NotionCoreRichCoreProjection.edits_append]
  simp [NotionCoreRichCoreProjection.edits,NotionCoreRichCoreProjection.project,isEdit]

private theorem lift_edit (transaction : Transaction) (payload : NotionCorePayload.Payload)
    (isEdit : transaction.payload = .edit payload)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State)
    (core : NotionCoreMachine.State) (after : NotionCoreRichSequential.State)
    (operation : NotionCoreMachine.applyTransaction actual.core ⟨transaction.id,payload⟩ = some core)
    (independent : NotionCoreRichSequential.coreBatch abstract
      ((NotionCoreMachineCommands.commands ⟨transaction.id,payload⟩).map
        NotionCoreSourceDocument.Command.semantic) = some after)
    (related : Related (NotionCoreRichSequential.Refinement.edited actual core) after) :
    ∃ next result, NotionCoreAtomicFormattingMachine.applyTransaction actual transaction = some next ∧
      Related next result ∧ NotionCoreRichSequentialInputs.applyTransaction abstract transaction = some result := by
  refine ⟨NotionCoreRichSequential.Refinement.edited actual core,after,?_,related,?_⟩
  · simp [NotionCoreAtomicFormattingMachine.applyTransaction,isEdit,operation,
      NotionCoreRichSequential.Refinement.edited]
  · simpa only [NotionCoreRichSequentialInputs.applyTransaction,NotionCoreRichSequentialInputs.command,
      isEdit,Option.bind_some,NotionCoreRichSequential.step] using independent

private theorem singleton_batch (abstract after : NotionCoreRichSequential.State)
    (command : NotionCoreSpec.Command)
    (one : NotionCoreRichSequential.coreStep abstract command = some after) :
    NotionCoreRichSequential.coreBatch abstract [command] = some after := by
  simp [NotionCoreRichSequential.coreBatch,one]

private theorem replay_append (state : NotionCoreAtomicFormattingMachine.State)
    (left right : List Transaction) :
    NotionCoreAtomicFormattingMachine.replay state (left ++ right) =
      (NotionCoreAtomicFormattingMachine.replay state left >>= fun next =>
        NotionCoreAtomicFormattingMachine.replay next right) := by
  induction left generalizing state with
  | nil => rfl
  | cons transaction rest ih =>
    simp only [List.cons_append,NotionCoreAtomicFormattingMachine.replay]
    cases one : NotionCoreAtomicFormattingMachine.applyTransaction state transaction <;> simp [ih]

/-- Every core-edit case uses the already proved honest plain protocol,
with annotation boundary integrity derived from the same rich source history. -/
theorem canonical_edit_batch_version (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (runs : List NotionRunAllocation.Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (transaction : Transaction) (payload : NotionCorePayload.Payload)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ transaction :: post)
    (isEdit : transaction.payload = .edit payload)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (related : Related actual abstract) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core ⟨transaction.id,payload⟩ = some core ∧
      NotionCoreRichSequential.coreBatch abstract
        ((NotionCoreMachineCommands.commands ⟨transaction.id,payload⟩).map
          NotionCoreSourceDocument.Command.semantic) = some after ∧ Related (edited actual core) after := by
  let plain := NotionCoreRichPlainNetwork.erase network
  have plainReach := NotionCoreRichPlainReach.erase_reachable reachable
  have plainClosed := NotionCoreRichPlainReach.erase_closed network runs closed
  have plainPosition := plain_edit_position network reachable runs pre post transaction payload position isEdit
  have plainReplay := plain_replayed pre actual replayed
  have supported := NotionCoreRichCanonicalIntegrity.supported_batches reachable runs pre
    (transaction :: post) position actual replayed
  have segments := NotionCoreRichCanonicalIntegrity.registered_segments reachable runs closed pre
    (transaction :: post) position actual replayed
  cases payload with
  | bootstrap atoms =>
    exact canonical_bootstrap_coreBatch plain plainReach _ plainClosed _ _ _ plainPosition
      actual abstract related plainReplay atoms rfl segments
  | create afterBlock =>
    obtain ⟨core,after,operation,one,nextRelated⟩ := canonical_create_coreStep plain plainReach _ plainClosed
      _ _ _ plainPosition actual abstract related plainReplay afterBlock rfl segments
    refine ⟨core,after,operation,?_,nextRelated⟩
    simpa [NotionCoreMachineCommands.commands,NotionCoreSourceDocument.Command.semantic] using
      singleton_batch abstract after _ one
  | insert block inst origin atoms =>
    have apart := NotionCoreRichCanonicalIntegrity.fresh_endpoints_insert reachable runs closed pre post
      transaction position actual replayed block inst origin atoms isEdit
    obtain ⟨core,after,operation,one,nextRelated⟩ := canonical_insert_coreStep plain plainReach _ plainClosed
      _ _ _ plainPosition actual abstract related plainReplay block inst origin atoms rfl supported apart
    refine ⟨core,after,operation,?_,nextRelated⟩
    simpa [NotionCoreMachineCommands.commands,NotionCoreSourceDocument.Command.semantic,
      NotionCoreMachineCommands.text,itemSlots] using singleton_batch abstract after _ one
  | erase block groups =>
    exact canonical_erase_coreBatch plain plainReach _ plainClosed _ _ _ plainPosition actual abstract
      related plainReplay block groups rfl supported
  | split block inst origin =>
    have apart := NotionCoreRichCanonicalIntegrity.fresh_endpoints_split reachable runs closed pre post
      transaction position actual replayed (NotionCoreMachine.blockName inst)
    exact canonical_split_coreBatch plain plainReach _ plainClosed _ _ _ plainPosition actual abstract
      related plainReplay block inst origin rfl segments supported apart
  | merge source inst stop =>
    obtain ⟨core,after,operation,one,nextRelated⟩ := canonical_merge_coreStep plain plainReach _ plainClosed
      _ _ _ plainPosition actual abstract related plainReplay source inst stop rfl
    refine ⟨core,after,operation,?_,nextRelated⟩
    simpa [NotionCoreMachineCommands.commands,NotionCoreSourceDocument.Command.semantic] using
      singleton_batch abstract after _ one

/-- Actual source replay and independent state evolution advance together on
each whole transaction. No different event order is chosen for the query. -/
theorem compose (all : List Transaction)
    (steps : ∀ pre suffix transaction, all = pre ++ transaction :: suffix →
      ∀ (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State),
      NotionCoreAtomicFormattingMachine.replay {} pre = some actual → Related actual abstract →
      ∃ next after, NotionCoreAtomicFormattingMachine.applyTransaction actual transaction = some next ∧
        Related next after ∧ NotionCoreRichSequentialInputs.applyTransaction abstract transaction = some after)
    (pre rest : List Transaction) (position : all = pre ++ rest)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (related : Related actual abstract) :
    ∃ final after, NotionCoreAtomicFormattingMachine.replay actual rest = some final ∧
      Related final after ∧ NotionCoreRichSequentialInputs.executeTransactions abstract rest = some after := by
  induction rest generalizing pre actual abstract with
  | nil => exact ⟨actual,abstract,rfl,related,rfl⟩
  | cons transaction rest ih =>
    obtain ⟨next,middle,operation,nextRelated,one⟩ :=
      steps pre rest transaction position actual abstract replayed related
    have nextReplayed : NotionCoreAtomicFormattingMachine.replay {} (pre ++ [transaction]) = some next := by
      rw [replay_append,replayed]
      simp [NotionCoreAtomicFormattingMachine.replay,operation]
    have nextPosition : all = (pre ++ [transaction]) ++ rest := by
      simpa only [List.append_assoc,List.singleton_append] using position
    obtain ⟨final,after,executed,finalRelated,independent⟩ :=
      ih (pre ++ [transaction]) nextPosition next middle nextReplayed nextRelated
    refine ⟨final,after,?_,finalRelated,?_⟩
    · simp [NotionCoreAtomicFormattingMachine.replay,operation,executed]
    · simp [NotionCoreRichSequentialInputs.executeTransactions,one,independent]

theorem initial_related : Related ({} : NotionCoreAtomicFormattingMachine.State)
    ({} : NotionCoreRichSequential.State) := by
  constructor
  · exact ⟨[],rfl,rfl⟩
  · intro inst
    simp [NotionCoreRichSequential.Refinement.Registered]
  · intro inst text found
    cases found
  · intro inst
    simp [NotionCoreFormattingPlanner.UniqueIds,NotionCoreAtomicFormattingMachine.instanceForest,
      NotionCoreAtomicFormattingMachine.plainState,NotionCoreFormattingMachine.instanceForest,
      NotionCoreMachine.getInstance,NotionCoreFormattingMachine.extract,NotionCoreOriginTree.preorder]
  · intro inst text found
    cases found

/-- An actual archived formatting request has supported boundaries and
retained physical providers in this canonical prefix. The source issuer,
closure and sorted header order supply every simulation premise. -/
theorem canonical_format_step_version
    (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (runs : List NotionRunAllocation.Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (transaction : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ transaction :: post)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (related : Related actual abstract)
    (parts : List NotionCoreRichPayload.Part) (value : Bool)
    (payload : transaction.payload = .format parts value) :
    ∃ next after, NotionCoreAtomicFormattingMachine.applyTransaction actual transaction = some next ∧
      Related next after ∧ NotionCoreRichSequentialInputs.applyTransaction abstract transaction = some after := by
  obtain ⟨⟨entry,member,rfl⟩,selected⟩ :=
    (NotionCoreRichProtocolEvents.transactionsFor_membership network runs transaction).mp
      (position ▸ List.mem_append_right pre (by simp))
  have compiled := NotionCoreRichProtocolFormatFacts.archived_compiles reachable entry member
  have ready := NotionCoreRichCanonicalIntegrity.format_parts_available reachable runs closed
    entry member selected pre post position actual replayed parts value payload
  have fresh := NotionCoreRichProtocolFormatFacts.replayed_batches_before reachable runs
    pre post entry.transaction position actual replayed
  cases mapped : parts.mapM NotionCoreRichSequentialInputs.region with
  | none => simp [NotionCoreRichSequentialInputs.command,payload,mapped] at compiled
  | some regions =>
    obtain ⟨next,after,operation,independent,nextRelated⟩ :=
      NotionCoreRichSequential.Refinement.format_transaction related entry.transaction parts regions value
        payload mapped ready fresh
    exact ⟨next,after,operation,nextRelated,independent⟩

theorem canonical_step_version (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (runs : List NotionRunAllocation.Run) (closed : NotionCoreRichProtocolEvents.Closed network runs)
    (pre post : List Transaction) (transaction : Transaction)
    (position : NotionCoreRichProtocolEvents.transactionsFor network runs = pre ++ transaction :: post)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : NotionCoreRichSequential.State)
    (replayed : NotionCoreAtomicFormattingMachine.replay {} pre = some actual)
    (related : Related actual abstract) :
    ∃ next after, NotionCoreAtomicFormattingMachine.applyTransaction actual transaction = some next ∧
      Related next after ∧ NotionCoreRichSequentialInputs.applyTransaction abstract transaction = some after := by
  cases payload : transaction.payload with
  | edit plain =>
    obtain ⟨core,after,operation,independent,nextRelated⟩ :=
      canonical_edit_batch_version network reachable runs closed pre post transaction plain position payload
        actual abstract replayed related
    exact lift_edit transaction plain payload actual abstract core after operation independent nextRelated
  | format parts value =>
    exact canonical_format_step_version network reachable runs closed pre post transaction position
      actual abstract replayed related parts value payload

/-- Complete direct-state rich refinement for every causally closed version
of an actual source archive. Replay success and all simulation invariants are
conclusions; the caller supplies only source reachability and causal closure. -/
theorem canonical_history_version (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network)
    (runs : List NotionRunAllocation.Run) (closed : NotionCoreRichProtocolEvents.Closed network runs) :
    ∃ actual abstract,
      NotionCoreAtomicFormattingMachine.replay {}
        (NotionCoreRichProtocolEvents.transactionsFor network runs) = some actual ∧
      Related actual abstract ∧
      NotionCoreRichSequentialInputs.executeTransactions {}
        (NotionCoreRichProtocolEvents.transactionsFor network runs) = some abstract := by
  exact compose (NotionCoreRichProtocolEvents.transactionsFor network runs)
    (fun pre post tx position actual abstract replayed related =>
      canonical_step_version network reachable runs closed pre post tx position actual abstract replayed related)
    [] (NotionCoreRichProtocolEvents.transactionsFor network runs) rfl {} {} rfl initial_related

/-- The ordinary sequential-history bridge is derived, not assumed by the
public protocol certificate. The complete same-event source history explains
the actual rich query and cannot explain an implementation failure instead. -/
theorem honest_history : NotionCoreRichProtocolTransport.HonestHistoryFor := by
  intro network reachable runs closed events payloads
  obtain ⟨actual,abstract,replayed,related,independent⟩ :=
    canonical_history_version network reachable runs closed
  obtain ⟨answer,rendered,observed⟩ := render_total_related related
  have eventRun : NotionCoreRichSequentialInputs.execute {} events = some abstract := by
    rw [NotionCoreRichSequentialInputs.execute_payloads,payloads]
    exact independent
  simpa only [replayed,Bind.bind,Option.bind,rendered,Option.map_some] using
    (NotionCoreRichSequentialInputs.updates_query_iff events
      (NotionCoreRichProtocolCarrier.neutral answer)).mpr ⟨abstract,eventRun,observed⟩

#print axioms canonical_step_version
#print axioms canonical_history_version
#print axioms honest_history

end Sal.MRDTs.Instances.NotionCoreRichCanonicalHistory
