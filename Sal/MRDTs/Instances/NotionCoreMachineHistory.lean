import Sal.MRDTs.Instances.NotionCoreMachineDocumentBootstrap
import Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
import Sal.MRDTs.Instances.NotionCoreSourceHistory

/-! Composition of actual canonical transaction simulations into the existing
atomic source history. All payload cases derive their source updates from honest reconstruction.
The resulting history theorem does not yet establish an RA event witness. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineHistory
open Sal.MRDTs.Paper1
open NotionCoreMachine
open NotionCorePayload (Transaction)
open NotionCoreMachineDocument (materializeDocument)
open NotionCoreMachineCommands (commands)

/-- The atomic history labels preserve one update per typed transaction. -/
def labels (txs : List Transaction) : List NotionCoreSourceHistory.Label :=
  txs.map (fun tx => .update (commands tx))

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- A composition lemma: each atomic simulation must be supplied at its actual
canonical position. No assertion of complete transaction simulation is made by
this lemma's premise. -/
theorem compose (all : List Transaction)
    (steps : ∀ pre suffix tx, all = pre ++ tx :: suffix →
      ∀ state document, replay {} pre = some state → materializeDocument state = some document →
      ∃ next after, applyTransaction state tx = some next ∧ materializeDocument next = some after ∧
        NotionCoreSourceDocument.Execution document (commands tx) after)
    (pre rest : List Transaction) (position : all = pre ++ rest)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document) :
    ∃ final after, replay state rest = some final ∧ materializeDocument final = some after ∧
      Runs NotionCoreSourceHistory.machine.transition document (labels rest) after := by
  induction rest generalizing pre state document with
  | nil => exact ⟨state,document,rfl,materialized,.nil document⟩
  | cons tx rest ih =>
    obtain ⟨next,middle,operation,projected,one⟩ := steps pre rest tx position state document replayed materialized
    have nextReplay : replay {} (pre ++ [tx]) = some next := by
      rw [replay_append,replayed]
      simp [replay,operation]
    have nextPosition : all = (pre ++ [tx]) ++ rest := by simpa [List.append_assoc] using position
    obtain ⟨final,after,executed,afterMat,history⟩ := ih (pre ++ [tx]) nextPosition next nextReplay middle projected
    refine ⟨final,after,?_,afterMat,?_⟩
    · simp [replay,operation,executed]
    · exact .cons one history

/-- Every payload of an honest canonical transaction executes and produces
its atomic source-history update. There are no residual per-payload guards. -/
theorem canonical_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (replayed : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document) :
    ∃ next after, applyTransaction state tx = some next ∧ materializeDocument next = some after ∧
      NotionCoreSourceDocument.Execution document (commands tx) after := by
  cases payload : tx.payload with
  | bootstrap atoms =>
    exact NotionCoreMachineDocumentBootstrap.canonical_bootstrap_source_execution network reachable peer
      pre suffix tx position state replayed document materialized atoms payload
  | create after =>
    simpa only [commands,payload] using NotionCoreMachineDocumentCreate.canonical_create_execution
      network reachable peer pre suffix tx position state replayed document materialized after payload
  | insert block inst origin atoms =>
    simpa only [commands,payload,NotionCoreMachineCommands.text] using
      NotionCoreMachineDocumentInsert.canonical_insert_execution network reachable peer pre suffix tx position
        state replayed document materialized block inst origin atoms payload
  | erase block inst targets =>
    simpa only [commands,payload] using NotionCoreMachineDocumentErase.canonical_erase_execution
      network reachable peer pre suffix tx position state replayed document materialized block inst targets payload
  | split block inst origin =>
    exact NotionCoreMachineDocumentSplit.canonical_split_execution network reachable peer pre suffix tx position
      state replayed document materialized block inst origin payload

/-- Honest per-peer reconstruction has an atomic source history on exactly
its canonical transaction list. Successful replay and projection are conclusions. -/
theorem honest_source_history (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session) :
    ∃ final document, NotionCoreReconstruction.reconstruct network peer = some final ∧
      materializeDocument final = some document ∧
      Runs NotionCoreSourceHistory.machine.transition []
        (labels (NotionCoreReconstruction.transactions network peer)) document := by
  exact compose (NotionCoreReconstruction.transactions network peer)
    (fun pre suffix tx position state document replayed materialized =>
      canonical_step network reachable peer pre suffix tx position state replayed document materialized)
    [] (NotionCoreReconstruction.transactions network peer) rfl {} rfl [] rfl

/-- Attach the actual renderer's answer to an established source history.
The same ordered updates are transported into the independent language; the
answer is derived from honest reconstruction and checked materialization. -/
theorem observed_history (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (document : NotionCoreSourceDocument.Document)
    (materialized : materializeDocument state = some document)
    (history : Runs NotionCoreSourceHistory.machine.transition []
      (labels (NotionCoreReconstruction.transactions network peer)) document) :
    ∃ answer, render state = some answer ∧
      NotionCoreHistory.spec.admits
        ((labels (NotionCoreReconstruction.transactions network peer)).map
          NotionCoreSourceHistory.semanticLabel ++ [.query () answer]) := by
  obtain ⟨checked,checkedReplay,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans reconstructed)
  subst checked
  have rendered := NotionCoreMachineDocument.materialized_render state part shape.1 shape.2.2 document materialized
  refine ⟨NotionCoreSpec.view (NotionCoreSourceDocument.project document),rendered,?_⟩
  have projected := NotionCoreSourceHistory.runs_sound history
  exact ⟨NotionCoreSourceDocument.project document,
    projected.append (.cons ⟨rfl,rfl⟩ (.nil _))⟩

/-- Every honest typed-core version returns an answer admitted by the
independent sequential specification on the same atomic transaction ordering.
This does not yet identify Sal event labels or discharge the RA order relation. -/
theorem honest_history (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session) :
    ∃ answer, (NotionCoreReconstruction.reconstruct network peer >>= render) = some answer ∧
      NotionCoreHistory.spec.admits
        ((labels (NotionCoreReconstruction.transactions network peer)).map
          NotionCoreSourceHistory.semanticLabel ++ [.query () answer]) := by
  obtain ⟨state,document,reconstructed,materialized,history⟩ := honest_source_history network reachable peer
  obtain ⟨answer,rendered,admitted⟩ := observed_history network reachable peer state reconstructed document materialized history
  exact ⟨answer,by simp [reconstructed,rendered],admitted⟩

#print axioms canonical_step
#print axioms honest_source_history
#print axioms honest_history

#print axioms observed_history

#print axioms compose
end Sal.MRDTs.Instances.NotionCoreMachineHistory
