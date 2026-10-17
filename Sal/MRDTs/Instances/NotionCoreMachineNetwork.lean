import Sal.MRDTs.Instances.NotionCoreMachineDelete
import Sal.MRDTs.Instances.NotionCoreReconstruction

/-! Positional requests execute against the peer's actual reconstructed document.
Successful issuance derives the earlier typed network guards. Reconstruction
and core deletion selection are partial: this is an admission connection, not
the missing theorem that every honest replay and valid request succeeds. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineNetwork
open NotionRunAllocation (Session)
open NotionCorePayload (BlockKey Payload Transaction)
open NotionCorePayloadNetwork (State)

inductive Request where
  | create (afterBlock : Option BlockKey)
  | insert (block : BlockKey) (index : Nat) (atoms : List Nat)
  | erase (block : BlockKey) (start stop : Nat)
  | split (block : BlockKey) (index : Nat)
  | merge (source : BlockKey)
  deriving DecidableEq, Repr

/-- Source early returns precede document reconstruction. Other empty clamped
ranges need actual visible character selection and are handled afterwards. -/
def Request.earlyNoop : Request → Bool
  | .insert _ _ atoms => atoms.isEmpty
  | .erase _ start stop => start == stop
  | _ => false

def prepareRequest (document : NotionCoreMachine.State) : Request → Option Payload
  | .create afterBlock => NotionCoreMachineClient.prepareCreate document afterBlock
  | .insert block index atoms => NotionCoreMachineClient.prepareInsert document block index atoms
  | .erase block start stop => NotionCoreMachineDelete.selectErase document block start stop
  | .split block index => NotionCoreMachineClient.prepareSplit document block index
  | .merge source => NotionCoreMachineClient.prepareMerge document source

/-- After the source early no-op checks, reconstruct the received version and select its actual
identities, then reserve the source transaction's whole item run. Empty requests
return none without changing the network or reserving a clock tick. -/
def issue (network : State) (session : Session) (request : Request) : Option State := do
  if request.earlyNoop then none else do
    let document ← NotionCoreReconstruction.reconstruct network session
    let payload ← prepareRequest document request
    let tx ← NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) session payload
    pure (NotionCorePayloadNetwork.emit network session payload tx)

theorem early_noop (network : State) (session : Session) (request : Request)
    (noop : request.earlyNoop = true) : issue network session request = none := by
  simp [issue, noop]

theorem prepared_references (network : State) (session : Session)
    (document : NotionCoreMachine.State)
    (accepted : NotionCoreReconstruction.reconstruct network session = some document)
    (request : Request) (payload : Payload)
    (prepared : prepareRequest document request = some payload) :
    ∀ address ∈ NotionCorePayloadNetwork.locatedReferences payload,
      NotionCorePayloadNetwork.Known network session address := by
  have received := NotionCoreReconstruction.transactions_received network session
  cases request with
  | create afterBlock =>
      cases afterBlock with
      | none =>
          simp [prepareRequest, NotionCoreMachineClient.prepareCreate] at prepared
          subst payload
          simp [NotionCorePayloadNetwork.locatedReferences]
      | some block =>
          simp only [prepareRequest, NotionCoreMachineClient.prepareCreate] at prepared
          split at prepared
          · simp only [Option.some.injEq] at prepared
            subst payload
            simp [NotionCorePayloadNetwork.locatedReferences]
          · contradiction
  | insert block index atoms =>
      exact NotionCoreMachineClient.prepared_insert_references
        network session _ document received accepted block index atoms payload prepared
  | erase block start stop =>
      exact NotionCoreMachineDelete.selectErase_references
        network session _ document received accepted block start stop payload prepared
  | split block index =>
      exact NotionCoreMachineClient.prepared_split_references
        network session _ document received accepted block index payload prepared
  | merge source =>
      simp only [prepareRequest, NotionCoreMachineClient.prepareMerge] at prepared
      split at prepared
      · cases last : ((NotionCoreMachine.visible document).take
            ((NotionCoreMachine.visible document).idxOf (NotionCoreMachine.blockName source))).getLast? with
        | none => simp [last] at prepared
        | some previous =>
          cases decoded : NotionCoreMachineClient.decodeBlock previous with
          | none => simp [last, decoded] at prepared
          | some target =>
            have same : Payload.merge source target = payload := by simpa [last, decoded] using prepared
            subst payload
            simp [NotionCorePayloadNetwork.locatedReferences]
      · contradiction

theorem prepared_creators (network : State) (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : Session) (document : NotionCoreMachine.State)
    (accepted : NotionCoreReconstruction.reconstruct network session = some document)
    (request : Request) (payload : Payload)
    (prepared : prepareRequest document request = some payload) :
    ∀ block ∈ NotionCoreCreatorNetwork.requiredBlocks payload,
      NotionCoreCreatorNetwork.KnownCreator network session block := by
  have received := NotionCoreReconstruction.transactions_received network session
  cases request with
  | create afterBlock =>
      exact NotionCoreMachineClient.prepared_create_creators
        network session _ document received accepted afterBlock payload prepared
  | insert block index atoms =>
      exact NotionCoreMachineClient.prepared_insert_creators
        network reachable session _ document received accepted block index atoms payload prepared
  | erase block start stop =>
      exact NotionCoreMachineDelete.selectErase_creators
        network reachable session _ document received accepted block start stop payload prepared
  | split block index =>
      exact NotionCoreMachineClient.prepared_split_creators
        network reachable session _ document received accepted block index payload prepared
  | merge source =>
      exact NotionCoreMachineClient.prepared_merge_creators
        network session _ document received accepted source payload prepared

/-- The concrete request transition supplies all of the old abstract admission
checks; it does not require the caller to prove those checks. -/
theorem issue_admitted {network next : State} (reachable : NotionCoreCreatorNetwork.Reach network)
    (session : Session) (request : Request) (issued : issue network session request = some next) :
    NotionCoreCreatorNetwork.Reach next := by
  have noSkip : request.earlyNoop = false := by
    cases skip : request.earlyNoop <;> simp_all [issue]
  cases current : NotionCoreReconstruction.reconstruct network session with
  | none => simp [issue, noSkip, current] at issued
  | some document =>
    cases selected : prepareRequest document request with
    | none => simp [issue, noSkip, current, selected] at issued
    | some payload =>
      cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) session payload with
      | none => simp [issue, noSkip, current, selected, reserved] at issued
      | some tx =>
        have equal : NotionCorePayloadNetwork.emit network session payload tx = next := by
          simpa [issue, noSkip, current, selected, reserved] using issued
        rw [← equal]
        exact .emit session payload tx reachable reserved
          (prepared_references network session document current request payload selected)
          (prepared_creators network reachable session document current request payload selected)

/-- Only concrete requests, receipt and clock gaps generate this network.
There is no supplied item-knowledge or creator-knowledge premise. -/
inductive Reach : State → Prop where
  | init : Reach NotionCorePayloadNetwork.initial
  | bootstrap (atoms : List Nat) : Reach (NotionCorePayloadNetwork.seeded atoms)
  | exchange {state : State} (target source : Session) :
      Reach state → Reach (NotionCorePayloadNetwork.exchange state target source)
  | gap {state : State} (session : Session) (ticks : Nat) :
      Reach state → Reach (NotionCorePayloadNetwork.gap state session ticks)
  | request {state next : State} (session : Session) (request : Request) :
      Reach state → issue state session request = some next → Reach next

/-- Reachability from positional requests derives all typed issuance invariants,
including located providers, creator availability, closure and fresh run IDs. -/
theorem creator_reachable {network : State} (reachable : Reach network) :
    NotionCoreCreatorNetwork.Reach network := by
  induction reachable with
  | init => exact .init
  | bootstrap atoms => exact .bootstrap atoms
  | exchange target source _ ih => exact .exchange target source ih
  | gap session ticks _ ih => exact .gap session ticks ih
  | request session request _ issued ih => exact issue_admitted ih session request issued

theorem issuance_reachable {network : State} (reachable : Reach network) :
    NotionCoreIssuance.Reach (NotionCorePayloadNetwork.forget network) :=
  NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable (creator_reachable reachable))

private def seeded : State := NotionCorePayloadNetwork.seeded [97,98]
private def inserted : Option State := issue seeded [65] (.insert .initial 1 [88,89])

/-- PASS+FAIL: positional selection chooses the existing a, reserves a two-item
run, and archives the resulting payload; empty insertion emits nothing. -/
theorem request_control :
    (inserted.map fun network => network.entries.head?.map (fun entry => entry.tx)) =
      some (some ⟨⟨3,[65]⟩,.insert .initial .initial (.item ⟨1,[65]⟩) [88,89]⟩) ∧
    (inserted.map fun network => network.entries.head?.map (fun entry => entry.tx.payload)) ≠
      some (some (.insert .initial .initial .start [88,89])) ∧
    inserted.map (fun network => (network.allocation.peers [65]).clock) = some 4 ∧
    issue seeded [65] (.insert .initial 1 []) = none := by
  simp only [inserted, issue, Request.earlyNoop, List.isEmpty_cons, List.isEmpty_nil,
    Bool.false_eq_true, if_false, if_true, seeded, NotionCoreReconstruction.reconstruct,
    NotionCoreReconstruction.transactions, NotionCorePayloadNetwork.seeded,
    List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  decide +kernel

#print axioms issue_admitted
#print axioms creator_reachable
#print axioms issuance_reachable
end Sal.MRDTs.Instances.NotionCoreMachineNetwork
